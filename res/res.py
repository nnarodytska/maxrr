#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## rc2.py
##
##  Created on: Dec 2, 2017
##      Author: Alexey S. Ignatiev
##      E-mail: aignatiev@ciencias.ulisboa.pt
##

"""
    ===============
    List of classes
    ===============

    .. autosummary::
        :nosignatures:

        RC2
        RC2Stratified

    ==================
    Module description
    ==================

    An implementation of the RC2 algorithm for solving maximum
    satisfiability. RC2 stands for *relaxable cardinality constraints*
    (alternatively, *soft cardinality constraints*) and represents an
    improved version of the OLLITI algorithm, which was described in
    [1]_ and [2]_ and originally implemented in the `MSCG MaxSAT
    solver <https://reason.di.fc.ul.pt/wiki/doku.php?id=mscg>`_.

    Initially, this solver was supposed to serve as an example of a possible
    PySAT usage illustrating how a state-of-the-art MaxSAT algorithm could be
    implemented in Python and still be efficient. It participated in the
    `MaxSAT Evaluations 2018
    <https://maxsat-evaluations.github.io/2018/rankings.html>`_ and `2019
    <https://maxsat-evaluations.github.io/2019/rankings.html>`_ where,
    surprisingly, it was ranked first in two complete categories: *unweighted*
    and *weighted*. A brief solver description can be found in [3]_. A more
    detailed solver description can be found in [4]_.

    .. [1] António Morgado, Carmine Dodaro, Joao Marques-Silva.
        *Core-Guided MaxSAT with Soft Cardinality Constraints*. CP
        2014. pp. 564-573

    .. [2] António Morgado, Alexey Ignatiev, Joao Marques-Silva.
        *MSCG: Robust Core-Guided MaxSAT Solving*. JSAT 9. 2014.
        pp. 129-134

    .. [3] Alexey Ignatiev, António Morgado, Joao Marques-Silva.
        *RC2: A Python-based MaxSAT Solver*. MaxSAT Evaluation 2018.
        p. 22

    .. [4] Alexey Ignatiev, António Morgado, Joao Marques-Silva.
        *RC2: An Efficient MaxSAT Solver*. MaxSAT Evaluation 2018.
        JSAT 11. 2019. pp. 53-64

    The file implements two classes: :class:`RC2` and
    :class:`RC2Stratified`. The former class is the basic
    implementation of the algorithm, which can be applied to a MaxSAT
    formula in the :class:`.WCNF` format. The latter class
    additionally implements Boolean lexicographic optimization (BLO)
    [5]_ and stratification [6]_ on top of :class:`RC2`.

    .. [5] Joao Marques-Silva, Josep Argelich, Ana Graça, Inês Lynce.
        *Boolean lexicographic optimization: algorithms &
        applications*. Ann. Math. Artif. Intell. 62(3-4). 2011.
        pp. 317-343

    .. [6] Carlos Ansótegui, Maria Luisa Bonet, Joel Gabàs, Jordi
        Levy. *Improving WPM2 for (Weighted) Partial MaxSAT*. CP
        2013. pp. 117-132

    The implementation can be used as an executable (the list of
    available command-line options can be shown using ``rc2.py -h``)
    in the following way:

    ::

        $ xzcat formula.wcnf.xz
        p wcnf 3 6 4
        1 1 0
        1 2 0
        1 3 0
        4 -1 -2 0
        4 -1 -3 0
        4 -2 -3 0

        $ rc2.py -vv formula.wcnf.xz
        c formula: 3 vars, 3 hard, 3 soft
        c cost: 1; core sz: 2; soft sz: 2
        c cost: 2; core sz: 2; soft sz: 1
        s OPTIMUM FOUND
        o 2
        v -1 -2 3
        c oracle time: 0.0001

    Alternatively, the algorithm can be accessed and invoked through the
    standard ``import`` interface of Python, e.g.

    .. code-block:: python

        >>> from pysat.examples.rc2 import RC2
        >>> from pysat.formula import WCNF
        >>>
        >>> wcnf = WCNF(from_file='formula.wcnf.xz')
        >>>
        >>> with RC2(wcnf) as rc2:
        ...     for m in rc2.enumerate():
        ...         print('model {0} has cost {1}'.format(m, rc2.cost))
        model [-1, -2, 3] has cost 2
        model [1, -2, -3] has cost 2
        model [-1, 2, -3] has cost 2
        model [-1, -2, -3] has cost 3

    As can be seen in the example above, the solver can be instructed
    either to compute one MaxSAT solution of an input formula, or to
    enumerate a given number (or *all*) of its top MaxSAT solutions.

    ==============
    Module details
    ==============
"""

#
#==============================================================================
from __future__ import print_function
import collections
from gc import garbage
import getopt
import itertools
from math import copysign
import sys,os
from tkinter import S

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, BASE)
from pysat_local.formula import CNFPlus, WCNFPlus, IDPool, CNF
from pysat_local.card import ITotalizer, CardEnc, EncType
from pysat_local.solvers import Solver, SolverNames
import re
import six
from six.moves import range
import sys
import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_pydot import write_dot
import copy
import gurobipy as gp
from gurobipy import GRB

from ortools.sat.python import cp_model

# names of BLO strategies
#==============================================================================
blomap = {'none': 0, 'basic': 1, 'div': 3, 'cluster': 5, 'full': 7}





#
#==============================================================================
class RC2(object):
    """
        Implementation of the basic RC2 algorithm. Given a (weighted)
        (partial) CNF formula, i.e. formula in the :class:`.WCNF`
        format, this class can be used to compute a given number of
        MaxSAT solutions for the input formula. :class:`RC2` roughly
        follows the implementation of algorithm OLLITI [1]_ [2]_ of
        MSCG and applies a few heuristics on top of it. These include

        - *unsatisfiable core exhaustion* (see method :func:`exhaust_core`),
        - *unsatisfiable core reduction* (see method :func:`minimize_core`),
        - *intrinsic AtMost1 constraints* (see method :func:`adapt_am1`).

        :class:`RC2` can use any SAT solver available in PySAT. The
        default SAT solver to use is ``g3`` (see
        :class:`.SolverNames`). Additionally, if Glucose is chosen,
        the ``incr`` parameter controls whether to use the incremental
        mode of Glucose [7]_ (turned off by default). Boolean
        parameters ``adapt``, ``exhaust``, and ``minz`` control
        whether or to apply detection and adaptation of intrinsic
        AtMost1 constraints, core exhaustion, and core reduction.
        Unsatisfiable cores can be trimmed if the ``trim`` parameter
        is set to a non-zero integer. Finally, verbosity level can be
        set using the ``verbose`` parameter.

        .. [7] Gilles Audemard, Jean-Marie Lagniez, Laurent Simon.
            *Improving Glucose for Incremental SAT Solving with
            Assumptions: Application to MUS Extraction*. SAT 2013.
            pp. 309-317

        :param formula: (weighted) (partial) CNF formula
        :param solver: SAT oracle name
        :param adapt: detect and adapt intrinsic AtMost1 constraints
        :param exhaust: do core exhaustion
        :param incr: use incremental mode of Glucose
        :param minz: do heuristic core reduction
        :param trim: do core trimming at most this number of times
        :param verbose: verbosity level

        :type formula: :class:`.WCNF` self.wght[u] 
        :type solver: str
        :type adapt: bool
        :type exhaust: bool
        :type incr: bool
        :type minz: bool
        :type trim: int
        :type verbose: int
    """

    def __init__(self, formula, solver='g3', adapt=False, exhaust=False, hybrid =False, closure =False, ilp = 0,
            incr=False, minz=False, trim=0, relax='rc2', verbose=0):
        """
            Constructor.
        """

        # saving verbosity level and other options
        self.verbose = verbose
        self.exhaust = exhaust
        self.hybrid = hybrid
        self.solver = solver
        self.adapt = adapt
        self.minz = minz
        self.trim = trim
        self.relax = relax
        self.graph =  nx.Graph()
        self.graph_labels = {}
        self.closure = closure
        self.ilp = ilp

      

        # clause selectors and mapping from selectors to clause ids
        self.sels, self.smap, self.sall, self.s2cl, self.sneg = [], {}, [], {}, set([])

        # other MaxSAT related stuff
        self.pool = IDPool(start_from=formula.nv + 1)
        self.wght = {}  # weights of soft clauses
        self.sums = []  # totalizer sum assumptions
        self.bnds = {}  # a mapping from sum assumptions to totalizer bounds
        self.tobj = {}  # a mapping from sum assumptions to totalizer objects
        self.cost = 0

        # mappings between internal and external variables
        VariableMap = collections.namedtuple('VariableMap', ['e2i', 'i2e'])
        self.vmap = VariableMap(e2i={}, i2e={})

        
        # initialize SAT oracle with hard clauses only
        self.init(formula, incr=incr)

        # core minimization is going to be extremely expensive
        # for large plain formulas, and so we turn it off here
        wght = self.wght.values()
        if not formula.hard and len(self.sels) > 100000 and min(wght) == max(wght):
            self.minz = False
            #exit()
    def __del__(self):
        """
            Destructor.
        """

        self.delete()

    def __enter__(self):
        """
            'with' constructor.
        """

        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """
            'with' destructor.
        """

        self.delete()

    def process_cc(self, formula):
        while True:        
            G = nx.Graph()
            for i, cl in enumerate(formula.hard):
                for c in cl:
                    G.add_edge(i, abs(c))
            ls_cc = nx.connected_components(G)    
            ccs = list(ls_cc)
            print(len(ccs))
            #exit()
            break




    def init(self, formula, incr=False):
        """
            Initialize the internal SAT oracle. The oracle is used
            incrementally and so it is initialized only once when
            constructing an object of class :class:`RC2`. Given an
            input :class:`.WCNF` formula, the method bootstraps the
            oracle with its hard clauses. It also augments the soft
            clauses with "fresh" selectors and adds them to the oracle
            afterwards.

            Optional input parameter ``incr`` (``False`` by default)
            regulates whether or not Glucose's incremental mode [7]_
            is turned on.

            :param formula: input formula
            :param incr: apply incremental mode of Glucose

            :type formula: :class:`.WCNF`
            :type incr: bool
        """

        # creating a solver object
        #self.clasue
        #self.hard = copy.deepcopy(formula.hard)
        #self.soft = []
        self.upperlevel = {}
        self.maxreslevel = {}
    


        if self.ilp > 0:
            if self.verbose > 1:
                print('c init formula: {0} vars, {1} hard, {2} soft'.format(formula.nv,
                    len(formula.hard), len(formula.soft)))         
            # disjoints = [-36239, -36240, -36241,-36242, -36243, -36244, -36245,-36246, -36247, -36248, -36249, -36250, -36251, -36252, -36253, -36254, -36255] 
            # for c in disjoints:
            #    formula.hard.append([c])   
            solution = self.solve_ortools_sat(formula, solve=False)
            presolve =  True
            exit()

            formula = self.solve_gurobi(formula, solve=True, presolve=presolve, solution = solution)
            #exit()            
            #formula = formula_new
            if (presolve):
                try:
                    self.cost  =  int(formula.cost)
                except:
                    pass
                if formula.atmosts:
                    for vars, rhs in formula.atmosts:
                        #print("atmost", vars, rhs, formula.nv)
                        cnf = CardEnc.atmost(lits=vars, bound= rhs, encoding= EncType.seqcounter, top_id = formula.nv)
                        formula.nv = cnf.nv + 1
                        #print( formula.nv)                    
                        for cl in cnf.clauses:
                            formula.hard.append(cl)

                if formula.equals:
                    for vars, rhs in formula.equals:
                        #print("equal", vars, rhs, )
                        cnf = CardEnc.equals(lits=vars, bound= rhs, encoding= EncType.seqcounter, top_id = formula.nv)
                        formula.nv = cnf.nv + 1
                        #print( formula.nv)                    
                        for cl in cnf.clauses:
                            formula.hard.append(cl)
            
            

            self.pool = IDPool(start_from=formula.nv + 1)
        self.formula = formula
        #exit()



        # # adding native cardinality constraints (if any) as hard clauses
        # # this can be done only if the Minicard solver is in use
        # # this cannot be done if RC2 is run from the command line
        # if isinstance(formula, WCNFPlus) and formula.atms:
        #     assert self.oracle.supports_atmost(), \
        #             '{0} does not support native cardinality constraints. Make sure you use the right type of formula.'.format(self.solver)

        #     for atm in formula.atms:
        #         self.oracle.add_atmost(*atm)

        # adding soft clauses to oracle
        softs = CNF()
        for i, cl in enumerate(formula.soft):
            
            selv = cl[0]  # if clause is unit, selector variable is its literal

            if len(cl) > 1:
                selv = self.pool.id()
                self.s2cl[selv] = cl[:]
                cl.append(-selv)
                softs.append(cl)
                print(cl)
            if selv not in self.wght:
                # record selector and its weight
                self.sels.append(selv)
                self.wght[selv] = formula.wght[i]
                self.smap[selv] = i
            else:
                # selector is not new; increment its weight
                self.wght[selv] += formula.wght[i]

       


        self.oracle = Solver(name=self.solver, bootstrap_with=formula.hard,
                incr=incr, use_timer=True)
                            
        for i, cl in enumerate(softs):
            self.oracle.add_clause(cl)        




        # storing the set of selectors
        self.sels_set = set(self.sels)
        self.sall = self.sels[:]

        # at this point internal and external variables are the same
        for v in range(1, formula.nv + 1):
            self.vmap.e2i[v] = v
            self.vmap.i2e[v] = v

        if self.verbose > 1:
            print('c formula: {0} vars, {1} hard, {2} soft max vars{3}'.format(formula.nv,
                len(formula.hard), len(formula.soft), self.pool.top))

        # self.reinit()

    # def reinit(self):
    #     # creating a solver object
    #     #self.clasue

    #     # clause selectors and mapping from selectors to clause ids
    #     #self.sels, self.smap, self.sall, self.s2cl, self.sneg = [], {}, [], {}, set([])

    #     # other MaxSAT related stuff
    #     #self.pool = IDPool(start_from=formula.nv + 1)
    #     #self.sums = []  # totalizer sum assumptions
    #     #self.cost = 0

    #     self.oracle = Solver(name=self.solver, bootstrap_with=self.hard,
    #             incr=incr, use_timer=True)

    #     # adding soft clauses to oracle
    #     for i, cl in enumerate(self.soft):
    #         self.oracle.add_clause(cl)

    #     if self.verbose > 1:
    #         print('c formula: {0} vars, {1} hard, {2} soft'.format(formula.nv,
    #             len(self.hard), len(self.soft)))       

    def add_clause(self, clause, weight=None):
        """
            The method for adding a new hard of soft clause to the
            problem formula. Although the input formula is to be
            specified as an argument of the constructor of
            :class:`RC2`, adding clauses may be helpful when
            *enumerating* MaxSAT solutions of the formula. This way,
            the clauses are added incrementally, i.e. *on the fly*.

            The clause to add can be any iterable over integer
            literals. The additional integer parameter ``weight`` can
            be set to meaning the the clause being added is soft
            having the corresponding weight (note that parameter
            ``weight`` is set to ``None`` by default meaning that the
            clause is hard).

            :param clause: a clause to add
            :param weight: weight of the clause (if any)

            :type clause: iterable(int)
            :type weight: int

            .. code-block:: python

                >>> from pysat.examples.rc2 import RC2
                >>> from pysat.formula import WCNF
                >>>
                >>> wcnf = WCNF()
                >>> wcnf.append([-1, -2])  # adding hard clauses
                >>> wcnf.append([-1, -3])
                >>>
                >>> wcnf.append([1], weight=1)  # adding soft clauses
                >>> wcnf.append([2], weight=1)
                >>> wcnf.append([3], weight=1)
                >>>
                >>> with RC2(wcnf) as rc2:
                ...     rc2.compute()  # solving the MaxSAT problem
                [-1, 2, 3]
                ...     print(rc2.cost)
                1
                ...     rc2.add_clause([-2, -3])  # adding one more hard clause
                ...     rc2.compute()  # computing another model
                [-1, -2, 3]
                ...     print(rc2.cost)
                2
        """

        # first, map external literals to internal literals
        # introduce new variables if necessary
        cl = list(map(lambda l: self._map_extlit(l), clause if not len(clause) == 2 or not type(clause[0]) == list else clause[0]))

        if not weight:
            if not len(clause) == 2 or not type(clause[0]) == list:
                # the clause is hard, and so we simply add it to the SAT oracle
                self.oracle.add_clause(cl)
            else:
                # this should be a native cardinality constraint,
                # which can be used only together with Minicard
                assert self.oracle.supports_atmost(), \
                        '{0} does not support native cardinality constraints. Make sure you use the right type of formula.'.format(self.solver)

                self.oracle.add_atmost(cl, clause[1])
        else:
            # soft clauses should be augmented with a selector
            selv = cl[0]  # for a unit clause, no selector is needed

            if len(cl) > 1:
                selv = self.pool.id()

                self.s2cl[selv] = cl[:]
                cl.append(-selv)
                self.oracle.add_clause(cl)

            if selv not in self.wght:
                # record selector and its weight
                self.sels.append(selv)
                self.wght[selv] = weight
                self.smap[selv] = len(self.sels) - 1
            else:
                # selector is not new; increment its weight
                self.wght[selv] += weight

            self.sall.append(selv)
            self.sels_set.add(selv)

    def delete(self):
        """
            Explicit destructor of the internal SAT oracle and all the
            totalizer objects creating during the solving process.
        """

        if self.oracle:
            if not self.oracle.supports_atmost():  # for minicard, there is nothing to free
                for t in six.itervalues(self.tobj):
                    t.delete()

            self.oracle.delete()
            self.oracle = None

    def compute(self):
        """
            This method can be used for computing one MaxSAT solution,
            i.e. for computing an assignment satisfying all hard
            clauses of the input formula and maximizing the sum of
            weights of satisfied soft clauses. It is a wrapper for the
            internal :func:`compute_` method, which does the job,
            followed by the model extraction.

            Note that the method returns ``None`` if no MaxSAT model
            exists. The method can be called multiple times, each
            being followed by blocking the last model. This way one
            can enumerate top-:math:`k` MaxSAT solutions (this can
            also be done by calling :meth:`enumerate()`).

            :returns: a MaxSAT model
            :rtype: list(int)

            .. code-block:: python

                >>> from pysat.examples.rc2 import RC2
                >>> from pysat.formula import WCNF
                >>>
                >>> rc2 = RC2(WCNF())  # passing an empty WCNF() formula
                >>> rc2.add_clause([-1, -2])
                >>> rc2.add_clause([-1, -3])
                >>> rc2.add_clause([-2, -3])
                >>>
                >>> rc2.add_clause([1], weight=1)
                >>> rc2.add_clause([2], weight=1)
                >>> rc2.add_clause([3], weight=1)
                >>>
                >>> model = rc2.compute()
                >>> print(model)
                [-1, -2, 3]
                >>> print(rc2.cost)
                2
                >>> rc2.delete()
        """

        # simply apply MaxSAT only once
        res = self.compute_()

        if res:
            # extracting a model
            self.model = self.oracle.get_model()

            if self.model is None and self.pool.top == 0:
                # we seem to have been given an empty formula
                # so let's transform the None model returned to []
                self.model = []

            self.model = filter(lambda l: abs(l) in self.vmap.i2e, self.model)
            self.model = map(lambda l: int(copysign(self.vmap.i2e[abs(l)], l)), self.model)
            self.model = sorted(self.model, key=lambda l: abs(l))

            return self.model

    def enumerate(self, block=0):
        """
            Enumerate top MaxSAT solutions (from best to worst). The
            method works as a generator, which iteratively calls
            :meth:`compute` to compute a MaxSAT model, blocks it
            internally and returns it.

            An optional parameter can be used to enforce computation of MaxSAT
            models corresponding to different maximal satisfiable subsets
            (MSSes) or minimal correction subsets (MCSes). To block MSSes, one
            should set the ``block`` parameter to ``1``. To block MCSes, set
            it to ``-1``. By the default (for blocking MaxSAT models),
            ``block`` is set to ``0``.

            :param block: preferred way to block solutions when enumerating
            :type block: int

            :returns: a MaxSAT model
            :rtype: list(int)

            .. code-block:: python

                >>> from pysat.examples.rc2 import RC2
                >>> from pysat.formula import WCNF
                >>>
                >>> rc2 = RC2(WCNF())  # passing an empty WCNF() formula
                >>> rc2.add_clause([-1, -2])  # adding clauses "on the fly"
                >>> rc2.add_clause([-1, -3])
                >>> rc2.add_clause([-2, -3])
                >>>
                >>> rc2.add_clause([1], weight=1)
                >>> rc2.add_clause([2], weight=1)
                >>> rc2.add_clause([3], weight=1)
                >>>
                >>> for model in rc2.enumerate():
                ...     print(model, rc2.cost)
                [-1, -2, 3] 2
                [1, -2, -3] 2
                [-1, 2, -3] 2
                [-1, -2, -3] 3
                >>> rc2.delete()
        """

        done = False
        while not done:
            model = self.compute()

            if model != None:
                if block == 1:
                    # to block an MSS corresponding to the model, we add
                    # a clause enforcing at least one of the MSS clauses
                    # to be falsified next time
                    m, cl = set(self.oracle.get_model()), []

                    for selv in self.sall:
                        if selv in m:
                            # clause is satisfied
                            cl.append(-selv)

                            # next time we want to falsify one of these
                            # clauses, i.e. we should encode the negation
                            # of each of these selectors
                            if selv in self.s2cl and not selv in self.sneg:
                                self.sneg.add(selv)
                                for il in self.s2cl[selv]:
                                    self.oracle.add_clause([selv, -il])

                    self.oracle.add_clause(cl)
                elif block == -1:
                    # a similar (but simpler) piece of code goes here,
                    # to block the MCS corresponding to the model
                    # (this blocking is stronger than MSS blocking above)
                    m = set(self.oracle.get_model())
                    self.oracle.add_clause([l for l in filter(lambda l: -l in m, self.sall)])
                else:
                    # here, we simply block a previous MaxSAT model
                    self.add_clause([-l for l in model])

                yield model
            else:
                done = True

    def compute_(self):
        """
            Main core-guided loop, which iteratively calls a SAT
            oracle, extracts a new unsatisfiable core and processes
            it. The loop finishes as soon as a satisfiable formula is
            obtained. If specified in the command line, the method
            additionally calls :meth:`adapt_am1` to detect and adapt
            intrinsic AtMost1 constraints before executing the loop.

            :rtype: bool
        """

        # trying to adapt (simplify) the formula
        # by detecting and using atmost1 constraints
        if self.adapt:
            self.adapt_am1()

        # main solving loop
        solve_res = self.oracle.solve(assumptions=self.sels + self.sums)
        while not solve_res:
            solve_res = True
            self.unkown_in_core = 0
            self.get_core()

            if not self.core:
                # core is empty, i.e. hard part is unsatisfiable
                return False
            if  self.relax=='rc2': 
                self.process_core()
            #print(self.relax)
            if  self.relax in ['mr2a','mr2b', 'mr2c', 'mr1a', 'mr1b', 'mr1c', 'mr1d', 'mr2d']: 
                self.process_core_maxres_tree()
                if self.closure:
                    #write_dot(self.graph, 'file.dot')
                    ls_cc = nx.connected_components(self.graph)    
                    ccs = list(ls_cc)
                    #print( len(ccs))
                    if len(list(ccs)) > 1:    
                        for ls in ccs:
                            cc = [int(l) for l in ls]
                            inter = list(set(self.core) & set(cc))
                            diff = list(set(cc) - set(self.core))
                            #print(inter, diff, self.core, ls )
                            #print(self.sels, self.sums)

                            if len(inter) > 0 and len(diff) > 0 :
                                assert(len(inter) == len(self.core))
                                focus = []
                                for s in self.sels + self.sums:
                                    if (s in cc) or (-s in cc):
                                        focus.append(s)
                                #print(f"focus {focus}  cc {cc} {self.sels + self.sums}")
                                solve_res = self.oracle.solve(assumptions=focus)
                                
            if (solve_res):
                solve_res = self.oracle.solve(assumptions=self.sels + self.sums)
            else:
                print("cover")



            if self.verbose > 1:
                print('c cost: {0}; core sz: {1}; soft sz: {2}'.format(self.cost,
                    len(self.core), len(self.sels) + len(self.sums)))
            #exit()
        return True

    def get_core(self):
        """
            Extract unsatisfiable core. The result of the procedure is
            stored in variable ``self.core``. If necessary, core
            trimming and also heuristic core reduction is applied
            depending on the command-line options. A *minimum weight*
            of the core is computed and stored in ``self.minw``.
            Finally, the core is divided into two parts:

            1. clause selectors (``self.core_sels``),
            2. sum assumptions (``self.core_sums``).
        """

        # extracting the core
        self.core = self.oracle.get_core()

        if self.core:
            # try to reduce the core by trimming
            self.trim_core()

            # and by heuristic minimization
            self.unkown_in_core = self.minimize_core()
            #print( "---", self.unkown_in_core)

            # the core may be empty after core minimization
            if not self.core:
                return

            # core weight
            self.minw = min(map(lambda l: self.wght[l], self.core))

            # dividing the core into two parts
            iter1, iter2 = itertools.tee(self.core)
            self.core_sels = list(l for l in iter1 if l in self.sels_set)
            self.core_sums = list(l for l in iter2 if l not in self.sels_set)


    def seq_counters_open(self, constraint, n, topv, last_layer = [], tight = True):
        
        #print(">>>>>>>>>>>>>>>>>>> SQ <<<<<<<<<<<<<<<<<<<")
        #print("input variables:")
        #print(vars_ids)
        card_formula = CNF()
        # sum_i=0^n-1 l_i >= C
        
        
        x = constraint["literals"]
        k = int(constraint["rhs_constant_max"])
            
        #print(f"literals {len(x)} max_bound {k}" )
                    
        if (k > n):
            print("max bound {k} >  len {n}")
            assert(False)            
        if (k <= 0):
            print("max bound {k} = 0")
            assert(False)            
        
        if (n == 1):
            print("n ({k}) = 1 (unit cores should be treated separatly ")
            s = [[-1] * (2) for i in range(n+1)]
            topv += 1
            s[1][1] = topv        
            # x[1] == s[1][1]
            card_formula.append([-x[1], s[1][1]])
            card_formula.append([x[1], -s[1][1]])
            return card_formula, s
        
        

        s = [[-1] * (k+1) for i in range(n+1)]
        # note that seq counters assume that we have variables from 1..n
        for  i in  range(1,n+1):
            if (i == n) and len(last_layer) >0:
                for  j in  range(1, k+1):            
                    s[i][j] = last_layer[j]        
                continue
            for  j in  range(1, k+1):
                topv += 1
                s[i][j] = topv
        ################################################################
        # s[1][1] <=>  x[1]
        # (not x[1] V  s[1][1])
        # (x[1] V  not s[1][1])     
                    
        # (not x[1] V  s[1][1])        
        card_formula.append([-x[1], s[1][1]])
        # (x[1] V  not s[1][1])     
        card_formula.append([x[1], -s[1][1]])

        # 1 < j <=k
        for j in range(2, k+1):
            #(not s[1][j])
            card_formula.append([-s[1][j]])
            
        #print(card_formula.clauses)

        #print("after first block s = ", s)
        # 1 < i <= n    
        for i in range(2, n+1):         
            #s[i][1] <=> x[i] \/ s[i-1][1]
            #s[i][1] \/ not x[i] 
            #s[i][1] \/ not s[i-1][1]
            #not s[i][1] \/ x[i] \/ s[i-1][1]
                
            # (s[i][1] \/ not x[i] )     
            #print(i, -x[i])
            #print(i, s[i][1])
            card_formula.append([-x[i], s[i][1]])
        
            # (s[i][1] \/ not s[i-1][1] )                
            card_formula.append([-s[i-1][1], s[i][1]])
                
            # not s[i][1] \/ x[i] \/ s[i-1][1]     
            card_formula.append([-s[i][1], x[i], s[i-1][1]])
            
        for j in range(2, k+1):
            for i in range(j, n+1): 
                #print(i,j)
            # 1 < j <=k
                
                if (i == j):
                    # corner case, e.g. we are at s_3,3 and look s_2,3 which must be false 
                    card_formula.append([-s[i-1][j]])
                    
            
                #s[i][j] <=> (x[i] /\ s[i-1][j-1]) \/ s[i-1][j]
        
                ##############################################
                #s[i][j] <= x[i] /\ s[i-1][j-1] \/ s[i-1][j]
                ###############################################
                #not s[i][j] \/(x[i] /\ s[i-1][j-1] \/ s[i-1][j])

                #s[i][j] \/ not x[i] \/ not s[i-1][j-1] 
                #s[i][j] \/ not s[i-1][j]
        
                #s[i][j] => x[i] /\ s[i-1][j-1] \/ s[i-1][j]
                # not s[i][j] \/ x[i]  \/ s[i-1][j]
                # not s[i][j] \/ s[i-1][j-1] \/ s[i-1][j]
                
                
                
                #s[i][j] \/ not x[i] \/ not s[i-1][j-1]                
                card_formula.append([s[i][j], -x[i], -s[i-1][j-1]])
                
                #s[i][j] \/ not s[i-1][j]                
                #print(i-1,j, s[i-1][j])
                card_formula.append([s[i][j], -s[i-1][j]])
        
                #not s[i][j] \/ x[i]  \/ s[i-1][j]   
                card_formula.append([- s[i][j], x[i],  s[i-1][j]])
        
                #not s[i][j] \/ s[i-1][j-1] \/ s[i-1][j]
                card_formula.append([-s[i][j], s[i-1][j-1],  s[i-1][j]])

        
        
        if (tight):
            tight_light = True
            if (tight_light):
                for i in range(2, n+1): 
                    #v[i] <=> (x[i] /\ s[i-1][k])
                    #-v[i] \/ x[i]
                    #card_formula.append([-v[i],x[i]])        
                    #-v[i] \/ s[i-1][k]
                    #card_formula.append([-v[i], s[i-1][k]])                
                    #v[i] \/ -x[i] \/ -s[i-1][k]
                    card_formula.append([-x[i],-s[i-1][k]])            

            else:
                v = [-1 for i in range(n+1)]
                for  i in  range(1,n+1):
                    topv += 1
                    v[i] = topv
            
                for i in range(2, n+1): 

                    #v[i] <=> (x[i] /\ s[i-1][k])
                    #-v[i] \/ x[i]
                    card_formula.append([-v[i],x[i]])        
                    #-v[i] \/ s[i-1][k]
                    card_formula.append([-v[i], s[i-1][k]])                
                    #v[i] \/ -x[i] \/ -s[i-1][k]
                    card_formula.append([v[i], -x[i],-s[i-1][k]])
                    
                    card_formula.append([-v[i]])
                
        #print(card_formula.clauses)
        # seal cardinality
        return card_formula, s, topv

    def solve_ortools_sat(self,formula, solve = False, presolve = True):        
         
        ##########################################
        self.ortools_model = cp_model.CpModel()
        max_id = self.pool.top+1

        self.ortools_vars = {}
        for c in range(max_id):
            #print(c)
            b = self.ortools_model.NewBoolVar(name= f"{c}")
            self.ortools_vars[c] = b
        
        #print(ortools)
        
        for j, cl in enumerate(formula.hard):
            con_vars = []
            rhs =  1
            
            #print(cl, max_id)
            for c in cl:
                if (c > 0):
                    con_vars.append(self.ortools_vars[abs(c)])
                else:
                    con_vars.append(self.ortools_vars[abs(c)].Not())
                    
            self.ortools_model.AddBoolOr(con_vars)       
        self.ortools_soft_vars = {}   
        ops = []
        wops = []
        for j, cl in enumerate(formula.soft):
           #print(cl)
            if (len(cl) == 1):                    
                c = cl[0]

                if (c > 0):
                    self.ortools_soft_vars[j] = self.ortools_vars[abs(c)].Not()                    
                else:
                    self.ortools_soft_vars[j] = self.ortools_vars[abs(c)]                    
            else:
                con_vars = []
                v = max_id + j
                b = self.ortools_model.NewBoolVar(name= f"{v}")
                self.ortools_vars[v] = b
                self.ortools_soft_vars[j] = b
                
                con_vars.append(self.ortools_vars[abs(v)])
                for c in cl:
                    if (c > 0):
                        con_vars.append(self.ortools_vars[abs(c)])
                    else:
                        con_vars.append(self.ortools_vars[abs(c)].Not())
                self.ortools_model.AddBoolOr(con_vars)       
            
            ops.append(self.ortools_soft_vars[j])
            wops.append(formula.wght[j])  
            
        # print(ops, wops)
        # exit()
          
        #print(ops)
        #print(wops)
        solver = cp_model.CpSolver()

        self.ortools_model.Minimize(cp_model.LinearExpr.WeightedSum(ops, wops))
        solver.parameters.log_search_progress = True
        solver.parameters.num_search_workers = 1
        solver.parameters.max_time_in_seconds = self.ilp


        status = solver.Solve(self.ortools_model)
        print('Solve status: %s' % solver.StatusName(status))
        if status == cp_model.OPTIMAL:
            print('Optimal objective value: %i' % solver.ObjectiveValue())
        print('Statistics')
        print('  - conflicts : %i' % solver.NumConflicts())
        print('  - branches  : %i' % solver.NumBranches())
        print('  - wall time : %f s' % solver.WallTime())

        print(solver.ResponseStats)
        solution = {}
        for c in range(max_id):
            #print(c)            
            b = self.ortools_vars[c]
            solution[c] = solver.BooleanValue(b)

        
        return solution

    def solve_gurobi(self,formula, solve = False, presolve = True, solution = None):
        with gp.Env(empty=True) as env:
            #env.setParam('OutputFlag', 0)
            env.setParam('TimeLimit', self.ilp)
            env.setParam('Threads', 1)            
            #env.setParam('Presolve', 2)
        
      

            

            
            
            env.start()
            ##########################################
            self.gurobi_model = gp.Model("whole", env=env)
            max_id = self.pool.top + 1

            self.gurobi_vars = {}
            for c in range(max_id):
                b = self.gurobi_model.addVar(vtype=GRB.BINARY, name= f"{c}",)
                self.gurobi_vars[c] = b
                if not (solution is  None):
                    try:
                        #print(c,solution[c])
                        b.setAttr('Start', solution[c])
                        #self.gurobi_model.addConstr(b == solution[c], f"clause_{c} = {solution[c]}")
                    except:
                        pass
                        print("-->", c)
            
            #print(gurobi_vars)
            
            for j, cl in enumerate(formula.hard):
                con_vars = []
                rhs =  1
                
                #print(cl, max_id)
                for c in cl:
                    if (c > 0):
                        con_vars.append(self.gurobi_vars[abs(c)])
                    else:
                        con_vars.append(-self.gurobi_vars[abs(c)])
                        rhs = rhs -1
                        
                self.gurobi_model.addConstr(gp.quicksum(con_vars) >= rhs, f"clause_{j}")       

            self.gurobi_soft_vars = {}   
            ops = []
            wops = []
            for j, cl in enumerate(formula.soft):
                if (len(cl) == 1):                    
                    c = cl[0]

                    if (c > 0):
                        self.gurobi_soft_vars[j] = 1-self.gurobi_vars[abs(c)]                    
                    else:
                        self.gurobi_soft_vars[j] = self.gurobi_vars[abs(c)]                    
                else:
                    con_vars = []
                    rhs =  1
                    v = max_id + j
                    b = self.gurobi_model.addVar(vtype=GRB.BINARY, name= f"{v}")
                    self.gurobi_vars[v] = b
                    self.gurobi_soft_vars[j] = b
                    
                    con_vars.append(self.gurobi_vars[abs(v)])
                    for c in cl:
                        if (c > 0):
                            con_vars.append(self.gurobi_vars[abs(c)])
                        else:
                            con_vars.append(-self.gurobi_vars[abs(c)])
                            rhs = rhs -1
                    self.gurobi_model.addConstr(gp.quicksum(con_vars) >= rhs, f"soft_clause_{j}")  
                
                ops.append(self.gurobi_soft_vars[j])
                wops.append(formula.wght[j])  
            # print(ops, wops)
            # exit()

            #self.gurobi_model.addConstr(gp.quicksum([ops[j]*wops[j] for j,_ in enumerate(ops)]) <= 18)  
            # self.gurobi_model.params.Method=1q
            # self.gurobi_model.params.TuneTimeLimit=60
            #self.gurobi_model.tune()            
            #print(ops)
            self.gurobi_model.setObjective(gp.quicksum([ops[j]*wops[j] for j,_ in enumerate(ops)]), GRB.MINIMIZE)
            formula_new = None
            self.gurobi_model.write("test.lp")


            if (solve):
                self.gurobi_model.optimize()
                obj = None
                solution_vars = []
                sols = []
                if self.gurobi_model.status == GRB.OPTIMAL:
                    obj = self.gurobi_model.objVal 
                    best_obj = int(obj)                
                else:
                    obj = -1
                    best_obj = self.gurobi_model.objVal      
                print(best_obj)

            if (presolve):
                try:
                    self.gurobi_model=self.gurobi_model.presolve()
                    self.gurobi_model.printStats() 
                    self.gurobi_model.write("pre-test.lp")
                    formula_new = WCNFPlus(from_gmodel=self.gurobi_model)                                                            
                    self.gmodel = self.gurobi_model
                except Exception as e:
                    print("-----------", e)
                    exit()


            return formula_new
    
    def add_upperlevel(self, lits, tag = 'base'):
        debug = False
        # if (len(lits) == 1):
        #     return lits[0]
        c = self.pool.id()    
        self.wght[c] = self.minw
    
        self.upperlevel[c] = {}
        self.upperlevel[c]["base"] = lits
        self.upperlevel[c]["tag"] = tag
        if debug: print(f"new {c} base {len(lits)}")
        formula = CNF()
        for u in lits:
            formula.append([-c, u])
        for cl in formula:
            #print(cl)
            #self.soft.append(cl)
            self.oracle.add_clause(cl)   

        return c     

    def graph_label(self, v, lv = None):
        if (lv is None):
            lv = f"{v}"
        if not (str(v) in self.graph_labels):
            self.graph_labels[str(v)] = f"{lv}"
        return self.graph_labels[str(v)]

    def resolution(self, core):
        new_sums =  []
        formula = CNF()

        while len(core) >= 2:
            u = self.pool.id()    
            v = self.pool.id()    
            #v <-> core[0] /\ core[1]
            #v \/ not core[0] \/ not core[1]
            #not v  \/ core[0] 
            #not v  \/  core[1]
            if (len(core) > 2):
                #formula.append([v, -core[0], -core[1]])
                formula.append([-v, core[0]])
                formula.append([-v, core[1]])
            #u <-> core[0] \/ core[1]
            #-u \/ core[0] \/ core[1]
            #u \/ -core[0] 
            #u \/ -core[1]
            formula.append([-u, core[0], core[1]])
            #formula.append([u, -core[0]])
            #formula.append([u, -core[1]])

            new_sums.append(u)
            self.wght[u] = self.minw
            self.graph_label(v,  f"{u}")
            self.graph_label(u,  f"{u}")



        
            #exit()
            if (self.relax in ['mr2a', 'mr2b', 'mr2d']):
                core = core[2:] + [ v ]
            if (self.relax in ['mr1a', 'mr1b',  'mr1d']):
                core = [v] + core[2:] 
            
        for cl in formula:
            #print(cl)
            #self.soft.append(cl)
            self.oracle.add_clause(cl)    
             
        return new_sums
    def process_core_maxres_tree(self):
        debug  = False 
        self.cost += self.minw
       # assumptions to remove
        self.garbage = set()
        remainig_core = []
        promising  = True
        flag_continue = False
        if debug: print(f"self.core {self.core}")
        if debug: print(f"self.upperlevel {self.upperlevel}")
        if debug: print(f"self.sums {self.sums }")
        if debug: print(f"self.sels {self.sels }")
        if debug: print(f"end: self.tobj {self.tobj }")

        #print(len(self.sels) , len(self.sums))
        if len(self.core_sels) != 1 or len(self.core_sums) > 0:
            while True:
                # process selectors in the core
                self.process_sels()
                #print(f"after  process_sels {len(self.garbage)}")

                # process previously introducded sums in the core
                self.process_sums()
                #print(f"after  process_sums_maxres {self.garbage}")
                
                prefix = True
                
                self.new_sums = []
                core            = []
                self.core = [-l for l in self.rels]
                
                has_upperlevel =  False
                #min_core  =[]
                diff = []
                keep_core = []
                unfolding ={}
                core_unfolding = []
                hard_clauses = []
                try:
                    self.unkown_in_core
                except:
                    self.unkown_in_core = len(self.core)
                
                if debug: print("core:", len(self.core), self.unkown_in_core)
                
                for c in self.core:
                    if c in self.upperlevel:
                        core = core + self.upperlevel[c]["base"]
                        #if debug: print(f"{c} -- {len(self.upperlevel[c]['base'])}")
                        #self.soft.append([-c])
                        #hard_clauses.append([-c])
                        has_upperlevel = True
                        #min_core = min_core + self.upperlevel[c]["base"]
                        unfolding[c] = self.upperlevel[c]["base"]
                        core_unfolding.append(c)
                    else:
                        core.append(c)
                        keep_core = keep_core + [c]
                if debug: print(f"self.core {self.core}")
                print("----", self.relax, has_upperlevel, flag_continue)
                if (self.relax in ['mr1d', 'mr2d']):                     
                    if (promising) and (has_upperlevel) and (not flag_continue):
                        if debug: print(f"-- minimization [{len(self.core)}]: {len(core)}/{len(keep_core)} -- > ", end = " ")                
                        #print(f"------{self.relax }")
                        if (self.relax in ['mr1d', 'mr2d']):                    
                            #print(copy.deepcopy(core_unfolding), copy.deepcopy(unfolding), copy.deepcopy(keep_core))                             
                            self.unkown_in_core = self.minimize_core_unfolding (copy.deepcopy(core_unfolding), copy.deepcopy(unfolding), copy.deepcopy(keep_core))  
                            #print(self.unkown_in_core)              
                        diff = list(set(core) - set(self.core))
                        #self.garbage = set(set(self.garbage) - set(diff))
                        remainig_core = remainig_core + diff
                        core = self.core
                        if debug: print(f"diff {diff}")

                        if debug : print(f" len(core) {len(core)}, len(remainig_core) {len(remainig_core)}")
                             #exit()
                for c in hard_clauses:
                    self.oracle.add_clause(c)

                exhaust_core = False
                

                ratio = float(self.unkown_in_core)/len(core)
                print(f"promising------------ {ratio} self.unkown_in_core = {self.unkown_in_core} {len(core)} {len(diff)}")
                #print(self.sels, self.sums)
                if (ratio > 0.1) or not(self.hybrid):
                    self.new_sums = self.resolution(core)
                    #print(self.new_sums, core)
                    if (self.closure):
                        for v1 in core:
                            for v2 in self.new_sums:
                                self.graph.add_edge(self.graph_label(v1), self.graph_label(v2))
                                #print(self.graph_label(v1), self.graph_label(v2))



                    if (self.relax in ['mr1a', 'mr2a']): 
                        self.sums = self.sums  + self.new_sums 
                    if (self.relax in ['mr1b', 'mr2b']):
                        self.sums = self.sums + self.new_sums[::-1]

                    if (self.relax in ['mr1a', 'mr2a', 'mr1b', 'mr2b']): 
                        for s in self.new_sums:
                            self.maxreslevel[s] = {}
                            self.maxreslevel[s]["base"] = [s]                          

                    if (self.relax in ['mr1d', 'mr2d']): 

                        lits = copy.deepcopy(self.new_sums)
                        c = self.add_upperlevel(lits)
                        #print(self.new_sums, self.closure)
                        if (self.closure):
                            for v1 in self.new_sums:
                                self.graph.add_edge(self.graph_label(v1), self.graph_label(c))
                                #print(self.graph_label(v1), self.graph_label(c))

                        #if debug: print(f" add_upperlevel {self.new_sums} {c}")
                        self.sums = self.sums + [c]
                        self.new_sums = [c]
                        #assert(len(remainig_core) ==0)
                        



                    print("mr")



                else:
                    print("rc2")
                    #print(self.core)
                    print(core)
                    self.core = core
                    assert(self.oracle.solve(assumptions= core) == False)
                    
                    self.rels = [-l for l in core]
                    t = self.create_sum()
                    #c = self.set_bound(t, 1)
                    

                    c = t

                    # # # apply core exhaustion if required
                    b = self.exhaust_core(t) if self.exhaust else 1
                    if b:
                        # save the info about this sum and
                        # add its assumption literal
                        c = self.set_bound(t, b)
                        if (self.closure):
                            for v1 in core:
                                self.graph.add_edge(self.graph_label(v1), self.graph_label(c))
                                #print(self.graph_label(v1), self.graph_label(c))

                    else:
                        # impossible to satisfy any of these clauses
                        # they must become hard
                        for relv in self.rels:
                            self.oracle.add_clause([relv])
                    #print(f"exaust b ={b}")
                    exhaust_core = True
                    self.new_sums = [c]



                    #print("---")
                    # if debug: print(f"self.core {self.core}")
                    # if debug: print(f"self.upperlevel {self.upperlevel}")
                    # if debug: print(f"self.sums {self.sums }")
                    # if debug: print(f"self.sels {self.sels }")
                #print(self.graph_labels)

                if (exhaust_core) or not(self.minz)  or self.oracle.solve(assumptions=self.new_sums):
                    if debug: print("exaust done")
                    #print("exaust done")
                    if (len(remainig_core) !=0): 
                        #if (len(remainig_core) > 50):
                        r = self.add_upperlevel(remainig_core, tag = "remainig_core")
                        self.sums = self.sums + [r]
                        if (self.closure):                            
                            for v1 in remainig_core:
                                self.graph.add_edge(self.graph_label(v1), self.graph_label(r))



                        # else:                       
                        # self.sums = self.sums + remainig_core

                        # self.garbage = set(set(self.garbage) - set(remainig_core))
                        # for s in remainig_core:
                        #     self.maxreslevel[s] = {}
                        #     self.maxreslevel[s]["base"] = [s]         
                        #if debug: print(f" remainig_core {remainig_core} /{self.new_sums}")
                   #exit()
                    break 
                else:
                    if debug: print("exaust continue")
                    #print("exaust continue")
                    flag_continue = True
                    self.get_core()
                    self.cost += self.minw

        else:
            # unit cores are treated differently
            # (their negation is added to the hard part)
            print("unit---")
            #self.hard.append([-self.core_sels[0]])
            print(f"{self.core} {self.core_sels}")

            self.oracle.add_clause([-self.core_sels[0]])     
            self.garbage.add(self.core_sels[0])
        if debug: print("filter_assumps_maxres")

        if debug: print(f"end: self.garbage {self.garbage }")

        self.filter_assumps()
        if debug: print(f"end: self.core {self.core}")
        if debug: print(f"end: self.upperlevel {self.upperlevel}")
        if debug: print(f"end: self.sums {self.sums }")
        if debug: print(f"end: self.sels {self.sels }")
        if debug: print(f"end: self.tobj {self.tobj }")



        #pos = nx.nx_agraph.graphviz_layout(self.graph)
        #nx.draw(self.graph, pos=pos)
        #plt.savefig("path.png")

        #print(len(self.sels) , len(self.sums))
        # remove unnecessary assumptions

        return



    # def filter_assumps_maxres(self):
    #     """
    #         Filter out unnecessary selectors and sums from the list of
    #         assumption literals. The corresponding values are also
    #         removed from the dictionaries of bounds and weights.

    #         Note that assumptions marked as garbage are collected in
    #         the core processing methods, i.e. in :func:`process_core`,
    #         :func:`process_sels`, and :func:`process_sums`.
    #     """

    #     self.sels = list(filter(lambda x: x not in self.garbage, self.sels))
    #     self.sums = list(filter(lambda x: x not in self.garbage, self.sums))

    #     self.sels_set.difference_update(set(self.garbage))

    #     self.garbage.clear()

    def process_core(self):
        """
            The method deals with a core found previously in
            :func:`get_core`. Clause selectors ``self.core_sels`` and
            sum assumptions involved in the core are treated
            separately of each other. This is handled by calling
            methods :func:`process_sels` and :func:`process_sums`,
            respectively. Whenever necessary, both methods relax the
            core literals, which is followed by creating a new
            totalizer object encoding the sum of the new relaxation
            variables. The totalizer object can be "exhausted"
            depending on the option.
        """

        # updating the cost
        self.cost += self.minw

        # assumptions to remove
        self.garbage = set()

        if len(self.core_sels) != 1 or len(self.core_sums) > 0:
            # process selectors in the core
            self.process_sels()

            # process previously introducded sums in the core
            self.process_sums()

            if len(self.rels) > 1:
                # create a new cardunality constraint
                t = self.create_sum()

                # apply core exhaustion if required
                b = self.exhaust_core(t) if self.exhaust else 1

                if b:
                    # save the info about this sum and
                    # add its assumption literal
                    self.set_bound(t, b)
                else:
                    # impossible to satisfy any of these clauses
                    # they must become hard
                    for relv in self.rels:
                        self.oracle.add_clause([relv])
                        
        else:
            # unit cores are treated differently
            # (their negation is added to the hard part)            
            #self.hard.append([-self.core_sels[0]])
            self.oracle.add_clause([-self.core_sels[0]])
            self.garbage.add(self.core_sels[0])

        # remove unnecessary assumptions
        self.filter_assumps()

    def adapt_am1(self):
        """
            Detect and adapt intrinsic AtMost1 constraints. Assume
            there is a subset of soft clauses
            :math:`\\mathcal{S}'\subseteq \\mathcal{S}` s.t.
            :math:`\sum_{c\in\\mathcal{S}'}{c\leq 1}`, i.e. at most
            one of the clauses of :math:`\\mathcal{S}'` can be
            satisfied.

            Each AtMost1 relationship between the soft clauses can be
            detected in the following way. The method traverses all
            soft clauses of the formula one by one, sets one
            respective selector literal to true and checks whether
            some other soft clauses are forced to be false. This is
            checked by testing if selectors for other soft clauses are
            unit-propagated to be false. Note that this method for
            detection of AtMost1 constraints is *incomplete*, because
            in general unit propagation does not suffice to test
            whether or not :math:`\\mathcal{F}\wedge l_i\\models
            \\neg{l_j}`.

            Each intrinsic AtMost1 constraint detected this way is
            handled by calling :func:`process_am1`.
        """

        # literal connections
        conns = collections.defaultdict(lambda: set([]))
        confl = []

        # prepare connections
        for l1 in self.sels:
            st, props = self.oracle.propagate(assumptions=[l1], phase_saving=2)
            if st:
                for l2 in props:
                    if -l2 in self.sels_set:
                        conns[l1].add(-l2)
                        conns[-l2].add(l1)
            else:
                # propagating this literal results in a conflict
                confl.append(l1)

        if confl:  # filtering out unnecessary connections
            ccopy = {}
            confl = set(confl)

            for l in conns:
                if l not in confl:
                    cc = conns[l].difference(confl)
                    if cc:
                        ccopy[l] = cc

            conns = ccopy
            confl = list(confl)

            # processing unit size cores
            for l in confl:
                self.core, self.minw = [l], self.wght[l]
                self.core_sels, self.core_sums = [l], []
                self.process_core()

            if self.verbose > 1:
                print('c unit cores found: {0}; cost: {1}'.format(len(confl),
                    self.cost))

        nof_am1 = 0
        len_am1 = []
        lits = set(conns.keys())
        while lits:
            am1 = [min(lits, key=lambda l: len(conns[l]))]

            for l in sorted(conns[am1[0]], key=lambda l: len(conns[l])):
                if l in lits:
                    for l_added in am1[1:]:
                        if l_added not in conns[l]:
                            break
                    else:
                        am1.append(l)

            # updating remaining lits and connections
            lits.difference_update(set(am1))
            for l in conns:
                conns[l] = conns[l].difference(set(am1))

            if len(am1) > 1:
                # treat the new atmost1 relation
                self.process_am1(am1)
                nof_am1 += 1
                len_am1.append(len(am1))

        # updating the set of selectors
        self.sels_set = set(self.sels)

        if self.verbose > 1 and nof_am1:
            print('c am1s found: {0}; avgsz: {1:.1f}; cost: {2}'.format(nof_am1,
                sum(len_am1) / float(nof_am1), self.cost))

    def process_am1(self, am1):
        """
            Process an AtMost1 relation detected by :func:`adapt_am1`.
            Note that given a set of soft clauses
            :math:`\\mathcal{S}'` at most one of which can be
            satisfied, one can immediately conclude that the formula
            has cost at least :math:`|\\mathcal{S}'|-1` (assuming
            *unweighted* MaxSAT). Furthermore, it is safe to replace
            all clauses of :math:`\\mathcal{S}'` with a single soft
            clause :math:`\sum_{c\in\\mathcal{S}'}{c}`.

            Here, input parameter ``am1`` plays the role of subset
            :math:`\\mathcal{S}'` mentioned above. The procedure bumps
            the MaxSAT cost by ``self.minw * (len(am1) - 1)``.

            All soft clauses involved in ``am1`` are replaced by a
            single soft clause, which is a disjunction of the
            selectors of clauses in ``am1``. The weight of the new
            soft clause is set to ``self.minw``.

            :param am1: a list of selectors connected by an AtMost1 constraint

            :type am1: list(int)
        """

        # assumptions to remove
        self.garbage = set()

        while len(am1) > 1:
            # computing am1's weight
            self.minw = min(map(lambda l: self.wght[l], am1))

            # pretending am1 to be a core, and the bound is its size - 1
            self.core_sels, b = am1, len(am1) - 1

            # incrementing the cost
            self.cost += b * self.minw

            # splitting and relaxing if needed
            self.process_sels()

            # updating the list of literals in am1 after splitting the weights
            am1 = list(filter(lambda l: l not in self.garbage, am1))

            # new selector
            selv = self.pool.id()

            # adding a new clause
            cl = [-l for l in self.rels] + [-selv]
            self.oracle.add_clause(cl)
            #self.soft.append([-l for l in self.rels] + [-selv])


            # integrating the new selector
            self.sels.append(selv)
            self.wght[selv] = self.minw
            self.smap[selv] = len(self.wght) - 1

        # removing unnecessary assumptions
        self.filter_assumps()

    def trim_core(self, core = None):
        """
            This method trims a previously extracted unsatisfiable
            core at most a given number of times. If a fixed point is
            reached before that, the method returns.
        """
        if core is None:
            core2trim = self.core
        else:
            core2trim = core
        for i in range(self.trim):
            # call solver with core assumption only
            # it must return 'unsatisfiable'
            self.oracle.solve(assumptions=core2trim)

            # extract a new core
            new_core = self.oracle.get_core()
            if len(new_core) == len(self.core):
                # stop if new core is not better than the previous one
                break

            # otherwise, update core
            self.core = new_core

    def minimize_core(self, core = None, keep_def = []):
        """
            Reduce a previously extracted core and compute an
            over-approximation of an MUS. This is done using the
            simple deletion-based MUS extraction algorithm.

            The idea is to try to deactivate soft clauses of the
            unsatisfiable core one by one while checking if the
            remaining soft clauses together with the hard part of the
            formula are unsatisfiable. Clauses that are necessary for
            preserving unsatisfiability comprise an MUS of the input
            formula (it is contained in the given unsatisfiable core)
            and are reported as a result of the procedure.

            During this core minimization procedure, all SAT calls are
            dropped after obtaining 1000 conflicts.
        """
        is_minimal = 0
        if not (core is None):
            self.core = core

        org_lens = len(self.core)

        if self.minz and len(self.core +keep_def ) > 1:
            self.core = sorted(self.core, key=lambda l: self.wght[l])
            

            
            keep = []
            if  (len(keep_def) > 0):
                keep  = keep_def
            #print(core, keep)
            core = self.core
            proj = keep + core 

            debug = False
            if debug:  print(f"min start {len(core)}/{len(keep)}")

            i = 0
            while len(core) > 0:
                to_test =  core[1:]
                #print(f"core {core} keep {keep} proj {proj}")

                if not (core[0] in proj):
                    #i = i+ 1
                    to_test = core[1:]
                    core = core[1:]
                    #print("continue")
                    continue

                keep = [c for c in keep if c in proj]

                
                
                if org_lens >  50: 
                    self.oracle.prop_budget(100000)
                else:
                    self.oracle.prop_budget(1000000)
                #print(prop)
                if self.oracle.solve_limited(assumptions= keep + to_test) == False:
                    newcore = self.oracle.get_core()
                    if (newcore is None):
                        newcore = []                    
                    proj =  newcore
                    # res, fixed = self.oracle.propagate(assumptions=newcore)
                    # print(res, fixed, newcore)                    
                elif self.oracle.get_status() == True:
                    keep.append(core[0])

                else:
                    keep.append(core[0])
                    is_minimal += 1
                if debug: print(f"{self.oracle.get_status()} {core[0]}")
                core = core[1:]
                    #break
                

            self.core =  keep
            #print(f"final {keep}")
            #assert(self.oracle.solve_limited(assumptions=self.core) == False)
            if debug: print(f"min end {len(self.core)}")
        return is_minimal
    def minimize_core_unfolding (self, core, unfolding, keep_def = []):
        """
            Reduce a previously extracted core and compute an
            over-approximation of an MUS. This is done using the
            simple deletion-based MUS extraction algorithm.

            The idea is to try to deactivate soft clauses of the
            unsatisfiable core one by one while checking if the
            remaining soft clauses together with the hard part of the
            formula are unsatisfiable. Clauses that are necessary for
            preserving unsatisfiability comprise an MUS of the input
            formula (it is contained in the given unsatisfiable core)
            and are reported as a result of the procedure.

            During this core minimization procedure, all SAT calls are
            dropped after obtaining 1000 conflicts.
        """
        if not (core is None):
            self.core = core
        is_minimal = 0
        total_soft  =[]
        for k,v in unfolding.items():
            #print(k,v)
            total_soft = total_soft +  v
        #print(f"keep {keep_def} total_soft {total_soft}")
        org_lens = len(self.core)
        if not self.minz:
             self.core = total_soft

        if self.minz and len(total_soft+keep_def) > 1:
            self.core = sorted(self.core, key=lambda l: self.wght[l])
            

            keep = []
            if  (len(keep_def) > 0):
                keep  = keep_def
            core = self.core
            proj = core + keep
            #print(f"proj {proj}")  

            debug = False
            if debug:  print(f"min start {len(core)}/{len(keep)}")

            while len(core) > 0:
                #print(f"{0}: core {core}, {core[0]}, proj {proj}")
                #assert(self.oracle.solve_limited(assumptions=core + keep) == False)
                if core[0] in unfolding:
                    #print("~~", proj, core[0])
                    if not(core[0] in proj):
                        core = core[1:]
                        continue
                    j = proj.index(core[0])
                    proj = proj[:j]+ unfolding[core[0]] + proj[(j+1):] 
                    core = unfolding[core[0]] + core[1:]                    

                to_test = core[1:]
                keep = [c for c in keep if c in proj]
                        

                if not (core[0] in proj):
                    #i = i+ 1
                    #print(f"continue {core[0] }")

                    to_test = core[1:]
                    core = core[1:]
                    continue
                #print("starting")
                if org_lens >  50: 
                    self.oracle.prop_budget(100000)
                else:
                    self.oracle.prop_budget(1000000)
                #print(to_test+keep)
   
                if self.oracle.solve_limited(assumptions= keep + to_test) == False:
                    newcore = self.oracle.get_core()
                    if (newcore is None):
                        newcore = []                    
                    proj =  newcore
                    #assert(self.oracle.solve_limited(assumptions=proj) == False)


                elif self.oracle.get_status() == True:
                    keep.append(core[0])
                else:
                    keep.append(core[0])
                    is_minimal += 1
                #assert(self.oracle.solve_limited(assumptions=core + keep) == False)

                core = core[1:]

                    #break
                if debug: print(f"{self.oracle.get_status() }")
                #assert(self.oracle.solve_limited(assumptions=core + keep) == False)

            self.core =  keep
            #print(keep)
            #assert(self.oracle.solve_limited(assumptions=self.core) == False)
            if debug: print(f"min end {len(self.core)}")
        return is_minimal

    def exhaust_core(self, tobj):
        """
            Exhaust core by increasing its bound as much as possible.
            Core exhaustion was originally referred to as *cover
            optimization* in [6]_.

            Given a totalizer object ``tobj`` representing a sum of
            some *relaxation* variables :math:`r\in R` that augment
            soft clauses :math:`\\mathcal{C}_r`, the idea is to
            increase the right-hand side of the sum (which is equal to
            1 by default) as much as possible, reaching a value
            :math:`k` s.t. formula
            :math:`\\mathcal{H}\wedge\\mathcal{C}_r\wedge(\sum_{r\in
            R}{r\leq k})` is still unsatisfiable while increasing it
            further makes the formula satisfiable (here
            :math:`\\mathcal{H}` denotes the hard part of the
            formula).

            The rationale is that calling an oracle incrementally on a
            series of slightly modified formulas focusing only on the
            recently computed unsatisfiable core and disregarding the
            rest of the formula may be practically effective.
        """

        # the first case is simpler
        if self.oracle.solve(assumptions=[-tobj.rhs[1]]):
            return 1
        else:
            self.cost += self.minw

        for i in range(2, len(self.rels)):
            # saving the previous bound
            self.tobj[-tobj.rhs[i - 1]] = tobj
            self.bnds[-tobj.rhs[i - 1]] = i - 1

            # increasing the bound
            self.update_sum(-tobj.rhs[i - 1])

            if self.oracle.solve(assumptions=[-tobj.rhs[i]]):
                # the bound should be equal to i
                return i

            # the cost should increase further
            self.cost += self.minw

        return None

    def process_sels(self):
        """
            Process soft clause selectors participating in a new core.
            The negation :math:`\\neg{s}` of each selector literal
            :math:`s` participating in the unsatisfiable core is added
            to the list of relaxation literals, which will be later
            used to create a new totalizer object in
            :func:`create_sum`.

            If the weight associated with a selector is equal to the
            minimal weight of the core, e.g. ``self.minw``, the
            selector is marked as garbage and will be removed in
            :func:`filter_assumps`. Otherwise, the clause is split as
            described in [1]_.
        """

        # new relaxation variables
        self.rels = []

        for l in self.core_sels:
            #print(f"l {l}, self.wght[l] {self.wght[l]}")
            if self.wght[l] == self.minw:
                # marking variable as being a part of the core
                # so that next time it is not used as an assump
                self.garbage.add(l)
            else:
                # do not remove this variable from assumps
                # since it has a remaining non-zero weight
                self.wght[l] -= self.minw

            # reuse assumption variable as relaxation
            self.rels.append(-l)


    def process_sums_one_lit(self, l):
        """
            Process cardinality sums participating in a new core.
            Whenever necessary, some of the sum assumptions are
            removed or split (depending on the value of
            ``self.minw``). Deleted sums are marked as garbage and are
            dealt with in :func:`filter_assumps`.

            In some cases, the process involves updating the
            right-hand sides of the existing cardinality sums (see the
            call to :func:`update_sum`). The overall procedure is
            detailed in [1]_.
        """

        if self.wght[l] == self.minw:
            # marking variable as being a part of the core
            # so that next time it is not used as an assump
            self.garbage.add(l)
        else:
            # do not remove this variable from assumps
            # since it has a remaining non-zero weight
            self.wght[l] -= self.minw

        # increase bound for the sum
        t, b = self.update_sum(l)

        # updating bounds and weights
        if b < len(t.rhs):
            lnew = -t.rhs[b]
            if lnew in self.garbage:
                self.garbage.remove(lnew)
                self.wght[lnew] = 0

            if lnew not in self.wght:
                self.set_bound(t, b)
            else:
                self.wght[lnew] += self.minw

        # put this assumption to relaxation vars
        self.rels.append(-l)


    def process_sums(self):
        """
            Process cardinality sums participating in a new core.
            Whenever necessary, some of the sum assumptions are
            removed or split (depending on the value of
            ``self.minw``). Deleted sums are marked as garbage and are
            dealt with in :func:`filter_assumps`.

            In some cases, the process involves updating the
            right-hand sides of the existing cardinality sums (see the
            call to :func:`update_sum`). The overall procedure is
            detailed in [1]_.
        """

        for l in self.core_sums:
            #print(f"l {l}")
            if (l in self.upperlevel) or (l in self.maxreslevel):            
                if l in self.upperlevel:
                    base = self.upperlevel[l]["base"]
                elif l in self.maxreslevel:
                    base = self.maxreslevel[l]["base"]
                else:
                    assert False

                self.garbage.add(l)
                for r in base:
                    if self.wght[r] == self.minw:
                        # marking variable as being a part of the core
                        # so that next time it is not used as an assump
                        self.garbage.add(r)
                        
                    else:
                        # do not remove this variable from assumps
                        # since it has a remaining non-zero weight
                        self.wght[r] -= self.minw

                self.rels.append(-l)             
            else:
                self.process_sums_one_lit(l)

    def create_sum(self, bound=1):
        """
            Create a totalizer object encoding a cardinality
            constraint on the new list of relaxation literals obtained
            in :func:`process_sels` and :func:`process_sums`. The
            clauses encoding the sum of the relaxation literals are
            added to the SAT oracle. The sum of the totalizer object
            is encoded up to the value of the input parameter
            ``bound``, which is set to ``1`` by default.

            :param bound: right-hand side for the sum to be created
            :type bound: int

            :rtype: :class:`.ITotalizer`

            Note that if Minicard is used as a SAT oracle, native
            cardinality constraints are used instead of
            :class:`.ITotalizer`.
        """

        if not self.oracle.supports_atmost():  # standard totalizer-based encoding
            # new totalizer sum
            t = ITotalizer(lits=self.rels, ubound=bound, top_id=self.pool.top)

            # updating top variable id
            self.pool.top = t.top_id

            # adding its clauses to oracle
            for cl in t.cnf.clauses:
                self.oracle.add_clause(cl)
        else:
            assert(False)
            # for minicard, use native cardinality constraints instead of the
            # standard totalizer, i.e. create a new (empty) totalizer sum and
            # fill it with the necessary data supported by minicard
            t = ITotalizer()
            t.lits = self.rels

            # a new variable will represent the bound
            bvar = self.pool.id()

            # proper initial bound
            t.rhs = [None] * (len(t.lits))
            t.rhs[bound] = bvar

            # new atmostb constraint instrumented with
            # an implication and represented natively
            rhs = len(t.lits)
            amb = [[-bvar] * (rhs - bound) + t.lits, rhs]

            # add constraint to the solver
            self.oracle.add_atmost(*amb)

        return t

    def update_sum(self, assump):
        """
            The method is used to increase the bound for a given
            totalizer sum. The totalizer object is identified by the
            input parameter ``assump``, which is an assumption literal
            associated with the totalizer object.

            The method increases the bound for the totalizer sum,
            which involves adding the corresponding new clauses to the
            internal SAT oracle.

            The method returns the totalizer object followed by the
            new bound obtained.

            :param assump: assumption literal associated with the sum
            :type assump: int

            :rtype: :class:`.ITotalizer`, int

            Note that if Minicard is used as a SAT oracle, native
            cardinality constraints are used instead of
            :class:`.ITotalizer`.
        """

        # getting a totalizer object corresponding to assumption
        t = self.tobj[assump]

        # increment the current bound
        b = self.bnds[assump] + 1

        if not self.oracle.supports_atmost():  # the case of standard totalizer encoding
            # increasing its bound
            t.increase(ubound=b, top_id=self.pool.top)

            # updating top variable id
            self.pool.top = t.top_id

            # adding its clauses to oracle
            if t.nof_new:
                for cl in t.cnf.clauses[-t.nof_new:]:
                    self.oracle.add_clause(cl)
        else:  # the case of cardinality constraints represented natively
            # right-hand side is always equal to the number of input literals
            rhs = len(t.lits)

            if b < rhs:
                # creating an additional bound
                if not t.rhs[b]:
                    t.rhs[b] = self.pool.id()

                # a new at-most-b constraint
                amb = [[-t.rhs[b]] * (rhs - b) + t.lits, rhs]
                self.oracle.add_atmost(*amb)

        return t, b

    def set_bound(self, tobj, rhs):
        """
            Given a totalizer sum and its right-hand side to be
            enforced, the method creates a new sum assumption literal,
            which will be used in the following SAT oracle calls.

            :param tobj: totalizer sum
            :param rhs: right-hand side

            :type tobj: :class:`.ITotalizer`
            :type rhs: int
        """

        # saving the sum and its weight in a mapping
        self.tobj[-tobj.rhs[rhs]] = tobj
        self.bnds[-tobj.rhs[rhs]] = rhs
        self.wght[-tobj.rhs[rhs]] = self.minw

        # adding a new assumption to force the sum to be at most rhs
        self.sums.append(-tobj.rhs[rhs])
        return -tobj.rhs[rhs]

    def filter_assumps(self):
        """
            Filter out unnecessary selectors and sums from the list of
            assumption literals. The corresponding values are also
            removed from the dictionaries of bounds and weights.

            Note that assumptions marked as garbage are collected in
            the core processing methods, i.e. in :func:`process_core`,
            :func:`process_sels`, and :func:`process_sums`.
        """

        self.sels = list(filter(lambda x: x not in self.garbage, self.sels))
        self.sums = list(filter(lambda x: x not in self.garbage, self.sums))

        #self.bnds = {l: b for l, b in six.iteritems(self.bnds) if l not in self.garbage}
        #self.wght = {l: w for l, w in six.iteritems(self.wght) if l not in self.garbage}

        self.sels_set.difference_update(set(self.garbage))

        self.garbage.clear()


    def oracle_time(self):
        """
            Report the total SAT solving time.
        """

        return self.oracle.time_accum()

    def _map_extlit(self, l):
        """
            Map an external variable to an internal one if necessary.

            This method is used when new clauses are added to the
            formula incrementally, which may result in introducing new
            variables clashing with the previously used *clause
            selectors*. The method makes sure no clash occurs, i.e. it
            maps the original variables used in the new problem
            clauses to the newly introduced auxiliary variables (see
            :func:`add_clause`).

            Given an integer literal, a fresh literal is returned. The
            returned integer has the same sign as the input literal.

            :param l: literal to map
            :type l: int

            :rtype: int
        """

        v = abs(l)

        if v in self.vmap.e2i:
            return int(copysign(self.vmap.e2i[v], l))
        else:
            i = self.pool.id()

            self.vmap.e2i[v] = i
            self.vmap.i2e[i] = v

            return int(copysign(i, l))


#
#==============================================================================
class RC2Stratified(RC2, object):
    """
        RC2 augmented with BLO and stratification techniques. Although
        class :class:`RC2` can deal with weighted formulas, there are
        situations when it is necessary to apply additional heuristics
        to improve the performance of the solver on weighted MaxSAT
        formulas. This class extends capabilities of :class:`RC2` with
        two heuristics, namely

        1. Boolean lexicographic optimization (BLO) [5]_
        2. diversity-based stratification [6]_
        3. cluster-based stratification

        To specify which heuristics to apply, a user can assign the ``blo``
        parameter to one of the values (by default it is set to ``'div'``):

        - ``'basic'`` ('BLO' only)
        - ``div`` ('BLO' + diversity-based stratification)
        - ``cluster`` ('BLO' + cluster-based stratification)
        - ``full`` ('BLO' + diversity- + cluster-based stratification)

        Except for the aforementioned additional techniques, every other
        component of the solver remains as in the base class :class:`RC2`.
        Therefore, a user is referred to the documentation of :class:`RC2` for
        details.
    """

    def __init__(self, formula, solver='g3', adapt=False, blo='div',
            exhaust=False, hybrid = False, closure = False, ilp = 0, incr=False, minz=False, nohard=False, trim=0,
            relax='rc2', verbose=0):
        """
            Constructor.
        """

        # calling the constructor for the basic version
        super(RC2Stratified, self).__init__(formula, solver=solver,
                adapt=adapt, exhaust=exhaust, hybrid = hybrid, closure=closure, ilp = ilp, incr=incr, minz=minz, trim=trim,relax =relax,
                verbose=verbose)

        self.levl = 0    # initial optimization level
        self.blop = []   # a list of blo levels

     

        # BLO strategy
        assert blo and blo in blomap, 'Unknown BLO strategy'
        self.bstr = blomap[blo]

        # do clause hardening
        self.hard = nohard == False

        # backing up selectors
        self.bckp, self.bckp_set = self.sels, self.sels_set
        self.sels = []

        # initialize Boolean lexicographic optimization
        self.init_wstr()

    def init_wstr(self):
        """
            Compute and initialize optimization levels for BLO and
            stratification. This method is invoked once, from the
            constructor of an object of :class:`RC2Stratified`. Given
            the weights of the soft clauses, the method divides the
            MaxSAT problem into several optimization levels.
        """

        # a mapping for stratified problem solving,
        # i.e. from a weight to a list of selectors
        self.wstr = collections.defaultdict(lambda: [])

        for s, w in six.iteritems(self.wght):
            self.wstr[w].append(s)

        # sorted list of distinct weight levels
        self.blop = sorted([w for w in self.wstr], reverse=True)

        # diversity parameter for stratification
        self.sdiv = len(self.blop) / 2.0

        # number of finished levels
        self.done = 0

    def compute(self):
        """
            This method solves the MaxSAT problem iteratively. Each
            optimization level is tackled the standard way, i.e. by
            calling :func:`compute_`. A new level is started by
            calling :func:`next_level` and finished by calling
            :func:`finish_level`. Each new optimization level
            activates more soft clauses by invoking
            :func:`activate_clauses`.
        """

        if self.done == 0 and self.levl != None:
            # it is a fresh start of the solver
            # i.e. no optimization level is finished yet

            # first attempt to get an optimization level
            self.next_level()

            while self.levl != None and self.done < len(self.blop):
                # add more clauses
                self.done = self.activate_clauses(self.done)

                if self.verbose > 1:
                    print('c wght str:', self.blop[self.levl])

                # call RC2
                if self.compute_() == False:
                    return

                # updating the list of distinct weight levels
                self.blop = sorted([w for w in self.wstr], reverse=True)

                if self.done < len(self.blop):
                    if self.verbose > 1:
                        print('c curr opt:', self.cost)

                    # done with this level
                    if self.hard:
                        # harden the clauses if necessary
                        self.finish_level()

                    self.levl += 1

                    # get another level
                    self.next_level()

                    if self.verbose > 1:
                        print('c')
        else:
            # we seem to be in the model enumeration mode
            # with the first model being already computed
            # i.e. all levels are finished and so all clauses are present
            # thus, we need to simply call RC2 for the next model
            self.done = -1  # we are done with stratification, disabling it
            if self.compute_() == False:
                return

        # extracting a model
        self.model = self.oracle.get_model()

        if self.model is None and self.pool.top == 0:
            # we seem to have been given an empty formula
            # so let's transform the None model returned to []
            self.model = []

        self.model = filter(lambda l: abs(l) in self.vmap.i2e, self.model)
        self.model = map(lambda l: int(copysign(self.vmap.i2e[abs(l)], l)), self.model)
        self.model = sorted(self.model, key=lambda l: abs(l))

        return self.model

    def next_level(self):
        """
            Compute the next optimization level (starting from the
            current one). The procedure represents a loop, each
            iteration of which checks whether or not one of the
            conditions holds:

            - partial BLO condition
            - diversity-based stratification condition
            - cluster-based stratification condition

            If any of these holds, the loop stops.
        """

        if self.levl >= len(self.blop):
            self.levl = None
            return

        # determining which heuristics to use
        div_str, clu_str = (self.bstr >> 1) & 1, (self.bstr >> 2) & 1

        # cluster of weights to build (if needed)
        cluster = [self.levl]
        print(self.blop)
        while self.levl < len(self.blop) - 1:
            # current weight
            wght = self.blop[self.levl]

            # number of selectors with weight less than current weight
            numr = sum([len(self.wstr[w]) for w in self.blop[(self.levl + 1):]])

            # sum of their weights
            sumr = sum([w * len(self.wstr[w]) for w in self.blop[(self.levl + 1):]])

            # partial BLO
            if wght > sumr and sumr != 0:
                break

            # diversity-based stratification
            if div_str and numr / float(len(self.blop) - self.levl - 1) > self.sdiv:
                break

            # last resort = cluster-based stratification
            if clu_str:
                # is the distance from current weight to the cluster
                # being built larger than the distance to the mean of
                # smaller weights?
                numc = sum([len(self.wstr[self.blop[l]]) for l in cluster])
                sumc = sum([self.blop[l] * len(self.wstr[self.blop[l]]) for l in cluster])

                if abs(wght - sumc / numc) > abs(wght - sumr / numr):
                    # remaining weights are too far from the cluster; stop
                    # here and report the splitting to be last-added weight
                    self.levl = cluster[-1]
                    break

                cluster.append(self.levl)

            self.levl += 1

    def activate_clauses(self, beg):
        """
            This method is used for activating the clauses that belong
            to optimization levels up to the newly computed level. It
            also reactivates previously deactivated clauses (see
            :func:`process_sels` and :func:`process_sums` for
            details).
        """

        end = min(self.levl + 1, len(self.blop))

        for l in range(beg, end):
            for sel in self.wstr[self.blop[l]]:
                if sel in self.bckp_set:
                    self.sels.append(sel)
                else:
                    self.sums.append(sel)

        # updating set of selectors
        self.sels_set = set(self.sels)

        return end

    def finish_level(self):
        """
            This method does postprocessing of the current
            optimization level after it is solved. This includes
            *hardening* some of the soft clauses (depending on their
            remaining weights) and also garbage collection.
        """

        # assumptions to remove
        self.garbage = set()

        # sum of weights of the remaining levels
        sumw = sum([w * len(self.wstr[w]) for w in self.blop[(self.levl + 1):]])

        # trying to harden selectors and sums
        for s in self.sels + self.sums:
            if self.wght[s] > sumw:
                self.oracle.add_clause([s])
                self.garbage.add(s)

        if self.verbose > 1:
            print('c hardened:', len(self.garbage))

        # remove unnecessary assumptions
        self.filter_assumps()

    def process_am1(self, am1):
        """
            Due to the solving process involving multiple optimization
            levels to be treated individually, new soft clauses for
            the detected intrinsic AtMost1 constraints should be
            remembered. The method is a slightly modified version of
            the base method :func:`RC2.process_am1` taking care of
            this.
        """

        # assumptions to remove
        self.garbage = set()

        # clauses to deactivate
        to_deactivate = set([])

        while len(am1) > 1:
            # computing am1's weight
            self.minw = min(map(lambda l: self.wght[l], am1))

            # pretending am1 to be a core, and the bound is its size - 1
            self.core_sels, b = am1, len(am1) - 1

            # incrementing the cost
            self.cost += b * self.minw

            # splitting and relaxing if needed
            super(RC2Stratified, self).process_sels()

            # updating the list of literals in am1 after splitting the weights
            am1 = list(filter(lambda l: l not in self.garbage, am1))

            # new selector
            selv = self.pool.id()

            # adding a new clause
            cl = [-l for l in self.rels] + [-selv]
            self.oracle.add_clause(cl)


            # integrating the new selector
            self.sels.append(selv)
            self.wght[selv] = self.minw
            self.smap[selv] = len(self.wght) - 1

            # do not forget this newly selector!
            self.bckp_set.add(selv)

            if self.done != -1 and self.wght[selv] < self.blop[self.levl]:
                self.wstr[self.wght[selv]].append(selv)
                to_deactivate.add(selv)

        # marking all remaining literals with small weights to be deactivated
        for l in am1:
            if self.done != -1 and self.wght[l] < self.blop[self.levl]:
                self.wstr[self.wght[l]].append(l)
                to_deactivate.add(l)

        # deactivating unnecessary selectors
        self.sels = list(filter(lambda x: x not in to_deactivate, self.sels))

        # removing unnecessary assumptions
        self.filter_assumps()

    def process_sels(self):
        """
            A redefined version of :func:`RC2.process_sels`. The only
            modification affects the clauses whose weight after
            splitting becomes less than the weight of the current
            optimization level. Such clauses are deactivated and to be
            reactivated at a later stage.
        """

        # new relaxation variables
        self.rels = []

        # selectors that should be deactivated (but not removed completely)
        to_deactivate = set([])

        for l in self.core_sels:
            if self.wght[l] == self.minw:
                # marking variable as being a part of the core
                # so that next time it is not used as an assump
                self.garbage.add(l)
            else:
                # do not remove this variable from assumps
                # since it has a remaining non-zero weight
                self.wght[l] -= self.minw

                # deactivate this assumption and put at a lower level
                # if self.done != -1, i.e. if stratification is disabled
                if self.done != -1 and self.wght[l] < self.blop[self.levl]:
                    self.wstr[self.wght[l]].append(l)
                    to_deactivate.add(l)

            # reuse assumption variable as relaxation
            self.rels.append(-l)

        # deactivating unnecessary selectors
        self.sels = list(filter(lambda x: x not in to_deactivate, self.sels))

    def process_sums(self):
        """
            A redefined version of :func:`RC2.process_sums`. The only
            modification affects the clauses whose weight after
            splitting becomes less than the weight of the current
            optimization level. Such clauses are deactivated and to be
            reactivated at a later stage.
        """

        # sums that should be deactivated (but not removed completely)
        to_deactivate = set([])

        for l in self.core_sums:


            if (l in self.upperlevel) or (l in self.maxreslevel):            
                if self.wght[l] == self.minw:
                    # marking variable as being a part of the core
                    # so that next time it is not used as an assump
                    self.garbage.add(l)
                else:
                    # do not remove this variable from assumps
                    # since it has a remaining non-zero weight
                    self.wght[l] -= self.minw

                    if self.done != -1 and self.wght[l] < self.blop[self.levl]:
                        self.wstr[self.wght[l]].append(l)
                        to_deactivate.add(l)

            else:
                if self.wght[l] == self.minw:
                    # marking variable as being a part of the core
                    # so that next time it is not used as an assump
                    self.garbage.add(l)
                else:
                    # do not remove this variable from assumps
                    # since it has a remaining non-zero weight
                    self.wght[l] -= self.minw

                    # # deactivate this assumption and put at a lower level
                    # # if self.done != -1, i.e. if stratification is disabled
                    if self.done != -1 and self.wght[l] < self.blop[self.levl]:
                        self.wstr[self.wght[l]].append(l)
                        to_deactivate.add(l)

                # increase bound for the sum
                t, b = self.update_sum(l)

                # updating bounds and weights
                if b < len(t.rhs):
                    lnew = -t.rhs[b]
                    if lnew in self.garbage:
                        self.garbage.remove(lnew)
                        self.wght[lnew] = 0

                    if lnew not in self.wght:
                        self.set_bound(t, b)
                    else:
                        self.wght[lnew] += self.minw

            # put this assumption to relaxation vars
            self.rels.append(-l)

        # deactivating unnecessary sums
        self.sums = list(filter(lambda x: x not in to_deactivate, self.sums))


#
#==============================================================================
def parse_options():
    """
        Parses command-line option
    """

    try:
        opts, args = getopt.getopt(sys.argv[1:], 'ab:c:e:hil:mps:tr:uvxy',
                ['adapt', 'block=', 'comp=', 'enum=', 'exhaust', 'closure', 'ilp=',  'help',
                    'incr', 'blo=', 'minimize', 'solver=', 'trim=', 'relax=','verbose',
                    'vnew'])
    except getopt.GetoptError as err:
        sys.stderr.write(str(err).capitalize())
        usage()
        sys.exit(1)

    adapt = False
    block = 'model'
    exhaust = False
    cmode = None
    to_enum = 1
    incr = False
    blo = 'none'
    minz = False
    solver = 'g3'
    trim = 0
    relax='rc2'
    verbose = 1
    vnew = False
    hybrid = False
    closure = False
    ilp = 0

    for opt, arg in opts:
        if opt in ('-a', '--adapt'):
            adapt = True
        elif opt in ('-b', '--block'):
            block = str(arg)
        elif opt in ('-c', '--comp'):
            cmode = str(arg)
        elif opt in ('-e', '--enum'):
            to_enum = str(arg)
            if to_enum != 'all':
                to_enum = int(to_enum)
            else:
                to_enum = 0
        elif opt in ('-h', '--help'):
            usage()
            sys.exit(0)
        elif opt in ('-i', '--incr'):
            incr = True
        elif opt in ('-l', '--blo'):
            blo = str(arg)
        elif opt in ('-m', '--minimize'):
            minz = True
        elif opt in ('-s', '--solver'):
            solver = str(arg)
        elif opt in ('-t', '--trim'):
            trim = int(arg)
        elif opt in ('-v', '--verbose'):
            verbose += 1
        elif opt == '--vnew':
            vnew = True
        elif opt in ('-x', '--exhaust'):
            exhaust = True
        elif opt in ('-y', '--hybrid'):
            hybrid = True
        elif opt in ('-u', '--closure'):
            closure = True
        elif opt in ('-p', '--ilp'):
            ilp = int(arg)            
        elif opt in ('-r', '--relax'):
            relax = str(arg) 
            assert(relax in ['mr1a', 'mr1b', 'mr1c', 'mr2a', 'mr2b',  'mr2c', 'mr1d', 'mr2d', 'rc2'])
        else:
            assert False, 'Unhandled option: {0} {1}'.format(opt, arg)


    # solution blocking
    bmap = {'mcs': -1, 'mcses': -1, 'model': 0, 'models': 0, 'mss': 1, 'msses': 1}
    assert block in bmap, 'Unknown solution blocking'
    block = bmap[block]
    return adapt, blo, block, cmode, to_enum, exhaust, hybrid, closure, ilp, incr, minz, \
            solver, trim, relax, verbose, vnew, args


#
#==============================================================================
def usage():
    """
        Prints usage message.
        """

    print('Usage:', os.path.basename(sys.argv[0]), '[options] dimacs-file')
    print('Options:')
    print('        -a, --adapt              Try to adapt (simplify) input formula')
    print('        -b, --block=<string>     When enumerating MaxSAT models, how to block previous solutions')
    print('                                 Available values: mcs, model, mss (default = model)')
    print('        -c, --comp=<string>      Enable one of the MSE18 configurations')
    print('                                 Available values: a, b, none (default = none)')
    print('        -e, --enum=<int>         Number of MaxSAT models to compute')
    print('                                 Available values: [1 .. INT_MAX], all (default = 1)')
    print('        -h, --help               Show this message')
    print('        -i, --incr               Use SAT solver incrementally (only for g3 and g4)')
    print('        -l, --blo=<string>       Use BLO and stratification')
    print('                                 Available values: basic, div, cluster, none, full (default = none)')
    print('        -m, --minimize           Use a heuristic unsatisfiable core minimizer')
    print('        -s, --solver=<string>    SAT solver to use')
    print('                                 Available values: g3, g4, lgl, mcb, mcm, mpl, m22, mc, mgh (default = g3)')
    print('        -t, --trim=<int>         How many times to trim unsatisfiable cores')
    print('                                 Available values: [0 .. INT_MAX] (default = 0)')
    print('        -v, --verbose            Be verbose')
    print('        --vnew                   Print v-line in the new format')
    print('        -x, --exhaust            Exhaust new unsatisfiable cores')
    print('        -y, --hybrid             Hybrid on')
    print('        -u, --closure            Closure on')
    print('        -p, --ilp                ILP on')
    


#
#==============================================================================
if __name__ == '__main__':
    adapt, blo, block, cmode, to_enum, exhaust, hybrid, closure, ilp, incr, minz, solver, trim, \
            relax, verbose, vnew, files = parse_options()


    if files:
        # parsing the input formula
        if re.search('\.wcnf[p|+]?(\.(gz|bz2|lzma|xz))?$', files[0]):
            formula = WCNFPlus(from_file=files[0])
        else:  # expecting '*.cnf[,p,+].*'
            formula = CNFPlus(from_file=files[0]).weighted()
        # enabling the competition mode
        if cmode:
            assert cmode in ('a', 'b'), 'Wrong MSE18 mode chosen: {0}'.format(cmode)
            adapt, blo, solver, exhaust, verbose = True, 'div', 'g4',  True,  3

            if cmode == 'a':
                trim = 5 if max(formula.wght) > min(formula.wght) else 0
                minz = False
            else:
                trim, minz = 0, True

            # trying to use unbuffered standard output
            if sys.version_info.major == 2:
                sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)

        # deciding whether or not to stratify
        if blo != 'none' and max(formula.wght) > min(formula.wght):
            MXS = RC2Stratified
        else:
            MXS = RC2

        

        # starting the solver
        with MXS(formula, solver=solver, adapt=adapt, exhaust=exhaust, hybrid = hybrid, closure= closure, ilp = ilp,
                incr=incr, minz=minz, trim=trim, relax=relax, verbose=verbose) as rc2:
            x,y = rc2.oracle.propagate()
            if isinstance(rc2, RC2Stratified):
                rc2.bstr = blomap[blo]  # select blo strategy
                if to_enum != 1:
                    # no clause hardening in case we enumerate multiple models
                    print('c hardening is disabled for model enumeration')
                    rc2.hard = False

            optimum_found = False
            for i, model in enumerate(rc2.enumerate(block=block), 1):
                optimum_found = True

                if verbose:
                    if i == 1:
                        print('s OPTIMUM FOUND')
                        print('o {0}'.format(rc2.cost))

                    if verbose > 3:
                        if vnew:  # new format of the v-line
                            print('v', ''.join(str(int(l > 0)) for l in model))
                        else:
                            print('v', ' '.join([str(l) for l in model]))

                if i == to_enum:
                    break
            else:
                # needed for MSE'20
                if verbose > 2 and vnew and to_enum != 1 and block == 1:
                    print('v')

            if verbose:
                if not optimum_found:
                    print('s UNSATISFIABLE')
                elif to_enum != 1:
                    print('c models found:', i)

                if verbose > 1:
                    print('c oracle time: {0:.4f}'.format(rc2.oracle_time()))
