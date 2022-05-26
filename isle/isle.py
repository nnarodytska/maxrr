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
import copy
import getopt
import itertools
from math import copysign
import math
import os
import random
import time
from pysat.formula import CNFPlus, WCNFPlus, IDPool
from pysat.card import ITotalizer
from pysat.solvers import Solver, SolverNames
import re
import six
from six.moves import range
import sys
#import pprofile
from graphviz import Digraph
from ortools.sat.python import cp_model

from circuit import *
from forest import *
from  or_tools import SolverOR, solve_ortools
import operator
from threading import Timer
CIRCUITINJECT_FULL = 0
CIRCUITINJECT_TOP = 1
CIRCUITINJECT_DELAYED = 2 

\
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

        :type formula: :class:`.WCNF`
        :type solver: str
        :type adapt: bool
        :type exhaust: bool
        :type incr: bool
        :type minz: bool
        :type trim: int
        :type verbose: int
    """

    def __init__(self, formula, solver='g3', adapt=False, exhaust=False,
            incr=False, minz=False, trim=0, verbose=0, circuitinject = CIRCUITINJECT_FULL):
        """
            Constructor.
        """

        # saving verbosity level and other options
        self.verbose = verbose
        self.exhaust = exhaust
        self.solver = solver
        self.adapt = adapt
        self.minz = minz
        self.trim = trim
        self.circuitinject = circuitinject
        self.use_accum_oracle = True

        # clause selectors and mapping from selectors to clause ids
        self.sels,  self.sneg = [],  set([])

        # other MaxSAT related stuff
        self.pool = IDPool(start_from=formula.nv + 1)
        self.wght = {}  # weights of soft clauses
        self.sums = []  # totalizer sum assumptions
        self.cost = 0
        self.round = 0
        self.time = 0
        self.timer = time.time()
        self.build_time = 0
        self.sat_time = 0
        self.garbage = set()

        self.asm2nodes = {}
        self.ortools_on = False
        self.or_model =  None
        self.hints, self.or_ub, self.or_lb = None, None, -100
        if (self.ortools_on):
            self.or_model =  SolverOR()
        
        


        

        # mappings between internal and external variables
        VariableMap = collections.namedtuple('VariableMap', ['e2i', 'i2e'])
        self.vmap = VariableMap(e2i={}, i2e={})

        # initialize SAT oracle with hard clauses only
        self.init(formula, incr=incr)

        # core minimization is going to be extremely expensive
        # for large plain formulas, and so we turn it off here
        wght = self.wght.values()

        self.test_cores = []
        
        if (False):
            self.test_cores = [[180, 178, 177],
            [174, 182, 172, 176],
            [173, 184, 181],
            [185, 175, 179],
            [189, 199, 195],
            [203, 191, 183],
            [201, 187, 209, 207, 205, 197],]
            #[193, 211]]        
            self.sol = [-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12, -13, -14, -15, -16, -17, -18, -19, -20, -21, -22, -23, -24, -25, -26, -27, -28, -29, -30, -31, -32, -33, -34, -35, -36, -37, -38, -39, -40, -41, -42, -43, -44, -45, -46, -47, -48, -49, -50, -51, -52, -53, -54, -55, -56, -57, -58, -59, -60, -61, -62, -63, -64, -65, -66, -67, -68, -69, -70, -71, -72, -73, -74, -75, -76, -77, -78, -79, -80, -81, 82, -83, -84, -85, -86, -87, -88, -89, -90, -91, -92, -93, -94, -95, -96, -97, -98, -99, -100, 101, -102, -103, -104, -105, -106, -107, -108, -109, -110, -111, -112, 113, -114, -115, -116, -117, -118, -119, -120, -121, -122, 123, -124, -125, -126, -127, -128, -129, -130, -131, -132, -133, -134, -135, -136, -137, -138, -139, -140, -141, -142, -143, -144, -145, -146, -147, -148, -149, -150, -151, 152, -153, -154, -155, -156, -157, -158, -159, -160, -161, 162, -163, -164, -165, -166, -167, -168, -169, -170, -171, -172, -173, -174, 175, 176, -177, -178, 179, -180, 181, 182, 183,-184]
        else:
            self.sol = []

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
        self.oracle = Solver(name=self.solver, bootstrap_with=formula.hard,
                incr=incr, use_timer=True)


        self.formula = formula
        self.orig_formula = copy.deepcopy(formula)

        # adding soft clauses to oracle

        dublicated = {} 
        removable = []
        keep = {}
        self.orig_sels = []

        for i, cl in enumerate(self.formula.soft):
            selv = cl[0]  # if clause is unit, selector variable is its literal

            if len(cl) > 1:
                continue
            if selv not in dublicated:
                # record selector and its weight
                dublicated[selv] = self.formula.wght[i]
                keep[selv] = i
            else:
                # selector is not new; increment its weight
                dublicated[selv] += self.formula.wght[i]
                removable.append(i)

        removable = sorted(removable, reverse=True)
        for selv, w in dublicated.items():
            if not (selv in keep):
                continue

            i = keep[selv]
            self.formula.wght[i] = w

        for idx in removable:            
            self.formula.wght.pop(idx)        
            self.formula.soft.pop(idx)

        self.forest = []

        for i, cl in enumerate(self.formula.soft):
            selv = cl[0]  # if clause is unit, selector variable is its literal
            if len(cl) > 1:
                selv = self.pool.id()
                cl.append(-selv)            
                self.add_new_clause(cl, self.formula.hard, self.oracle)
            
            t = self.create_node(name = "{-selv}", u = selv,  v = selv,  weight = self.formula.wght[i],  type = INITIAL_SELECTOR, status = STATUS_ACTIVE)
            self.forest.append(t.u)

            
            if selv  in self.wght:         
                assert False, "we should not have duplicates"

        self.rebuild(init = True)


        # at this point internal and external variables are the same
        for v in range(1, formula.nv + 1):
            self.vmap.e2i[v] = v
            self.vmap.i2e[v] = v

        if self.verbose > 1:
            print('c formula: {0} vars, {1} hard, {2} soft'.format(formula.nv,
                len(self.formula.hard), len(self.formula.soft)))

        if (not self.orig_formula.hard and len(self.sels) > 100000 and min(self.orig_formula.wght) == max(self.orig_formula.wght)) or ( len(self.sels) > 500000 ):
            self.minz = False  
        print(self.minz)
        #exit()

    def create_node(self, name, u, v, weight, type, status, children = None, into_phase = 0):

        node = Circuit(name,        
                        u = u,
                        v = v, 
                        weight = weight, 
                        type = type, 
                        status = status,
                        children = children,
                        into_phase = into_phase
                        )        
        if (type == INITIAL_SELECTOR):
            self.orig_sels.append(u)

        self.asm2nodes[u] = node
        return node

    def rebuild(self, reactivate = False, init = False, debug = False):

        print("------------->  rebuild  <-----------------")
        


        if self.use_accum_oracle:
            if (init):
                self.oracle = Solver(name=self.solver, bootstrap_with=self.formula.hard, use_timer=True)
                if (self.or_model is not None): self.or_model.add_hards(self.formula)
                
            self.time = self.oracle.time_accum()
        else:    
            tm = time.time()
            try:
                self.time += self.oracle.time_accum()
            except:
                pass            
            self.oracle = Solver(name=self.solver, bootstrap_with=self.formula.hard, use_timer=True)
            self.build_time  += time.time() - tm


        prev_asm_len = len(self.sums + self.sels)
        if (prev_asm_len == 0):
            prev_asm_len = len(self.forest)
        else:
            prev_asm_len = prev_asm_len - 1
        self.sels, self.sums, self.sneg = [], [], set([])

        
        self.wght = {}  # weights of soft clauses
        active_u2l =  u_and_level_active(self.asm2nodes)

        sorted_active_u2l = {k: v for k, v in sorted(active_u2l.items(), key=lambda item: item[1])}

        for u, _ in sorted_active_u2l.items():
            #print(f"--------------{u}------------")
            node= forest_find_node(u, self.asm2nodes)
            #print(node)
            if node.type == INITIAL_SELECTOR:
                self.sels.append(node.u)
            else:
                self.sums.append(node.u)
            assert(node.status  == STATUS_ACTIVE)
            self.wght[node.u] =  node.weight

        if not (self.use_accum_oracle):
            u_nodes = forest_filter(self.asm2nodes, status = None)
            for i, u in enumerate(u_nodes):
                node = forest_find_node(u, self.asm2nodes)
                for v_cl in node.v_clauses:
                    #print(v_cl)
                    self.oracle.add_clause(v_cl)

                for u_cl in node.u_clauses:
                    #print(v_cl)
                    self.oracle.add_clause(u_cl)
                    


        # storing the set of selectors
        self.sels_set = set(self.sels)
        self.sums_set = set()
        print(f" self.sels  = {len(self.sels)}")
        print(f" self.sums  = {len(self.sums)}")
        #print(f" self.sels  = {(self.sels)}")
        #print(f" self.sums  = {sorted(self.sums)}")

        #print(len(self.sums + self.sels), prev_asm_len )

        # if not (reactivate):
        #     if not (len(self.sums + self.sels) <= prev_asm_len): 
        #         forest_build_graph(self.forest)        
        #     assert(len(self.sums + self.sels) <= prev_asm_len)


    def delete(self):
        """
            Explicit destructor of the internal SAT oracle and all the
            totalizer objects creating during the solving process.
        """

        if self.oracle:
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
        debug = False
        res = self.compute_()
        if debug: print(res)

        # or_model, or_model_ub = solve_ortools(self.formula, self.forest, to = 600)
        # print(self.)
        # exit()

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

    def reactivate(self, model):
        if (self.circuitinject == CIRCUITINJECT_DELAYED):
            return self.delayed_reactivation(model)
        else:
            return self.reactivation(model)

    def reactivation(self, model):
        #  selectors_nodes = []
        # for t in self.forest:
        #     get_nodes(t, selectors_nodes)
        #     # for node in selectors_nodes:
        #     #     print(node)
        # for node in selectors_nodes:
        #     u =  node.u
        #     print(u, model[u-1])

        #print("-------------")              
        u_waiting_selectors_nodes = forest_filter(self.asm2nodes, STATUS_WAITING)
        violated_waiting = 0
        for u in u_waiting_selectors_nodes:
            node = forest_find_node(u, self.asm2nodes)
            #print(u, model[u-1])
            #if u != model[u-1]:
            if(True):
                node.status = STATUS_ACTIVE
                violated_waiting += 1
        if violated_waiting == 0:
            print(f"sat model while waiting {len(u_waiting_selectors_nodes)}")
        else:
            print(f"reactivate {len(u_waiting_selectors_nodes)}")        
        
        return violated_waiting


    def delayed_reactivation(self, model = None, forest = None):
        #  selectors_nodes = []
        # for t in self.forest:
        #     get_nodes(t, selectors_nodes)
        #     # for node in selectors_nodes:
        #     #     print(node)
        # for node in selectors_nodes:
        #     u =  node.u
        #     print(u, model[u-1])

        #print("-------------")              
        if (forest is None):
            forest = self.forest
        u_folded_selectors_nodes = forest_filter(self.asm2nodes, STATUS_FOLDED)
        # for node in folded_selectors_nodes:
        #     print(node.__str__())
        violated_folded = 0
        #forest_build_graph(self.forest)
        for u in u_folded_selectors_nodes:
            node = forest_find_node(u, self.asm2nodes)
            #print(node)
            #print(u, model[u-1])
            if True:
            #if node.v != model[node.v-1]:
                self.delayed_resolution(circuits = [n.u for n in node.children], t = node, unfoldng = True)
                violated_folded += 1
        if violated_folded == 0:
            print(f"sat model while folded {len(u_folded_selectors_nodes)}")
        else:
            print(f"reactivate folded {violated_folded}/{len(u_folded_selectors_nodes)}")        
        
        #forest_build_graph(self.forest, fname= "g_"+GRAPH_PRINT_DEF)

        #self.circuitinject = CIRCUITINJECT_FULL
        return violated_folded



    def force_model(self, solution, force_flag = True):
        self.forced_model = force_flag
        self.model = []
        for k, v in solution.items():
            if (v <= 0):
                self.model.append(-(k-1))
            else:
                self.model.append(k-1)        

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

        if self.adapt:
            self.adapt_am1()
            self.rebuild(reactivate = True, init = True)
            
            #exit()

            #or_model, or_model_ub = solve_ortools(self.formula, self.forest)

        debug = False
        # main solving loop
        #if debug: print(self.sels + self.sums)
        unsat  = not self.oracle.solve(assumptions=self.sels + self.sums)
        #assert(self.oracle.solve(assumptions=self.sol))
        print(f"start  unsat {unsat}")

        while unsat:

            self.get_core()

            if not self.core:
                # core is empty, i.e. hard part is unsatisfiable
                return False
            self.process_core()
            #print(f"~~~~~~~~~~~~~~~~~~~~~~~~~ core {self.core} round {self.round}")

            if self.verbose > 1:
                print(f"c cost: {self.cost}; core sz: {len(self.core)}; soft sz: {len(self.sels) + len(self.sums)} {self.oracle_time():.4f}/{self.build_time:.4f}/{self.sat_time:.4f}")

            self.rebuild()
            
            if (self.or_model is not None): 
                #print(self.hints)
                
                hints, or_ub, or_lb = self.or_model.minimize(self.orig_sels, self.asm2nodes, hints = self.hints, lb = max(self.cost, self.or_lb),  ub = self.or_ub, to = 60)

                if (len(hints.items()) > 0 ): 
                    self.hints, self.or_ub, self.or_lb  = hints, or_ub, or_lb 
                    if (or_ub == or_lb):
                        self.force_model(hints)
                        self.cost = or_ub
                        return True

            # assert(self.oracle.solve(assumptions=self.sol))
            # model = self.oracle.get_model()
            # for s in self.sums+self.sels + [193, 197, 209, 187, 207, 205, 201, 214, 216]:
            #     try:
            #         print(s, model[s-1])
            #     except:
            #         pass

            # forest_build_graph(self.forest, fname= GRAPH_PRINT_DEF+f"-{self.round}-start")


            unsat  = not self.oracle.solve(assumptions=self.sels + self.sums)
            delayed_selectors_nodes = []
            if (not unsat):
                delayed_selectors_nodes = list(forest_filter(self.asm2nodes, status = STATUS_WAITING)) +  list(forest_filter(self.asm2nodes, status = STATUS_FOLDED))
            rebuild = 0
            while (not unsat) and len(delayed_selectors_nodes) > 0:
                tm = time.time()                     
                model = self.oracle.get_model()
                #forest_build_graph(self.forest, fname= GRAPH_PRINT_DEF+f"-{self.round}")
                nb_violated = self.reactivate(model)
                #forest_build_graph(self.forest, fname= "g_"+GRAPH_PRINT_DEF+f"-{self.round}")
                print(f"any violated? {nb_violated}")

                if (nb_violated == 0):
                    break

                self.rebuild(reactivate = True)
                # assert(self.oracle.solve(assumptions=self.sol))
                # model = self.oracle.get_model()
                # for s in self.sums+self.sels:
                #     print(s, model[s-1])
                
                #forest_build_graph(self.forest, fname= GRAPH_PRINT_DEF+f"-{self.round}-rebuild-{rebuild}")
                
                rebuild +=1

                unsat  = not self.oracle.solve(assumptions=self.sels + self.sums)
                self.sat_time  += time.time() - tm

                print("---", unsat)#, self.sels, self.sums)
                # if (self.cost >= 7) and unsat:
                #     for cl in self.formula.soft:
                #         print(cl)
                #     print(-172, -173, -174, 175, 176, -177, -178, 179, -180, 181, 182, 183,-184)
                #     #exit()
                
                if (debug):
                    forest_build_graph(self.forest, self.asm2nodes)
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
        if len(self.test_cores) > 0:                
            self.core = self.test_cores[0]
            self.test_cores = self.test_cores[1:]
            assert(not self.oracle.solve(assumptions=self.core))
        else:        
            self.core = self.oracle.get_core()

        if self.core:
            # try to reduce the core by trimming
            self.trim_core()

            # and by heuristic minimization
            self.minimize_core()

            # the core may be empty after core minimization
            if not self.core:
                return

            # core weight
            self.minw = min(map(lambda l: self.wght[l], self.core))

            # # dividing the core into two parts
            iter1, iter2 = itertools.tee(self.core)
            self.core_sels = list(l for l in iter1 if l in self.sels_set)
            self.core_sums = list(l for l in iter2 if l not in self.sels_set)



    def deactivate_sel(self, u):
        node  = forest_find_node(u, mapping = self.asm2nodes)
        node.status = STATUS_INACTIVE
        node.weight = 0
        self.garbage.add(u)

    def deactivate_unit(self, u):        
        node  = forest_find_node(u, mapping = self.asm2nodes)
        node.status = STATUS_INACTIVE        
        self.add_new_clause([-u], node.u_clauses, self.oracle, label = "", debug = False)
        

    def update_weight_sel(self, u, new_weight):
        node  = forest_find_node( u, mapping = self.asm2nodes)
        node.weight = new_weight

    
    def add_new_clause(self, cl, vec= None, oracle = None, label = "",  debug = False):
        if (vec is not None):
            vec.append(cl)  
        if (oracle is not None):
            oracle.add_clause(cl)
        if (self.or_model is not None): self.or_model.create_clauses_con(cl)
        if (debug): print(label,  cl)


    def added_folded_gate(self, t, v, half, full_encoding = True, debug = False):
        cl = [v]
        label =  "------> added_folded_gate"        
        for u in half:
            self.add_new_clause ([-v,u], t.v_clauses, self.oracle, label, debug)

            cl.append(-u)
        if (full_encoding):
            self.add_new_clause (cl, t.v_clauses, self.oracle, label, debug)


    def added_gate_u(self, t,  core0, core1, full_encoding = False, debug = False):
        #u <-> core[0] \/ core[1]
        #-u \/ core[0] \/ core[1]
        #u \/ -core[0] 
        #u \/ -core[1]
        label =  "------> added_gate_u"
        self.add_new_clause ([-t.u, core0, core1], t.u_clauses, self.oracle, label)

        if (full_encoding):
            self.add_new_clause ([t.u, -core0], t.u_clauses, self.oracle, label, debug)
            self.add_new_clause ([t.u, -core1], t.u_clauses, self.oracle, label, debug)

    def added_gate_v(self, t,  core0, core1, full_encoding = False, debug = False):
        #v <-> core[0] /\ core[1]
        #v \/ not core[0] \/ not core[1]
        #not v  \/ core[0] 
        #not v  \/  core[1]
            
        label =  "------> added_gate_v"        
        self.add_new_clause ([-t.v, core0], t.u_clauses, self.oracle, label, debug)
        self.add_new_clause ([-t.v, core1], t.u_clauses, self.oracle, label, debug)

        if (full_encoding):
            self.add_new_clause( [t.v, -core0, -core1], t.u_clauses, self.oracle, label, debug)

    def added_gate(self, t,  core0, core1):
        self.added_gate_v(t,  core0, core1)
        self.added_gate_u(t,  core0, core1)


    def sanity_build_up(self, node, c, upper):
        if c in upper:
            assert(node.v == c)
        else:
            assert(node.u == c)

    def resolution(self, core):
        new_relaxs = []
        # if(self.round > 0):
        #     print("--->", core, self.round )
        #     forest_build_graph(self.forest, fname= f"graph-{self.round}")
        circuits = []
        root_nodes = set()
        #random.shuffle(core)
        for c in core:
            node  = forest_find_node(u = c, mapping = self.asm2nodes)
            #print(node)
            circuits.append(node.u)
            assert(node.u == c)
            if node.is_root():
                root_nodes.add(node.u)

        len_core = len(core)
        upper = []
        pointer = 0
        clean_thresh = 5000
        while pointer+1 < len(core):
            u = self.pool.id()    
            v = self.pool.id()    
            
            if (len(core)%5000 ==0):
                print(len(core))
                
            node0  = forest_find_node(u = circuits[pointer],     mapping = self.asm2nodes) 
            node1  = forest_find_node(u = circuits[pointer + 1], mapping = self.asm2nodes) 
            
            if (len_core < 100):
                self.sanity_build_up(node0, core[pointer], upper)
                self.sanity_build_up(node1, core[pointer + 1], upper) 

            status = STATUS_ACTIVE
            if (self.circuitinject == CIRCUITINJECT_TOP) and (len(core) > 2):
                status = STATUS_WAITING
            
            t = self.create_node(name = f"{-u}", u = u,  v = v,  weight = self.minw,  type = SELECTOR, status = status, children = [node0, node1], into_phase = self.round)
            #print(t.u)
            #print(core[0], core[1], node0.u, node1.u)
            if (t.status == STATUS_ACTIVE):
                new_relaxs.append(u)

            ######################################################3
            self.added_gate(t, core[pointer], core[pointer + 1])
            ######################################################
            
            core = core + [ v ]    
            circuits = circuits +[ t.u]    
            if (len_core < 100): upper.append(v)
            pointer = pointer + 2
           
            if (pointer > clean_thresh) and len(core) > clean_thresh + 2:
                core = core[clean_thresh:]   
                circuits = circuits[clean_thresh:]   
                pointer = 0

        set_topdown_levels(t, level = 0)
        self.forest.append(t.u)
        self.filter_forest(root_nodes)
        return new_relaxs

    def folded_half(self, children, debug = False):
        node = None
        t_w = None
        if len(children) == 1: 
            u = children[0].u
            v = children[0].v
            node = children[0]
            t_w = u
        else:
            u = self.pool.id()    
            v = self.pool.id()    
            node = self.create_node(name = f"{-u}", u = u,  v = v,  weight = self.minw,  type = SELECTOR, status = STATUS_FOLDED, children = children, into_phase = self.round)
            self.added_folded_gate(node, v, [n.u for n in children])
            if (debug): print("--->", node, v, [n.u for n in children])
            t_w = v
        return node, t_w

    def us2nodes(self, us):
        nodes = []
        for u in us:
            nodes.append(forest_find_node(u, mapping = self.asm2nodes))
        return nodes
    def delayed_resolution_unfolding(self, core = None, circuits = None, t = None, debug = False):
        #print("*****************8 delayed_resolution_unfolding *****************")
        assert(not (circuits is None))
        assert(not (t is None))
        for u in circuits:
            node= forest_find_node(u , mapping = self.asm2nodes)
            assert not node.is_root(), f"Folded node is a root {node}"

                

        if (len(circuits) > 2):

            for u in circuits:
                node = forest_find_node(u, mapping = self.asm2nodes)
                node.parents = []
                
            len_half = int(len(circuits)/2)
            for u in  circuits[:len_half]:
                print(u)
            half1 = self.us2nodes( circuits[:len_half])
            half2 = self.us2nodes( circuits[len_half:]) 
            
            t1, t1_w = self.folded_half(half1)
            if (debug): print([n.u for n in half1], f"t {t}",  f"t1 {t1} w {t1_w} ")
            t2, t2_w = self.folded_half(half2)
            if (debug):  print([n.u for n in half2], f"t {t}",  f"t2 {t2} w {t2_w}")




            t.status   = STATUS_ACTIVE
            t.children = [t1, t2]
            assert(t.u_clauses == [])
            t.v_clauses = []   
            t1.parents.append(t)             
            t2.parents.append(t)             
            
            self.added_gate(t, t1_w, t2_w)

        elif  len(circuits) == 2:          
            t.status   = STATUS_ACTIVE
            [t1, t2] = t.children
            if (debug):  print(t.v_clauses)                 
            assert(t.u_clauses == [])
            self.added_gate_u(t,  t1.u, t2.u)
        
        else:
            pass


    
    def delayed_resolution(self, core = None, circuits = None,  unfoldng = False, t = None, debug = False):
        new_relaxs = []
        # if(self.round > 0):
        #     print("--->", core, self.round )
        #     forest_build_graph(self.forest, fname= f"graph-{self.round}")
        
        assert(self.circuitinject == CIRCUITINJECT_DELAYED)

        if (unfoldng):
            self.delayed_resolution_unfolding(core = core, circuits = circuits, t =t)
            return
        
        root_nodes = set()

        assert(not (core is None))
        circuits = []
        #forest_build_graph(self.forest, fname= GRAPH_PRINT_DEF+f"-{self.round}-a")

        for c in core:
            node  = forest_find_node(u = c, mapping = self.asm2nodes)
            circuits.append(node.u)
            if node.is_root():
                root_nodes.add(node.u)


        u = self.pool.id()    
        v = self.pool.id()


        if (len(circuits) > 2):
 
            len_half = int(len(circuits)/2)
            half1 = self.us2nodes( circuits[:len_half])
            half2 = self.us2nodes( circuits[len_half:]) 
            
            t1, t1_w = self.folded_half(half1)
            t2, t2_w = self.folded_half(half2)

            t = self.create_node(name = f"{-u}", u = u,  v = v,  weight = self.minw,  type = SELECTOR, status = STATUS_ACTIVE, children = [t1, t2], into_phase = self.round)
    
            if (t.status == STATUS_ACTIVE):
                new_relaxs.append(u)
            self.added_gate(t, t1_w, t2_w)
            if (debug): print([n.u for n in half1], f"t {t}",  f"t1 {t1} w {t1_w} ")            
            if (debug): print([n.u for n in half2], f"t {t}",  f"t1 {t2} w {t2_w} ")
        else:               
            t1  =  forest_find_node(u = circuits[0], mapping = self.asm2nodes)
            t2  =  forest_find_node(u = circuits[1], mapping = self.asm2nodes) 
            t = self.create_node(name = f"{-u}", u = u,  v = v,  weight = self.minw,  type = SELECTOR, status = STATUS_ACTIVE, children = [t1, t2], into_phase = self.round)

            if (t.status == STATUS_ACTIVE):
                new_relaxs.append(u)  
            t1.parents.append(t)
            t2.parents.append(t)                
                
            self.added_gate(t, t1.u, t2.u)
                
            self.sanity_build_up(t1, core[0], [])
            self.sanity_build_up(t2, core[1], [])                 
                        
            
        
        self.forest.append(t.u)
        self.filter_forest(root_nodes)


        return new_relaxs

    
    def filter_forest(self, not_nodes):
        #print(len(not_nodes), len(self.forest))

        self.forest = list(filter(lambda x: x not in not_nodes, self.forest))



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
        self.round +=1 

        # assumptions to remove
        self.garbage = set()

        if  len(self.core_sels + self.core_sums) > 1:
            rels = self.process_assumptions()
            self.core = [-l for l in rels]
            self.add_new_clause(rels, vec = self.formula.hard, oracle= self.oracle)
            #print(self.core, self.core_sums, self.core_sels)
            #self.add_new_clause(self.core , self.formula.hard, self.oracle)
            if self.circuitinject == CIRCUITINJECT_DELAYED:

                if (len(self.core) <= 4):
                    self.circuitinject = CIRCUITINJECT_FULL
                    self.resolution(self.core)
                    self.circuitinject = CIRCUITINJECT_DELAYED
                else:
                    self.delayed_resolution(self.core)
            else:

                self.resolution(self.core)
                
        else:
            # unit cores are treated differently
            # (their negation is added to the hard part)
            self.deactivate_unit(u = self.core[0])
            #assert(self.core[0] in self.forest)
            self.filter_forest([self.core[0]])

        # print("*************************")
        # for t in self.forest:
        #     traverse(t)

        #
        # print("------------------------")
        # for j, t in enumerate(self.forest):
        #     print(f"----->  tree {j} ")
        #     traverse(t)
        #return new_relaxs

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
                #print(am1)
                self.process_am1(am1)
                nof_am1 += 1
                len_am1.append(len(am1))

        # updating the set of selectors
        #self.sels_set = set(self.sels)

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
            self.core_sels, self.core_sums, b = am1, [], len(am1) - 1

            # incrementing the cost
            self.cost += b * self.minw

            # splitting and relaxing if needed
            #print(1, len(self.forest))
            #print(self.core_sels, self.core_sums)
            rels = self.process_assumptions()

            #for v in self.garbage:
            #   print(v) 
            # updating the list of literals in am1 after splitting the weights
            am1 = list(filter(lambda l: l not in self.garbage, am1))

            #print(2, am1, len(am1))

            # new selector
            selv = self.pool.id()

            # adding a new clause
            self.add_new_clause([-l for l in rels] + [-selv], self.formula.hard, self.oracle)
 

            t = self.create_node(name = f"{-selv}", u = selv,  v = selv,  weight = self.minw,  type = INITIAL_SELECTOR, status = STATUS_ACTIVE)

            self.forest.append(t.u)
            for u in self.garbage:
                #print(u)
                node = forest_find_node(u = u, mapping = self.asm2nodes)
                node.status = STATUS_INACTIVE


        # removing unnecessary assumptions
        self.filter_forest(self.garbage)

        self.garbage = set()

        #print("-->", len(self.forest))
        #print(len(self.forest), "<--")
        #print("return")


    def trim_core(self):
        """
            This method trims a previously extracted unsatisfiable
            core at most a given number of times. If a fixed point is
            reached before that, the method returns.
        """

        for i in range(self.trim):
            # call solver with core assumption only
            # it must return 'unsatisfiable'
            self.oracle.solve(assumptions=self.core)

            # extract a new core
            new_core = self.oracle.get_core()

            if len(new_core) == len(self.core):
                # stop if new core is not better than the previous one
                break

            # otherwise, update core
            self.core = new_core

   


    def minimize_core(self):
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
 
        debug = False
        #print(self.minz)
        if self.minz and len(self.core) > 1 and (len(self.core) < 1000) and len(self.formula.hard) < 10000000:
            self.core = sorted(self.core, key=lambda l: self.wght[l])
            u2l = u_and_level(self.core, self.asm2nodes)
            self.core = list({k: v for k, v in sorted(u2l.items(), key=lambda item: item[1], reverse=True)})


            
            i = 0
            keep = []
            core = self.core
            proj = keep + core 
            
            start_prop = 5000000
            def_prop = 100000
            misses_in_a_row = 50
            miss = 0
            time_total = 0
            core = self.core
            time_per_call = 2
         
                

            while len(core) > 0:
                if (miss == misses_in_a_row):
                    keep = keep + to_test
                    break
                to_test =  core[1:]
                #node = forest_find_node(core[0], self.asm2nodes)
                #print(node)
                #print(f"core {core} keep {keep} proj {proj}")

                if not (core[0] in proj):
                    #i = i+ 1
                    to_test = core[1:]
                    core = core[1:]
                    #print("continue")
                    continue

                keep = [c for c in keep if c in proj]
                #################################################
                #self.oracle.clear_interrupt()
                self.oracle.prop_budget(start_prop)
                #def interrupt(s):
                #    s.interrupt()                
                #timer = Timer(time_per_call, interrupt, [self.oracle])            
                start =time.time()
                #timer.start()

                status = self.oracle.solve_limited(assumptions= keep + to_test)        
                
                #timer.cancel()
                #print((time.time() - start))        
                time_total = time_total + (time.time() - start)
                #self.oracle.clear_interrupt()
                
                if (time_total > 30):
                    start_prop = def_prop
                #    time_per_call = 1
                
                ##############################################

                if debug:  print('c oracle time: {0:.4f}'.format(time_total))
                #print(prop)
                if status  == False:
                    newcore = self.oracle.get_core()
                    if (newcore is None):
                        newcore = []                    
                    proj =  newcore                 
                elif self.oracle.get_status() == True:
                    keep.append(core[0])

                else:
                    keep.append(core[0])
                if status == None:
                    miss +=1

            

                if debug: print(f"{self.oracle.get_status()} {core[0]} {len(keep + to_test)}")
                core = core[1:]
                    #break
                

            self.core =  keep
            #print(f"final {keep}")
            #assert(self.oracle.solve_limited(assumptions=self.core) == False)
            if debug: print(f"min end {len(self.core)}")           
            #self.oracle.clear_interrupt()
 
            
    def process_assumptions(self):
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
        rels = []

        for l in self.core_sels + self.core_sums:
            if self.wght[l] == self.minw:
                self.deactivate_sel(u = l)
            else:
                # do not remove this variable from assumps
                # since it has a remaining non-zero weight
                self.wght[l] -= self.minw
                self.update_weight_sel(u = l, new_weight = self.wght[l])

            # reuse assumption variable as relaxation
            rels.append(-l)
        return rels

  

  
    def oracle_time(self):
        """
            Report the total SAT solving time.
        """
        if (self.use_accum_oracle):
            return  self.oracle.time_accum() 

        else:
            end = time.time()
            return self.time + self.oracle.time_accum() #+  end - self.timer - self.build_time

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
def parse_options():
    """
        Parses command-line option
    """

    try:
        opts, args = getopt.getopt(sys.argv[1:], 'ab:c:e:hil:ms:rt:vx',
                ['adapt', 'block=', 'comp=', 'enum=', 'exhaust', 'help',
                    'incr', 'blo=', 'minimize', 'solver=', 'trim=',  'circuitinject=','verbose',
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
    verbose = 1
    vnew = False
    circuitinject = 0

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
        elif opt in ('-r', '--circuitinject'):
            circuitinject = int(arg)            
        elif opt in ('-v', '--verbose'):
            verbose += 1
        elif opt == '--vnew':
            vnew = True
        elif opt in ('-x', '--exhaust'):
            exhaust = True
        else:
            assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

    # solution blocking
    bmap = {'mcs': -1, 'mcses': -1, 'model': 0, 'models': 0, 'mss': 1, 'msses': 1}
    assert block in bmap, 'Unknown solution blocking'
    block = bmap[block]

    return adapt, blo, block, cmode, to_enum, exhaust, incr, minz, \
            solver, trim, circuitinject, verbose, vnew, args


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


#
#==============================================================================
if __name__ == '__main__':
    adapt, blo, block, cmode, to_enum, exhaust, incr, minz, solver, trim, \
            circuitinject, verbose, vnew, files = parse_options()

    if files:
        # parsing the input formula
        if re.search('\.wcnf[p|+]?(\.(gz|bz2|lzma|xz))?$', files[0]):
            formula = WCNFPlus(from_file=files[0])
        else:  # expecting '*.cnf[,p,+].*'
            formula = CNFPlus(from_file=files[0]).weighted()

        # enabling the competition mode
        if cmode:
            assert cmode in ('a', 'b'), 'Wrong MSE18 mode chosen: {0}'.format(cmode)
            adapt, blo, exhaust, solver, verbose = True, 'div', True, 'g4', 3

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
        with MXS(formula, solver=solver, adapt=adapt, exhaust=exhaust,
                incr=incr, minz=minz, trim=trim, circuitinject=circuitinject, verbose=verbose) as rc2:

            
            # if isinstance(rc2, RC2Stratified):
            #     rc2.bstr = blomap[blo]  # select blo strategy
            #     if to_enum != 1:
            #         # no clause hardening in case we enumerate multiple models
            #         print('c hardening is disabled for model enumeration')
            #         rc2.hard = False

            optimum_found = False
            model  = rc2.compute()
            # profiler = pprofile.Profile()
            # with profiler:
            #     model  = rc2.compute()
            #     profiler.dump_stats("profiler_stats.txt")                
            
            if not (model is None):
                optimum_found = True

                if verbose:

                    print('s OPTIMUM FOUND')
                    print('o {0}'.format(rc2.cost))
                    print(verbose)

                    if verbose > 3:
                        if vnew:  # new format of the v-line
                            print('v', ''.join(str(int(l > 0)) for l in model))
                        else:
                            print('v', ' '.join([str(l) for l in model]))

            else:
                # needed for MSE'20
                if verbose > 2 and vnew and to_enum != 1 and block == 1:
                    print('v')

            if verbose:
                if not optimum_found:
                    print('s UNSATISFIABLE')
                elif to_enum != 1:
                    print('c models found:', 0)

                if verbose > 1:
                    print('c oracle time: {0:.4f}'.format(rc2.oracle_time()))
