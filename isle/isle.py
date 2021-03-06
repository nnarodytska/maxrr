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
from math import ceil, copysign
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
from  or_tools import DEFAULT_ILP, DEFAULT_ILPCPU, DEFAULT_ILPPREP, SolverOR, solve_ortools
import operator
from threading import Timer
CIRCUITINJECT_FULL = 0
CIRCUITINJECT_TOP = 1
CIRCUITINJECT_DELAYED = 2 
CIRCUIT_COMPRESSED = 3
CIRCUIT_PARTIAL_SOFT = 4

DEFAULT_MIN_WINDOW = 16
DEFAULT_MAX_WINDOW = 10000000
try:
    import gurobipy as gp
    from gurobipy import GRB
except:
    pass

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
            incr=False, minz=False, trim=0, verbose=0, circuitinject = CIRCUITINJECT_FULL, min_window = None, max_window = None, ilp = DEFAULT_ILP, ilpcpu = DEFAULT_ILPCPU, ilpprep = DEFAULT_ILPPREP):
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
        self.min_window = min_window
        self.init_cost = 0
        if self.min_window is None:
            self.min_window = DEFAULT_MIN_WINDOW

        self.max_window = max_window
        if self.max_window is None:
            self.max_window = DEFAULT_MAX_WINDOW
        
        self.ilp = ilp
        self.ilpcpu = ilpcpu
        self.ilpprep = ilpprep

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
        self.upperlevel = {}

        self.bnds = {}  # a mapping from sum assumptions to totalizer bounds
        self.tobj = {}  # a mapping from sum assumptions to totalizer objects

        self.org_oracle = None

        self.asm2nodes = {}
        self.ortools_on = False
        self.or_model =  None
        self.or_time = 0
        self.maxhs_on = True
        self.or_card_model = None
        self.org_oracle = None
        self.hints, self.or_ub, self.or_lb = None, None, -100
        if (self.ortools_on):
            self.or_model =  SolverOR(self.ilpcpu)

             
  
        

        # mappings between internal and external variables
        VariableMap = collections.namedtuple('VariableMap', ['e2i', 'i2e'])
        self.vmap = VariableMap(e2i={}, i2e={})


        self.blop = None
        #print(max(formula.wght), min(formula.wght))
        self.level = 0
        self.max_level = 10

        # initialize SAT oracle with hard clauses only
        self.init(formula, incr=incr)


        #wght = self.wght.values()



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
        #self.orig_formula = copy.deepcopy(formula)

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

        #self.forest = []
        self.wstr = set()
            
        
        for i, cl in enumerate(self.formula.soft):
            selv = cl[0]  # if clause is unit, selector variable is its literal
            if len(cl) > 1:
                selv = self.pool.id()
                cl.append(-selv)            
                self.add_new_clause(cl, self.formula.hard)
            
            t = self.create_node(name = "{-selv}", u = selv,  v = selv,  weight = self.formula.wght[i],  type = INITIAL_SELECTOR, status = STATUS_ACTIVE)
            #self.forest.append(t.u)

            self.wstr.add(self.formula.wght[i])
            # if selv  in self.wght:         
            #     assert False, "we should not have duplicates"


        if max(formula.wght) > min(formula.wght):
            print(self.wstr)
            # sorted list of distinct weight levels
            self.blop = sorted([w for w in list(self.wstr)], reverse=True)
            self.level = 0
            sz = len(self.blop)
            self.max_level =  15
            self.max_level =   self.max_level  if sz > self.max_level else sz            
            step = ceil(sz/ self.max_level ) if sz > self.max_level else 1
            self.weight_bounds = []
            for i in range(0,sz, step):
                self.weight_bounds.append(self.blop[i])
            self.weight_bounds.pop(-1)
            self.weight_bounds.append(0)
            

        if (self.maxhs_on):
            self.or_card_model =  SolverOR(self.ilpcpu)

        self.rebuild(init = True)


        # at this point internal and external variables are the same
        for v in range(1, formula.nv + 1):
            self.vmap.e2i[v] = v
            self.vmap.i2e[v] = v

        if self.verbose > 1:
            print('c formula: {0} vars, {1} hard, {2} soft'.format(formula.nv,
                len(self.formula.hard), len(self.formula.soft)))

        if (not self.formula.hard and len(self.sels) > 100000 and min(self.orig_formula.wght) == max(self.orig_formula.wght)) or ( len(self.sels) > 500000 ):
            self.minz = False  
        print(self.minz)


        #exit()

    def create_node(self, name, u, v, weight, type, status, level = DUMMY_LEVEL, cu = DUMMY_U,  cu_cover = DUMMY_U_COVER, tobj =None, tobj_bound = 0, children = None, into_phase = 0):

        node = Circuit(name,        
                        u = u,
                        v = v, 
                        cu = cu,
                        cu_cover = cu_cover,
                        tobj = tobj,
                        tobj_bound = tobj_bound,
                        level = level,
                        weight = weight, 
                        type = type, 
                        status = status,
                        children = children,
                        into_phase = into_phase
                        )        
        if (type == INITIAL_SELECTOR):
            self.orig_sels.append(u)
        if node.type == COMPRESSSOR:
            self.asm2nodes[cu] = node         
        else:
            self.asm2nodes[u] = node
        return node

   
    def solve_gurobi(self, formula, solution = None, to = 60):
        with gp.Env(empty=True) as env:
            #env.setParam('OutputFlag', 0)
            env.setParam('TimeLimit', to)
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
                        b.setAttr('VarHintVal', solution[c])
                        b.setAttr('Start', solution[c])

                        #self.gurobi_model.addConstr(b == solution[c], f"clause_{c} = {solution[c]}")
                    except:
                        pass
                        #print("-->", c)
            
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
            #self.gurobi_model.write("test.lp")


            self.gurobi_model.optimize()                
            obj = None
            sols = []
            t = self.gurobi_model.Runtime
            if self.gurobi_model.status in {GRB.OPTIMAL, GRB.TIME_LIMIT}:
                try:
                    solution_vars = {}
                    obj =  math.ceil(self.gurobi_model.objVal)
                    lb_obj =  math.ceil(self.gurobi_model.objbound)
                    best_obj = int(obj)             
                    for c in range(max_id):                
                        b = self.gurobi_vars[c]
                        solution_vars[c] = int(b.x)
                except:
                    pass
            else:
                obj = -1
                best_obj =  math.ceil(self.gurobi_model.objVal)
                lb_obj = math.ceil(self.gurobi_model.objbound)
                solution_vars = None



                #print(best_obj)


            # if (presolve):
            #     try:
            #         self.gurobi_model=self.gurobi_model.presolve()
            #         self.gurobi_model.printStats() 
            #         self.gurobi_model.write("pre-test.lp")
            #         formula_new = WCNFPlus(from_gmodel=self.gurobi_model)                                                            
            #         self.gmodel = self.gurobi_model
            #     except Exception as e:
            #         print("-----------", e)
            #         exit()


            return best_obj, lb_obj, solution_vars, self.gurobi_model.status, t, self.gurobi_model.SolCount#formula_new


    def rebuild(self,  init = False, debug = False):

        print("------------->  rebuild  <-----------------")
        


        if self.use_accum_oracle:
            if (init):
                self.oracle = Solver(name=self.solver, bootstrap_with=self.formula.hard, use_timer=True)
                self.org_oracle = Solver(name=self.solver, bootstrap_with=self.formula.hard, use_timer=True)
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


        # prev_asm_len = len(self.sums + self.sels)
        # if (prev_asm_len == 0):
        #     prev_asm_len = len(self.forest)
        # else:
        #     prev_asm_len = prev_asm_len - 1
        self.sels, self.sums, self.sneg = [], [], set([])

        
        self.wght = {}  # weights of soft clauses
        active_u2l =  u_and_level_active(self.asm2nodes)

        
        # for a,b in self.asm2nodes.items():
        #     print("-->", a,b)


        sorted_active_u2l = {k: v for k, v in sorted(active_u2l.items(), key=lambda item: item[1])}

        for u, _ in sorted_active_u2l.items():
            #print(f"--------------{u}------------")
            node= forest_find_node(u, self.asm2nodes)
            #print(node)
            node_id = node.u
            if self.blop is not None:
                #print(node.weight, self.weight_bounds)
                if node.weight < self.weight_bounds[self.level]:
                    #print(f"skip {node.weight}/{self.weight_bounds[self.level]}/{self.level} ")
                    continue
                    exit()

            if node.type == INITIAL_SELECTOR:
                self.sels.append(node_id)
            elif node.type == COMPRESSSOR:
                node_id = node.cu
                self.sums.append(node_id)                
            else:
                self.sums.append(node_id)
            assert(node.status  == STATUS_ACTIVE)
            self.wght[node_id] =  node.weight

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
        res, or_status  = self.compute_()
        if debug: print(res)

        # or_model, or_model_ub = solve_ortools(self.formula, self.forest, to = 600)
        # print(self.)
        # exit()
        if res and or_status  == cp_model.OPTIMAL:
            return self.model

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

    def reactivate(self, model, rebuild = 0):
        if (self.circuitinject == CIRCUITINJECT_DELAYED):
            unfolded = 0
            for i in range(2**rebuild+1):
                new_unfolded = self.delayed_reactivation(model)
                if (new_unfolded == 0):
                    break
                unfolded += new_unfolded
            return unfolded
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
        # if (forest is None):
        #     forest = self.forest
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
                cld = [n.u for n in node.children]
                if (len(cld) > 0):
                    self.delayed_resolution(circuits = cld, t = node, unfoldng = True)
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

    def or_call(self, cost_vars, lb=None, ub=None, to = 60, init = False):
        if (self.or_model is None): 
            return False
        # if not init:
        #     ub = self.or_ub - self.cost - 1

        hints, or_ub, or_lb = self.or_model.minimize(cost_vars, self.asm2nodes, hints = self.hints, lb = lb,  ub = ub, to = to)
        self.or_time = self.or_time + self.or_model.time
        if (len(hints.items()) > 0 ): 
            if (init):
                self.hints, self.or_ub, self.or_lb  = hints, or_ub + self.cost, or_lb + self.cost
                print(f"self.or_ub {self.or_ub} self.or_lb {self.or_lb} ")
            else:
                assert(False)
                # self.or_ub = min(or_ub + self.cost, self.or_ub) 
                # if (self.or_model.status == cp_model.INFEASIBLE):
                #     exit()           

            if (self.or_model.status == cp_model.OPTIMAL):
                self.force_model(hints)
                self.cost = self.or_ub
                assert(self.or_ub ==  self.or_lb)

            for u in cost_vars:
                val = hints[abs(u)]
                if ((val == False) and (u > 0)) or ((val == True) and (u < 0)):                
                    
                    node= forest_find_node(u, self.asm2nodes)
                    if node.type == SUM:
                        print(u,val)
                    #print(node)
            #if (or_ub == or_lb):
            #    self.force_model(hints)
            #    self.cost = or_ub
        return self.or_model.status
    def call_maxhs(self):
        or_lb = self.cost
        while(True):
            hints, or_ub, or_lb = self.or_card_model.circuit_maxhs(cost_vars=self.orig_sels, mapping=self.asm2nodes, lb = or_lb)        
            if (or_ub < self.cost):
                print(or_ub, self.cost)
                # if (debug):
                #     forest_build_graph(self.asm2nodes)                
                exit()
            else:
                if (self.cost > 69):
                    assm = []
                    for u in self.orig_sels:
                        val = hints[abs(u)]
                        #print(u,val)
                        if val and u > 0:
                            assm.append(u)
                        elif not val and u < 0:
                            assm.append(u)
                    #print(assm)
                    #print(self.sels + self.sums)

                    unsat  = not self.org_oracle.solve(assumptions=assm)
                    assert(unsat)

                    self.core = self.org_oracle.get_core()
                    if self.core:
                        # core = copy.deepcopy(self.core)

                        # for i in range(10):
                            #self.core = copy.deepcopy(core)
                            print(self.core)

                            random.shuffle(self.core)
                
                            # try to reduce the core by trimming
                            self.trim_core(oracle = self.org_oracle)

                            # and by heuristic minimization
                            self.minimize_core(oracle = self.org_oracle, issort=False)     
                            print(self.core)       
                            print("--is UNSAT ", unsat)
                            self.or_card_model.add_clause([-u for u in self.core])
                    else:
                        break
                    #exit()
                else:
                    break
  
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
            self.rebuild(init = True)

        debug = False
        # main solving loop
        
        if debug: print(self.sels + self.sums)

        

        #self.or_model.feasibility(assumptions=self.sels + self.sums, mapping=self.asm2nodes)
        #print(self.ilp)
        # if (self.ilp > 0):
        #     print(self.init_cost)
        #     self.solve_gurobi(self.formula, to = self.ilp)
        #     exit()


        #     status = self.or_call(cost_vars=self.sels + self.sums, to = self.ilp, init = True)
        #     if (status == cp_model.OPTIMAL):
        #         print(f"c cost: {self.cost};  soft sz: {len(self.sels) + len(self.sums)} {self.oracle_time():.4f}/{self.build_time:.4f}/{self.sat_time:.4f}")
        #         return True,  cp_model.OPTIMAL
                
        #     if (status == cp_model.FEASIBLE) and (self.cost + 1 == self.or_ub):
        #         self.force_model(self.hints)
        #         print(f"c cost: {self.cost};  soft sz: {len(self.sels) + len(self.sums)} {self.oracle_time():.4f}/{self.build_time:.4f}/{self.sat_time:.4f}")
        #         return True,  cp_model.OPTIMAL


        unsat  = not self.oracle.solve(assumptions=self.sels + self.sums)
        #assert(self.oracle.solve(assumptions=self.sol))
        print(f"start  unsat {unsat}")

        while unsat or  self.level < self.max_level:

            while (not unsat):
                tm = time.time()                     
                self.level +=1
                if   (self.blop is not None) and (self.level == self.max_level):
                    return True, None
                self.rebuild()       
                self.adapt_am1()
                self.rebuild()                

                print(unsat,  self.level, self.max_level)
                unsat  = not self.oracle.solve(assumptions=self.sels + self.sums)
                self.sat_time  += time.time() - tm

                print("---", unsat)#, self.sels, self.sums)
            


            self.get_core()

            if not self.core:
                # core is empty, i.e. hard part is unsatisfiable
                return False, None
            self.process_core()
            if debug: print(f"~~~~~~~~~~~~~~~~~~~~~~~~~ core {self.core} round {self.round}")

            self.add_new_clause([-u for u in self.core], vec = self.formula.hard, oracle= self.oracle)

            #self.call_maxhs()


            if self.verbose > 1:
                print(f"c cost: {self.cost}; core sz: {len(self.core)}; soft sz: {len(self.sels) + len(self.sums)} {self.oracle_time():.4f}/{self.build_time:.4f}/{self.sat_time:.4f}/min_w {self.weight_bounds[self.level]}")


            # print(self.cost + 1, self.or_ub)
            # if (self.cost + 1 == self.or_ub):
            #     self.force_model(self.hints)
            #     self.cost =  self.or_ub
            #     print("---")
            #     return True,  cp_model.OPTIMAL


            self.rebuild()
            #if debug: print(f"~~~~~~~~~~~~~~~~~~~~~~~~~ sels {self.sels } sums {self.sums}")

            sums = forest_filter(self.asm2nodes, type= SUM)
            #print(sums)
            # if (len(sums) > 0) and self.ilp:
            #     self.or_call(cost_vars=self.sels + self.sums, to = 30)
            
            unsat  = not self.oracle.solve(assumptions=self.sels + self.sums)
            #delayed_selectors_nodes = []
            #if (not unsat): delayed_selectors_nodes = list(forest_filter(self.asm2nodes, status = STATUS_WAITING)) +  list(forest_filter(self.asm2nodes, status = STATUS_FOLDED))
            
            rebuild = 0
            #if (not unsat): delayed_selectors_nodes = list(forest_filter(self.asm2nodes, status = STATUS_STATIFIED))
            print(unsat,  self.level, self.max_level)
                

            
        return True, None

    def get_core(self, oracle = None):
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

        if oracle is None:
            oracle = self. oracle

        # extracting the core
      
        self.core = oracle.get_core()

        if self.core:
            # try to reduce the core by trimming
            self.trim_core(oracle = oracle)

            # and by heuristic minimization
            self.minimize_core(oracle = oracle)

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

    def deactivate_compressor(self, u):
        node  = forest_find_node(u, mapping = self.asm2nodes)
        self.add_new_clause([-u], node.u_clauses, self.oracle, label = "", debug = False)
        node.status = STATUS_INACTIVE
        node.weight = 0

    def deactivate_unit(self, u):        
        node  = forest_find_node(u, mapping = self.asm2nodes)
        node.status = STATUS_INACTIVE        
        self.add_new_clause([-u], node.u_clauses, self.oracle, label = "", debug = False)
        

    def update_weight_sel(self, u, new_weight):
        node  = forest_find_node( u, mapping = self.asm2nodes)
        node.weight = new_weight

    
    def add_new_clause(self, cl, vec= None, oracle = None, label = "",  debug = False, special = False, special_solver = None):
        #print(cl)
        if (special):
            if (self.or_card_model is not None): special_solver.add_clause(cl)
            return 
        assert((vec is not None) or (oracle is not None))
        if (vec is not None): vec.append(cl)  
        if (oracle is not None): oracle.add_clause(cl)
        if (self.or_model is not None): self.or_model.add_clause(cl)
        if (self.or_card_model is not None): self.or_card_model.add_clause(cl)
        #if (extra_sat_solver is not None): extra_sat_solver.add_clause(cl)

        if (debug): print(label,  cl)


    def added_folded_gate(self, t, v, half, full_encoding = False, debug = False):
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

        # for maxhs via ortools
        self.add_new_clause([t.u, -core0], special = True, special_solver = self.or_card_model)
        self.add_new_clause([t.u, -core1], special = True, special_solver = self.or_card_model)        

        #print(cl)

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
        
        # for maxhs via ortools
        self.add_new_clause([t.v, -core0, -core1], special = True, special_solver = self.or_card_model)        

    def added_gate(self, t,  core0, core1):
        self.added_gate_v(t,  core0, core1)
        self.added_gate_u(t,  core0, core1)


    def sanity_build_up(self, node, c, upper):
        if c in upper:
            assert(node.v == c)
        else:
            assert(node.u == c)


    def add_upperlevel(self, lits):
        debug = False
        
        cu = self.pool.id()    
        node = self.create_node(name = f"{-cu}", u = DUMMY_U,  v = DUMMY_U, cu = cu,  cu_cover = copy.deepcopy(lits), weight = self.minw, level = self.round, type = COMPRESSSOR, status = STATUS_ACTIVE, into_phase = self.round)        
        self.wght[cu] = self.minw
    
        if debug: print(f"new {cu} base {len(lits)}")
        for u in lits:
            self.add_new_clause([-cu, u], node.v_clauses, self.oracle)
        self.upperlevel[cu] = cu

    def resolution(self, core, status_def = STATUS_ACTIVE):
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

            status = status_def
            if (self.circuitinject == CIRCUITINJECT_TOP) and (len(core) > 2):
                status = STATUS_WAITING
            
            t = self.create_node(name = f"{-u}", u = u,  v = v,  weight = self.minw,  type = SELECTOR, status = status, children = [node0, node1], into_phase = self.round)
            #print(t.u)
            #print(core[0], core[1], node0.u, node1.u)
            if (t.status == status_def):
                new_relaxs.append(u)

            ######################################################3
            self.added_gate(t, core[pointer], core[pointer + 1])
            ######################################################
            
            core = core + [ v ]    
            circuits = circuits +[ t.u]    
            # core =  [ v ] + core[2:]
            # circuits =  [ t.u]   + circuits[2:]

            pointer = pointer + 2
            if (pointer > clean_thresh) and len(core) > clean_thresh + 2:
                core = core[clean_thresh:]   
                circuits = circuits[clean_thresh:]   
                pointer = 0


            if (len_core < 100): upper.append(v)
           
    
        set_topdown_levels(t, level = 0)
        #self.forest.append(t.u)
        #self.filter_forest(root_nodes)
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
            # for u in  circuits[:len_half]:
            #     print(u)
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
                        
            
        
        #self.forest.append(t.u)
        #self.filter_forest(root_nodes)


        return new_relaxs

    
    # def filter_forest(self, not_nodes):
    #     #print(len(not_nodes), len(self.forest))

    #     self.forest = list(filter(lambda x: x not in not_nodes, self.forest))


    def uncompress_core(self, compressed_core, uncompressed_core):
        debug = True
        if len(uncompressed_core) == 0:
            uncompressed_core = []            
            for cu in compressed_core:
                if cu in self.upperlevel:
                    node = forest_find_node(cu, self.asm2nodes)
                    uncompressed_core = uncompressed_core + node.cu_cover
                    self.deactivate_compressor(cu)
                    self.upperlevel.pop(cu)
                else:
                    uncompressed_core = uncompressed_core + [cu]

        else:
            left_over = []
            for cu in compressed_core:
                if cu in self.upperlevel:
                    node = forest_find_node(cu, self.asm2nodes)
                    left_over += list(set(node.cu_cover) - set(uncompressed_core))
                    if debug: print(f"left_over {left_over}")
                    # if (len(left_over) > 0):
                    #     if (len(left_over) <= 2):
                    #         for a in left_over:
                    #             node = forest_find_node(a, self.asm2nodes)
                    #             node.status = STATUS_ACTIVE
                    #     else:
                    #         self.add_upperlevel(left_over)
                                    
                    self.deactivate_compressor(cu)
                    self.upperlevel.pop(cu)       
            if (len(left_over) > 0):                     
                self.add_upperlevel(left_over)
        return uncompressed_core


    # def set_bound(self, tobj, rhs):
    #     """
    #         Given a totalizer sum and its right-hand side to be
    #         enforced, the method creates a new sum assumption literal,
    #         which will be used in the following SAT oracle calls.

    #         :param tobj: totalizer sum
    #         :param rhs: right-hand side

    #         :type tobj: :class:`.ITotalizer`
    #         :type rhs: int
    #     """

    #     # saving the sum and its weight in a mapping
    #     self.tobj[-tobj.rhs[rhs]] = tobj
    #     self.bnds[-tobj.rhs[rhs]] = rhs
    #     self.wght[-tobj.rhs[rhs]] = self.minw

    #     # adding a new assumption to force the sum to be at most rhs
    #     #self.sums.append(-tobj.rhs[rhs])
    #     return -tobj.rhs[rhs]

    def create_sum(self, lits, bound=0):
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

        # new totalizer sum
        tobj = ITotalizer(lits=lits, ubound=bound, top_id=self.pool.top)

        children = []
        for neg_u in lits:
            u = -neg_u
            node = forest_find_node(u, self.asm2nodes)
            children.append(node)
            assert(node.status == STATUS_ACTIVE)
            #print(node)
            self.deactivate_sel(u)
        
        # updating top variable id
        self.pool.top = tobj.top_id    
        
        
        u =  -tobj.rhs[bound]
        node = self.create_node(name = f"{-u}", u = u,  v = DUMMY_U,  weight = self.minw,  level = bound,  tobj = tobj, tobj_bound = bound,  children = children, type = SUM, status = STATUS_ACTIVE)
        #self.forest.append(u)

        for cl in tobj.cnf.clauses:            
            self.add_new_clause(cl, node.u_clauses, self.oracle)


        return node

    def update_sum(self, u):
       
        # getting a totalizer object corresponding to assumption
        node = forest_find_node(u, self.asm2nodes)
        # increment the current bound
        
        if len(node.children) - 1 <= node.tobj_bound:
            return


        # increasing its bound
        node.tobj.increase(ubound=node.tobj_bound+1, top_id=self.pool.top)

        # updating top variable id
        self.pool.top = node.tobj.top_id
        #print(node.tobj.rhs, node.tobj_bound, node.children)        
        
        #print(len(node.tobj.rhs))
        u = -node.tobj.rhs[node.tobj_bound+1]        
        bound = node.tobj_bound + 1
        update_node = self.create_node(name = f"{-u}", u =u,  v = DUMMY_U,  weight = self.minw,  tobj = node.tobj, level = bound, tobj_bound = bound, children = node.children, type = SUM, status = STATUS_ACTIVE)

        # adding its clauses to oracle
        if update_node.tobj.nof_new:
            for cl in update_node.tobj.cnf.clauses[-update_node.tobj.nof_new:]:
                self.add_new_clause(cl, update_node.u_clauses, self.oracle)
        return update_node


    def update_sums(self, sums):
        for u in sums:
            node = forest_find_node(u, self.asm2nodes)
            if node.type == SUM:
                #print(node)
                update_node = self.update_sum(u)
                #print(update_node)

    def create_partial_sum(self, sum, test = False):
        bound = 0
        update_node = self.create_sum(sum, bound=bound)
        ou = update_node.u
        if test:
            for _ in range(len(sum)-1):
                bound =  bound + 1
                update_node = self.update_sum(update_node.u)
                #print(ou, bound, update_node)        
    def create_partial_sums(self, sums, min_window, max_window, test = False):
        if len(sums) >= min_window:                    
            while(len(sums) > 0):
                #print(min_window, max_window)
                top_relaxs = sums[:max_window]                    
                counted_zeros  = [-u for u in top_relaxs]
                self.create_partial_sum(counted_zeros, test = test)
                sums = sums[max_window:]
                print(len(top_relaxs))


    def process_core(self, sat_round  = 0):
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
        #print("-->", self.sels, self.sums)
        if  len(self.core_sels + self.core_sums) > 1:
            rels = self.process_assumptions()
            self.core = [-l for l in rels]
            #print(self.core, self.core_sums, self.core_sels)
            #self.add_new_clause(self.core , self.formula.hard, self.oracle)
            if self.circuitinject == CIRCUITINJECT_DELAYED:
                if (len(self.core) <= 4):
                    self.circuitinject = CIRCUITINJECT_FULL
                    self.resolution(self.core)
                    self.circuitinject = CIRCUITINJECT_DELAYED
                else:
                    self.delayed_resolution(self.core)

            elif self.circuitinject == CIRCUIT_COMPRESSED:

                compressed_core = copy.deepcopy(self.core)
                print(f"compressed_core {len(compressed_core)}")
                self.minimize_core(unfolding = True)      
                uncompressed_core = self.uncompress_core(compressed_core, self.core)                    
                #print(uncompressed_core)
                new_relaxs = self.resolution(uncompressed_core, status_def = STATUS_COMPRESSED)
                cu = self.add_upperlevel(new_relaxs)
            
            elif self.circuitinject == CIRCUIT_PARTIAL_SOFT:
                core = copy.deepcopy(self.core)
                new_relaxs = self.resolution(self.core)
                test = False
                self.create_partial_sums(new_relaxs, min_window = self.min_window, max_window = self.max_window, test = test)
                if not test: self.update_sums(core)
            else:
                self.resolution(self.core)
                
        elif (self.core[0] in self.upperlevel):
            uncompressed_core = self.uncompress_core([self.core[0]], [])                    
            new_relaxs = self.resolution(uncompressed_core, status_def = STATUS_COMPRESSED)
            cu = self.add_upperlevel(new_relaxs)


        else:
            # unit cores are treated differently
            # (their negation is added to the hard part)
            self.deactivate_unit(u = self.core[0])
            #assert(self.core[0] in self.forest)
            #self.filter_forest([self.core[0]])
            if self.circuitinject == CIRCUIT_PARTIAL_SOFT:
                self.update_sums(self.core)


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
           # print(lits)
            am1 = [min(lits, key=lambda l: len(conns[l]))]


            for l in sorted(conns[am1[0]], key=lambda l: len(conns[l])):
                if l in lits:
                    for l_added in am1[1:]:
                        if l_added not in conns[l]:
                            break
                    else:
                        am1.append(l)
            #print(am1)
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
        self.init_cost = self.cost

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
            print(am1)
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

            #self.forest.append(t.u)
            for u in self.garbage:
                #print(u)
                node = forest_find_node(u = u, mapping = self.asm2nodes)
                node.status = STATUS_INACTIVE


        # removing unnecessary assumptions
        #self.filter_forest(self.garbage)

        self.garbage = set()

        #print("-->", len(self.forest))
        #print(len(self.forest), "<--")
        #print("return")


    def trim_core(self, oracle = None):
        """
            This method trims a previously extracted unsatisfiable
            core at most a given number of times. If a fixed point is
            reached before that, the method returns.
        """
        if oracle is None: oracle = self.oracle
        for i in range(self.trim):
            # call solver with core assumption only
            # it must return 'unsatisfiable'
            oracle.solve(assumptions=self.core)

            # extract a new core
            new_core = oracle.get_core()

            if len(new_core) == len(self.core):
                # stop if new core is not better than the previous one
                break

            # otherwise, update core
            self.core = new_core

   


    def minimize_core(self, core = None,  unfolding = False, oracle = None,  issort = True):
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
        if oracle is None: oracle = self.oracle

        if (core is not None):
            self.core = core
        debug = False
        if debug: print(f"input core {len(self.core)} unfolding {unfolding}")
        #print(self.minz)
        lnc = len(self.core)
        core_size_thesh = 1000
        
        if (len(self.core) >= core_size_thesh) and unfolding:
            new_core = []
            for u in self.core:
                if u in self.upperlevel:
                    node = forest_find_node(u, self.asm2nodes)                
                    new_core  = new_core+ node.cu_cover
                else:
                    new_core = new_core + [u]
            self.core = new_core
            return


        if self.minz and len(self.core) > 1 and (len(self.core) < core_size_thesh) :
            #if debug: 
            #print(self.core, self.wght)
            if (issort):
                try:
                    self.core = sorted(self.core, key=lambda l: self.wght[l])
                except:
                    pass
                # print(self.core)
                # for v,k in  self.asm2nodes.items():
                #     print(v,k)
                u2l = u_and_level(self.core, self.asm2nodes)
                self.core = list({k: v for k, v in sorted(u2l.items(), key=lambda item: item[1], reverse=True)})


            
            i = 0
            keep = []
            core = self.core
            proj = keep + core 
            def_prop = 100000
            #if (lnc < 250):

            start_prop = 500000
            misses_in_a_row = 50
            miss = 0
            time_total = 0
            core = self.core
            unfolded = set()
                

            while len(core) > 0:
                if (miss == misses_in_a_row):
                    if (unfolding):
                        new_core = copy.deepcopy(keep)
                        for u in to_test:
                            if u in self.upperlevel:
                                node = forest_find_node(u, self.asm2nodes)                
                                new_core  = new_core+ node.cu_cover
                            else:
                                new_core = new_core + [u]
                        keep = new_core                    
                    else:
                        keep = keep + to_test

                    break

                if unfolding:
                    if core[0] in self.upperlevel:
                        cu = core[0]                     
                        node = forest_find_node(cu, self.asm2nodes)                
                        #print(f" unfolding {core[0]} --> {node.cu_cover}" )
                        u2l = u_and_level(node.cu_cover, self.asm2nodes)
                        cu_cover = list({k: v for k, v in sorted(u2l.items(), key=lambda item: item[1], reverse=True)})
                        core  =  cu_cover+ core[1:]
                        proj  = node.cu_cover + proj
                        for a in node.cu_cover:
                            unfolded.add(a)
                    elif core[0] in unfolded:
                        proj  = [core[0]] + proj
                    else:
                        keep.append(core[0])
                        to_test =  core[1:]
                        core = core[1:]
                        #print("continue")
                        continue

                
                to_test =  core[1:]
                #node = forest_find_node(core[0], self.asm2nodes)
                #print(node)
               # print(f"core {core} keep {keep} proj {proj}")

                if not (core[0] in proj):
                    #i = i+ 1
                    to_test = core[1:]
                    core = core[1:]
                    #print("continue")
                    continue

                keep = [c for c in keep if c in proj]
                #################################################
                #oracle.clear_interrupt()
                oracle.prop_budget(start_prop)
                #def interrupt(s):
                #    s.interrupt()                
                #timer = Timer(time_per_call, interrupt, [oracle])            
                start =time.time()
                #timer.start()
                #if debug: print(f"core {keep + to_test}")

                status = oracle.solve_limited(assumptions= keep + to_test)        
                
                #timer.cancel()
                #print((time.time() - start))        
                time_total = time_total + (time.time() - start)
                #oracle.clear_interrupt()
                
                if (time_total > 30):
                   start_prop = def_prop
                   time_per_call = 1
                
                ##############################################

                if debug:  print('c oracle time: {0:.4f}'.format(time_total))
                #print(prop)
                if status  == False:
                    newcore = oracle.get_core()
                    if (newcore is None):
                        newcore = []                    
                    proj =  newcore                 
                elif oracle.get_status() == True:
                    keep.append(core[0])

                else:
                    keep.append(core[0])
                if status == None:
                    miss +=1

            

                if debug: print(f"{oracle.get_status()} {core[0]} {len(keep + to_test)}")
                core = core[1:]
                    #break
                

            self.core =  keep
            #print(f"final {keep}")
            #assert(oracle.solve_limited(assumptions=self.core) == False)
            if debug: print(f"min end {len(self.core)}")           
            #oracle.clear_interrupt()
            if (unfolding) and debug:
                for u in self.core:
                    node = forest_find_node(u, self.asm2nodes)
                    assert(node.type != COMPRESSSOR)
 
            
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
            return  self.oracle.time_accum() +self.or_time

        else:
            end = time.time()
            return self.time +self.or_time + self.oracle.time_accum() #+  end - self.timer - self.build_time

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
        opts, args = getopt.getopt(sys.argv[1:], 'ab:c:e:hil:ms:pqrt:vxyz',
                ['adapt', 'block=', 'comp=', 'enum=', 'exhaust', 'help',
                    'incr', 'blo=', 'minimize', 'solver=', 'trim=',  'circuitinject=','verbose','minw=','maxw=','ilp=', 'ilpcpu=', 'ilpprep=',
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
    min_window= None
    max_window = None
    ilp = DEFAULT_ILP
    ilpprep = DEFAULT_ILPPREP
    ilpcpu = DEFAULT_ILPCPU

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
        elif opt in ('-p', '--maxw'):
            max_window = int(arg)            
        elif opt in ('-q', '--minw'):
            min_window = int(arg)   
        elif opt in ('-y', '--ilp'):
            ilp = int(arg)      
        elif opt in ('-z', '--ilpcpu'):
            ilpcpu = int(arg)       
        elif opt in ('-z', '--ilpprep'):
            ilpprep = int(arg)                                                
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

    return adapt, blo, block, cmode, to_enum, exhaust, incr, minz,\
            solver, trim, circuitinject, min_window, max_window,  ilp, ilpcpu, ilpprep, verbose, vnew, args


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
            circuitinject,  min_window, max_window, ilp, ilpcpu, ilpprep, verbose, vnew, files = parse_options()
    

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

        MXS = RC2

        # starting the solver

        with MXS(formula, solver=solver, adapt=adapt, exhaust=exhaust,
                incr=incr, minz=minz, trim=trim, circuitinject=circuitinject,  
                min_window = min_window, max_window = max_window, 
                ilp = ilp, ilpcpu = ilpcpu, ilpprep = ilpprep, verbose=verbose) as rc2:

            
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
