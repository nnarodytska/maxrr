
from copy import deepcopy
from math import ceil, floor

from numpy import append
import networkx as nx
from networkx.drawing.nx_pydot import write_dot

import networkx as nx
import matplotlib
#matplotlib.use("Agg")
import matplotlib.pyplot as plt
from ortools.sat.python import cp_model

from forest import forest_filter, forest_find_node
from circuit import INITIAL_SELECTOR, STATUS_ACTIVE, STATUS_INACTIVE

class SolverOR(object):
    def __init__(self):
        self.model = cp_model.CpModel()
        self.ortools_vars = {}

    def add_hards(self, formula):    
        for j, cl in enumerate(formula.hard):                   
            #print(cl)
            self.create_clauses_con(cl)

    def create_clauses_con(self,  cl):
        con_vars = []
        rhs =  1            
        #print(cl, max_id)
        for c in cl:

            b = self.get_var(c)
            if (c > 0):
                con_vars.append(b)
            else:
                con_vars.append(b.Not())     
        
        self.model.AddBoolOr(con_vars)       
        #print(cl, con_vars)

    def minimize(self,  cost_vars, mapping, hints = None, lb = None, ub = None, to = 600):        
        ortools_soft_vars = {}   
        ops = []
        wops = []        
        wght = []
        for j, u in enumerate(cost_vars):           
            b = self.get_var(u)
            ortools_soft_vars[abs(u)] = b
            if (u > 0):
                ops.append(b.Not())
                
            else:
                ops.append(b)
            assert(self.ortools_vars[abs(u)] == b)
            node = forest_find_node(u,mapping)
            wops.append(node.oweight)  
            
        #print(ops, wops, ub)
    
        #ortools_model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) ==0)
        if not (lb is None):
            self.model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) >= ceil(lb))
        if not (ub is None):
            self.model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) <= floor(ub))

        self.model.Minimize(cp_model.LinearExpr.WeightedSum(ops, wops))
    
        self.model.ClearHints()
        if not(hints is None):
            for c, v in hints.items():
                b = get_var(self.model, self.ortools_vars, c)
                self.model.AddHint(b,v)
                #print(b,v)

        solver = cp_model.CpSolver()
        solver.parameters.log_search_progress = True
        solver.parameters.num_search_workers = 8
        solver.parameters.min_num_lns_workers = 1
        #solver.parameters.interleave_search = True
        solver.parameters.max_time_in_seconds = to
        solver.parameters.cp_model_presolve = False
        #solver.parameters.search_branching = cp_model.sat_parameters_pb2.SatParameters.AUTOMATIC_SEARCH
        #solver.parameters.
        status = solver.Solve(self.model)
        print('Solve status: %s' % solver.StatusName(status))
        self.model.ClearHints()

        if status == cp_model.OPTIMAL or status ==  cp_model.FEASIBLE:
            print('Optimal objective value: %i' % solver.ObjectiveValue())
            print('Statistics')
            print('  - conflicts : %i' % solver.NumConflicts())
            print('  - branches  : %i' % solver.NumBranches())
            print('  - wall time : %f s' % solver.WallTime())
            print(solver.ResponseStats)
            solution = {}
            print(cost_vars)

            ub = solver.ObjectiveValue()
            for c, b in sorted(self.ortools_vars.items()):
                #print(c, b)            
                b = self.ortools_vars[c]
                solution[c] = solver.BooleanValue(b)
            #     if abs(c) in ortools_soft_vars:
            #         if abs(c) in extra_nodes_abs_u:
            #             print("---->", b, c, solver.BooleanValue(b))
            #         else:
            #             print(b, c, solver.BooleanValue(b))
            # #assert(False)
            #exit()
            return solution, solver.ObjectiveValue(), solver.BestObjectiveBound()
        elif  status ==  cp_model.INFEASIBLE:
            return {}, None, None

        return {}, None, None

    def feasibility(self,  assumptions, mapping, hints = None, lb = None, ub = None, to = 600):        
        
        ortools_soft_vars = {}   
        ops = []

        for j, u in enumerate(assumptions):           
            b = self.get_var(u)
            ortools_soft_vars[abs(u)] = b
            if (u > 0):
                ops.append(b)
                
            else:
                ops.append(b.Not())
            assert(self.ortools_vars[abs(u)] == b)
        self.model.ClearAssumptions()
        self.model.AddAssumptions(ops)
            
        #print(ops, wops, ub)
    
        # #ortools_model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) ==0)
        # if not (lb is None):
        #     self.model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) >= ceil(lb))
        # if not (ub is None):
        #     self.model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) <= floor(ub))

        # self.model.Minimize(cp_model.LinearExpr.WeightedSum(ops, wops))
    
        #self.model.ClearHints()
        # if not(hints is None):
        #     for c, v in hints.items():
        #         b = get_var(self.model, self.ortools_vars, c)
        #         self.model.AddHint(b,v)
        #         #print(b,v)

        solver = cp_model.CpSolver()
        solver.parameters.log_search_progress = True
        solver.parameters.num_search_workers = 16
        #solver.parameters.min_num_lns_workers = 1
        #solver.parameters.interleave_search = True
        solver.parameters.max_time_in_seconds = to
        #solver.parameters.cp_model_presolve = False
        # #solver.parameters.search_branching = cp_model.sat_parameters_pb2.SatParameters.AUTOMATIC_SEARCH
        # #solver.parameters.
        status = solver.Solve(self.model)
        print('Solve status: %s' % solver.StatusName(status))
        self.model.ClearAssumptions()

        if status == cp_model.OPTIMAL or status ==  cp_model.FEASIBLE:
            print('Optimal objective value: %i' % solver.ObjectiveValue())
            print('Statistics')
            print('  - conflicts : %i' % solver.NumConflicts())
            print('  - branches  : %i' % solver.NumBranches())
            print('  - wall time : %f s' % solver.WallTime())
            print(solver.ResponseStats)
            solution = {}
            #print(ops)

            ub = solver.ObjectiveValue()
            for c, b in sorted(self.ortools_vars.items()):
                #print(c, b)            
                b = self.ortools_vars[c]
                solution[c] = solver.BooleanValue(b)
            #     if abs(c) in ortools_soft_vars:
            #         if abs(c) in extra_nodes_abs_u:
            #             print("---->", b, c, solver.BooleanValue(b))
            #         else:
            #             print(b, c, solver.BooleanValue(b))
            # #assert(False)
            #exit()
            return solution, solver.ObjectiveValue(), solver.BestObjectiveBound()
        elif  status ==  cp_model.INFEASIBLE:

            print("UNSAT")
            print('SufficientAssumptionsForInfeasibility = 'f'{solver.SufficientAssumptionsForInfeasibility()}')

            return {}, None, None

        return {}, None, None

    def get_var(self, c):
        c = abs(c)
        if (c in self.ortools_vars):
            return self.ortools_vars[c]
        b = self.model.NewBoolVar(name= f"{c}")
        self.ortools_vars[c] = b
        return b

def get_var(ortools_model, ortools_vars, c):
    c = abs(c)
    if (c in ortools_vars):
        return ortools_vars[c]
    b = ortools_model.NewBoolVar(name= f"{c}")
    ortools_vars[c] = b
    return b
def create_clauses_con(ortools_model, ortools_vars, cl):
    con_vars = []
    rhs =  1            
    #print(cl, max_id)
    for c in cl:

        b = get_var(ortools_model, ortools_vars, c)
        if (c > 0):
            con_vars.append(b)
        else:
            con_vars.append(b.Not())     
    
    ortools_model.AddBoolOr(con_vars)       
    #print(cl, con_vars)


def add_hards(ortools_model, ortools_vars, formula, forest):    
    for j, cl in enumerate(formula.hard):                   
        create_clauses_con(ortools_model, ortools_vars, cl)

    nodes = forest_filter(forest)
    for i, node in enumerate(nodes):


        for v_cl in node.v_clauses:
            create_clauses_con(ortools_model, ortools_vars, v_cl)

        for u_cl in node.u_clauses:
            create_clauses_con(ortools_model, ortools_vars, u_cl) 

   

def solve_ortools(formula, forest, extra_nodes = None, minimization = [], hints = None, lb = None, ub = None, to = 600):        
         
    ##########################################
    ortools_model = cp_model.CpModel()
    ortools_vars = {}
    #print(ortools)        
    add_hards(ortools_model, ortools_vars, formula, forest)
    sels = []
    sums = []
    wght = {}
    selectors_nodes = forest_filter(forest, status=STATUS_ACTIVE)
    extra_nodes_abs_u = []
    if not(extra_nodes is None):
        selectors_nodes = selectors_nodes + extra_nodes
        extra_nodes_abs_u = [abs(n.u) for n in extra_nodes]

    #print([n.u for n in selectors_nodes])
    for i, node in enumerate(selectors_nodes):
        #print(node)
        if node.type == INITIAL_SELECTOR:
            sels.append(node.u)
        else:
            sums.append(node.u)
        
        
        assert(not (extra_nodes is None) or (node.status  == STATUS_ACTIVE))
        wght[node.u] =  node.weight
    ortools_soft_vars = {}   
    ops = []
    wops = []
    softs = sels + sums
    print(softs)
    # if (len(minimization) > 0):
    #     softs = minimization
    #     for j, c in enumerate(softs):           
    #         assert(c in  sels + sums) 
    #         b = get_var(ortools_model, ortools_vars, c)
    #         ortools_soft_vars[j] = b         
    #         ops.append(b)
    #     ortools_model.AddAssumptions(ops)
    # else: 

    if True:
        #print(f"softs {softs}")
        for j, c in enumerate(softs):           
            b = get_var(ortools_model, ortools_vars, c)
            ortools_soft_vars[abs(c)] = b
            if (c > 0):
                ops.append(b.Not())
                
            else:
                ops.append(b)
            assert( ortools_vars[abs(c)] == b)
            if not(extra_nodes_abs_u is None):
                wops.append(1)  
            else:
                wops.append(wght[c])  
            
        #print(ops, wops)
    
        #ortools_model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) ==0)
        if not (lb is None):
            ortools_model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) >= lb)
        if not (ub is None):
            ortools_model.Add(cp_model.LinearExpr.WeightedSum(ops, wops) <= ub)

        ortools_model.Minimize(cp_model.LinearExpr.WeightedSum(ops, wops))
    

    if not(hints is None):
        for c,v in hints.items():
            b = get_var(ortools_model, ortools_vars, c)
            ortools_model.AddHint(b,v)
            #print(b,v)

    solver = cp_model.CpSolver()
    solver.parameters.log_search_progress = True
    solver.parameters.num_search_workers = 1
    solver.parameters.max_time_in_seconds = to
    #solver.parameters.
    status = solver.Solve(ortools_model)
    print('Solve status: %s' % solver.StatusName(status))
    if status == cp_model.OPTIMAL or status ==  cp_model.FEASIBLE:
        print('Optimal objective value: %i' % solver.ObjectiveValue())
        print('Statistics')
        print('  - conflicts : %i' % solver.NumConflicts())
        print('  - branches  : %i' % solver.NumBranches())
        print('  - wall time : %f s' % solver.WallTime())
        print(solver.ResponseStats)
        solution = {}
        print(extra_nodes_abs_u)

        ub = solver.ObjectiveValue()
        for c, b in sorted(ortools_vars.items()):
            #print(c, b)            
            b = ortools_vars[c]
            solution[c] = solver.BooleanValue(b)
        #     if abs(c) in ortools_soft_vars:
        #         if abs(c) in extra_nodes_abs_u:
        #             print("---->", b, c, solver.BooleanValue(b))
        #         else:
        #             print(b, c, solver.BooleanValue(b))
        # #assert(False)
        #exit()
        return solution, solver.ObjectiveValue()
    elif  status ==  cp_model.INFEASIBLE:
        return [], None
	#     infeasibles = solver.SufficientAssumptionsForInfeasibility()
	#     print(f"Infeasible variables: {len(infeasibles)}")
	    #for i in infeasibles:
	    #    print(i, ortools_model.GetBoolVarFromProtoIndex(i))
    

    return None, None