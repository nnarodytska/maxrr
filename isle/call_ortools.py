
from copy import deepcopy

from numpy import append
import networkx as nx
from networkx.drawing.nx_pydot import write_dot

import networkx as nx
import matplotlib
#matplotlib.use("Agg")
import matplotlib.pyplot as plt
from ortools.sat.python import cp_model

from forest import forest_active, forest_nodes
from circuit import INITIAL_SELECTOR, STATUS_ACTIVE, STATUS_INACTIVE

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

    nodes = forest_nodes(forest)
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
    selectors_nodes = forest_active(forest)
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