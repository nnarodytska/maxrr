
from copy import deepcopy

from numpy import append
import networkx as nx
from networkx.drawing.nx_pydot import write_dot

import networkx as nx
import matplotlib
#matplotlib.use("Agg")
import matplotlib.pyplot as plt
from graphviz import Digraph

from circuit import build_graph, find_u, get_active_selectors_nodes, get_folded_selectors_nodes, get_nodes, get_waiting_selectors_nodes


def forest_find_node(forest, u):
    node = None            
    for i, t in enumerate(forest):
        # print(f"circuit #{i}")
        # traverse(t)
        node = find_u(t, u = u)            
        if not (node is None):
            break
    if (node is None):
        assert False, f"could not find {u}"
        
        
    return node

def forest_build_graph(forest, fname ='graph.dot'):
    graph = Digraph()
    edges = []
    nodes = []
    for t in forest:
        build_graph(t, graph = graph, nodes = nodes,  edges = edges, is_top = True, fname = fname)    

def unique_nodes(nodes, unique):
    if (unique):
        nodes = list(set(nodes))
    return nodes
    
def forest_folded(forest, unique = True):
    nodes = []
    for t in forest:
        get_folded_selectors_nodes(t, nodes)

    return unique_nodes(nodes, unique)


def forest_waiting(forest, unique = True):
    nodes = []
    for t in forest:
        get_waiting_selectors_nodes(t, nodes)

    return unique_nodes(nodes, unique)

def forest_active(forest, unique = True):
    nodes = []
    for i, t in enumerate(forest):
        get_active_selectors_nodes(t, nodes)

    return unique_nodes(nodes, unique)         

def forest_nodes(forest, unique = True):
    nodes = []
    for i, t in enumerate(forest):
        get_nodes(t, nodes)

    return unique_nodes(nodes, unique)  