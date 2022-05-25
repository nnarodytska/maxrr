
from copy import deepcopy

from numpy import append
import networkx as nx
from networkx.drawing.nx_pydot import write_dot

import networkx as nx
import matplotlib
#matplotlib.use("Agg")
import matplotlib.pyplot as plt
from graphviz import Digraph

from circuit import INITIAL_SELECTOR, STATUS_ACTIVE, STATUS_WAITING, build_graph, find_u, get_active_selectors_nodes, get_active_selectors_u_and_level_nodes, get_folded_selectors_nodes, get_nodes, get_waiting_selectors_nodes


def forest_find_node (u,  mapping):
    assert u in mapping, f"u={u} is missing"
    return mapping[u]

def forest_build_graph(forest, mapping, fname ='graph.dot'):
    graph = Digraph()
    edges = []
    nodes = []
    for u in forest:
        t = mapping[u]
        build_graph(t, graph = graph, nodes = nodes,  edges = edges, is_top = True, fname = fname)    

def unique_nodes(nodes, unique):
    if (unique):
        nodes = list(set(nodes))
    return nodes
    
# def forest_folded(forest, mapping, unique = True):
#     nodes = []
#     for u in forest:
#         t = forest_find_node(u, mapping)
#         get_folded_selectors_nodes(t, nodes)

#     return unique_nodes(nodes, unique)


def forest_filter(mapping, status):
    nodes = set()
    for u, node in mapping.items():
        if node.status == status or (status is None):
            nodes.add(u)

    return nodes

# def forest_active(forest, mapping, unique = True):
#     nodes = []
#     for u in forest:
#         t = forest_find_node(u, mapping)
#         get_active_selectors_nodes(t, nodes)

#     return unique_nodes(nodes, unique)         

def u_and_level_active(mapping):
    u2l = {}
    for u, node in mapping.items():
        if node.status == STATUS_ACTIVE:
            if (node.type == INITIAL_SELECTOR):
                u2l[u]= 0               
            else:
                u2l[u]= (node.level+1)*1000 - node.into_phase

    return u2l

# def forest_nodes(forest, mapping, unique = True):
#     nodes = []
#     for u in forest:
#         t = forest_find_node(u, mapping)
#         get_nodes(t, nodes)

#     return unique_nodes(nodes, unique)  