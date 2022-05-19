
from contextlib import AsyncExitStack
from copy import deepcopy

from numpy import append
import networkx as nx
from networkx.drawing.nx_pydot import write_dot

import networkx as nx
import matplotlib
#matplotlib.use("Agg")
import matplotlib.pyplot as plt
from graphviz import Digraph


INITIAL_SELECTOR    = "i-sel"
SELECTOR            = "sel"

STATUS_ACTIVE       = "A"
STATUS_INACTIVE     = "I"
STATUS_WAITING      = "W"
STATUS_FOLDED       = "F"

GRAPH_PRINT_DEF     = 'graph.dot'
def node_label(node):
    s =  f"{node.u}({node.status})"
    return s

def build_graph(root, graph = None, nodes = [], edges = [], is_top = False, fname = GRAPH_PRINT_DEF):
    if graph == None:
        graph =  Digraph()
    if len(root.children) == 0 and is_top:
        graph.edge(node_label(root), node_label(root))
    for child in root.children:
        if not(root.u in nodes):
            nodes.append(node_label(root))

        if not ([root.u, child.u] in edges):
            graph.edge(node_label(root), node_label(child))
            edges.append([root.u, child.u])
            #print(f"adding {root.u} -- {child.u}")
        else:
            # for e in graph.edges:
            #     print(e)
            #print(f"skipping {root.u} -- {child.u}")
            pass
        build_graph(child, graph = graph, nodes = nodes, edges = edges)
    if (is_top):
        #
        #f = plt.figure()
        #print(graph.source)
        #graph.view()
        filename = graph.render(filename=fname,  format='pdf')

        


def traverse(root, tab = 0):
    print(' '*tab + root.__str__())
    tab = tab + 2
    for child in root.children:
        traverse(child, tab)

def get_folded_selectors_nodes(root, nodes = []):
    if (root.status == STATUS_FOLDED):
        nodes.append(root)   
    for child in root.children:
        get_folded_selectors_nodes(child, nodes)

def get_active_selectors_nodes(root, nodes = []):
    if (root.status == STATUS_ACTIVE):
        nodes.append(root)   
    for child in root.children:
        get_active_selectors_nodes(child, nodes)

def get_waiting_selectors_nodes(root, nodes = []):
    if (root.status == STATUS_WAITING):
        nodes.append(root)   
    for child in root.children:
        get_waiting_selectors_nodes(child, nodes)


def get_nodes(root, nodes = []):    
    nodes.append(root)   
    for child in root.children:
        get_nodes(child, nodes)

def find_u(root, u):
    if (root.u == u):        
        return root
    for child in root.children:
        node = find_u(child, u)
        if not (node is None):
            return node

def is_inactive(root):
    if (root.status != STATUS_INACTIVE):        
        return False
    for child in root.children:
        not_inactive = is_inactive(child)
        if not not_inactive:
            return not_inactive
    return True

class Circuit(object):
    def __init__(self, data, children=None, parent=None, u = None, v = None, weight = None, type = None, status = None, into_phase = 0):
        self.data = data
        self.children = children or []
        for child in self.children:
            child.parents.append(self)
        self.parents = []
        if not (parent is None):
            self.parents.append(parent)        
        self.u = u
        self.v = v
        self.weight = weight
        self.type = type
        self.status = status
        self.v_clauses = [] 
        self.u_clauses = [] 
        self.into_phase = into_phase
        
        if (self.type == INITIAL_SELECTOR):
            assert(self.u == self.v)


    # def add_child(self, data):
    #     new_child = Tree(data, parent=self)
    #     self.children.append(new_child)
    #     return new_child

    def is_root(self):
        return len(self.parents) == 0

    def is_leaf(self):
        return not self.children

    def __str__(self):
        s = f"({self.u}:p{self.into_phase}: {self.type}, {self.status})"
        if self.is_leaf():
            return "*" + s 
        return  s 

