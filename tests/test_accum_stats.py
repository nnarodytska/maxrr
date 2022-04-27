from pysat_local.solvers import Solver
from pysat_local.formula import CNF

solvers = ['cadical',
           'gluecard30',
           'gluecard41',
           'glucose30',
           'glucose41',
           'lingeling',
           'maplechrono',
           'maplecm',
           'maplesat',
           'mergesat3',
           'minicard',
           'minisat22',
           'minisat-gh']

def test_solvers():
    cnf = CNF(from_clauses=[[1, 2, 3], [-1, 2], [-2]])

    for name in solvers:
        with Solver(name=name, bootstrap_with=cnf) as solver:
            solver.solve()
            stats = solver.accum_stats()
            assert 'conflicts' in stats, 'No conflicts for {0}'.format(name)
            assert 'decisions' in stats, 'No decisions for {0}'.format(name)
            assert 'propagations' in stats, 'No propagations for {0}'.format(name)
            assert 'restarts' in stats, 'No restarts for {0}'.format(name)

