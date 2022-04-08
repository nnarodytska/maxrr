#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## fm.py
##
##  Created on: Feb 5, 2018
##      Author: Antonio Morgado, Alexey Ignatiev
##      E-mail: {ajmorgado, aignatiev}@ciencias.ulisboa.pt
##

"""
    ===============
    List of classes
    ===============

    .. autosummary::
        :nosignatures:

        FM

    ==================
    Module description
    ==================

    This module implements a variant of the seminal core-guided MaxSAT
    algorithm originally proposed by [1]_ and then improved and modified
    further in [2]_ [3]_ [4]_ [5]_. Namely, the implementation follows the
    WMSU1 variant [5]_ of the algorithm extended to the case of *weighted
    partial* formulas.

    .. [1] Zhaohui Fu, Sharad Malik. *On Solving the Partial MAX-SAT Problem*.
        SAT 2006. pp. 252-265

    .. [2] Joao Marques-Silva, Jordi Planes. *On Using Unsatisfiability for
        Solving Maximum Satisfiability*. CoRR abs/0712.1097. 2007

    .. [3] Joao Marques-Silva, Vasco M. Manquinho. *Towards More Effective
        Unsatisfiability-Based Maximum Satisfiability Algorithms*. SAT 2008.
        pp. 225-230

    .. [4] Carlos Ansótegui, Maria Luisa Bonet, Jordi Levy. *Solving
        (Weighted) Partial MaxSAT through Satisfiability Testing*. SAT 2009.
        pp. 427-440

    .. [5] Vasco M. Manquinho, Joao Marques Silva, Jordi Planes. *Algorithms
        for Weighted Boolean Optimization*. SAT 2009. pp. 495-508

    The implementation can be used as an executable (the list of available
    command-line options can be shown using ``fm.py -h``) in the following way:

    ::

        $ xzcat formula.wcnf.xz
        p wcnf 3 6 4
        1 1 0
        1 2 0
        1 3 0
        4 -1 -2 0
        4 -1 -3 0
        4 -2 -3 0

        $ fm.py -c cardn -s glucose3 -vv formula.wcnf.xz
        c cost: 1; core sz: 2
        c cost: 2; core sz: 3
        s OPTIMUM FOUND
        o 2
        v -1 -2 3 0
        c oracle time: 0.0001

    Alternatively, the algorithm can be accessed and invoked through the
    standard ``import`` interface of Python, e.g.

    .. code-block:: python

        >>> from pysat.examples.fm import FM
        >>> from pysat.formula import WCNF
        >>>
        >>> wcnf = WCNF(from_file='formula.wcnf.xz')
        >>>
        >>> fm = FM(wcnf, verbose=0)
        >>> fm.compute()  # set of hard clauses should be satisfiable
        True
        >>> print(fm.cost) # cost of MaxSAT solution should be 2
        >>> 2
        >>> print(fm.model)
        [-1, -2, 3]

    ==============
    Module details
    ==============
"""

#
#==============================================================================
from __future__ import print_function

import glob
import os
import copy

from os import path
from posixpath import split
root_dir = "/home/nina/workspace/data/mse21_complete_unwt/"
results =  "/home/nina/workspace/data/mse21_unwt_results/"

focus =[]
# focus = ["kbtree9_7_3_5_90_2.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_30_4.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_40_4.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_20_4.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_20_6.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_40_6.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_70_6.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_60_4.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_50_3.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_30_1.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_40_2.wcsp.wcnf.gz", 
# "kbtree9_7_3_5_30_5.wcsp.wcnf.gz"]

rc2 = [False, "rc2"]
rc2comp = [True, "rc2comp"]
cashwmaxsat = [False, "cashwmaxsat"]

res  = [True, "maxres",  "-r mr1a ", "v0"]
res_v1 = [True, "maxres", "-r mr1b ", "v1"]
res_v2 = [True, "maxres", "-r mr2a ",  "v2"]
res_v3 = [True, "maxres", "-r mr2b",  "v3"] # with closure
res_v4 = [False, "maxres", " ",  "v4"] # no closure
res_v5 = [False, "maxres", " --ilp=5 ",  "v5"] # gurobi

resrg  = [False, "resrg",  "", "v0"]

to = [3600]#, 3600*3]

maxhs = [False, "maxhs"]
eva = [False, "eva"]

gen_run = True
process_run = False
if (gen_run):
    with open('run.txt', 'w') as the_file:
        for tm in to:
            known = []

            for filename in glob.iglob(root_dir + '**/**', recursive=True):
                if(os.path.isfile(filename)):
                    if (filename in known):
                        continue
                    #print (filename)
                    desktop = "maxrr" # pysat
                    local_desktop = "pysat" # 

                    known.append(filename)
                    res_filename = filename.replace("mse21_complete_unwt", "mse21_unwt_results")
                    res_filename_1 =  filename.replace("mse21_complete_unwt", "mse21_complete_unwt_unzip")

                    name = (res_filename.split("/"))[-1]

                    if len(focus) > 0  and not(name in focus):
                        continue
                    
                    timetag = ""
                    if (tm > 3601):
                        timetag = str(tm) + "."
                    if (rc2[0]):
                        s = f"timeout -t {tm}s python3 -u ../examples/rc2.py -vv {filename} > {res_filename}.{rc2[1]}.{timetag}res "
                        the_file.write(f'{s}\n')
                    if (rc2comp[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s maplesat -v {filename} > {res_filename}.{rc2comp[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (maxhs[0]):
                        s = f"timeout {tm}s  /home/nina/workspace/maxhs/bin/maxhs -verb=2 {filename} > {res_filename}.{maxhs[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (eva[0]):
                        s = f"timeout {tm}s  /home/nina/workspace/{desktop}/eva/eva500  {filename} > {res_filename}.{eva[1]}.{timetag}res 2>&1 "
                        the_file.write(f'{s}\n')

                    if (cashwmaxsat[0]):
                        s =  f"gunzip -c {filename} > {res_filename_1}.wcnf; \n"
                        s = s + f"timeout {tm}s  /home/nina/workspace/cashmaxsat/bin/cashwmaxsat   -no-bin -no-sat -m -bm  {res_filename_1}.wcnf > {res_filename}.{cashwmaxsat[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s maplesat {res[2]}  -vv {filename} > {res_filename}.l2.{res[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v1[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s maplesat {res_v1[2]}  -vv {filename} > {res_filename}.{res_v1[3]}.{res_v1[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v2[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s  maplesat {res_v2[2]} -vv {filename} > {res_filename}.{res_v2[3]}.{res_v2[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v3[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s  maplesat {res_v3[2]} -vv {filename} > {res_filename}.{res_v3[3]}.{res_v3[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v4[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s  maplesat {res_v4[2]} -vv {filename} > {res_filename}.{res_v4[3]}.{res_v4[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v5[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{local_desktop}/res/res.py -c b -s  maplesat {res_v5[2]} -vv {filename} > {res_filename}.{res_v5[3]}.{res_v5[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (resrg[0]):
                        s = f"timeout {tm}s python3 -u /home/nina/workspace/{desktop}/res/res.py -c b -s maplesat {resrg[2]}  -vv {filename} > {res_filename}.{resrg[3]}.{resrg[1]}.{timetag}res "
                        the_file.write(f'{s}\n')


                    #s = f"python3 ../examples/fm.py   -vv {filename} > {res_filename}.fm.res "
                    #the_file.write(f'{s}\n')

                else:
                    filename1 = filename.replace("mse21_complete_unwt", "mse21_unwt_results")
                    filename2 = filename.replace("mse21_complete_unwt", "mse21_complete_unwt_unzip")
                    print(filename1)
                    print(filename2)

                    try:
                        os.mkdir(filename1)
                    except:
                        pass
                    try:
                        os.mkdir(filename2)
                    except:
                        pass


if (process_run):
    rc2comp = [True, "rc2comp"]

    maxhs = [True, "maxhs"]
    resrg  = [True, "resrg",  "", "v0"]


    to = [3600]#, 3600]#, 3600*3]
    for tm in to:

        results_rc2comp = {}
        results_maxsatcomp = {}
        results_cashwmaxsat = {}
        results_res = {}    
        results_eva = {}
        results_resrg = {}
        results_res_v3 = {}
        results_res_v4 = {}
        results_res_v5 = {}

        known = []
        
        dummy =  [-1, tm, -1, -1]
        timetag = ""
        if (tm > 3601):
            timetag = str(tm) + "."
        for filename in glob.iglob(root_dir + '**/**', recursive=True):
                if(os.path.isfile(filename)):
                    if (filename in known):
                        continue
                    #print (filename)

                    known.append(filename)
                    res_filename = filename.replace("mse21_complete_unwt", "mse21_unwt_results")
                    res_filename_1 =  filename.replace("mse21_complete_unwt", "mse21_complete_unwt_unzip")
                    file_name = (res_filename.split("/"))[-1]
                    file_name = file_name[0:80]
                    #print(res_filename, file_name)
                    #print(dummy)
                    if (rc2[0]):
                        s = f"{res_filename}.{rc2[1]}.{timetag}res"
                        assert(path.isfile(s))
                    if (rc2comp[0]):
                        s = f"{res_filename}.{rc2comp[1]}.{timetag}res"
                        res = copy.deepcopy(dummy)
                        results_rc2comp[file_name] = res

                        if not (path.isfile(s)):
                            results_rc2comp[file_name] = copy.deepcopy(dummy)
                        else:

                            file = open(s, "r")

                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c oracle time:"
                                if  f ==  line[:len(f)]:
                                    time = float(line[len(f):])
                                    res[1] = time
                                f = "c cost:"
                                if  f ==  line[:len(f)]:
                                    r  = (line[len(f):]).split(";")[0]
                                    #print(r)
                                    res[2] = int(r)
                        if len(res) == 0:
                            results_rc2comp[file_name] = copy.deepcopy(dummy)
                        else:
                            results_rc2comp[file_name] = res
                        

                    if (maxhs[0]):
                        res =  copy.deepcopy(dummy)
                        results_maxsatcomp[file_name] = res                        

                        s = f"{res_filename}.{maxhs[1]}.{timetag}res"
                        #print(s)
                        if not (path.isfile(s)):
                            results_rc2comp[file_name] = copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
                    
                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c CPU:"
                                if  f ==  line[:len(f)]:
                                    time = float(line[len(f):])
                                    res[1] = time
                                f = "c Best LB Found:"
                                if  f ==  line[:len(f)]:
                                    res[2] = int(line[len(f):])
                                f = "c Best UB Found:"
                                if  f ==  line[:len(f)]:
                                    res[3] = int(line[len(f):])
                                    results_maxsatcomp[file_name]  =  copy.deepcopy(dummy)
                                    results_maxsatcomp[file_name][2] = res[2]
                                    results_maxsatcomp[file_name][3] = res[3]

                                    break
                                # f = "c unsolved"
                                # if  f ==  line[:len(f)]:
                                #     results_maxsatcomp[file_name]  =  copy.deepcopy(dummy)
                                #     results_maxsatcomp[file_name][2] = res[2]
                                #     results_maxsatcomp[file_name][3] = res[3]
                                    
                        if len(res) == 0:
                            results_maxsatcomp[file_name] =  copy.deepcopy(dummy)
                        else:
                            results_maxsatcomp[file_name] = res                        


                    if (cashwmaxsat[0]):
                        res =  copy.deepcopy(dummy)
                        results_cashwmaxsat[file_name] = res    
                        maxhs[0]
                        s = f"{res_filename}.{cashwmaxsat[1]}.{timetag}res"
                        #print(s)
                        if not (path.isfile(s)):
                            results_cashwmaxsat[file_name] =  copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
                            for line in file:
                                #print(s)
                                if "o " ==  line[:2] and len(line) < 10:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c CPU time               : "
                                if  f ==  line[:len(f)]:
                                    r = line[len(f):]
                                    r = (r.split(" "))[0]
                                    time = float(r)
                                    res[1] = time

                        if len(res) == 0:
                            results_cashwmaxsat[file_name] =  copy.deepcopy(dummy)
                        else:
                            results_cashwmaxsat[file_name] = res    
                    if (resrg[0]):
                        
                        s = f"{res_filename}.{resrg[3]}.{resrg[1]}.{timetag}res"
                        #s = f"{res_filename}.{res[1]}.res"
                        res = copy.deepcopy(dummy)
                        results_resrg[file_name] = res
                        
                        #s = f"{res_filename}.{res[1]}.res"
                        if not (path.isfile(s)):
                            results_resrg[file_name] = copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c oracle time:"
                                if  f ==  line[:len(f)]:
                                    time = float(line[len(f):])
                                    res[1] = time
                                f = "c cost:"
                                if  f ==  line[:len(f)]:
                                    r  = (line[len(f):]).split(";")[0]
                                    #print(r)
                                    res[2] = int(r)

                        if len(res) == 0:
                            results_resrg[file_name] = copy.deepcopy(dummy)
                        else:
                            results_resrg[file_name] = res
                    if (res[0]):
                        
                        s = f"{res_filename}.l2.{res[1]}.{timetag}res"
                        #s = f"{res_filename}.{res[1]}.res"
                        res = copy.deepcopy(dummy)
                        results_res[file_name] = res
                        
                        #s = f"{res_filename}.{res[1]}.res"
                        if not (path.isfile(s)):
                            results_res[file_name] = copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c oracle time:"
                                if  f ==  line[:len(f)]:
                                    time = float(line[len(f):])
                                    res[1] = time
                                f = "c cost:"
                                if  f ==  line[:len(f)]:
                                    r  = (line[len(f):]).split(";")[0]
                                    #print(r)
                                    res[2] = int(r)

                        if len(res) == 0:
                            results_res[file_name] = copy.deepcopy(dummy)
                        else:
                            results_res[file_name] = res


                    if (eva[0]):
                        
                        s = f"{res_filename}.{eva[1]}.{timetag}res"
                        res = copy.deepcopy(dummy)
                        results_eva[file_name] = res

                        if not (path.isfile(s)):
                            results_eva[file_name] = copy.deepcopy(dummy)
                        else:

                            file = open(s, "r")
                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[2] = opt
                                f = "c UNSAT LB:"
                                if  f ==  line[:len(f)]:                        
                                    r  = (line[len(f):]).split(",")[1]
                                    #print(r, line)
                                    r  = r.split(":")[1]
                                    time = float(r)
                                    res[1] = time
                                f = "s OPTIMUM FOUND"
                                if  f ==  line[:len(f)]:
                                    r  = (line[len(f):]).split(";")[0]
                                    #print(r)
                                    res[0] = res[2]

                        if len(res) == 0:
                            results_eva[file_name] = copy.deepcopy(dummy)
                        else:
                            results_eva[file_name] = res

                    if (res_v3[0]):
     
                        s = f"{res_filename}.{res_v3[3]}.{res_v3[1]}.{timetag}res"
                        print(s)
                        res = copy.deepcopy(dummy)
                        results_res_v3[file_name] = res
                        
                        #s = f"{res_filename}.{res[1]}.res"
                        if not (path.isfile(s)):
                            results_res_v3[file_name] = copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c oracle time:"
                                if  f ==  line[:len(f)]:
                                    time = float(line[len(f):])
                                    res[1] = time
                                f = "c cost:"
                                if  f ==  line[:len(f)]:
                                    r  = (line[len(f):]).split(";")[0]
                                    #print(r)
                                    res[2] = int(r)

                        if len(res) == 0:
                            results_res_v3[file_name] = copy.deepcopy(dummy)
                        else:
                            results_res_v3[file_name] = res                        
                  


                    if (res_v4[0]):
                        s = f"{res_filename}.{res_v4[3]}.{res_v4[1]}.{timetag}res"
                        #s = f"{res_filename}.{res[1]}.res"
                        res = copy.deepcopy(dummy)
                        results_res_v4[file_name] = res
                        
                        #s = f"{res_filename}.{res[1]}.res"
                        if not (path.isfile(s)):
                            results_res_v4[file_name] = copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
                            for line in file:
                                if "o " ==  line[:2]:
                                    opt = int(line[2:])
                                    res[0] = opt
                                f = "c oracle time:"
                                if  f ==  line[:len(f)]:
                                    time = float(line[len(f):])
                                    res[1] = time
                                f = "c cost:"
                                if  f ==  line[:len(f)]:
                                    r  = (line[len(f):]).split(";")[0]
                                    #print(r)
                                    res[2] = int(r)

                        if len(res) == 0:
                            results_res_v4[file_name] = copy.deepcopy(dummy)
                        else:
                            results_res_v4[file_name] = res   


                    if (res_v5[0]):
                        s = f"{res_filename}.{res_v5[3]}.{res_v5[1]}.{timetag}res"
                        #s = f"{res_filename}.{res[1]}.res"
                        res = copy.deepcopy(dummy)
                        results_res_v5[file_name] = res
                        
                        #s = f"{res_filename}.{res[1]}.res"
                        if not (path.isfile(s)):
                            results_res_v5[file_name] = copy.deepcopy(dummy)
                        else:
                            file = open(s, "r")
   
                            for line in file:
                                if "Exp" ==  line[:3]:
                                    r = line.split()
                                    r = r[-2].replace(",","") 
                                    time = float(r)
                                    res[1] = time
                                f = "Best"
                                #print(line)
                                if  f ==  line[:4]:
                                    r = line.split()
                                    r = r[2].replace(",","")                                    
                                    if r != "-":
                                        opt = float(r)
                                        res[0] = int(opt)
                                        r = r[4].replace(",","")                                     
                                        opt = float(r)                             
                                        res[2] = int(opt)

                        if len(res) == 0:
                            results_res_v5[file_name] = copy.deepcopy(dummy)
                        else:
                            results_res_v5[file_name] = res   

        #print(results_res_v4.items())

        #exit()
        opt = "opt"
        lb = "lb"
        ub = "ub"
        with open(f'results.{timetag}txt', 'w') as the_file:
            h_res = f"{opt:<5}/{lb:<5}  {res[1]:<10} "
            h_eva = f" {opt:<5}/{lb:<5} {eva[1]:<10} "
            h_rc2comp = f"{opt:<5}/{lb:<5}   {rc2comp[1]:<10}"
            h_maxhs = f"{opt:<5}/{lb:<5}/{ub:<5}   {maxhs[1]:<10}"
            h_cashwmaxsat = f"{opt:<10}   {cashwmaxsat[1]:<12}"
            h_resrg = f"{opt:<5}/{lb:<5}  {resrg[1]:<10} "
            h_res_v3 = f"{opt:<5}/{lb:<5}  {res_v3[1]:<10} "
            h_res_v4 = f"{opt:<5}/{lb:<5}  {res_v4[1]:<10} "
            h_res_v5 = f"{opt:<5}/{lb:<5}  {res_v5[1]:<10} "
            s = f"     {f:<80} {h_resrg} {h_rc2comp} {h_maxhs} {h_res_v3} {h_res_v4}  {h_res_v5}"
            print(s)
            the_file.write(f'{s}\n')

            for f,v in results_rc2comp.items():
                #print(results_rc2comp[f])
                #print(results_maxsatcomp[f])
                #print(results_cashwmaxsat[f])
                #print(results_res[f])
                #print(results_eva[f])
                
                try:
                    if (results_rc2comp[f][0] >  -1) and  (results_maxsatcomp[f][0] > -1):
                        assert(results_rc2comp[f][0] == results_maxsatcomp[f][0])
                    if (results_resrg[f][0] >  -1) and  (results_maxsatcomp[f][0] > -1):
                        assert(results_resrg[f][0] == results_maxsatcomp[f][0])
                                            
                    # if (cashwmaxsat[0]):                
                    #     if (results_cashwmaxsat[f][0] >  -1) and  (results_maxsatcomp[f][0] > -1):
                    #         assert(results_cashwmaxsat[f][0] == results_maxsatcomp[f][0])
                    # if (results_res[f][0] >  -1) and  (results_maxsatcomp[f][0] > -1):
                    #     assert(results_res[f][0] == results_maxsatcomp[f][0])
                    # if (results_res[f][0] >  -1) and  (results_rc2comp[f][0] > -1):
                    #     assert(results_res[f][0] == results_rc2comp[f][0])
                except:
                    print("*********check results")
                pref = ""
                if (results_maxsatcomp[f][0] > -1) and results_rc2comp[f][0] == -1:
                    pref = "*** "
                elif (results_maxsatcomp[f][0] == -1) and results_rc2comp[f][0] > -1:
                    pref = "+++ "
                else:
                    pref = "    "
                
                try:
                    s_res = f"{results_res[f][0]:<5}/{results_res[f][2]:<5} {results_res[f][1]:<10}"
                except:
                    pass

                try:
                    s_resrg = f"{results_resrg[f][0]:<5}/{results_resrg[f][2]:<5} {results_resrg[f][1]:<10}"
                except:
                    pass

                try:
                    s_res_v3 = f"{results_res_v3[f][0]:<5}/{results_res_v3[f][2]:<5} {results_res_v3[f][1]:<10}"
                except:
                    s_res_v3 = f"{0:<5}/{0:<5} {0:<10}"
                    pass

                try:
                    s_res_v4 = f"{results_res_v4[f][0]:<5}/{results_res_v4[f][2]:<5} {results_res_v4[f][1]:<10}"
                except:
                    s_res_v4= f"{0:<5}/{0:<5} {0:<10}"
                    pass

                try:
                    s_res_v5 = f"{results_res_v5[f][0]:<5}/{results_res_v5[f][2]:<5} {results_res_v5[f][1]:<10}"
                except:
                    s_res_v5= f"{0:<5}/{0:<5} {0:<10}"
                    pass


                try:
                    s_eva = f"{results_eva[f][0]:<5}/{results_eva[f][2]:<5} {results_eva[f][1]:<10}"
                except:
                    pass

                try:
                    s_rc2comp = f"{results_rc2comp[f][0]:<5}/{results_rc2comp[f][2]:<5} {results_rc2comp[f][1]:<10}"
                except:
                    pass

                try:
                    s_maxhs  = f"{results_maxsatcomp[f][0]:<5}/{results_maxsatcomp[f][2]:<5}/{results_maxsatcomp[f][3]:<5} {results_maxsatcomp[f][1]:<10} "
                except:
                    pass




                s = f"{pref} {f:<80} {s_resrg} {s_rc2comp} {s_maxhs} {s_res_v3} {s_res_v4}  {s_res_v5}"
                print(s)
                the_file.write(f'{s}\n')