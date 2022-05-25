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

from solved_guropy import solved_gurobi, unsolved
from os import path
from posixpath import split
root_dir = "/home/nina/workspace/data/mse21_complete_unwt/"
results =  "/home/nina/workspace/data/mse21_unwt_results/"

#unsolved = []
unsolved =solved_gurobi + unsolved

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
rc2comp = [False, "rc2comp"]
cashwmaxsat = [False, "cashwmaxsat"]

res_v0  = [False, "maxres","--circuitinject=0", "v0"]
res_v1 = [True, "maxres", "--circuitinject=1", "v1"]
res_v2 = [False, "maxres", "--circuitinject=0",  "v2"]
res_v3 = [False, "maxres", "--circuitinject=2",  "v3"] # with closure
res_v4 = [False, "maxres", "--circuitinject=2",  "v4"] # 
res_v5 = [False, "maxres", "-r mr1b -y -u",  "v5"] 
res_v6 = [False, "maxres", "-r mr2a -y ",  "v6"] 
res_v7 = [False, "ortools", "",  "ortools"] 

# gurobi
or_tools = False
run_file = './run.txt'
if (or_tools):
    run_file = './or_run.txt'
resrg  = [False, "resrg",  "", "v0"]

to = [3600]#, 3600*3]

maxhs = [False, "maxhs"]
eva = [False, "eva"]

def process_instance(res_filename, res_v, timetag, dummy, file_name, results_res_v):

    s = f"{res_filename}.{res_v[3]}.{res_v[1]}.{timetag}res"
    #print(s)
    res = copy.deepcopy(dummy)
    results_res_v[file_name] = res
    
    #s = f"{res_filename}.{res[1]}.res"
    if not (path.isfile(s)):
        results_res_v[file_name] = copy.deepcopy(dummy)
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
        results_res_v[file_name] = copy.deepcopy(dummy)
    else:
        results_res_v[file_name] = res                        
    
    return results_res_v


gen_run = True
process_run = True
if (gen_run):
    with open(run_file, 'w') as the_file:
        for tm in to:
            known = []

            for filename in glob.iglob(root_dir + '**/**', recursive=True):
                if(os.path.isfile(filename)):
                    if (filename in known):
                        continue
                    # 
                    flag = False
                    for gs in unsolved:
                        #print(gs, filename)
                        if (filename.find(gs) != -1):
                            # print ("---", filename)
                            # exit()       
                            flag = True
                    if (flag):
                        continue
                    known.append(filename)

                    desktop = "maxrr" # pysat
                    local_desktop = "pysat" # 

                    known.append(filename)
                    
                    res_filename = filename.replace("mse21_complete_unwt", "mse21_unwt_results")
                    if (or_tools):
                        res_filename = filename.replace("mse21_complete_unwt", "mse21_unwt_ortools")
                        try:
                            os.mkdir("/home/nina/workspace/data/mse21_unwt_ortools/")
                        except:
                            pass

                    res_filename_1 =  filename.replace("mse21_complete_unwt", "mse21_complete_unwt_unzip")

                    name = (res_filename.split("/"))[-1]

                    if len(focus) > 0  and not(name in focus):
                        continue
                    
                    timetag = ""
                    if (tm > 3601):
                        timetag = str(tm) + "."
                    if (rc2[0]):
                        s = f"timeout -t {tm}s python3.8.8 -u ../examples/rc2.py -vv {filename} > {res_filename}.{rc2[1]}.{timetag}res "
                        the_file.write(f'{s}\n')
                    if (rc2comp[0]):
                        #s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b  -v {filename} > {res_filename}.{rc2comp[1]}.{timetag}res "
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/examples/rc2.py -c b  -v {filename} > {res_filename}.{rc2comp[1]}.{timetag}res "
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

                    if (res_v0[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b  {res_v0[2]}  -vv {filename} > {res_filename}.{res_v0[3]}.{res_v0[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v1[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b  {res_v1[2]}  -vv {filename} > {res_filename}.{res_v1[3]}.{res_v1[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v2[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b {res_v2[2]} -vv {filename} > {res_filename}.{res_v2[3]}.{res_v2[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v3[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b {res_v3[2]} -vv {filename} > {res_fiename}.{res_v3[3]}.{res_v3[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v4[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b {res_v4[2]} -vv {filename} > {res_filename}.{res_v4[3]}.{res_v4[1]}.{timetag}res "
                        the_file.write(f'{s}\n')

                    if (res_v5[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b {res_v5[2]} -vv {filename} > {res_filename}.{res_v5[3]}.{res_v5[1]}.{timetag}res "
                        the_file.write(f'{s}\n')


                    if (res_v6[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b {res_v6[2]} -vv {filename} > {res_filename}.{res_v6[3]}.{res_v6[1]}.{timetag}res "
                        the_file.write(f'{s}\n')


                    if (res_v7[0]):
                        os.system("gunzip -c {filename} > {res_filename_1}.wcnf")
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b {res_v7[2]} -vv {filename} > {res_filename}.{res_v7[3]}.{res_v7[1]}.{timetag}res "
                        the_file.write(f'{s}\n')


                    if (resrg[0]):
                        s = f"timeout {tm}s python3.8 -u /home/nina/workspace/{desktop}/isle/isle.py -c b  {resrg[2]}  -vv {filename} > {res_filename}.{resrg[3]}.{resrg[1]}.{timetag}res "
                        the_file.write(f'{s}\n')


                    #s = f"python3.8 ../examples/fm.py   -vv {filename} > {res_filename}.fm.res "
                    #the_file.write(f'{s}\n')

                else:
                    filename1 = filename.replace("mse21_complete_unwt", "mse21_unwt_results")
                    if (or_tools):
                        filename1 = filename.replace("mse21_complete_unwt", "mse21_unwt_ortools")
                        try:
                            os.mkdir("/home/nina/workspace/data/mse21_unwt_ortools/")
                        except:
                            pass                    
                    filename2 = filename.replace("mse21_complete_unwt", "mse21_complete_unwt_unzip")
                    #print(filename1)
                    #print(filename2)

                    try:
                        os.mkdir(filename1)
                    except:
                        pass
                    try:
                        os.mkdir(filename2)
                    except:
                        pass


if (process_run):
    # rc2comp = [True, "rc2comp"]

    maxhs = [True, "maxhs"]
    rc2comp = [True, "rc2comp"]
    res_v0  = [True, "maxres", "--circuitinject=0", "v0"]
    res_v1 = [True, "maxres", "--circuitinject=1", "v1"]
    res_v2 = [True, "maxres", "--circuitinject=2", "v2"]
    res_v3 = [True, "maxres", "--circuitinject=2", "v3"]
    res_v4 = [True, "maxres", "--circuitinject=2", "v3"]

    # resrg  = [True, "resrg",  "", "v0"]


    to = [3600]#, 3600]#, 3600*3]
    for tm in to:

        results_rc2comp = {}
        results_maxsatcomp = {}
        results_cashwmaxsat = {}
        results_eva = {}
        results_resrg = {}
        results_res_v0 = {}            
        results_res_v1 = {}    
        results_res_v2 = {}    
        results_res_v3 = {}
        results_res_v4 = {}
        results_res_v5 = {}
        results_res_v6 = {}
        results_res_v7 = {}                

        known = []
        
        dummy_init =  [-1, tm, -1, -1]
        timetag = ""
        if (tm > 3601):
            timetag = str(tm) + "."
        all_files = [] 
        for filename in glob.iglob(root_dir + '**/**', recursive=True):
                    dummy = copy.deepcopy(dummy_init)
                    #print (filename)

                    if(os.path.isfile(filename)):
                        if (filename in known):
                            continue
                    
                        flag = False
                        for gs in unsolved:
                            #print(gs, filename)
                            if (filename.find(gs) != -1):
                                # print ("---", filename)
                                # exit()       
                                flag = True
                        if (flag):
                            continue
                                

                        known.append(filename)

                        res_filename = filename.replace("mse21_complete_unwt", "mse21_unwt_results")
                        #res_filename_1 =  filename.replace("mse21_complete_unwt", "mse21_complete_unwt_unzip")
                        file_name_clean = (res_filename.split("/"))[-1]
                        file_name = res_filename[-80:]
                        dummy.append(file_name_clean[:80])
                        all_files.append([file_name,file_name_clean[:80]])

                        #print(res_filename, file_name)
                        #exit()
                        #print(dummy)
                        if (rc2[0]):
                            s = f"{res_filename}.{rc2[1]}.{timetag}res"
                            assert(path.isfile(s))
                        if (rc2comp[0]):
                            s = f"{res_filename}.{rc2comp[1]}.{timetag}res"
                            s = s.replace("mse21_unwt_results", "mse21_unwt_results_g4_rc2_many_mrs")
			    #"mse21_unwt_results_g4_rc2_many_mrs")#"mse21_unwt_results_back")#
                            #print(s)
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
                            #print("maxhsmaxhsmaxhsmaxhs")
                            res_filename_maxhs = res_filename.replace("mse21_unwt_results", "mse21_unwt_results_no_min")
                            res =  copy.deepcopy(dummy)
                            results_maxsatcomp[file_name] = res                        

                            s = f"{res_filename_maxhs}.{maxhs[1]}.{timetag}res"
                            # print("---",s)
                            # exit()
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

                        if (res_v0[0]):
                            results_res_v0 = process_instance(res_filename, res_v0, timetag, dummy, file_name, results_res_v0)  
                        if (res_v1[0]):
                            results_res_v1 = process_instance(res_filename, res_v1, timetag, dummy, file_name, results_res_v1)  
                        if (res_v2[0]):
                            results_res_v2 = process_instance(res_filename, res_v2, timetag, dummy, file_name, results_res_v2)  
                        if (res_v3[0]):
                            results_res_v3 = process_instance(res_filename, res_v3, timetag, dummy, file_name, results_res_v3)
                        if (res_v4[0]):
                            results_res_v4 = process_instance(res_filename, res_v4, timetag, dummy, file_name, results_res_v4)                     
                        if (res_v5[0]):
                            results_res_v5 = process_instance(res_filename, res_v5, timetag, dummy, file_name, results_res_v5)
                        if (res_v6[0]):
                            results_res_v6 = process_instance(res_filename, res_v6, timetag, dummy, file_name, results_res_v6)
                        if (res_v7[0]):
                            results_res_v7 = process_instance(res_filename, res_v7, timetag, dummy, file_name, results_res_v7)


                        # if (res_v4[0]):
                        #     s = f"{res_filename}.{res_v4[3]}.{res_v4[1]}.{timetag}res"
                        #     #s = f"{res_filename}.{res[1]}.res"
                        #     res = copy.deepcopy(dummy)
                        #     results_res_v4[file_name] = res
                            
                        #     #s = f"{res_filename}.{res[1]}.res"
                        #     if not (path.isfile(s)):
                        #         results_res_v4[file_name] = copy.deepcopy(dummy)
                        #     else:
                        #         file = open(s, "r")
                        #         for line in file:
                        #             if "o " ==  line[:2]:
                        #                 opt = int(line[2:])
                        #                 res[0] = opt
                        #             f = "c oracle time:"
                        #             if  f ==  line[:len(f)]:
                        #                 time = float(line[len(f):])
                        #                 res[1] = time
                        #             f = "c cost:"
                        #             if  f ==  line[:len(f)]:
                        #                 r  = (line[len(f):]).split(";")[0]
                        #                 #print(r)
                        #                 res[2] = int(r)

                        #     if len(res) == 0:
                        #         results_res_v4[file_name] = copy.deepcopy(dummy)
                        #     else:
                        #         results_res_v4[file_name] = res   


                        # if (res_v5[0]):
                        #     s = f"{res_filename}.{res_v5[3]}.{res_v5[1]}.{timetag}res"
                        #     #s = f"{res_filename}.{res[1]}.res"
                        #     res = copy.deepcopy(dummy)
                        #     results_res_v5[file_name] = res
                            
                        #     #s = f"{res_filename}.{res[1]}.res"
                        #     if not (path.isfile(s)):
                        #         results_res_v5[file_name] = copy.deepcopy(dummy)
                        #     else:
                        #         file = open(s, "r")
    
                        #         for line in file:
                        #             if "Exp" ==  line[:3]:
                        #                 r = line.split()
                        #                 r = r[-2].replace(",","") 
                        #                 time = float(r)
                        #                 res[1] = time
                        #             f = "Best"
                        #             #print(line)
                        #             if  f ==  line[:4]:
                        #                 r = line.split()
                        #                 r = r[2].replace(",","")                                    
                        #                 if r != "-":
                        #                     opt = float(r)
                        #                     res[0] = int(opt)
                        #                     r = r[4].replace(",","")                                     
                        #                     opt = float(r)                             
                        #                     res[2] = int(opt)

                        #     if len(res) == 0:
                        #         results_res_v5[file_name] = copy.deepcopy(dummy)
                        #     else:
                        #         results_res_v5[file_name] = res   

            #print(results_res_v4.items())

        #exit()
        opt = "opt"
        lb = "lb"
        ub = "ub"
        with open(f'results.{timetag}txt', 'w') as the_file:
            h_eva = f" {opt:<5}/{lb:<5} {eva[1]:<10} "
            h_rc2comp = f"{opt:<5}/{lb:<5}   {rc2comp[1]:<10}"
            h_maxhs = f"{opt:<5}/{lb:<5}/{ub:<5}   {maxhs[1]:<10}"
            h_cashwmaxsat = f"{opt:<10}   {cashwmaxsat[1]:<12}"
            h_resrg = f"{opt:<5}/{lb:<5}  {resrg[1]:<10} "
            h_res_v0 = f"{opt:<5}/{lb:<5}  {res_v0[1]:<10} "
            h_res_v1 = f"{opt:<5}/{lb:<5}  {res_v1[1]:<10} "
            h_res_v2 = f"{opt:<5}/{lb:<5}  {res_v2[1]:<10} "
            h_res_v3 = f"{opt:<5}/{lb:<5}  {res_v3[1]:<10} "
            h_res_v4 = f"{opt:<5}/{lb:<5}  {res_v4[1]:<10} "
            h_res_v5 = f"{opt:<5}/{lb:<5}  {res_v5[1]:<10} "
            h_res_v6 = f"{opt:<5}/{lb:<5}  {res_v6[1]:<10} "
            h_res_v7 = f"{opt:<5}/{lb:<5}  {res_v7[1]:<10} "
            #s = f"     {f:<80}  {h_rc2comp} {h_maxhs} {h_res_v0} {h_res_v1}  {h_res_v2}   {h_res_v3}"
            #s = f"     {f:<80}  {h_rc2comp}  {h_res_v4}"
            s = f"     {' ':<80}  {h_rc2comp} {h_maxhs}  {h_res_v0} {h_res_v1}  {h_res_v2}  {h_res_v3} {h_res_v4}   "#{h_res_v5}  {h_res_v6}  {h_res_v7}"
            print(s)
            the_file.write(f'{s}\n')

            for fls in all_files:
                f = fls[0]
                #print(f)
                file_name  = fls[1]
                gs_pref = " "
                for gs in solved_gurobi:
                    if (gs.find(file_name)!= -1):
                        gs_pref = "^"
                #exit()

                #print(results_rc2comp[f])
                #print(results_maxsatcomp[f])
                #print(results_cashwmaxsat[f])
                #print(results_res[f])
                #print(results_eva[f])
                
                try:
                    if (results_rc2comp[f][0] >  -1) and  (results_res_v1[f][0] > -1):
                        assert(results_rc2comp[f][0] == results_res_v1[f][0])
                    # if (results_resrg[f][0] >  -1) and  (results_res_v4[f][0] > -1):
                    #     assert(results_resrg[f][0] == results_res_v4[f][0])
                                            
                    # if (cashwmaxsat[0]):                
                    #     if (results_cashwmaxsat[f][0] >  -1) and  (results_maxsatcomp[f][0] > -1):
                    #         assert(results_cashwmaxsat[f][0] == results_maxsatcomp[f][0])
                    # if (results_res[f][0] >  -1) and  (results_maxsatcomp[f][0] > -1):
                    #     assert(results_res[f][0] == results_maxsatcomp[f][0])
                    # if (results_res[f][0] >  -1) and  (results_rc2comp[f][0] > -1):
                    #     assert(results_res[f][0] == results_rc2comp[f][0])
                except:
                    print("*********check results")
                pref = gs_pref
                if (results_res_v2[f][0] > -1) and results_rc2comp[f][0] == -1:
                    pref =pref + "**"
                elif (results_res_v2[f][0] == -1) and results_rc2comp[f][0] > -1:
                    pref = pref + "~~"
                else:
                    pref = pref+  "  "


                if (results_res_v2[f][0] > -1) and results_maxsatcomp[f][0] == -1:
                    pref =pref + "**"
                elif (results_res_v2[f][0] == -1) and results_maxsatcomp[f][0] > -1:
                    pref = pref + "++"
                else:
                    pref = pref+  "  "



                # if (results_res_v0[f][0] > -1) and results_maxsatcomp[f][0] == -1:
                #     pref =pref + "**"
                # elif (results_res_v0[f][0] == -1) and results_maxsatcomp[f][0] > -1:
                #     pref = pref + "^^"
                # else:
                #     pref = pref+  "  "


                try:
                    s_resrg = f"{results_resrg[f][0]:<5}/{results_resrg[f][2]:<5} {results_resrg[f][1]:<10}"
                except:
                    pass
                                
                try:
                    s_res_v0 = f"{results_res_v0[f][0]:<5}/{results_res_v0[f][2]:<5} {results_res_v0[f][1]:<10}"
                except:
                    pass

                try:
                    s_res_v1 = f"{results_res_v1[f][0]:<5}/{results_res_v1[f][2]:<5} {results_res_v1[f][1]:<10}"
                except:
                    pass

                try:
                    s_res_v2 = f"{results_res_v2[f][0]:<5}/{results_res_v2[f][2]:<5} {results_res_v2[f][1]:<10}"
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
                    s_res_v6 = f"{results_res_v6[f][0]:<5}/{results_res_v6[f][2]:<5} {results_res_v6[f][1]:<10}"
                except:
                    s_res_v6= f"{0:<5}/{0:<5} {0:<10}"
                    pass

                try:
                    s_res_v7 = f"{results_res_v7[f][0]:<5}/{results_res_v7[f][2]:<5} {results_res_v7[f][1]:<10}"
                except:
                    s_res_v7= f"{0:<5}/{0:<5} {0:<10}"
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




                #s = f"{pref} {f:<80}  {s_rc2comp} {s_maxhs} {s_res_v0} {s_res_v1}  {s_res_v2}  {s_res_v3}"
                s = f"{pref} {file_name:<80} {s_rc2comp}  {s_maxhs}  {s_res_v0}{s_res_v1}  {s_res_v2}    {s_res_v3} {s_res_v4} " #  {s_res_v5}   {s_res_v6}  {s_res_v7}"
                #s = f"{pref} {f:<80}  {s_rc2comp}  {s_res_v4}"

                print(s)
                the_file.write(f'{s}\n')
