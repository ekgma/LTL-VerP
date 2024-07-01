from genericpath import isfile
import math
import os
import sys 



def get_result(bench,formula):
    min_time = 1800000
    last_time = -1 
    result = "UNKNOWN"
    if not os.path.exists(f"outputs/benchmarks/{formula}/{bench}.t2.out"):
        return (result,"-")
    with open(f"outputs/benchmarks/{formula}/{bench}.t2.out","r") as fr:
        lines = fr.readlines()
        for line in lines:
            if "BUCHI proved" in line: 
                result = "Yes"
            if "total time used" in line and result=="Yes": 
                last_time = int(line.split()[-1])
                break
    if result=="UNKNOWN":
        return (result,"-")
    return (result,str(last_time))






benchmarks = []
with open("all_linear.txt","r") as fr:
    benchmarks=[x[:-1] for x in fr.readlines()]
with open("all_poly.txt","r") as fr:
    benchmarks=benchmarks+[x[:-1] for x in fr.readlines()]

folders = ["RA","RA-not","OV","OV-not","RC","RC-not","PR","PR-not"]
print("benchmark, RA, time, RA-not, time, OV, time, OV-not, time, RC, time, RC-not, time, PR, time, PR-not, time")
for bench in benchmarks:
    row = bench
    for formula in folders:
        (result,time) = get_result(bench,formula)
        row=row+", "+result+", "+time
    print(row)