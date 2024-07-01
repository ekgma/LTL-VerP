# Artifact of submission #117 Sound and Complete Witnesses for Template-based Verification of LTL Properties on Polynomial Programs

## Introduction

This repository contains the artifact of the paper titled "Sound and Complete Witnesses for Template-based Verification of LTL Properties on Polynomial Programs" accepted at FM 2024. 

The task of verifying an LTL formula on a program can be reduced to verifying a Büchi specification on the product transition system. This tool takes a non-deterministic transition system together with a Büchi specification as input and based on user preferences tries to either (i) prove the existence of a run in the program that satisfies the Büchi condition or (ii) demonstrate that every run of the program satisfies the Büchi condition. 

NOTE: The experiments presented in the paper use three SMT solvers: [Barcelogic](https://www.cs.upc.edu/~oliveras/bclt-main.html), [MathSAT5](https://mathsat.fbk.eu/) and [Z3](https://www.microsoft.com/en-us/research/project/z3-3/). However, due to license restrictions, we could not put Barcelogic in this repository. Without Barcelogic, the artifact will fail on a few benchmarks that were reported as solved in the paper. To solve the remaining benchmark, one needs to add Barcelogic's binary to the solvers folder manually. 

## Getting Started Guide - Running the Tool in Docker

In order to load and run the experiments in a docker container, the following commands should be executed: 

```
docker build -t artifact .
docker run -it artifact
```

Then, to build our tool run the following command in the docker terminal:
```
./build.sh
```

In order to reproduce the results in the paper, run the following commands:

```
./experiments.sh
```

This will run our tool on all the benchmarks provided in the `benchmarks` folder. However, this will run all the possible configurations of our tool which will take weeks to be finished. Therefore, we have gathared the list of benchmarks that can be solved by our strongest configuration (with linear templates and `mathsat` as solver). To run the tool on these benchmarks, simply run the following command:

```
./experiments_best_config.sh
```

In this command, as a speedup, we have further reduced the timeout of the tool to 10 minutes. This command terminated in less than 48 hours on our device. Note that this command will fail to prove a few of the benchmarks as (i) it only considers linear templates, (ii) it only uses `mathsat` for solving the SMT instances, and (iii) the timeout is reduced from 30 minutes to 10 minute. 

The outputs of the above commands will be stored in the `outputs` directory. The following command summarizes the results in CSV format:

```
python3 make_csv.py
```

## Building From Source

### Dependencies

The tool is written in Java and works well with Openjdk 11 on Linux machines (some of the dependencies are not available for Mac OS).

Our tool also makes use of [ASPIC](https://laure.gonnord.org/pro/aspic/aspic.html) which depends on `libmpfr4`. However, if your machine has `libmpfr6` you can create a symbolic link to it using the following command:

```
ln -s /usr/lib/x86_64-linux-gnu/libmpfr.so.6 /usr/lib/x86_64-linux-gnu/libmpfr.so.4
```

### Build

To build the tool simply run:

```
./build.sh
```

This will create two `jar` files: `existential.jar` and `universal.jar`. 

### Reproducing Experimental Results

To reproduce the complete exprimental results, run `./experiments.sh` and then `python3 make_csv.py`. The former runs all the experiments on input files provided in the `benchmarks` folder and writes the results in the `outputs` folder. The latter reads the contents of the `outputs` folder and summarizes them in CSV format. 

Alternatively, one can run `./experiments_best_config.sh` to run the expriments using the strongest configuration obtained in our experiments. Note that since we are not running all configurations and not using Barcelogic here, some examples will not be proved. Please see the [Getting Started Guide section](#getting-started-guide---running-the-tool-in-docker) above for more info. 

### Tool Reusability: Running the Tool on New Examples

To use the tool on a single program with a Büchi specification, run the following command: 

```
./run_existential.sh [input file] [tmp folder]
./run_universal.sh [input file] [tmp folder]
```
where `[tmp folder]` is a directory that the tool can use to store its temprorary files. 

The first command is for solving existential Büchi program analysis problem (EB-PA) and the second one is for universal Büchi program analysis (UB-PA). The above commands will run all the configurations of the tool on the given input program. To only run the *best config*, use the following commands:

```
./run_existential_best.sh [input file] [tmp folder]
./run_universal_best.sh [input file] [tmp folder]
```

### Tool Reusability: Transition Systems Syntax

The input syntax follows that of [T2](https://github.com/mmjb/T2) with several additional expressions:

- The set of Büchi states must be provided before the transitions in an expression as follows:
```
BUCHI: {[state], [state], ...};
```
- The pre-condition can be stated as follows: 
```
PRE: {[predicate]};
```

See the inputs provided in the `benchmarks` folder as examples. 

### Tool Reusability: LTL Analysis

In order to use our tool for analysis of LTL specification, one should take the product of the corresponding Büchi automaton and the input transition system. We provide a python script for producing the product. 

Given a Büchi automaton in `[BA]` and a transition system without Büchi specification in `[input]`, the following command saves the product transition system in `[output]`:

```
python3 mult.py [input] [BA] [output]
```

#### Syntax of Büchi Automatons

The Büchi automatons syntax also follows that of [T2](https://github.com/mmjb/T2) with the following additions:

- Büchi states of the automaton must be stated before the transitions as follows:
```
Buchi: [state] [state] [state];
```

- The $at(l)$ predicates which constraint the state at which the transition is enabled are presented by the following expression:
```
assume_line([state]);
```

- Similarly, $\neg at(l)$ predicates can be used as follows:
```
assume_not_line([state]);
```

- The transitions of the automaton cannot contain assignments.

See `example_ba.t2` as an example Büchi automaton presented in this syntax. 