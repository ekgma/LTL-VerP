#!/bin/bash

declare -a specs=("RA" "OV" "RC" "PR")
mkdir -p tmp

for spec in "${specs[@]}"; do
    mkdir -p outputs/benchmarks/$spec
    mkdir -p outputs/benchmarks/$spec-not

    while read p; do 
        b=($p)
        input="benchmarks/$spec/${b[0]}.t2"
        echo "==============================="
        echo $input
        ./run_universal_best.sh $input tmp/ > outputs/$input.out
        echo "==============================="
    done < "best_config/$spec.txt"

    while read p; do 
        b=($p)
        input="benchmarks/$spec-not/${b[0]}.t2"
        echo "==============================="
        echo $input 
        ./run_existential_best.sh $input tmp/ > outputs/$input.out
        echo "==============================="
    done < "best_config/$spec-not.txt"
done