#!/bin/bash

declare -a specs=("RA" "OV" "RC" "PR")
mkdir -p tmp

for spec in "${specs[@]}"; do
    mkdir -p outputs/benchmarks/$spec
    mkdir -p outputs/benchmarks/$spec-not

    for input in benchmarks/$spec/*; do
        echo "==============================="
        echo $input
        ./run_universal.sh $input tmp/ > outputs/$input.out
        echo "==============================="
    done 
    
    for input in benchmarks/$spec-not/*; do
        echo "==============================="
        echo $input
        ./run_existential.sh $input tmp/ > outputs/$input.out
        echo "==============================="
    done
done