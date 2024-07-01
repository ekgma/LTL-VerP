

declare -a solvers=("mathsat" "z3")
declare -a inv1=("aspic" "noaspic")
declare -a inv2=("sting" "nosting")
declare -a varType=("Int" "Real")

for((degree=1;degree<=2;degree++)) do 
    for solver in "${solvers[@]}"; do
        for aspic in "${inv1[@]}"; do
            for sting in "${inv2[@]}"; do
                for type in "${varType[@]}"; do
                    timeout 1800 java -jar -Xss1024M universal.jar $1 $solver $2 solvers $type $degree 0 $sting $aspic 2>&1
                    x=$?;
                    if [ $x -eq 3 ]
                    then
                        >&2 echo "The input program satisfies the universal Buchi specification.";
                        >&2 echo "Tool Config: $solver $type $degree $sting $aspic"
                        exit
                    fi;
                done
            done
        done 
    done 
done
