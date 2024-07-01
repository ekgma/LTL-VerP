
declare -a varType=("Int" "Real")

for type in "${varType[@]}"; do
    timeout 600 java -jar -Xss1024M universal.jar $1 mathsat $2 solvers $type 1 0 nosting aspic 2>&1
    x=$?;
    if [ $x -eq 3 ]
    then
        >&2 echo "The input program satisfies the universal Buchi specification.";
        >&2 echo "Tool Config: mathsat $type 1 nosting aspic"
        exit
    fi;
done
