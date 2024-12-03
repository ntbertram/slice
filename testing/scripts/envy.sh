#!/bin/bash
# USAGE: bash envy.sh [FLAGS] [ABBREVIATIONS] [PROTOCOL]
# Evalues the envy-freeness of [PROTOCOL] using [ABBREVIATIONS} (filenames separated by commas)  and reports runtime
# DOES NOT WORK WELL WITH WMH4

# FLAGS:
# -n : Do not reduce constraints to linear real arithmetic
# -a [NUM] : Specifies the number of times to run, and reports the average runtime (for verification speed evaluation)


SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

cd $SCRIPT_DIR/../../

a_flag='1'
n_flag=''
while getopts 'na:' flag; do
  case "${flag}" in
    a) a_flag="${OPTARG}" ;;
    n) n_flag='true' ;;
  esac
done
shift $(($OPTIND -1))

arg="envy"
if [[ $n_flag == "true" ]]; then
    arg="envy_no_red"
fi

abbs=$1 #string contaning all abbrev filenames, separated by commas
proto=$2 #protocol filename

{ time -p OCAMLRUNPARAM=b dune exec exec/solver.exe $abbs $proto "paths"; }  2>/dev/null

touch /dev/shm/slicecompiletime
rm /dev/shm/slicecompiletime
touch /dev/shm/slicecompiletime

for ((i = 0; i < a_flag; i++)); do
    { time -p OCAMLRUNPARAM=b dune exec exec/solver.exe $abbs $proto $arg; } >/dev/null 2>>/dev/shm/slicecompiletime
done
compileTime=$(
    cat /dev/shm/slicecompiletime | awk '
        /real/ { time = time + $2; nt++ }
        END {
            printf("%.2f\n", time/nt);
            }'
)
#compileTime=$(cat /dev/shm/slicecompiletime | grep -Eo '[0-9]+.[0-9]+' | head -n 1)
touch /dev/shm/slicesolvetime
rm /dev/shm/slicesolvetime
touch /dev/shm/slicesolvetime
for ((i = 0; i < a_flag; i++)); do
    { time -p z3 -smt2 "solve.smt2"; } >/dev/shm/sliceres 2>>/dev/shm/slicesolvetime
done

solveTime=$(
    cat /dev/shm/slicesolvetime | awk '
        /real/ { time = time + $2; nt++ }
        END {
            printf("%.2f\n", time/nt);
            }'
)
#solveTime=$(cat /dev/shm/slicesolvetime | grep -Eo '[0-9]+.[0-9]+' | head -n 1)

cat /dev/shm/sliceres
echo -e "Compile time \t $compileTime"
echo -e "Solve time \t $solveTime"
