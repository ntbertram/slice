#!/bin/bash
# USAGE: bash batch_envy.sh [FLAGS] [FILE]
# Evalutes the envy-freeness of all protocols in [FILE] and reports the runtime of the verification
# DOES NOT WORK WELL WITH WMH4

# FLAGS:
# -n : Do not reduce constraints to linear real arithmetic
# -a [NUM] : Specifies the number of times to run, and reports the average runtime (for verification speed evaluation)


SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

cd $SCRIPT_DIR/../../

abbrv="$SCRIPT_DIR/../../examples/abb.prtcl"

a_flag='1'
n_flag=''
while getopts 'na:' flag; do
  case "${flag}" in
    a) a_flag="${OPTARG}" ;;
    n) n_flag='true' ;;
  esac
done
shift $(($OPTIND -1))


arg=""
if [[ $n_flag == "true" ]]; then
    arg="-n"
fi

loc=$1

tables () {
    echo "Protocol name,Paths,Program size (Lines),Constraint size (Lines),Result,Compile (s),Z3 (s)"
    for file in $loc/*; do
        if [[ $file == *.prtcl ]]; then
            program_line_number=$(printf "%s" "$(< $file)" | awk 'END { print NR }')

            # echo $file
            new_file=$(basename "$file" .prtcl)
            output=$(bash $SCRIPT_DIR/envy.sh -a $a_flag $arg $abbrv $file)
            num_paths=$(echo "$output" | grep -Eo '[0-9]+' | head -n 1)
            status=$(echo "$output" | grep -Eo "unsat|sat" | head -n 1)
            compile_time=$(echo "$output" | grep "Compile" | grep -Eo '[0-9]+(.[0-9]+)?') #| head -n 1)
            solve_time=$(echo "$output" | grep "Solve" | grep -Eo '[0-9]+(.[0-9]+)?') #| tail -n 1

            constraint_line_number=$(awk 'END { print NR }' solve.smt2)
            new_file=$(basename "$file" .prtcl)
            echo "${new_file},$num_paths,$program_line_number,$constraint_line_number,$status,$compile_time,$solve_time"
        fi
    done
}

tables | sort --numeric-sort -t ',' -k 2 | column -t -s','
