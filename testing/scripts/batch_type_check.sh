#!/bin/bash


# USAGE: bash batch_type_check.sh [FOLDER]
# Type checks all protocols in [FOLDER] (not recursively)


SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

tables () {
    echo "Protocol name,Result"
    for file in $1*; do
        if [[ $file == *.prtcl ]]; then
            is_typed="Other error"
            err=$(bash $SCRIPT_DIR/type_check.sh $file | grep --ignore-case "error") #| sed -E 's/(Compile|solve|time|Z3|CVC5|\t| )*//' | sed -z 's/\n/,/g;s/,$/\n/')
            syntax_err=$(echo $err | grep --extended-regexp "(syntax|character)")
            type_err=$(echo $err | grep "Types")
            if [[ $type_err != "" ]]; then
                is_typed="Type error"
            fi
            if [[ $syntax_err != "" ]]; then
                is_typed="Syntax error"
            fi
            if [[ $err == "" ]]; then
                is_typed="Well-typed"
            fi
            name=$(echo "$file" | sed -E 's/(^(.*?)\/|.prtcl)//g')
            echo "${name},${is_typed}"
        fi
    done
}

tables $1 | column -t -s','
