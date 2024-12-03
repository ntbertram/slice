#!/bin/bash

# USAGE: bash type_check.sh [PROTOCOL]
# Type checks [PROTOCOL]


SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

abbrv="$SCRIPT_DIR/../../examples/abb.prtcl"
cd $SCRIPT_DIR/../../

out=$(OCAMLRUNPARAM=b dune exec exec/type_checker.exe $abbrv $1 2>&1)
if [[ $? != 0 ]]; then
    echo "$out" | grep --ignore-case "error"
else
    echo "$out"
fi
