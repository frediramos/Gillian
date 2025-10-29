#!/bin/bash

folder="$1"
bin="$2"
cmds="$3"

for filename in "${folder}"/*.js; do
    [ -f "$filename" ] || break
    echo "Running file : ${filename}"
    ./testCosette.sh "$filename" "$bin" "$cmds"
done