#!/bin/bash

folder="$1"
bin="$2"
cmds="$3"

./testCosetteFolder.sh "Examples/Cosette/Buckets/${folder}" "$bin" "$cmds"
sleep 1
