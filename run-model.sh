#!/bin/bash

FILE="Gillian-JS/lib/Semantics/semantics.ml"
REPLACEMENT=""

if [ "$1" == "-logg" ]; then
    REPLACEMENT="LoggingMemory"
elif [ "$1" == "-lift" ]; then
    REPLACEMENT="JSILSMemory"
elif [ "$1" == "-loglift" ]; then
    REPLACEMENT="LogLiftingMemory"
else
    echo "Usage: $0 [-logg | -lift | -loglift] <command>"
    exit 1
fi

TARGET="$2"
if [ -z "$TARGET" ]; then
    echo "Error: <file> argument is required"
    exit 1
fi

# Backup
cp "$FILE" "$FILE.bak"

# Replace the part before .M in 'module Legacy_symbolic = <Something>.M'
sed -E -i "s/^(module Legacy_symbolic *= *)[^.[:space:]]+(\.M)/\1${REPLACEMENT}\2/" "$FILE"

# Run command if provided
eval "dune exec -- gillian-js wpst ${TARGET}"

# Restore original file
mv "$FILE.bak" "$FILE"
