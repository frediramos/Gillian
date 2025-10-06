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
    echo "Usage: $0 [-logg | -lift | -loglift] <file>"
    exit 1
fi

TARGET="$2"
if [ -z "$TARGET" ]; then
    echo "Error: <file> argument is required"
    exit 1
fi

# Backup
cp "$FILE" "$FILE.bak"

# Detect sed flavor (GNU vs BSD)
if sed --version >/dev/null 2>&1; then
    SED_INLINE=(-i)
else
    SED_INLINE=(-i "")
fi

sed -E "${SED_INLINE[@]}" \
    "s/^(module Legacy_symbolic *= *)[^.[:space:]]+(\.M)/\1${REPLACEMENT}\2/" \
    "$FILE"

eval "dune exec -- gillian-js wpst ${TARGET}"

mv "$FILE.bak" "$FILE"
