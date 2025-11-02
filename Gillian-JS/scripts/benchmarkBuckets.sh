#!/bin/bash

# -------------------------------
# Default values
# -------------------------------
TS=$(date +"%d-%m-%Y--%H-%M-%S")
DEFAULT_FOLDER="buckets-$TS"

# -------------------------------
# Binaries and test struct folders
# -------------------------------
bins=("gillian-js" "gillian-js-logg" "gillian-js-loglift")

all_structs=(
    arrays
    bag
    bstree
    dictionary
    heap
    linkedlist
    multidictionary
    queue
    priorityqueue
    set
    stack
)

# -------------------------------
# Parse command-line options
# -------------------------------
while [[ $# -gt 0 ]]; do
    case "$1" in
        -o|--out)
            FOLDER="$2"
            shift 2
            ;;
        -s|--struct)
            STRUCT="$2"
            shift 2
            ;;
        *)
            echo "Usage: $0 [-o folder] [-s struct]"
            exit 1
            ;;
    esac
done


# Fallback to default folder if --out not provided
FOLDER="${FOLDER:-$DEFAULT_FOLDER}"
mkdir -p "$FOLDER"

# Fallback to all struct folders if --struct not provided
if [[ -z "$STRUCT" ]]; then
    STRUCTS=("${all_structs[@]}")
else
    STRUCTS=("$STRUCT")
fi


# -------------------------------
# Setup environment
# -------------------------------
echo "Benchmarking object models in Buckets.js"
start_time=$SECONDS

echo "Results folder: $FOLDER"
eval "$(opam env)"
(
    cd ..
    dune build
    dune install
)

# -------------------------------
# Run benchmarks
# -------------------------------
for bin in "${bins[@]}"; do
    echo "Running Buckets.js tests with bin = '${bin}'"
    for folder_name in "${STRUCTS[@]}"; do
        ./testBucketsFolder.sh "$folder_name" "$bin" "--stats -l disabled"
        
        # Store results
        mv results-* "$FOLDER"
    done
done

# -------------------------------
# Generate tables
# -------------------------------
./tabulate-results.py "$FOLDER" -sj -o "$FOLDER"

# -------------------------------
# Save nohup output if exists
# -------------------------------
if [[ -f "nohup.out" ]]; then
    mv nohup.out "$FOLDER/"
fi

# -------------------------------
# Zip results
# -------------------------------
zip -rq "${FOLDER}.zip" "$FOLDER"

# -------------------------------
# Print elapsed time
# -------------------------------
end_time=$SECONDS
duration=$((end_time - start_time))

hours=$((duration / 3600))
minutes=$(((duration % 3600) / 60))
seconds=$((duration % 60))

script_name=$(basename "$0")
echo
echo "Total time ($script_name): ${hours}:${minutes}:${seconds}"
