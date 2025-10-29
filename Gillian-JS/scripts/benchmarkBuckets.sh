#!/bin/bash

# -------------------------------
# Default values
# -------------------------------
TS=$(date +"%d-%m-%Y--%H-%M-%S")
DEFAULT_FOLDER="buckets-benchmarks-$TS"

# -------------------------------
# Parse command-line options
# -------------------------------
FOLDER=""
while getopts "f:" opt; do
    case $opt in
        f) FOLDER="$OPTARG" ;;
        *) echo "Usage: $0 [-f folder]"; exit 1 ;;
    esac
done

# Fallback to default folder if not provided
FOLDER="${FOLDER:-$DEFAULT_FOLDER}"
mkdir -p "$FOLDER"

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
# Binaries and test folders
# -------------------------------
bins=("gillian-js" "gillian-js-logg" "gillian-js-loglift")

folders=(
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
# Run benchmarks
# -------------------------------
for bin in "${bins[@]}"; do
    echo "Running Buckets.js tests with bin = '${bin}'"
    for folder_name in "${folders[@]}"; do
        ./testBucketsFolder.sh "$folder_name" "$bin" "--stats -l disabled"
        
        # Store results
        mv results-* "$FOLDER"
    done
done

# -------------------------------
# Save nohup output if exists
# -------------------------------
if [[ -f "nohup.out" ]]; then
    mv nohup.out "$FOLDER/"
fi

# -------------------------------
# Zip results
# -------------------------------
zip -r "${FOLDER}.zip" "$FOLDER"

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
echo "[#] Total time ($script_name): ${hours}:${minutes}:${seconds} (hh:mm:ss) [#]"
