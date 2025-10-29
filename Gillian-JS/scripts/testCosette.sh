#!/bin/bash

if [[ -z "${GITHUB_ACTIONS}" ]]; then
  eval $(opam env)
fi

filename="$1"
bin="$2"
cmds="$3"

echo $filename

stats() {
  local filename="$1"
  local bin="$2"
  local cmds="$3"
  local name="$(basename "$filename" .js)"
  local results="results-${bin}-${name}"

  mkdir -p $results
  "$bin" "wpst" "$filename" $cmds > "out.log" 2>&1
  outs=("stats.json" "file.log" "out.log")

  # Failing to move output files helps identifying bugs
  for f in "${outs[@]}"; do
    mv "$f" "${results}/" 
  done
}

if [[ "$cmds" == *"--stats"* ]]; then
  stats "$filename" "$bin" "$cmds"
else
  time "$bin" "wpst" "$filename" $cmds
fi