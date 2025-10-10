#!/bin/bash

# ANSI color codes
GREEN="\033[0;32m"
RED="\033[0;31m"
RESET="\033[0m"

TMP="/tmp/gillian_output.log"
LOGS="logs"

# Collect all tests and binaries
tests=(tests/*.js)
execs=("-js" "-js-logg" "-js-loglift")

# Total number of runs
total=$(( ${#tests[@]} * ${#execs[@]} ))

# Counters
current=0
passed=0
failed=0

run_test() {
    file=$1
    execs=("-js" "-js-logg" "-js-loglift")

    for bin in "${execs[@]}"; do
        ((current++))
        filename=$(basename "$file")
        cmd="dune exec -- gillian${bin} wpst ${file} -l disabled"
        log_file="${LOGS}/${filename}-gillian${bin}.log"

        eval "$cmd" > $TMP 2>&1
        ret=$?

        if [ $ret -eq 0 ]; then
            ((passed++))
            echo -e "[$current/$total] ${GREEN} Success: $file (gilian$bin)${RESET}"
            rm -f $TMP
        else
            ((failed++))
            mkdir -p $LOGS
            mv $TMP "$log_file"
            echo -e "[$current/$total] ${RED} Failed ($ret): $file (gilian$bin) -> $log_file${RESET}"
        fi
    done
}

eval $(opam env)

for test in tests/*.js; do
    run_test "$test"
done

# Summary
echo
echo -e "${GREEN}Passed: $passed${RESET} | ${RED}Failed: $failed${RESET} | Total: ${total})"
echo