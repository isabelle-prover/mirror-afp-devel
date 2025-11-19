#!/bin/bash

# Arguments
expected_states=$1  # expected number of states
expected_property=$2  # e.g. "is satisfied" or "is not satisfied"
command_to_run="${@:3}"  # command to execute

# Run command and capture output
command_output=$($command_to_run 2>&1)
last_three_lines=$(echo "$command_output" | tail -n 3)

expected_states="# explored states: $expected_states"

# Check if output matches expected format
if echo "$last_three_lines" | grep -Fxq "$expected_states" && echo "$last_three_lines" | grep -Fxq "$expected_property"; then
    echo "Match found!"
    exit 0
else
    echo "No match!"
    echo "Actual output:"
    echo "$last_three_lines"
    exit 1
fi

