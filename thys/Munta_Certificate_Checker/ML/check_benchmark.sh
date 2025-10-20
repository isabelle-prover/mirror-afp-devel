#!/bin/bash

command_to_run="${@:1}"  # command to execute

# Run command and capture output
command_output=$($command_to_run 2>&1)

if echo $command_output | grep "Certificate was accepted"; then
  echo "Accepted";
  exit 0
else
  echo "Rejected";
  exit 1
fi
