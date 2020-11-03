#!/bin/bash
unzip kissat-master.zip
unzip sml-parse-comb-master.zip
mlton encode_problem.mlb
mlton decode_model.mlb
