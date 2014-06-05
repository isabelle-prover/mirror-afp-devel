#!/bin/bash

case $1 in
    l) l="CAVA-Libs";;
    ltl) l="CAVA-LTL";;
    *) l="HOL";;
esac

cd ..

isabelle tty -l $l <<"EOF"
use_thy "CAVA_Code";
EOF
