#!/bin/bash

case $1 in
    l) l="CAVA-Libs";;
    ltl) l="CAVA-LTL";;
    *) l="HOL";;
esac

cd ..

isabelle_process -e 'use_thy "CAVA_Code";' -q $l

