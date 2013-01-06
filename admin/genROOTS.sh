#!/bin/bash
cd $(hg root)/thys
ls | grep -v "ROOTS\|LICENSE" > ROOTS
