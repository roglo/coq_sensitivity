#!/bin/bash

latexmk -pdf -halt-on-error "$1" > latex.log 2>&1

if [ $? -ne 0 ]; then
    grep -A 10 "Runaway argument?" latex.log
    make clean >/dev/null 2>&1
    exit 1
else
    exit 0
fi
