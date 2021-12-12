#!/bin/sh
# usage: ./interface file.v
#   returns the code of file.v without the proofs
#   (all code from "Proof" to "Qed" is stripped)

grep -v '^Proof.*Qed' $* | sed -e '/^Proof/,/^Qed/d'
