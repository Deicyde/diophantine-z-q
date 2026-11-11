#!/bin/bash
# usage: extract.sh file  -> prints the sec:pole section (to the next \section)
awk '/\\section\{The pole predicate/{p=1} p&&/\\section\{Multiplication/{exit} p' "$1"
