#!/bin/bash
# usage: balance.sh BUILD WEIGHTS.json E NCOORD
set -e
B=$1; W=$2; E=$3; N=$4
cp $W $B/weights.json
python3 -B tools/balance_weights.py $B $B/weights.json > $B/balance.log
python3 -B tools/check_diagonal_weights.py $B --expected-exponent $E --expected-coordinates $N --weights $B/weights.json --report $B/diagonal-check-weights.json | python3 -c "import json,sys;d=json.load(sys.stdin);print('diagcheck',d['status'],len(d['maximumAbsoluteCoefficient']))"
python3 -B tools/verify_diag.py $B
python3 -c "import json;d=json.load(open('$B/balanced/summary.json'));print({k:d[k] for k in ['coordinates','residuals','monomials','integerContent','inputFourthPowerCoefficient','maximumCoefficientDigits','maximumCoefficientBits','scaledCoordinates']})"
