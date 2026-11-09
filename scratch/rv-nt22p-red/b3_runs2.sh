#!/bin/bash
PY=/tmp/rvred-venv/bin/python
while pgrep -f b3_runs.sh >/dev/null; do sleep 10; done
$PY b3_ap.py -69 480480 2547011473
$PY b3_ap.py -70 13160467320 2924927297
$PY b3_ap.py -70 13160467320 2924927297 random S0only
