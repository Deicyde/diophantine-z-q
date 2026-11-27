#!/bin/bash
# usage: lead-poll.sh [FILE...]  — wait up to 580 s until the inbox changes or any FILE exists; print what happened.
I=~/dzq-runs/lead-inbox.md; m0=$(stat -c %Y $I)
for i in $(seq 58); do
  [ "$(stat -c %Y $I)" != "$m0" ] && { echo "INBOX CHANGED; last entry: $(grep -E '^## ' $I | tail -1)"; exit 0; }
  for f in "$@"; do [ -e "$f" ] && { echo "EXISTS $f"; exit 0; }; done
  sleep 10
done
echo "timeout; last inbox entry: $(grep -E '^## ' $I | tail -1)"
