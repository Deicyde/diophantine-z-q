#!/bin/bash
# CONTRIB-BUILD measurement: lake build of every ZInQKernel/Contrib/*.lean module (by name), under /usr/bin/time -v,
# with the cgroup's memory.current sampled every 2 s (aggregate peak over all processes of this scope).
# Usage: bash scratch/fold-ds966/contrib_build.sh LABEL   (from the repo root); writes /tmp/fds-cb-LABEL.{log,time,mem}
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
L=$1
G=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
MODS=$(git ls-files 'ZInQKernel/Contrib/*.lean' | sed 's#[.]lean$##; s#/#.#g')
echo "modules: $(echo "$MODS" | wc -l)" > /tmp/fds-cb-$L.mem
rm -f /tmp/fds-cb-$L.done /tmp/fds-cb-$L.max
base=$(cat $G/memory.current)
echo "cgroup memory.current at start: $base" >> /tmp/fds-cb-$L.mem
( mx=0; while [ ! -f /tmp/fds-cb-$L.done ]; do c=$(cat $G/memory.current); [ $c -gt $mx ] && mx=$c && echo $mx > /tmp/fds-cb-$L.max; sleep 2; done ) &
/usr/bin/time -v -o /tmp/fds-cb-$L.time lake build $MODS > /tmp/fds-cb-$L.log 2>&1
echo "exit $?" >> /tmp/fds-cb-$L.mem
touch /tmp/fds-cb-$L.done; sleep 3
echo "cgroup memory.current peak (2 s samples): $(cat /tmp/fds-cb-$L.max)" >> /tmp/fds-cb-$L.mem
