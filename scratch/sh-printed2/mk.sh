#!/bin/bash
# Assemble ShPrinted2.lean = Head (import of the kernel's TailZ19) + sh-route's Top, CA1, CA2, CA3, Final
# (verbatim copies of origin/wip/sh-route:scratch/sh-route/*.lean, import lines dropped) + this task's parts.
cd "$(dirname "$0")"
{ cat Head.lean; echo;
  for f in SR_Top SR_CA1 SR_CA2 SR_CA3 SR_Final "$@"; do grep -v '^import' $f.lean; echo; done; } > ShPrinted2.lean
