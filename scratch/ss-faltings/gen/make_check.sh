#!/bin/sh
# ss-faltings: BypassCheck.lean = BypassFold.lean + the closure check (new top vs old top) + #print axioms of the
# new theorems of SSFaltings.lean / SSFaltingsGR9.lean. Usage (repository root): sh scratch/ss-faltings/gen/make_check.sh [NEWTOP OLDTOP NEWR]
set -e
D=scratch/ss-faltings
NEWTOP=${1:-sixContactMin_of_open77sf}
OLDTOP=${2:-sixContactMin_of_open76}
cat $D/BypassFold.lean > $D/BypassCheck.lean
NEWR=${3:-OpenResearchLeaves58SF}
sed -e "s/@NEWTOP@/$NEWTOP/; s/@OLDTOP@/$OLDTOP/" $D/closure_check_tail.lean >> $D/BypassCheck.lean
sed -e "s/@NEWTOP@/$NEWTOP/; s/@OLDTOP@/$OLDTOP/; s/@NEWR@/$NEWR/" $D/dead_probe_tail.lean >> $D/BypassCheck.lean
for n in faltingsSemistableHeightBC_of_ss2 semistableReductionThm_of_IF exists_three_or_five_isUnit \
  semistableReductionThmIF_of_raynaud stableFaltingsHeight_eq_of_semistableF stableFaltingsHeight_eq_of_isStableFaltingsHeightF \
  isStableFaltingsHeight_uniqueF exists_semistable_neronF isStableFaltingsHeight_iffF stableFaltingsHeight_ne_botF \
  stableHeightFinite_ofF r21_of_leavesF r18_of_leavesF r22_of_upperF r19_of_leavesF r20Lower_of_leavesF \
  r21_of_grBostF "r21_of_grBostF'"; do
  echo "#print axioms ZInQ.SSFaltings.$n" >> $D/BypassCheck.lean
done
echo "#print axioms HDec.HSyn.sixContactMin_of_open76_sf" >> $D/BypassCheck.lean
