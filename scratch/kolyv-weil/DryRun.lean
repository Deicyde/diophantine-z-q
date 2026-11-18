import ZInQKernel.Contrib.OneProof.KolyvWeil.PoleCompleteness
import ZInQKernel.OneProof.Discharges

/-!
A scoped fixture for the headline's pole argument: its inputs are the exact four pole binders
from `Main.lean`. The project checker looks up `ZInQ.OneProof.frozenTarget` by name; define that
name locally for this run, with the pole-completeness conclusion. This isolates the changed
consumer from the unchanged H assembly. This file must not be imported into the real headline.
-/

open ZInQ.Manuscript in
theorem ZInQ.OneProof.frozenTarget
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hB : PoleS12.BCDTThmA) (hK : PoleS12.KolyvaginThm1) : PoleCompleteness :=
  PoleS12.poleCompleteness_of_restrictedConverseGenuine_final hRC h54 hB hK

open ZInQ.Manuscript in
theorem ZInQ.OneProof.poleArgumentKolyvWeilDryRun
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (h54 : PoleS12.Lemma54)
    (hB6 : KolyvWeil.BCDTThmA6) (hKPrint : KolyvWeil.KolyvaginThm1Print) : PoleCompleteness :=
  KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print hRC h54 hB6 hKPrint

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.modules.all
      (fun m => !(`ZInQKernel.Contrib.TYZGenus).isPrefixOf m.module) do
    throwError "unexpected TYZGenus import"

#print axioms ZInQ.Manuscript.KolyvWeil.IsConductor.unique
#print axioms ZInQ.Manuscript.KolyvWeil.BCDTThmA6
#print axioms ZInQ.Manuscript.KolyvWeil.KolyvaginThm1Print
#print axioms ZInQ.Manuscript.KolyvWeil.kolyvaginThm1_of_prints
#print axioms ZInQ.Manuscript.KolyvWeil.kolyvaginRankOne_of_prints
#print axioms ZInQ.OneProof.poleArgumentKolyvWeilDryRun
#discharges
