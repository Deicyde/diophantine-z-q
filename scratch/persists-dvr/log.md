# persists-dvr results log

Base: wip/r6-nf 0bc2446d.

## Consumers of `semistablePersistsSHcp` at the base (VERIFIED, grep)
- Only reader: `HDec.HSyn.ss1_ss3_of14NF` (ZInQKernel/OneProof/H/TailZ26.lean L200-205), term
  `GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t) ...`.
- All other occurrences are bundle declarations / copies (TailZ23 L693, TailZ25-29, TailZ33-34).
- `r.sga3_VIB_3_10`, `r.sga7_IX_3_3` are fields of `OpenResearchLeaves14` (TailZ23 L660, L662);
  `t.geomConnOfRationalPoint` of `OpenTextbookLeaves10` (used at TailZ23 L786).

## Plan (refined from triage2)
- No field change of `κ̄` needed: `ReductGlue.isSemistable_bcDVR_iff` (TailZ14 L1299) moves semistability of `𝒩` to
  `bcDVR hO 𝒩` given algebraic residue extension; prove that for finite K'/K (scaling argument).
- Core lemma over O': `U ⊆ (𝒩 ×_O O')_{κ̄'}` semi-abelian lands in `(W ×_O O')_{κ̄'}` (range = preimage of `idCompSet`),
  then compose with `j_{κ̄'}`; same `U, B, π, e`. No torus transport, no GeomConn for the fibre step.

## Build notes
- Copied build tree is stale (oleans 11-15 05:46, before r6-nf; NeronDVR.olean missing): first build rebuilds.

## Compile outcomes
- 11-15 23:3x: scratch/persists-dvr/Core.lean compiles (VERIFIED). `#print axioms`:
  `semistablePersistsDVR_of_printed`, `ss1_ss3_of_printedNF`, `semistablePersistsSHcp_of_SH`:
  [propext, Classical.choice, Quot.sound].
- `lake build ZInQKernel.Contrib.OneProof.PersistsDVR` succeeds (VERIFIED; only warning: deprecated `if_pos`).
- Finding: `ReductB.SemistablePersistsSHcp` is a specialization of `SemistablePersistsDVR`, so the field is
  discharged outright (`semistablePersistsSHcp_of_SH`); autofold applies, no consumer reroute needed.
- GeomConnOfRationalPoint is used only inside the chain's `idCompSubgroup_of`, `idCompBaseChangeDVR_of`,
  `identityComponentBaseChangeDVRRange_of`; the fibre step needs no field change (no torus transport).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PersistsDVR`
  succeeds (12987 jobs); frozenTarget axioms standard at the base (VERIFIED).
- `#discharges` (scratch/persists-dvr/discharges.txt): `OpenResearchLeaves21.semistablePersistsSHcp` discharged by
  `GapPersists.semistablePersistsSHcp_of_SH` (assumes SGA3_VIB_3_10, SGA7_IX_3_3_SH,
  NeronBaseChangeStrictHenselization, GeomConnOfRationalPoint) and by `semistablePersistsSHcp_of_printed`
  (assumes SGA3_VIB_3_10, SGA7_IX_3_3, GeomConnOfRationalPoint); standard axioms (VERIFIED).
- `autofold.py scratch/persists-dvr/autofold.json --dry-run`: exit 0, strict 45/10 on 55 -> 44/10 on 54, strictest
  44/11 -> 43/11. Its module (line 1 stripped, scratch/persists-dvr/FoldCheck.lean) compiles;
  `sixContactMin_of_open29` standard axioms (VERIFIED).
- scratch/persists-dvr/axioms.txt: #check of the four exported theorems and #print axioms of all six (VERIFIED).
