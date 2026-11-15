# composite-out log

## 2026-11-15 06:20 start
- Base: origin/main 43513d87 + merge origin/wip/qmrec-printed (a05c57ef, contains shimura-split2) + merge
  origin/wip/dcy3-used (36240662). Merges clean (VERIFIED, git).

## Findings (reading)
- `shimuraFamilyAb` needs a holomorphic map `ℍ → Y(ℂ)` (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens
  open, regular functions pull back to analytic functions). None of MainTheoremCM, HomLatticeCorr,
  uniformizationLeafAll, gagaMorphism, the X6 leaves, R1fpPropsAb states any dependence of a point of Y on τ:
  they speak of single objects / algebraic morphisms. VERIFIED by reading the definitions (TailZ35 bundle,
  ShimuraSplit2, QMRecPrinted, TailZ16 R1fpPropsAb). So (b) needs an analytic leaf (SPECULATIVE judgement that
  no Lean route avoids one; it is the content of Shimura MT I, complex part).
- `Y3Connected` (dcy3-used's proof) reads the openness clause of `IsHolFamily` (step 1, `tind`): also analytic.
- shimura-split2's `ShimuraHolFamilyAb`/`ShimuraHolModAll` give a holomorphic family whose object is ℂ²/Λ_τ as a
  QM PAIR only (level structure unspecified, may jump with τ). With an unknown level the dcy3 argument does not
  go through directly (the B^×_+-relation becomes `F(x) = F(x ε_{γτ} γ ε_τ⁻¹)` with unknown ε's).
- Plan: leaf `ShimuraHolFamilyL3` = ShimuraHolFamilyAb with the level structure fixed (`MIsAt P τ g₀` for one
  `g₀ ∈ 𝒪̂^×`, all τ). Then: two families A_τ = y_τ, B_τ = y_τ ≫ e_c (c ∈ 𝒪^× from R1heckeProps, c ≡ (1+i+j)⁻¹
  mod 3); every ℂ-point is A or B (ComplexUnifL3 + dcy3 decomp3 + DCRelTransport + UnifDetermines); reciprocity
  at √2+i (QMReciprocityL3 ⇐ MainTheoremCM) sends A_z to B_z; clopen indicator constant.

## 06:45 build tree
- Copied ~/dzq-wt/p1-quot3/.lake/build and lean/.lake/build (p1-quot3 = same shared sources + dcy3-used; only
  extra Contrib modules differ, VERIFIED git diff). `lake build ZInQKernel.Contrib.OneProof.QMRecPrinted
  ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used`: built ShimuraSplit2 (88 s), QMRecPrinted (14 s), rest
  replayed; "Build completed successfully (12232 jobs)" (VERIFIED).

## 06:55 CompositeOut.lean compiles (VERIFIED)
- `ZInQKernel/Contrib/OneProof/CompositeOut.lean` (namespace CompositeOut), imports QMRecPrinted and
  DeligneComponentsY3Used. `lake env lean`: 0 errors, ~7 s; output scratch/composite-out/compile1.txt.
- New leaf `CompositeOut.ShimuraHolFamilyL3` (∃ fine witness, holomorphic y_τ, ∃ g₀ ∈ 𝒪̂^×, ∀ τ, object MIsAt τ g₀).
- Proved, axioms [propext, Classical.choice, Quot.sound]:
  - `y3ConnectedAb_of_L3 : ShimuraHolFamilyL3 → MainTheoremCM → UniformizationLeafAll → GAGAMorphism →
     MumfordTorsionAlgClosed → MumfordGroupLaw → DCY3Used.Y3ConnectedAb`
  - `y3Connected_of_L3` (chain form HDec.TSHecke.Y3Connected)
  - `shimuraFamilyAb_of_L3 : ShimuraHolFamilyL3 → ShimuraFamilyAb`
  - `rayClassCMAb_of_L3 : ShimuraHolFamilyL3 → MainTheoremCM → textbook ×3 → RayClassCMAb`
  - `compositeUses_of_L3` (the three together)
- Glue proved on the way: `mIsAt_rightMul` (rightMul u: T(τ,g) ↦ T(τ,g u⁻¹)), `dcRel_K3`, `exists_unitO`
  (unit of 𝒪 ≡ g mod 3), `family_one` (normalize g₀ to 1 via a Hecke automorphism), `h4_K3`, `connected_of_family`.

## 07:30 level-free version compiles (VERIFIED)
- py/classes.py (VERIFIED, computed): (𝒪/3𝒪)^× has 72 classes; mulCoordR associative on them; class of
  c = ofInt(1,1,-1,0) has order 8, class of ω⁻¹ = ofInt(1,0,-1,0) order 6; the squares of the conjugates of ω̄⁻¹
  are 4 classes of order 3 (nList); for each of them every class is n^{e1}(c n c^7)^{e2} c^k (tab2, 288 entries).
- scratch/composite-out/Tables.lean: inv3_spec, nList_spec, tab2_spec by `decide`, 13 s total (VERIFIED).
- CompositeOut.lean §7-§8: `connected_of_holFamily` (family known only as QM pairs, level free) and
  `y3ConnectedAb_of_hol : ShimuraHolFamilyAb → MainTheoremCM → textbook ×3 → MumfordGroupLaw → Y3ConnectedAb`,
  `y3Connected_of_hol`, `y3Connected_of_modAll` (ShimuraHolModAll + deligneComponentsX6PrintedAb witness),
  `compositeUses_of_hol` (rayClassCMAb ∧ shimuraFamilyAb ∧ Y3Connected). All [propext, Classical.choice,
  Quot.sound]; compile ~15 s (compile2.txt).
- Relations used: classes (K₃), reciprocity at √2+i (h ≡ c⁻¹ mod 3), elliptic point i√3 of ω = (1+j)/2
  (dcRel_fix with eigenvalue (1+i√3)/2). Conjugators = levels of the family at the two points (unknown, global
  units by `levelUnit`); the decide tables cover every conjugator.
- Consequence: the new leaf ShimuraHolFamilyL3 is NOT needed; shimura-split2's leaf (a consequence of the
  composite, `shimuraHolFamilyAb_of_composite`) and qmrec-printed's MainTheoremCM suffice for all three uses.

## 08:00 contributor-kit checks (VERIFIED)
- Restructured CompositeOut.lean: level-free route only, no new leaf (the L3 variant is kept as
  scratch/composite-out/CompositeOutWithL3.lean, namespace CompositeOutL3, compiles, 0 errors).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.CompositeOut`:
  "Build completed successfully (12998 jobs)".
- `#discharges` (Discharges-output.txt): "63 open hypotheses, 2215 theorems checked, 7 discharge one"; none by
  CompositeOut (expected: the composite field itself is not proved; its three uses are, as in dcy3-used).
- BypassFold.lean (on top of dcy3-used's dry run): OpenResearchLeaves23 = 22 − shimuraMainThmIDeligneY3AbU +
  mainTheoremCM + shimuraHolModAll; openResearchLeaves20_of_23; y3Connected := CompositeOut.y3Connected_of_modAll;
  sixContactMin_of_open31 and frozenTarget_compositeOut: [propext, Classical.choice, Quot.sound].
