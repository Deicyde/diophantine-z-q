# phisurj log

Base wip/leaf-fold33b 0e3c31258; `git merge origin/main`: already up to date (2026-11-16 17:40).

## Findings (reading)
- Field: `PicDict.MumfordPhiSurjectiveAC` (PicDictionary.lean:1564), in `HDec.HSyn.OpenAddedLeaves20`
  (TailZ47.lean:29), other fields picRepresentableAbVar, picZeroAbVar, weilPairingMumford. VERIFIED (read).
- Consumers of the field (VERIFIED, grep): TailZ45:123, TailZ46:104, HomFreeFiniteAlgClosedReroute.lean:2082,
  all through `PicFix.phiAmpleIsogeny_of_printed _ l.mumfordPhiSurjectiveAC : T09Pic.PhiAmpleIsogeny`.
- The statement quantifies over Mumford's Pic⁰ = translation-invariant classes (`AC.IsTI`), not over points of
  the identity component `B` of the Picard scheme. So it contains (a) "every TI class is a point of B"
  (the converse of the proved `picZeroPtsTranslInv_of_leaves`), besides (b) "λ_L : A → B is onto".
- No proved theorem in the tree gives (a), dim Pic⁰ = g, #A[n] = n^{2g}, or torsion density (code survey).
- `AvSplit.MumfordTorsionAlgClosed` (TailQ.lean:1257, A(k)[n] ≅ (ZMod n)^{2g}) is an open textbook leaf
  (`OpenTextbookLeaves15.mumfordTorsionAlgClosed`) and is proved on origin/proof/picard-fibres-20261116
  (`ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`, not merged here). VERIFIED (git show).

## Lean results (all VERIFIED: compiled on this host, `lake env lean`, LEAN_NUM_THREADS=8)
- Build tree copied from the leaf-fold33b worktree (same commit 0e3c31258), `.lake/build` and `lean/.lake/build`.
- `scratch/phisurj/DimSurj.lean`: `PhiSurj.surjective_of_dim_le` — a locally quasi-finite closed morphism
  `f : X → Y`, `Y` irreducible, `dim X = a`, `dim Y ≤ a`, is surjective. Compiles.
- `scratch/phisurj/PhiSurj.lean`: `exists_torsAddEquiv` (A[n] ≃+ (ZMod n)^{2 dim A} for A over any field, from
  `AvSplit.MumfordTorsionAlgClosed` at A_K̄ through `pts` and `dim_baseChange_scheme`), `card_le_of_perfect`
  (#B[n] ≤ n^m if A[n] ≅ (ZMod n)^m and the right kernel of e : A[n] × B[n] → μ_n is trivial),
  `dim_le_of_weil`, `phiAmpleIsogeny_of_weil : WeilPairingMumford → MumfordTorsionAlgClosed → PhiAmpleIsogeny`.
  `#print axioms` = [propext, Classical.choice, Quot.sound].
- `ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyWeil.lean` (same content): `lake build
  ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyWeil` → "Build completed successfully (12814 jobs)".
- `scratch/phisurj/FoldTailZ49.lean` (hand fold): `OpenAddedLeaves21` = OpenAddedLeaves20 without
  `mumfordPhiSurjectiveAC`; `sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves15)
  (l : OpenAddedLeaves21)` through `sixContactMin_of_open37_hf`, the field's three readers fed by
  `phiAmpleIsogeny_of_weil l.weilPairingMumford t.mumfordTorsionAlgClosed`. Axioms standard (34 s).
- `scratch/phisurj/FrozenTargetDryRun.lean`: Main's `frozenTarget` body with `open42` and `OpenAddedLeaves21`
  (`frozenTarget_phisurj`), axioms standard.
- `scratch/phisurj/Discharges.lean` → `discharges.txt`: "#discharges: 43 open hypotheses, 8602 theorems checked,
  48 discharge one"; no line for `PhiSurj.*` (expected: `PhiAmpleIsogeny` is not an open hypothesis type; the
  field `MumfordPhiSurjectiveAC` is rerouted, not filled).
- (a)-reduction (VERIFIED, compiled; now also in the contribution file, rebuilt 18:19):
  `PhiSurj.TIClassesInPicZeroAC` (def, Prop: over k = k̄ every translation-invariant class is `kClass` of a
  k-point of B), `mumfordPhiSurjectiveAC_of_ti (ha h1 h2 h4 hT) : MumfordPhiSurjectiveAC`,
  `tiClassesInPicZeroAC_of_phiSurjective (h8) : TIClassesInPicZeroAC`; helpers `kClass_injective` (Kleiman 9.2.5
  at Spec k̄, as pic-dict's L5), `exists_lift_kpt`, `kpt_comp_phiL`. Axioms standard.
- `#discharges` rerun: "43 open hypotheses, 8612 theorems checked, 49 discharge one"; new line
  `DISCHARGES [OpenAddedLeaves20.mumfordPhiSurjectiveAC] by PhiSurj.mumfordPhiSurjectiveAC_of_ti still assumes:
  [PhiSurj.TIClassesInPicZeroAC, T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar, T09Pic.WeilPairingMumford,
  AvSplit.MumfordTorsionAlgClosed]`.
- `autofold-ti.json` (alternative: fill the field from (a)) --dry-run: "strict count: 13/20 on 33 -> 12/21 on 33;
  strictest 13/20 -> 12/21" and refuses (GLUE rise; (a) flagged pending reading). Not recommended.
- Reroute fold count (computed from kinds.tsv: the row `mumfordPhiSurjectiveAC` is LEAF/LEAF): H 13/20 on 33 ->
  12/20 on 32.
- By-products (VERIFIED: compiled; `ZInQKernel/Contrib/OneProof/MumfordSquareMulN.lean`, lake build ok,
  axioms standard, `scratch/phisurj/axioms-byproducts.txt`): `PhiSurj.mumfordSquareAC_of_open :
  PicRepresentableAbVar → PicZeroAbVar → PicDict.MumfordSquareAC` (Mumford §6 Cor. 4) and
  `PhiSurj.mumfordMulNPicZeroAC_of_open : … → PicDict.MumfordMulNPicZeroAC` (Mumford §8 (iv)), via
  `mumfordBundle_eq_one_of_isTI` (Λ(c) = 1 for translation-invariant c) and `hom_ext_kpt`. Not on the fold's
  route; they are two of the four Mumford displays weil-proof's reduction of `weilPairingMumford` still assumed.

## Phase 2: dropping the Weil-pairing leaf (VERIFIED, compiled)
- Merged origin/wip/weil-proof (clean, adds WeilFormula.lean, WeilFormulaTheta.lean, docs, scratch); both build.
- `ZInQKernel/Contrib/OneProof/PhiSurjDescent.lean`: `PhiSurj.Desc.nonempty_iso_of_invariant` — fpqc descent of a
  `tᵢ`-invariant trivialization `𝒪 ≅ m^*M` along `m` when the sections `x ↦ (x, tᵢ x)` cover `X ×_{m,X,m} X` by open
  immersions (vendored `nonempty_iso_of_toDescentData_iso`, Mathlib `DescentData'`). lake build ok.
- `ZInQKernel/Contrib/OneProof/PhiAmpleIsogenyOpen.lean` (lake build ok, 12861 jobs):
  `AVDesc.mul_props` ([n] étale, surjective, proper), `mul_cover`, `sec_isOpenImmersion`, `sec_cover`
  (Jacobson + k-points), `formula_nondeg_right` (right kernel of Mumford's formula pairing trivial: pic-dict's
  `MumfordWeilNondegAC`, second conjunct, in the form "formula ≡ 1 ⇒ c = 1"), `card_isDT_le`
  (#{c TI, cⁿ = 1} ≤ n^{2 dim X}), `dim_le_of_open`, `phiAmpleIsogeny_of_open : PicRepresentableAbVar →
  PicZeroAbVar → MumfordTorsionAlgClosed → PhiAmpleIsogeny`, `mumfordPhiSurjectiveAC_of_ti_open`.
  All standard axioms (`scratch/phisurj/axioms.txt`).
- Fold updated (`FoldTailZ49.lean`, `FrozenTargetDryRun.lean`): `phiAmpleIsogeny_of_open l.picRepresentableAbVar
  l.picZeroAbVar t.mumfordTorsionAlgClosed`; both compile, standard axioms.
- `#discharges` rerun: "43 open hypotheses, 8799 theorems checked, 56 discharge one"; `mumfordPhiSurjectiveAC_of_ti_open`
  still assumes [TIClassesInPicZeroAC, PicRepresentableAbVar, PicZeroAbVar, MumfordTorsionAlgClosed].

## Phase 3: `weilPairingMumford` discharged too (VERIFIED, compiled)
- `ZInQKernel/Contrib/OneProof/WeilPairingMumfordOpen.lean` (lake build ok, 12862 jobs):
  `dim_le_of_lqf`, `dim_ge_of_open`, `exists_zmod_mu_injective`, `exists_char_ne_zero`, `left_kernel_of_open`
  (left kernel of a pairing A[n] × B[n] → μ_n with trivial right kernel is trivial, by counting),
  `weilNondegRight_of_open` (pic-dict coordinates), `weilPairingMumford_of_open : PicRepresentableAbVar →
  PicZeroAbVar → MumfordTorsionAlgClosed → WeilPairingMumford` (copy of pic-dict's `weilPairingMumford_of_printed`
  with the leaves replaced by theorems and the perfectness clause reproved; the only use of
  `MumfordPhiSurjective` there was for the left kernel).
- `#discharges`: "43 open hypotheses, 8809 theorems checked, 57 discharge one";
  `DISCHARGES [OpenAddedLeaves20.weilPairingMumford] by PhiSurj.weilPairingMumford_of_open still assumes:
  [T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar, AvSplit.MumfordTorsionAlgClosed]`.
- `autofold-weil.json` --dry-run: "strict count: 13/20 on 33 -> 13/19 on 32; strictest 13/20 -> 13/19"; printed module
  (`FoldDryRunWeil.lean`) compiles to `sixContactMin_of_open42`, standard axioms.
- Combined hand fold (`FoldTailZ49.lean`: OpenAddedLeaves21 = {picRepresentableAbVar, picZeroAbVar}) and
  `FrozenTargetDryRun.lean` compile, standard axioms. Count (kinds.tsv rows LEAF/LEAF + GLUE/GLUE removed):
  13/20 on 33 -> 12/19 on 31.
- `lake build +Main +Discharges +WeilPairingMumfordOpen +PhiAmpleIsogenyWeil +MumfordSquareMulN`: Build completed.
