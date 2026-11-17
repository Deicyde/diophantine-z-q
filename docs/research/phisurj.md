# phisurj: `mumfordPhiSurjectiveAC` removed (rerouted) and `weilPairingMumford` proved — −2, no new leaf; both from L1, L2 and the torsion leaf, with a Lean proof of Mumford §20 nondegeneracy

Task phisurj. Base wip/leaf-fold33b 0e3c31258 (`git merge origin/main`: already up to date); origin/wip/weil-proof
merged (clean, only adds files). Field `mumfordPhiSurjectiveAC : PicDict.MumfordPhiSurjectiveAC` of
`HDec.HSyn.OpenAddedLeaves20` (`TailZ47.lean:29`; statement `ZInQKernel/Contrib/OneProof/PicDictionary.lean:1564`,
Mumford §8 Thm 1 over `k = k̄`).

## 1. Result

**Two fields of `OpenAddedLeaves20` leave the open hypotheses, with no new leaf (H: `13/20 on 33 -> 12/19 on 31`):**

* `mumfordPhiSurjectiveAC` is **rerouted** (as homfree-noemb did for `homFreeFiniteAlgClosed`): its readers only
  need `PhiAmpleIsogeny`, now a theorem. The Prop `MumfordPhiSurjectiveAC` itself is not proved (§2).
* `weilPairingMumford` is **proved** (autofoldable; §1b):

  ```lean
  theorem PhiSurj.weilPairingMumford_of_open (h1 : T09Pic.PicRepresentableAbVar) (h2 : T09Pic.PicZeroAbVar)
      (hT : AvSplit.MumfordTorsionAlgClosed) : T09Pic.WeilPairingMumford
  ```

Details of the reroute:

* All three readers of the field (`TailZ45.lean:123`, `TailZ46.lean:104`, `HomFreeFiniteAlgClosedReroute.lean:2082`;
  VERIFIED by grep) use it only through `PicFix.phiAmpleIsogeny_of_printed l.mumfordKLFiniteSectionAC
  l.mumfordPhiSurjectiveAC : T09Pic.PhiAmpleIsogeny`.
* `T09Pic.PhiAmpleIsogeny` (`λ_L : A → Pic⁰` finite and surjective, every field, every ample `L`) is now a theorem
  from statements that are already open:

  ```lean
  theorem PhiSurj.phiAmpleIsogeny_of_open (h1 : T09Pic.PicRepresentableAbVar) (h2 : T09Pic.PicZeroAbVar)
      (hT : AvSplit.MumfordTorsionAlgClosed) : T09Pic.PhiAmpleIsogeny
  ```

  L1, L2 are fields of the same bundle `OpenAddedLeaves20`; `mumfordTorsionAlgClosed` (Mumford §4,
  `A(k)[n] ≅ (ℤ/n)^{2g}`) is a field of the textbook bundle `OpenTextbookLeaves15`, and is proved outright on
  origin/proof/picard-fibres-20261116 (`ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`; read, not
  merged or compiled here). `weilPairingMumford` is **not** used.
* The proof (§3) uses no cohomology: a dimension count, the torsion count, Mumford's Weil-pairing formula
  (weil-proof's `mumfordWeilPairingAC_proof`) and a **new Lean proof of the descent half of Mumford §20**
  (`PhiSurj.AVDesc.formula_nondeg_right`, fpqc descent along `[n]`).
* **Hand fold** `scratch/phisurj/FoldTailZ49.lean`: `OpenAddedLeaves21` (= `OpenAddedLeaves20` without
  `mumfordPhiSurjectiveAC` and `weilPairingMumford`) and
  `sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves21)`;
  `scratch/phisurj/FrozenTargetDryRun.lean` proves `ZInQ.FrozenTarget` from Main's hypotheses with `OpenAddedLeaves21`
  in place of `OpenAddedLeaves20`. Both compile with `[propext, Classical.choice, Quot.sound]`.

Count: the LEAF/LEAF row `mumfordPhiSurjectiveAC` (`docs/one-proof/kinds.tsv:31`) and the GLUE/GLUE row
`weilPairingMumford` leave; no row enters. On this base H goes from `13/20 on 33` to `12/19 on 31` (strict and
strictest). The `weilPairingMumford` part alone is an autofold (`scratch/phisurj/autofold-weil.json`, dry run
`13/20 on 33 -> 13/19 on 32`); the reroute part is computed from kinds.tsv (autofold cannot express a reroute).

## 1b. `weilPairingMumford` (VERIFIED: compiled, standard axioms)

File `ZInQKernel/Contrib/OneProof/WeilPairingMumfordOpen.lean` (imports `PhiAmpleIsogenyOpen`; `lake build` ok).
The proof is pic-dict's assembly `PicDict.weilPairingMumford_of_printed` (copied) with every input now a theorem:

| pic-dict input | now |
|---|---|
| `MumfordSquare` (§6 Cor. 4) | `mumfordSquare_of_ac (mumfordSquareAC_of_open h1 h2)` (this task) |
| `MumfordMulNPicZero` (§8 (iv)) | `mumfordMulNPicZero_of_ac (mumfordMulNPicZeroAC_of_open h1 h2)` (this task) |
| `MumfordWeilPairing` (§20) | weil-proof's `mumfordWeilPairingAC_proof` |
| `MumfordWeilAlt` (§23) | weil-proof's `mumfordWeilAltAC_proof` |
| `PhiAmpleIsogeny` | `phiAmpleIsogeny_of_open h1 h2 hT` (this task, §3) |
| `MumfordWeilNondeg`, right kernel | `weilNondegRight_of_open` from `AVDesc.formula_nondeg_right` (descent, §3) |
| `MumfordWeilNondeg`, left kernel, and `MumfordPhiSurjective` (used there only for the left kernel) | `left_kernel_of_open`: `y ↦ e(·, y)` embeds `B[n]` into `Hom(A[n], μ_n)`; `#B[n] = n^{2 dim B} = n^{2 dim A} ≥ #Hom(A[n], μ_n)` (torsion leaf; `dim A ≤ dim B` from the finite `λ_L`, `dim_le_of_lqf`); so the embedding is onto, and characters `(ℤ/n)^{2g} → μ_n` separate points (a primitive root, Mathlib's `HasEnoughRootsOfUnity`) |

`#discharges`: `DISCHARGES [OpenAddedLeaves20.weilPairingMumford] by PhiSurj.weilPairingMumford_of_open still
assumes: [T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar, AvSplit.MumfordTorsionAlgClosed]`, standard axioms.

By-products (VERIFIED, compiled, standard axioms; §6): the second conjunct (right kernel) of pic-dict's leaf
`MumfordWeilNondegAC` in the form "formula ≡ 1 ⇒ c = 1"; `MumfordSquareAC` (Mumford §6 Cor. 4) and
`MumfordMulNPicZeroAC` (§8 (iv)) from L1, L2; Mumford §8 Thm 1 from one named Prop (a) `TIClassesInPicZeroAC` plus
L1, L2 and the torsion leaf.

## 2. What `MumfordPhiSurjectiveAC` says, and the part that is out of reach

Over `k = k̄`, for `c₀` ample and `c` **translation-invariant** (`AC.IsTI`), `c = t_x^*c₀ ⊗ c₀⁻¹` for some `x`.
Mumford's `Pic⁰` here is the group of translation-invariant classes, not the identity component `B` of the Picard
scheme. So the Prop is the conjunction of

* **(a)** every translation-invariant class is a `k`-point of `B` (the converse of pic-dict's proved
  `picZeroPtsTranslInv_of_leaves`), and
* **(b)** `λ_L : A → B` is onto (the surjective half of `PhiAmpleIsogeny`): proved here (§3).

(a) is exactly what is missing (VERIFIED, compiled):

```lean
def PhiSurj.TIClassesInPicZeroAC : Prop   -- over k = k̄: every IsTI class c is kClass rep c = y ≫ j, y : X(k) → B
theorem PhiSurj.mumfordPhiSurjectiveAC_of_ti_open (ha : TIClassesInPicZeroAC) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (hT : AvSplit.MumfordTorsionAlgClosed) : MumfordPhiSurjectiveAC
theorem PhiSurj.tiClassesInPicZeroAC_of_phiSurjective (h8 : MumfordPhiSurjectiveAC) : TIClassesInPicZeroAC
```

(the first lifts `y` along the surjective `λ` to a `k`-point, `exists_lift_kpt`, and compares classes by Kleiman 9.2.5
at `Spec k̄`, `kClass_injective`, as pic-dict's L5; the second uses the proved `exists_isAmple_of_isAlgClosed`).

(a) says that a class with `φ_c = 0` has Néron–Severi class zero (`NS(A) → Hom(A, Â)` injective). For **torsion**
classes of order prime to the characteristic it now follows from this task's counts (`B[n] ↪ {c : IsTI, cⁿ = 1}`,
which has at most `n^{2g} = #B[n]` elements). For non-torsion classes the published proofs go through Mumford's
cohomological proof of §8 Thm 1 (vanishing of `H^*(A, M)` for nontrivial `M ∈ Pic⁰`, Künneth/Leray for
`m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*(L ⊗ M)⁻¹`) or Weil's algebraic equivalence (Lang, *Abelian varieties*, Ch. IV); neither is in
the tree (STANDARD; locators UNVERIFIED). Families built from translates of a translation-invariant `c` are constant,
so the tree's family arguments cannot move `c` into `B`. No reader needs (a).

## 3. The proof of `PhiAmpleIsogeny` (L1, L2, torsion leaf)

All VERIFIED (compiled; axioms standard, `scratch/phisurj/axioms.txt`). Notation: `A` over a field `K`, `rep` a
representation of `Pic_{A/K}`, `(B, j)` with `IsPicZero rep B j`, `L` ample, `λ : A → B` with `λ ≫ j = φ_L`.

1. **`λ` finite**: phi-ample's `finite_ker_pts` and pic-dict's `finiteOfFiniteKerPts`.
2. **Descent half of Mumford §20** (`AVDesc.formula_nondeg_right`): over `k = k̄`, `n` invertible, if
   `ψ : 𝒪 ≅ n^*M` has formula `t_x^*ψ ∘ ψ⁻¹ = 1` at every `x ∈ X[n](k)`, then `c = 1`.
   * `[n]` is étale, surjective, proper (weil-proof's argument), hence an fpqc covering.
   * The sections `y ↦ (y, y + x)` are open immersions (the tree's `isOpenImmersion_of_section`) and cover
     `X ×_{[n],X,[n]} X`: a closed point outside would be a `k`-point `(y₁, y₂)` with `n y₁ = n y₂` (Jacobson), which
     is the section at `x = y₂ − y₁`.
   * Generic descent (`Desc.nonempty_iso_of_invariant`): with Mathlib's `DescentData'` over the chosen pullback, the
     compatibility of `pOU ≫ ψ` is checked after pulling back along the sections, where it is the invariance of `ψ`
     (coherences `pOU_inv_comp`, `pullbackComp`, `mapComp'`); the vendored `nonempty_iso_of_toDescentData_iso` (fpqc
     descent of quasi-coherent modules is fully faithful) gives `M ≅ 𝒪`.
3. **`#{c ∈ Pic(X) translation-invariant, cⁿ = 1} ≤ n^{2 dim X}`** (`AVDesc.card_isDT_le`): trivializations exist
   (`n^*c = cⁿ`, `mumfordMulNPicZeroAC_of_open`, §6); `c ↦ ē_n(·, c)` lands in `Hom(X[n], μ_n)` (weil-proof's
   `mumfordWeilPairingAC_proof`: well defined, `μ_n`-valued, bimultiplicative) and is injective (equal characters
   give `ē_n(·, c c'⁻¹) ≡ 1`, then step 2); `X[n] ≅ (ℤ/n)^{2 dim X}` is the torsion leaf, transported to `k`-points.
4. **`dim B ≤ dim A`** (`dim_le_of_open`): for a prime `ℓ ∈ {2, 3}` invertible in `K`, `y ↦ M_y` embeds `B[ℓ]` into
   the translation-invariant classes of order dividing `ℓ` on `A_K̄` (pic-dict's `picClass_injective`,
   `picZeroPtsTranslInv_of_leaves`), so `ℓ^{2 dim B} = #B[ℓ] ≤ ℓ^{2 dim A_K̄} = ℓ^{2 dim A}` (torsion leaf on `B`,
   `dim_baseChange_scheme`).
5. **`λ` onto** (`surjective_of_dim_le`): a locally quasi-finite closed `f : X → Y`, `Y` irreducible,
   `dim Y ≤ dim X = a < ∞`, is surjective; otherwise `Z ↦ f(Z)` is strictly monotone on irreducible closed subsets
   (a strict specialization stays strict under a locally quasi-finite map, `ne_of_specializes_of_lqf`) with all
   `f(Z)` in the proper closed `f(X)`, so `a + 1 ≤ dim Y` (Mathlib `Order.krullDim_le_of_strictMono`,
   `Order.krullDim_WithTop`).

An earlier variant, `PhiSurj.phiAmpleIsogeny_of_weil (h4 : WeilPairingMumford) (hT)` (in `PhiAmpleIsogenyWeil.lean`),
replaces steps 2–3 by the right-kernel clause of `weilPairingMumford`; it is no longer needed.

## 4. Files (contributions; none imports `ZInQKernel.OneProof.Main`; no `sorry`; no build-time code)

| file | imports | content | `lake build` |
|---|---|---|---|
| `Contrib/OneProof/PhiAmpleIsogenyWeil.lean` | `MumfordKLFinite`, `AbVarBC.Mul`, `AbVarBC.Dim` | `surjective_of_dim_le`, torsion transport, `phiAmpleIsogeny_of_weil`, (a) and `mumfordPhiSurjectiveAC_of_ti` | ok (12814 jobs) |
| `Contrib/OneProof/PhiSurjDescent.lean` | `WeilFormula` (weil-proof), vendored descent | generic descent `Desc.nonempty_iso_of_invariant` | ok |
| `Contrib/OneProof/PhiAmpleIsogenyOpen.lean` (**the theorem for the fold**) | `PhiSurjDescent`, `WeilFormulaTheta`, `MumfordSquareMulN` | `formula_nondeg_right`, `card_isDT_le`, `dim_le_of_open`, `phiAmpleIsogeny_of_open`, `mumfordPhiSurjectiveAC_of_ti_open` | ok (12861 jobs) |
| `Contrib/OneProof/MumfordSquareMulN.lean` | `PhiAmpleIsogenyWeil` | `mumfordSquareAC_of_open`, `mumfordMulNPicZeroAC_of_open` | ok |
| `Contrib/OneProof/WeilPairingMumfordOpen.lean` (**the theorem for the `weilPairingMumford` fold**) | `PhiAmpleIsogenyOpen` | `left_kernel_of_open`, `weilNondegRight_of_open`, `weilPairingMumford_of_open` | ok (12862 jobs) |

Dependency: `WeilFormula.lean`, `WeilFormulaTheta.lean` are weil-proof's (merged into this branch); the fold needs
them on the integration branch.

## 5. Fold

* **`weilPairingMumford`: autofold** `scratch/phisurj/autofold-weil.json` (`proof`:
  `_root_.PhiSurj.weilPairingMumford_of_open {n}.picRepresentableAbVar {n}.picZeroAbVar {t}.mumfordTorsionAlgClosed`,
  no leaves). Dry run on this base: `strict count: 13/20 on 33 -> 13/19 on 32; strictest 13/20 -> 13/19`; the printed
  module (`scratch/phisurj/FoldDryRunWeil.lean`, line 1 stripped) compiles to `sixContactMin_of_open42`, standard
  axioms.
* **Both fields: hand fold** `scratch/phisurj/FoldTailZ49.lean` (recommended): `OpenAddedLeaves21 =
  {picRepresentableAbVar, picZeroAbVar}`; `openAddedLeaves18_of_OpenAddedLeaves21` fills `phiAmpleIsogeny` with
  `phiAmpleIsogeny_of_open` and `weilPairingMumford` with `weilPairingMumford_of_open`; compiles, standard axioms;
  `FrozenTargetDryRun.lean` likewise. Count `13/20 on 33 -> 12/19 on 31`.
* **`mumfordPhiSurjectiveAC` alone: not autofoldable**: autofold fills a field with a proof of the field's type, and `MumfordPhiSurjectiveAC` is not
  proved. `scratch/phisurj/autofold.json` records the reroute (empty `discharges`).
* The hand fold in detail (compiles against the built `TailZ48`): new module importing `TailZ48` and
  `WeilPairingMumfordOpen`; `OpenAddedLeaves21`; `openAddedLeaves18_of_OpenAddedLeaves21`
  (`phiAmpleIsogeny := PhiSurj.phiAmpleIsogeny_of_open n.picRepresentableAbVar n.picZeroAbVar
  t.mumfordTorsionAlgClosed`, `weilPairingMumford := PhiSurj.weilPairingMumford_of_open …`, `egaIV_8_10_5_xii` as in
  `TailZ45:120`); `openTextbookLeaves13HF_of_open15_21` (as `openTextbookLeaves13_of_OpenTextbookLeaves14_hf`, poincare
  from the same term); `sixContactMin_of_open42` through `sixContactMin_of_open37_hf`. Main's `frozenTarget` then takes
  `l : OpenAddedLeaves21` (`FrozenTargetDryRun.lean`). kinds.tsv/claims.tsv: drop the `mumfordPhiSurjectiveAC` and
  `weilPairingMumford` rows; no rows added.
* **Alternative, not recommended**: fill the field from (a) (`scratch/phisurj/autofold-ti.json`, written for the older
  `_of_ti`; dry run `13/20 on 33 -> 12/21 on 33`, refused since GLUE rises: (a) flagged pending reading).
  `#discharges` matches `PhiSurj.mumfordPhiSurjectiveAC_of_ti_open` (still assumes `[PhiSurj.TIClassesInPicZeroAC,
  T09Pic.PicRepresentableAbVar, T09Pic.PicZeroAbVar, AvSplit.MumfordTorsionAlgClosed]`). Rating of (a): printed form
  **no, pending reading** — Mumford's `Pic⁰` is by definition the translation-invariant classes; that they are the
  points of the identity component of the fppf Picard scheme is §8 Thm 1 with §13 and Kleiman §9.5, not one print.
  It is a consequence of the replaced leaf (`tiClassesInPicZeroAC_of_phiSurjective`), never stronger.
* `#discharges` (`scratch/phisurj/discharges.txt`): `43 open hypotheses, 8809 theorems checked, 57 discharge one`;
  the `PhiSurj` lines are `weilPairingMumford_of_open` (§1b) and the (a)-alternatives; `phiAmpleIsogeny_of_open` has
  no line (expected: it proves the readers' `PhiAmpleIsogeny`, no longer an open hypothesis type).

## 6. By-products (not needed for the count)

* `formula_nondeg_right` (the right-kernel conjunct of pic-dict's leaf `MumfordWeilNondegAC`, Mumford §20); the left
  kernel at the level of `weilPairingMumford` is `left_kernel_of_open` (§1b).
* `mumfordSquareAC_of_open` (Mumford §6 Cor. 4): `φ_c = λ_c ≫ j` with `λ_c` a homomorphism
  (`exists_hom_comp_eq_phiL`), `kClass` injective and multiplicative.
* `mumfordMulNPicZeroAC_of_open` (Mumford §8 (iv)): `λ_c = 0` for translation-invariant `c` (`hom_ext_kpt`), so `Λ(c)`
  is classified by the constant map and normalized, hence `Λ(c) = 1` (`Θ_inj`, as phi-ample); induct.
* These were three of the four Mumford displays weil-proof's reduction of `weilPairingMumford` assumed
  (`MumfordSquareAC`, `MumfordMulNPicZeroAC`, `MumfordWeilNondegAC` (half), `MumfordPhiSurjectiveAC`); no count on
  this base changes.

## 7. New leaves and their rating

None (recommended reroute). The alternative of §5 would add (a), rated printed form: no, pending reading.

## 8. What remains

* (a) `TIClassesInPicZeroAC` for non-torsion classes: no cohomology-free route found (§2). The field's statement
  stays unproved; its readers no longer need it.
* `mumfordTorsionAlgClosed` disappears as a textbook field once origin/proof/picard-fibres-20261116 lands; then
  `PhiAmpleIsogeny` rests on L1, L2 alone.
* `weilPairingMumford` is done (§1b). The AC-level statement `MumfordWeilNondegAC` (left conjunct) is not proved as
  stated; the K-level left kernel needed for `weilPairingMumford` is (`left_kernel_of_open`).

## 9. Scratch

`scratch/phisurj/`: development copies (`DimSurj.lean`, `PhiSurj.lean`, `TIReduction.lean`, `SquareAC.lean`,
`MulNAC.lean`, `Descent.lean`, `AVDescent.lean`), copies of the contributions (`PhiAmpleIsogenyWeil.lean.txt`,
`PhiAmpleIsogenyOpen.lean.txt`, `WeilPairingMumfordOpen.lean.txt`), `WeilOpen.lean`, `autofold-weil.json`,
`autofold-weil-dryrun.txt`, `FoldDryRunWeil.lean`, the fold (`FoldTailZ49.lean`, `FrozenTargetDryRun.lean`), `Discharges.lean`,
`discharges.txt`, `Axioms.lean`, `axioms.txt`, `AxiomsByproducts.lean`, `axioms-byproducts.txt`, `autofold.json`,
`autofold-ti.json`, `autofold-ti-dryrun.txt`, `log.md`.
