# g12-det: `G12Weight`, `DetTate`, `ResQFiniteIndex` (glue of g0-mod-galois)

Task g12-det, 2026-11-13. Lean: `scratch/g12-det/` (log: `scratch/g12-det/log.md`). The three
Props are copied verbatim from `scratch/g0-mod-galois/part_galois.lean` (`G12Weight`) and
`part_det.lean` (`DetTate`, `ResQFiniteIndex`), with what they depend on.

## 1. Result

| Prop | Status | Rests on |
|---|---|---|
| `ResQFiniteIndex` | **PROVED** | Mathlib only |
| `DetTate` | **PROVED from leaves** | weil-pairing's leaves `T09_SymmIsogenyExists` (T9 restated), `IsogenyQuasiInverse`, `DivisiblePoints`, and Objects' leaf `PkgI3.TateModuleFree` (T26) |
| `G12Weight` | **REDUCED** | GLUE `HTConj`; LEAVES `SenTwist` (Sen 1980), `FiniteImageHT` (Tate 1967, Ax–Sen–Tate); plus the leaves that `G12Weight` already takes (R13, R14, R15, T18, T19). `TwistExists` and `TwistConj` are PROVED (see §4 for the compile status) |

All statements below were checked with `lake env lean`; all theorems print
`[propext, Classical.choice, Quot.sound]` (VERIFIED, compiled).

```
theorem G0Galois.resQFiniteIndex : ResQFiniteIndex                       -- ResQ.lean
theorem G0Galois.detTate_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    (hT : PkgI3.TateModuleFree) : DetTate                                -- DetLeaves.lean
theorem G0Galois.g12Weight_of (hTE : TwistExists) (hTC : TwistConj) (hHC : HTConj)
    (hSen : SenTwist) (hFI : FiniteImageHT) : G12Weight                  -- Weight.lean
```

**Finding (VERIFIED, compiled `g12Weight_concl_iff`).** For `1 ≤ k`, `G12Weight`'s conclusion
`∃ n, {n, n + 1 − k} = {0, −1}` is equivalent to `k = 2`. The statement is true and not vacuous
(its hypotheses are met by Glazer's `r₅`); no statement was changed.

## 2. `ResQFiniteIndex` (proved, Mathlib only)

`scratch/g12-det/ResQ.lean`. The embedding `qEmbRing K : ℚ̄ → K̄` that
`Field.absoluteGaloisGroup.map` chooses is bijective (`K̄` is integral over `ℚ`, so
`IsAlgClosed.ringHom_bijective_of_isIntegral`). Let `K' ⊆ ℚ̄` be the image of `K`; then
`[K' : ℚ] = [K : ℚ]`. Every `σ ∈ Fix(K')` is `resQ K τ` for `τ = e σ e⁻¹` (`e = qEmbRing K`, a
`K`-automorphism of `K̄`), by `eq_resQ`. So `Fix(K') ≤ range (resQ K)`. Mathlib's
`finrank_eq_fixingSubgroup_index` gives `[G_ℚ : Fix(K')] = [K':ℚ] ≠ 0`, and
`Subgroup.finiteIndex_of_le` finishes.

## 3. `DetTate` (proved from leaves)

`det V_ℓ(A) = χ_ℓ^{dim A}` needs the sign that `det² = χ^{2g}` (all that scratch/weil-pairing
proved, `det_galRep_sq`) leaves open, i.e. the Pfaffian. The chain, each step compiled:

1. `darboux : Darboux` (`scratch/g12-det/Darboux.lean`; also inside DetTate.lean). A
   nondegenerate alternating form on a `2n`-dimensional space has a basis with Gram matrix
   Mathlib's `Matrix.J`. Proof by induction: split off a hyperbolic plane `span{e, f}`
   (`B e f = 1`), use `isCompl_orthogonal_of_restrict_nondegenerate`, and recurse on its
   orthogonal complement. A family with Gram matrix `J` is a basis because `J² = −1` and its
   size equals the dimension.
2. `sympSimDet_of_darboux : Darboux → SympSimDet`. If `B(fx, fy) = c B(x, y)` with `c ≠ 0`, then
   `det f = cⁿ`. In a Darboux basis, `M · diag(1, c⁻¹)` lies in `Sp_{2n}`, and Mathlib's
   `Matrix.SymplecticGroup.det_eq_one` (Pfaffian-free) gives determinant 1.
3. `cyc_eq_of_intertwines`, `cycQ_resQ`. Cyclotomic characters agree along an intertwining
   ring map, so `χ_ℓ^{ℚ̄}(resQ σ) = χ_ℓ^{K̄}(σ)`.
4. `detTate_of : TateGSp → SympSimDet → DetTate`. `TateGSp` provides a nondegenerate alternating
   `B` on `V_ℓ(A)` with `dim = 2g` and multiplier `χ_ℓ^{K̄}`. Then `LinearMap.det_baseChange`
   moves the result from `ℚ_ℓ` to `ℚ̄_ℓ ⊗ V_ℓ(A)`.
5. `tateGSp_of_zl : TatePairingZl → PkgI3.TateModuleFree → TateGSp`. Given the `ℤ_ℓ`-valued
   pairing on `T_ℓ A`, take its Gram matrix in a basis of the free module `T_ℓ A`, map it to
   `ℚ_ℓ`, and form the bilinear form with that matrix in the base-changed basis
   (`Algebra.TensorProduct.basis`, `LinearMap.toMatrix_baseChange`). Nondegeneracy holds
   because the determinant is nonzero over the domain `ℤ_ℓ`; the form is alternating because
   its Gram matrix is skew with zero diagonal and the characteristic is 0. The dimension
   `2g = rank T_ℓ` comes from T26.
6. `tatePairingZl_of_leaves`. Take the pairing `(tatePairing S.D S.lam).compr₂ (tmuCoordLin hg)`
   from weil-pairing. It is alternating (`tatePairing_self`, since `λ` is symmetric) and has
   multiplier `χ_ℓ` (`tatePairing_cyclotomic`). Its left kernel is trivial
   (`tatePairing_left_ker`, `tmuCoordLin_injective`). This needs weil-pairing §1-§9, which
   `DetLeaves.lean` copies verbatim (WeilPairing.lean L6-1149, minus `twist_finite_four`, which
   imports `GlueAssembly`).

Leaves used: `T09_SymmIsogenyExists` (Mumford §§6, 8, 13, 20, 23), `IsogenyQuasiInverse` (Mumford
§7-8), `DivisiblePoints` (Mumford §4 App. 2, §6), `PkgI3.TateModuleFree` (Mumford §18-19), with
weil-pairing's locators (UNVERIFIED numbering). They are stated over the Objects layer
`PkgI3.AbVar`, the same as `DetTate`. Objects' PkgI3 section equals Split.lean L2418-2764 up to
whitespace (VERIFIED, `diff`).

Consequence for g0-mod-galois: in `g12Det_of`, `DetTate` can now be replaced by these four leaves,
so `G12Det` rests on `R14Det`, T18 and those leaves. `ResQFiniteIndex` is a theorem.

## 4. `G12Weight` (reduced)

`scratch/g12-det/part_weight.lean` and `part_twist.lean`. `build.sh` appends them to g0-split's
`Split.lean`, which gives `Weight.lean`.

New definitions: `IsTwist ρ' ψ ρ` (`ρ'(σ) = ψ(σ) ρ(σ)`) and `IsConj r ρ'` (`r(σ) = P ρ'(σ) P⁻¹`).

| Piece | Kind | Statement | Status |
|---|---|---|---|
| `TwistExists` | glue | `σ ↦ ψ(σ)ρ(σ)` is a continuous representation | PROVED (`twistExists`) |
| `TwistConj` | glue | `r` irreducible, `ρ` semisimple attached to `g`, `r` attached up to twist `ψ` ⇒ `r ≅ ψ⊗ρ` | PROVED from T18 + T19 (`twistConj_of`): traces agree at Frobenius (`ιC` injective), hence everywhere (`eq_of_eq_on_arithFrob`); `r` is semisimple (Burnside-irreducible), `ψ⊗ρ` is semisimple; then Brauer–Nesbitt |
| `HTConj` | glue | Hodge–Tate weights (`PkgI4.LocalHasHTWeights`) do not change under conjugation by `P ∈ GL_n(ℚ̄_ℓ)` | OPEN. True: enlarge `E` to contain the entries of `P^{±1}`; `E'⊗_E V ≅ V^{[E':E]}` as `ℚ_p[G]`-modules, so `htMult` is unchanged. Needs the definitions' base-change API |
| `SenTwist` | **leaf** | `ρ` and `ψ⊗ρ` Hodge–Tate with full-size weight multisets `S`, `S'` ⇒ `S' = S + s` for some `s ∈ ℤ` | Sen, Invent. Math. 62 (1980): Hodge–Tate ⇔ Sen operator semisimple with integer eigenvalues, and `Θ_{ψ⊗V} = Θ_ψ + Θ_V` (UNVERIFIED numbering) |
| `FiniteImageHT` | **leaf** | finite image ⇒ Hodge–Tate with all weights 0 | Tate 1967 §3 Thm 2 + Ax–Sen–Tate, Hilbert 90 (UNVERIFIED numbering) |

Proof of `g12Weight_of`:
- R14 gives a semisimple `ρ_g`. It is converted from `HSyn.GaloisRep` to `PkgI4.GaloisRep`; the
  two structures have the same fields, and `AttachedTo` and `IsSemisimple` have the same bodies.
- `TwistExists` gives `ρ' = ψ⊗ρ_g`, `TwistConj` gives `r ≅ ρ'`, and `HTConj` gives
  `ρ'` weights `{0, −1}`.
- **k ≥ 2:** R13 (`PkgI4.EigenformHT`) gives `ρ_g` weights `{0, 1−k}`, and `SenTwist` gives
  `{0, −1} = {s, s+1−k}`, so take `n = s`.
- **k = 1:** R15 (`HSyn.DeligneSerreConseq`) gives finite image, `FiniteImageHT` gives weights
  `{0, 0}`, and `SenTwist` gives `{0, −1} = {s, s}`, which is impossible.

**Finding (argument; the statement form is a design point).** `SenTwist` needs
`card S = card S' = n`. `HasHTWeights S` with `card S < n` holds for representations that are
not Hodge–Tate. For example, a nilpotent Sen operator gives `S = {0}`. If `ψ` has a non-integral
Sen weight, then `S' = ∅ ≠ S + s`. So the leaf is stated with full size. In `G12Weight` both
sizes are 2.

## 5. What remains

- `HTConj` (glue): invariance of `PkgI4.htMult` under extension of the coefficient field and
  under isomorphism. This is definitional bookkeeping, and nothing in Mathlib does it today.
- The leaves `SenTwist` and `FiniteImageHT` are new. They should be added to the leaf list
  (Sen 1980; Tate 1967 / Ax–Sen–Tate) and need a primary-source check of the theorem numbers.
- Integration: `GaloisPieces.weight` can be replaced by `HTConj`, `SenTwist` and `FiniteImageHT`;
  `detTate` by the four leaves of §3; and `finIndex` by `resQFiniteIndex`.

## 6. Files

- `scratch/g12-det/ResQ.lean`: `ResQFiniteIndex`, proved.
- `scratch/g12-det/DetTate.lean`: `Darboux`, `SympSimDet`, `TateGSp`, `TatePairingZl`, and the
  chain from §3 except its last step.
- `scratch/g12-det/Darboux.lean`: standalone proof of `Darboux`.
- `scratch/g12-det/DetLeaves.lean` (from `build_det.sh`): `part_wp.lean` (weil-pairing §1-§9),
  then the body of DetTate.lean, then `part_leaves.lean`. It proves `detTate_of_leaves`.
- `scratch/g12-det/Weight.lean` (from `build.sh`): Split.lean, then `part_weight.lean`, then
  `part_twist.lean`. It proves `g12Weight_of`, `twistExists`, `twistConj_of` and
  `g12Weight_of_HT`.
- Prerequisite for Weight.lean: `lake build ZInQKernel.Hypotheses.JHeight
  ZInQKernel.Compiler.Precision.HeightConstant`.
