# g12-det: `G12Weight`, `DetTate`, `ResQFiniteIndex` (glue of g0-mod-galois)

Task g12-det, 2026-11-13. Lean: `scratch/g12-det/` (log: `scratch/g12-det/log.md`). The three
Props are copied verbatim from `scratch/g0-mod-galois/part_galois.lean` (`G12Weight`) and
`part_det.lean` (`DetTate`, `ResQFiniteIndex`), with what they depend on.

## 1. Result

**All three targets are closed: two are proved and one is proved from two new leaves.**

| Prop | Status | Rests on |
|---|---|---|
| `ResQFiniteIndex` | **PROVED** | Mathlib only |
| `DetTate` | **PROVED from leaves** | weil-pairing's leaves `T09_SymmIsogenyExists` (T9 restated), `IsogenyQuasiInverse` and `DivisiblePoints`, plus Objects' leaf `PkgI3.TateModuleFree` (T26) |
| `G12Weight` | **PROVED from two new leaves** | `SenTwist` (Sen 1980) and `FiniteImageHT` (Tate 1967 with Ax–Sen–Tate). It also uses the leaves that `G12Weight` itself takes as hypotheses (R13, R14, R15, T18, T19). Every glue piece is proved: `TwistExists`, `TwistConj` (from T18 and T19), and `HTConj` (via `HTExtend`) |

The main theorems are below. Each is checked with `lake env lean`, and each `#print axioms`
gives `[propext, Classical.choice, Quot.sound]`, with no `sorry` (VERIFIED, compiled):

```
theorem G0Galois.resQFiniteIndex : ResQFiniteIndex                       -- ResQ.lean
theorem G0Galois.detTate_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    (hT : PkgI3.TateModuleFree) : DetTate                                -- DetLeaves.lean
theorem G0Galois.g12Weight_of_senTwist (hSen : SenTwist) (hFI : FiniteImageHT) :
    G12Weight                                                            -- Weight.lean
```

**Finding (VERIFIED, compiled as `g12Weight_concl_iff`).** For `1 ≤ k`, `G12Weight`'s conclusion
`∃ n, {n, n + 1 − k} = {0, −1}` is equivalent to `k = 2`. The statement is true and not vacuous.
Its hypotheses hold for Glazer's `r₅`; a model review also gives the witness `V_5` of a non-CM
elliptic curve over ℚ with `ψ = 1`. No statement was changed.

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

## 4. `G12Weight` (proved from two new leaves)

The Lean is in `scratch/g12-det/part_weight.lean`, `part_twist.lean`, `part_htconj.lean`,
`part_htextend.lean` and `part_final.lean`. `build.sh` appends them to g0-split's `Split.lean`,
which gives `Weight.lean`.

New definitions: `IsTwist ρ' ψ ρ` (`ρ'(σ) = ψ(σ) ρ(σ)`) and `IsConj r ρ'` (`r(σ) = P ρ'(σ) P⁻¹`).

| Piece | Kind | Statement | Status |
|---|---|---|---|
| `TwistExists` | glue | `σ ↦ ψ(σ)ρ(σ)` is a continuous representation | PROVED (`twistExists`) |
| `TwistConj` | glue | if `r` is irreducible, `ρ` is semisimple and attached to `g`, and `r` is attached up to the twist `ψ`, then `r ≅ ψ⊗ρ` | PROVED from T18 and T19 (`twistConj_of`). Traces agree at Frobenius because `ιC` is injective, hence everywhere by `eq_of_eq_on_arithFrob`. `r` is semisimple because it is irreducible in Burnside's form, and `ψ⊗ρ` is semisimple. Brauer–Nesbitt then gives the conjugacy |
| `HTConj` | glue | Hodge–Tate weights (`PkgI4.LocalHasHTWeights`) are unchanged by conjugation by `P ∈ GL_n(ℚ̄_ℓ)` | PROVED from `HTExtend` (`htConj_of`). Let `E' = E ⊔ ℚ_ℓ(entries of P^{±1})`, which is finite. Conjugating the `E'`-model by `P` gives `ℚ_ℓ`-isomorphic `htSpace`s (`finrank_htSpace_conj`) |
| `HTExtend` | glue | a model over a finite `E` with weights `S` gives a model over any finite `E' ⊇ E` with weights `S` | PROVED (`htExtend`). A basis of `E'/E` of size `m` gives `htSpace(ρ_{E'}) ≅ htSpace(ρ_E)^m` (`htSpaceExtendEquiv`), and then `htMult = (m·d)/(m·e) = d/e` |
| `SenTwist` | **leaf** | if `ρ` and `ψ⊗ρ` are Hodge–Tate with full-size weight multisets `S`, `S'`, then `S' = S + s` for some `s ∈ ℤ` | Sen, Invent. Math. 62 (1980): a representation is Hodge–Tate iff its Sen operator is semisimple with integer eigenvalues, and `Θ_{ψ⊗V} = Θ_ψ + Θ_V` (UNVERIFIED numbering) |
| `FiniteImageHT` | **leaf** | a representation with finite image is Hodge–Tate with all weights 0 | Tate 1967 §3 Thm 2, Ax–Sen–Tate, Hilbert 90 (UNVERIFIED numbering) |

How `g12Weight_of` goes:
- R14 gives a semisimple `ρ_g`. It converts from `HSyn.GaloisRep` to `PkgI4.GaloisRep` because
  the two have the same fields and `AttachedTo` and `IsSemisimple` have the same bodies.
- `TwistExists` gives `ρ' = ψ⊗ρ_g`, `TwistConj` gives `r ≅ ρ'`, and `HTConj` gives `ρ'` the
  weights `{0, −1}`.
- **k ≥ 2:** R13 (`PkgI4.EigenformHT`) gives `ρ_g` the weights `{0, 1−k}`. `SenTwist` then gives
  `{0, −1} = {s, s+1−k}`, so `n = s`.
- **k = 1:** R15 (`HSyn.DeligneSerreConseq`) gives finite image, so `FiniteImageHT` gives the
  weights `{0, 0}`. `SenTwist` would then give `{0, −1} = {s, s}`, which is impossible.

The final assembly is `g12Weight_of_senTwist := g12Weight_of_htExtend htExtend`, with
`g12Weight_of_htExtend := g12Weight_of_HT (htConj_of ·)` and
`g12Weight_of_HT := g12Weight_of twistExists (twistConj_of hFD hBN)`.

**Note on the statement of `SenTwist`** (argument, SPECULATIVE). `SenTwist` assumes
`card S = card S' = n`, which makes both representations Hodge–Tate. Without full size the
statement can fail. A nilpotent Sen operator gives `HasHTWeights {0}` for a 2-dimensional
representation that is not Hodge–Tate, and if `ψ` has a non-integral Sen weight then
`S' = ∅ ≠ S + s`. In `G12Weight` both sizes are 2. The model review judged `SenTwist`, as
stated, to be a consequence of Sen's theorem and not stronger than it.

## 5. Model review and what remains

A read-only subagent review (no Lean) found no serious issue: every new Prop is true and
non-vacuous, and neither leaf is stronger than its source. Its notes:
- `htMult`'s division is exact, because `htSpace` is an `E`-space under precomposition.
- `SympSimDet` holds even without `c ≠ 0`.
- `TatePairingZl` is exactly what weil-pairing's lemmas give.

What remains:
- **The two new leaves `SenTwist` and `FiniteImageHT`.** They should join the leaf list (Sen 1980;
  Tate 1967 with Ax–Sen–Tate) and need a primary-source check of their theorem numbers.
- **Integration into g0-mod-galois's bundle `GaloisPieces`:**
  - `weight` becomes `SenTwist` + `FiniteImageHT` (`g12Weight_of_senTwist`).
  - `detTate` becomes the four leaves of §3 (`detTate_of_leaves`). Those leaves are stated over
    Objects' `PkgI3.AbVar`, which matches Split.lean's copy.
  - `finIndex` is discharged by `resQFiniteIndex`.

## 6. Files

- `scratch/g12-det/ResQ.lean`: proof of `ResQFiniteIndex`.
- `scratch/g12-det/DetTate.lean`: `Darboux`, `SympSimDet`, `TateGSp`, `TatePairingZl`, and the
  chain of §3 up to `detTate_of_zl`.
- `scratch/g12-det/Darboux.lean`: a standalone proof of `Darboux`.
- `scratch/g12-det/DetLeaves.lean`, built by `build_det.sh`: `part_wp.lean` (weil-pairing §1-§9),
  then the DetTate.lean body, then `part_leaves.lean`. It ends in `detTate_of_leaves`.
- `scratch/g12-det/Weight.lean`, built by `build.sh`: Split.lean followed by the `part_*.lean`
  files of §4. It ends in `g12Weight_of_senTwist`.
- `scratch/g12-det/HTFast.lean`: a faster check of `htConj_of` and `htExtend`, built from
  Split.lean L1-4727, `part_htdefs.lean`, `part_htconj.lean` and `part_htextend.lean`. One run
  takes about 1 minute.
- Before building Weight.lean or HTFast.lean, run `lake build ZInQKernel.Hypotheses.JHeight
  ZInQKernel.Compiler.Precision.HeightConstant`.
