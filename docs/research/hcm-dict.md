# hcm-dict: `hCM` replaced by Shimura's Theorem 5.4 in printed form

Task hcm-dict, 2026-11-16. Base: wip/leaf-fold33b 4da8d4f3 (merging origin/main changed nothing). Log:
`scratch/hcm-dict/log.md`. Lean: `ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean`; development copy
`scratch/hcm-dict/Dict.lean`.

## 1. Result

The frozenTarget hypothesis `hCM : T5Glue.ShimuraMainCM` is now proved in Lean from one new leaf,
`ZInQ.Contrib.HCMDict.ShimuraThm54`. That leaf is Shimura 1971 Thm 5.4 as printed (an analytic isomorphism
`ξ : ℂ/𝔞 → E(ℂ)` gives an analytic isomorphism `ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` with `ξ(u)^σ = ξ'(s⁻¹u)`), stated over Mathlib's
Weierstrass curves and their points. Everything below is VERIFIED (compiled):

```
theorem ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed (h : ShimuraThm54) : T5Glue.ShimuraMainCM
```

* The axioms are `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no `axiom`, and no code that runs at build time.
* `#discharges` (`scratch/hcm-dict/Discharges-output.txt`):
  ```
  DISCHARGES [hCM] by ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed
    still assumes: [ZInQ.Contrib.HCMDict.ShimuraThm54]
    axioms: [propext, Classical.choice, Quot.sound]
  ```
* The manual fold is `scratch/hcm-dict/FoldCheck.lean` (output `FoldCheck-output.txt`). It contains:
  * `frozenTarget_hCMPrinted`, which calls `frozenTarget` with `hCM` filled;
  * `frozenTarget_hCMPrinted'`, the folded `Main.lean` body itself.

  Both use only the standard axioms. `scratch/hcm-dict/MainFolded.lean` is `Main.lean` with the fold applied. It
  compiles on its own, and `ZInQ.OneProof.frozenTarget` uses only the standard axioms.
* GLUE count:
  * The `hCM` row was `consequence / GLUE / GLUE`. It becomes `published (unread) / LEAF / LEAF`.
  * Strict GLUE goes from 22 to 21, and strictest GLUE from 22 to 21.
  * No new GLUE is added: the one new statement is the leaf itself.

## 2. The new leaf

```lean
def ShimuraThm54 : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticUnif E (kappa m '' 𝔞) ξ →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUnif (E.map (σ : ℂ →+* ℂ)) (kappa m '' sInvLat m s 𝔞) ξ' ∧
      ∀ u v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)
```

Where the definitions come from:

* From `ShimuraMainCM` unchanged: `QNeg`, `ιC`, `kappa`, `ArtinCond`, `sInvLat`, `finPart`, `latHat`, `AfK` (all from
  `RingClassLattice.lean`), and the normalization of `e`.
* New definitions:
  * `conjPt σ` is `P ↦ P^σ` on `E(ℂ) = E.toAffine.Point` (Mathlib's points): `(x, y) ↦ (σx, σy)` and `O ↦ O`.
  * `E^σ` is `E.map σ`.
  * `IsAnalyticUnif E Λ ξ` means that `ξ : ℂ → E(ℂ)` is additive and onto, that `ξ z = O ↔ z ∈ Λ`, and that `ξ` is
    holomorphic in affine coordinates near every point not sent to `O`. Concretely, near such a point there are an
    open `U` and functions `X, Y` holomorphic on `U` with `ξ z = (X z, Y z)` for every `z ∈ U`.

**Rating: printed form.** The reasons:

1. **The statement is Thm 5.4 as printed, weakened in three places.** Each change makes it a consequence of the
   print, never stronger:
   * the uniqueness of `ξ'` is dropped;
   * `E` ranges over short Weierstrass models only (every elliptic curve over `ℂ` has one);
   * `𝔞` comes with a period pair (that is, `𝔞` is a lattice in `K`).
2. **The Lean notion matches "analytic isomorphism", and this is proved in Lean.** There are two halves:
   * `isAnalyticUnif_iff` together with `exists_lattice_eq` says that the maps satisfying `IsAnalyticUnif` on a short model
     are exactly `z ↦ (℘_{L₀}(αz), ℘'_{L₀}(αz)/2)`, where `E = E_{L₀}` and `L₀ = αΛ`. Those are the analytic group
     isomorphisms `ℂ/Λ → E(ℂ)`. So the hypothesis is not weaker than the printed one, and the leaf is not stronger
     than the print.
   * Conversely, an analytic group isomorphism is holomorphic in the affine chart, so it satisfies `IsAnalyticUnif`.
3. **Either reading of "analytic isomorphism" works.** If the print's phrase is read without the group law, the
   printed `ξ'` still sends `0` to `O`: take `u = 0`, so `ξ'(0) = ξ(0)^σ = O`. A biholomorphism of complex tori that
   fixes `0` is a group isomorphism, so the conclusion still follows. The group-law reading is the one in Shimura's
   §4–5 setting (UNVERIFIED, from memory).
4. **The setting is inherited from the old leaf, without change.** This covers:
   * the normalization of `[s, K]`: Tau Ceti's Artin map sends a uniformizer to the arithmetic Frobenius, and the old
     docstring's re-check note still applies;
   * the convention `v` represents `s⁻¹u` iff `s_f v − u ∈ 𝔞̂`.

   These are the same as in `ShimuraMainCM`, which a statement review (two lenses, from memory) found faithful.
5. **Locator:** Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm 5.4; Lang,
   *Elliptic functions*, Ch. 10 Thm 3. Both numbers are UNVERIFIED (from memory; not read here). Proposed
   `locators.md` row: `ShimuraThm54 | Shimura 1971 Thm 5.4 (and Lang, Elliptic functions, Ch. 10 Thm 3) | unread |
   numbers UNVERIFIED`. I did not edit locators.md because it is a shared file; the integrator adds the row.

## 3. The proof (what was missing between the print and the coordinate form)

The proof has six steps. All are compiled in `ShimuraMainCM.lean`.

1. **`toPoint_isAnalyticUnif`.** The Weierstrass map `ξ_L(z) = (℘_L(z), ℘'_L(z)/2)` on
   `E_L : y² = x³ − g₂/4·x − g₃/4` is an analytic isomorphism with kernel `L`. Inputs:
   * the vendored FLT theorem `PeriodPair.isUniformization_toPoint` (additive, onto, kernel `L`), already built in the
     tree;
   * Mathlib's `analyticOnNhd_weierstrassP` and `analyticOnNhd_derivWeierstrassP`.
2. **`exists_lattice_eq`.** Every short elliptic model over `ℂ` is `L.weierstrassCurve` for some period pair `L`.
   * Start from the vendored `exists_variableChange_smul_weierstrassCurve_eq`, which uses `jLattice_surjective`.
   * A variable change between two short models has `r = s = t = 0`.
   * Then rescale the lattice by `u` (using `T5Glue.IsScale`).
3. **`exists_local_lift`.** Near some point, `ξ` lifts holomorphically through `ξ_{L₀}`:
   * use the local inverse of `℘_{L₀}` at `ω₁/4`, where `℘' ≠ 0` because `ω₁/2 ∉ L₀`;
   * compose it with the `x`-coordinate of `ξ`;
   * fix the sign of `y` by continuity.

   This is adapted from the vendored FLT proof `kw_surgehgf4_hH2d_…` (Apache-2.0, cited in the file).
4. **`exists_eq_toPoint_mul`.** `ξ(z) = ξ_{L₀}(αz)` for every `z`:
   * The lift `g`, normalized so that `g(0) = 0`, is additive near `0`: the defect lies in `L₀` and is small, and `L₀`
     is discrete.
   * So `g'` is constant near `0`, which gives `g(t) = αt` there.
   * The equality extends to all of `ℂ` through `ξ(z) = n·ξ(z/n)`.
5. **`isAnalyticUnif_iff` and `eq_scaled_of_isAnalyticUnif`.** The kernels give `L₀ = αΛ`. Then `IsScale` turns
   `ξ_{L₀}(αz)` into `(μ²℘_Λ(z), μ³℘'_Λ(z)/2)` with `μ = α⁻¹`, and the model's coefficients become
   `a₄ = −μ⁴g₂(Λ)/4` and `a₆ = −μ⁶g₃(Λ)/4`.
6. **`shimuraMainCM_of_printed`.** This is the assembly:
   * Apply the leaf to `E_P` and `ξ_P`.
   * Apply step 5 to the `ξ'` it returns, on `E_P^σ` with the lattice `P'` (`κ(s⁻¹𝔞) = P'.lattice`).
   * The coefficients give `IsConjModel σ P P' μ`.
   * For `u ∉ 𝔞`, `ξ'(κv) = ξ_P(κu)^σ ≠ O`, so `κv ∉ P'`. Comparing coordinates then gives the two equations of
     `ShimuraMainCM`.

## 4. Deliverables

All under `scratch/hcm-dict/` unless a path is given:

* `ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean`, the contribution. It imports `RingClassLattice` and four vendored
  FLT theorem modules, all already built; it does not import `Main`. Size: 28 KB.
* `Discharges.lean` and `Discharges-output.txt`.
* `FoldCheck.lean` and `FoldCheck-output.txt`, the manual fold.
* `MainFolded.lean`: `Main.lean` with the fold applied, compiled on its own.
* `kinds-row.tsv`, the new `hCM` row: `frozenTarget hCM published unread … LEAF LEAF`.
* `log.md` and `Dict.lean`.

**Fold spec for `Main.lean`.** Four changes:

* add `import ZInQKernel.Contrib.OneProof.ShimuraMainCM`;
* change the binder to `(hCM : ZInQ.Contrib.HCMDict.ShimuraThm54)`;
* replace both uses of `hCM` (the `tyzThm35ReadingA_noHX` argument and the `grossZagierHeegnerCd_of_printed` argument)
  by `(ZInQ.Contrib.HCMDict.shimuraMainCM_of_printed hCM)`;
* update the kinds.tsv row as in `kinds-row.tsv`.

## 5. Open points

* **Theorem numbers.** The numbers for Shimura Thm 5.4 and Lang Ch. 10 Thm 3 are UNVERIFIED. The new leaf enters as
  "unread" until a statement check compares it with the print.
* **Claim conflict.** `docs/one-proof/claims.tsv` lists `hCM` as held by the host task cm-primitive, which is looking
  at the reading risk of `MainTheoremCMPol`. The integrator should reconcile this result with that claim.
* **Not proved in Lean:** that `IsAnalyticUnif` matches the genuine notion for non-short Weierstrass models. It is not
  needed, because the leaf only quantifies over short models.
