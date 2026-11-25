# hecke-pin: the dictionary steps of `HeckeJ1DS`, `AfShimura`, `AfCharpolyDS965` pin Diamond–Shurman's objects

Task hecke-pin, 2026-11-17. Lean: `ZInQKernel/Contrib/OneProof/HeckePin.lean` (namespace `AfTateLam.HeckePin`).
Scratch: `scratch/hecke-pin/` (log, verbatim target copy, `#discharges` output, autofold spec, fold dry run).

## 1. Verdict

The shared dictionary gap of the three r16CoreY leaves is closed, with one difference between the parts:

* **Two parts are proved with no extra input.** Gap 2b: `A_f` is unique up to unique isomorphism compatible with
  `π`. Gap 3: `θ` is pinned, since `a_n ∈ ℚ(a_p, χ(d))`.
* **The other two parts rest on smaller named Props.** Gap 1 (`KillsIf` is DS's `I_f`) and gap 2a (`T_p`, `⟨d⟩`
  are pinned) reduce to these:

| Prop | used for | kind | status |
|---|---|---|---|
| `X1TauPoints` | gaps 1, 2a | LEAF candidate: consequence of DS §7.7, not printed form | open |
| `AbelJacobiX1` | gap 1 | LEAF candidate: composite of DS Thm 6.1.2 (Abel) with the algebraic Jacobian, not printed form | open |
| `EichlerPrimitive` | gap 1 | GLUE | **proved** (`eichlerPrimitive`) |
| `EichlerHecke` | gap 1 | GLUE | **proved** (`eichlerHecke`) |
| `ConstOnTauPoints` | gap 2a | GLUE (standard algebraic geometry) | open |

Everything compiles. Every main theorem uses only the standard axioms (VERIFIED, `scratch/hecke-pin/Axioms-output.txt`
and `Discharges-output.txt`).

**Per row** (details in §6):

* `HeckeJ1DS`: the dictionary gap is closed modulo `X1TauPoints` and `ConstOnTauPoints`.
* `AfShimura`: the dictionary gap is closed modulo `X1TauPoints` and `AbelJacobiX1` (for `I_f`), and
  `X1TauPoints` and `ConstOnTauPoints` (for the pinning of `T_p`, `⟨d⟩`). The parts about `A_f` and `θ` are closed
  outright.
* `AfCharpolyDS965`: same as `AfShimura`.

**The reading** (§5): DS's identification of the §9.5 representation with 9.6.5's `ρ_{f,λ}` at `k = 2` is
*asserted*, not presupposed. It is in the
paragraph after Thm 9.6.5, on the same page: p. 404 of the corrected fourth printing (2016) (HUMAN-READ,
zachbaugher, issue #14 comment 7121091136).

**A side result.** The proved `EichlerHecke` fixes the orientation of `IsHeckeT`'s double-coset formula: the
operator it defines has eigenvalue `a_p(f)` on the `f`-part, through `Ψ` (Claim B). It is not, for example, the
transpose `⟨p⟩⁻¹T_p`, whose eigenvalue for `p ∤ N` is `χ(p)⁻¹a_p` (STANDARD; DS §5.5, number UNVERIFIED). So
`evF(T_p) = a_p` in `KillsIf` is the matching normalization.

## 2. Gap 1: `KillsIf` uses DS's `I_f`

`KillsIf` quantifies over `h ∈ ker(evF)` in the free algebra on `T_p`, `⟨d⟩`. DS's `I_f = {T ∈ 𝕋_ℤ : Tf = 0}`
is an ideal of the image `𝕋_ℤ`. The two agree exactly when `ker(heckeJ) ⊆ ker(evF)`.

**Theorem** (`evF_eq_zero_of_heckeJ_eq_zero_of_leaves`; VERIFIED, compiles). Take `X1TauPoints`, `AbelJacobiX1`,
`N ≥ 2`, `f` with `IsNormalizedEigenform f χ`, a model `X` (with `IsCurve` and `IsX1Gen`), a Jacobian `(J, aj)`,
and any `tp`, `δ` with `IsHeckeT` and `IsDiamond`. Then `heckeJ tp δ h = 0` implies `evF χ f h = 0`.

Consequences, proved from it:
* `evF_wellDefined`: the eigenvalue of `T ∈ 𝕋_ℤ` on `f` is well defined.
* `image_ker_evF_eq_IfDS`: `heckeJ(ker evF) = IfDS`. Here `IfDS` is the set of `T ∈ 𝕋_ℤ` all of whose
  representatives have eigenvalue 0 on `f`, which is DS Def. 6.6.3's `I_f`.
* `killsIf_iff_IfDS_of_leaves`: `KillsIf φ ↔ ∀ T ∈ I_f, T ≫ φ = 0`.

**Proof** (all steps in Lean):
1. *Formal divisors.* `Dv = ℍ →₀ ℤ`, with the double-coset operators `T̃_p[τ] = Σ_{j<p}[(τ+j)/p] + [p∤N][γ_p(pτ)]`
   and `⟨d⟩~[τ] = [γ_dτ]`, for chosen `γ ∈ Γ₀(N)` (`exists_gamma`). The free algebra acts through `heckeD`, and
   degree 0 is preserved (`heckeD_D0`).
2. *Claim A* (`cls_heckeD`). Write `cls(Σ n_τ[τ]) = Σ n_τ aj(x_τ)` in `J(ℂ)`. Then `cls ∘ heckeD h = heckeJ h ∘ cls` on
   degree-0 divisors. This follows from `IsHeckeT` and `IsDiamond` on the generators `[τ] − [τ₀]`, which span
   degree 0 (`D0_le_span`), and induction over `FreeAlgebra`.
3. *Claim B* (`psi_heckeD`). Write `Ψ(Σ n_τ[τ]) = Σ n_τ F(τ)`, where `F` is a holomorphic primitive of `f`. Then
   `Ψ ∘ heckeD h = evF(h) · Ψ` on degree-0 divisors. This follows from `EichlerHecke` on the generators and
   induction.
4. *Conclusion.* Suppose `heckeJ h = 0`. For `D = [τ] − [τ₀]` the divisor `heckeD h D` has trivial class, so by
   `AbelJacobiX1` the number `evF(h)(F(τ) − F(τ₀))` lies in a countable set `Λ` for every `τ`. `F` is continuous
   and, since `a₁ = 1`, not constant. `ℍ` is connected, so the range of `F` is uncountable
   (`const_of_countable`, via Mathlib's `Cardinal.Real.Icc_countable_iff`). Hence `evF(h) = 0`.

**The Eichler glue is proved:**
* `eichlerPrimitive : EichlerPrimitive`. `F(τ) = G(e^{2πiτ})/(2πi)`, where `G` is a primitive on the unit disc of
  `dslope (cuspFunction f) 0` (Mathlib's Morera theorem on a disc, `DifferentiableOn.isExactOn_ball`).
* `eichlerHecke : EichlerHecke`, in two parts:
  * `hecke_eigen_fun`. `(1/p)Σ_{j<p} f((τ+j)/p) + pχ(p)f(pτ) = a_p f(τ)` as functions on `ℍ`. The proof uses the
    `q`-expansion (Mathlib's `ModularForm.hasSum_qExpansion`), the root-of-unity sum `sum_exp_shift`, reindexing
    along `m ↦ pm`, and the coefficient recurrence `coeff_rec_prime` (from `IsNormalizedEigenform`).
  * `eichler_heckeT` and `eichler_diamond`. The derivative of `Σ F((τ+j)/p) + F(γ(pτ)) − a_pF(τ)` (respectively
    `F(γτ) − χ(d)F(τ)`) vanishes on `ℍ`, by `hasDerivAt_moebius`, `HasNebentypus` and
    `ModularForm.SL_slash_apply`. So it is constant (`IsOpen.is_const_of_deriv_eq_zero` on the convex half-plane).

## 3. Gap 2: pinning

* **`isAfQuotient_unique`** (no input): two `(A, π)`, `(A', π')` with `IsAfQuotient` are related by a unique
  isomorphism `ι` with `π ≫ ι = π'`. Every homomorphism `A → A'` compatible with the projections equals `ι`.
  Two supporting lemmas:
  * `hom_ext_of_isAfQuotient`: homomorphisms out of `A_f` are determined by their composite with `π`.
  * `induced_comm`: the endomorphisms that `T_p` induces on `A` and on `A'` correspond under `ι`.
* **`isHeckeT_unique`, `isDiamond_unique`**: two endomorphisms of `J` with `IsHeckeT` for the same `p` (or
  `IsDiamond` for the same `d`) are equal.
  * Inputs: `X1TauPoints` and `ConstOnTauPoints`.
  * `isHeckeT_agree` and `isDiamond_agree` show the two endomorphisms act identically on every class
    `aj(x_τ)/aj(x_{τ'})`. The `y`, `z` points come from `X1TauPoints` and `γ` from `exists_gamma_prime` or
    `exists_gamma_unit`.
  * `end_eq_of_classes`: then `g = (aj ≫ t)/(aj ≫ t')` is constant on the `x_τ` and sends `P₀` to `0`. By
    `ConstOnTauPoints`, `g = 1`. By the Albanese uniqueness in `IsJacobian`, `t = t'`.
* `ConstOnTauPoints` (GLUE, unproved). A `ℚ`-morphism `X → J` that takes the same value at all the `x_τ` and
  sends `P₀` to `0` is `0`. Proof sketch:
  * The `x_τ` with distinct `j(τ)` are distinct `ℂ`-points, because `j_X` is regular at `x_τ` with value `j(τ)`.
  * They are therefore infinitely many closed points of the irreducible curve `X_ℂ`.
  * The fibre of `g_ℂ` over the common value is closed and contains them, so it is all of `X_ℂ`.
  * Evaluating at `P₀` gives the value `0`.

  **Why it is not proved here.** A search of Mathlib and the tree found the ingredients but not the result:
  * Equalizers into separated schemes are closed immersions (`isClosedImmersion_equalizer_ι_left`).
  * `ext_of_apply_eq` works over an algebraically closed base. `ext_of_fromSpecResidueField_eq` works for a
    dense set of points.
  * Field base change is faithful (`fieldBaseChange_faithful`, CloudW07), which allows descending from `X_ℂ`.
  * The `ℂ`-points of `X_ℂ` are its closed points (`pointEquivClosedPoint`).

  Two pieces are missing:
  * the dimension-one fact that a closed subset of an integral curve containing infinitely many closed points is
    the whole curve;
  * geometric irreducibility of `X_ℂ`. `IsCurve` gives only geometric connectedness, and smooth plus geometrically
    connected implies geometrically irreducible, but that implication is not in the tree.

  A `ℂ`-point over `ℚ` can lie over the generic point of `X`, so the argument has to run on `X_ℂ`. The route is:
  base-change to `ℂ`, take the closed equalizer of `g_ℂ` and the constant map, apply the dimension-one fact,
  apply `ext_of_apply_eq`, and descend. This is a project-size AG formalization, so it is left as named GLUE.

## 4. Gap 3: `θ` is pinned

* `coeff_mem_genField` (no input): for a normalized eigenform, `a_n(f) ∈ ℚ(a_p(f) : p prime; χ(d) : d ∈ (ℤ/N)^×)`.
  Uses `a₀ = 0` (`coeff_zero_eq`, a cusp form), `a₁ = 1`, multiplicativity on coprime factors, and
  `a_{p^{e+2}} = a_p a_{p^{e+1}} − χ(p) p a_{p^e}`, all from `IsNormalizedEigenform`'s coefficient relations, by
  strong induction. The tree's own recurrence is not needed.
* `theta_unique` (no input beyond `IsAfQuotient`): two `θ, θ'` with `IsAfAction` for the same `(A, π)` are equal.
  The induced endomorphisms are unique by `hom_ext_of_isAfQuotient`, and the `c` with `c = χ(d)` is unique since
  `K_f ⊆ ℂ`. So `θ` and `θ'` agree on the `a_p` and the `χ(d)`. Their equalizer is an intermediate field (inverses
  are unique in `End⁰`), so it contains `coeffField f = ℚ(a_n)`.

## 5. Reading: Diamond–Shurman p. 404 (corrected fourth printing, 2016)

Thm 9.6.5 is on p. 404 of the corrected fourth printing (2016): VERIFIED by a human reader's print copy (issue #14
comment 7000317188, made for the earlier `dsThm965Printed` row). A second human reading in a print copy, made
for this row (HUMAN-READ, zachbaugher, issue #14 comment 7121091136), quotes the paragraph after the theorem on
p. 404 and reads §9.5 on pp. 395–402 (not the proofs of Lemma 9.5.3 and Thm 9.5.4).

* The relevant sentence is in the paragraph after the theorem, on the same page (HUMAN-READ, zachbaugher,
  issue #14 comment 7121091136). It begins "Section 9.5 constructed ρ_{f,λ} when k = 2 but didn't prove that
  ρ_{f,λ} is irreducible or that the equation is the characteristic equation."
* It **asserts** the identification: it names the §9.5 construction as the `k = 2` instance of the theorem's
  `ρ_{f,λ}`. So Thm 9.6.5 at `k = 2` claims the characteristic equation for the §9.5 representation.
* The sentence gives no proof or reference for that claim. It flags that §9.5 did not prove it.
* AfCharpolyDS965's reading: the human reading (issue #14 comment 7121091136) rates it a consequence, GLUE. DS
  print the `k = 2` characteristic equation without proof or citation (§9.5 proves only that `ρ_{f,λ}(Frob_𝔭)`
  satisfies the quadratic), and the step from DS's transported Galois action to the Lean's algebraic `A_f` is a
  dictionary argument that is not in the print. Shimura 1971 Thm 7.14 is unread as a second locator.

## 6. The three rows

| row | shared dictionary gap | what remains |
|---|---|---|
| `HeckeJ1DS` | closed modulo `X1TauPoints`, `ConstOnTauPoints`: the `T_p`, `⟨d⟩` asserted to exist are DS's (unique) | its own reading (DS §6.3, §7.9; AI-read) |
| `AfShimura` | closed: `A_f` unique (no input), `θ` unique (no input), `KillsIf` = DS's `I_f` (modulo `X1TauPoints`, `AbelJacobiX1`), `T_p`, `⟨d⟩` pinned (modulo `X1TauPoints`, `ConstOnTauPoints`) | its own reading (Shimura 1973 Thm 1) |
| `AfCharpolyDS965` | closed, as for `AfShimura` (same hypotheses) | the k = 2 identification is asserted by DS (§5); human reading |

**New Props and their ratings:**
* `X1TauPoints`: LEAF candidate, not printed form. It is a consequence of DS §7.7
  (`X₁(N) = X₁(N)_alg,ℂ` with function field `ℂ(j, f₁)`). The step from Riemann-surface points to `ℂ`-points of the
  `ℚ`-scheme, and the limit form of regularity in `AtTau`, are dictionary steps.
* `AbelJacobiX1`: LEAF candidate, not printed form. It composes four sources:
  * DS Thm 6.1.2;
  * DS §3.3 (weight-2 cusp forms are holomorphic differentials);
  * the algebraic Jacobian theory (Milne 1986, Thm 1.1 / Prop. 6.1; numbers UNVERIFIED);
  * algebraic = meromorphic functions (DS §7.2).
* `ConstOnTauPoints`: GLUE, standard algebraic geometry, unproved.
* `EichlerPrimitive`, `EichlerHecke`: GLUE, proved.

**These Props are audit inputs, not hypotheses of the fold.** The fold's leaf set does not change: `r16CoreY`
is still discharged by `AfTateLam.r16CoreY_of_ds965`, and the fold dry run gives the same `11/18 on 29 -> 15/17
on 32` as r16-det. `scratch/hecke-pin/autofold.json` is r16-det's spec with the leaves' docs extended by the
audit notes. It also adds an `audit_props` list giving the kind and flag of the new Props; `autofold.py --dry-run`
accepts it.

## 7. Files and checks

* `ZInQKernel/Contrib/OneProof/HeckePin.lean`: new, about 1100 lines. `lake build ZInQKernel.Contrib.OneProof.HeckePin`
  succeeds (VERIFIED).
* Docstring pointers (text only) added to `HeckeJ1DS`, `AfShimura` (`AfTateLambda.lean`) and `AfCharpolyDS965`
  (`R16CoreYDS965.lean`).
* `scratch/hecke-pin/Target.lean`: verbatim copies of the three leaves and of the definitions they use
  (`IsX1Gen`, `RegAt`, `AtTau`, `shiftDiv`, `mulNat`, `IsHeckeT`, `IsDiamond`, `evF`, `heckeJ`, `KillsIf`,
  `IsAfQuotient`, `IsAfAction`). `heckePin_copy_iff` holds by `Iff.rfl` (VERIFIED).
* `scratch/hecke-pin/Discharges-output.txt`: `#discharges` lists `r16CoreY` by `r16CoreY_of_ds965` (unchanged).
  The HeckePin theorems discharge no open field, as expected; their axioms are standard.
* `scratch/hecke-pin/FoldDryRun.lean`: compiles. `sixContactMin_of_open49` uses only the standard axioms (VERIFIED).
