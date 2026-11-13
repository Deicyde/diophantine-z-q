# t-brauer-purity: textbook leaves T1, T2, T14, T15

Status: research note (task t-brauer-purity, 2026-11-12). Lean companion: `scratch/t-brauer-purity/`
(results log `log.md`). Base 01267822 (origin/wip/integrate-w34b). No file under `ZInQKernel/`,
`blueprint/`, or another task's notes was edited.

Marks: **VERIFIED** (read in a source named here, computed, or compiled), **STANDARD** (published,
with reference), **SPECULATIVE** (an assessment). There is no network on this host, so theorem numbers
given from memory are **UNVERIFIED**.

## 1. Verdict

**Leaf T2 (Abhyankar's lemma, DVR form, `PkgI2.AbhyankarDVR`) is proved**, against the kernel's own
definition. **T15's real-place conjunct is proved**, so T15 reduces to its finite-place half. T1, T14
and T15 at `ℚ_p` are not proved. Everything below is VERIFIED: compiled with `lake env lean`, no
`sorry`, axioms `[propext, Classical.choice, Quot.sound]`.

1. **T2: proved.**
   * Kernel form: `scratch/t-brauer-purity/T2Kernel.lean` imports `ZInQKernel.HDecomp.Objects`
     (the kernel's definition, nothing copied but the proof) and proves
     `TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}` and
     `TBrauerPurityT2K.abhyankarDVR_objBridge : ObjBridge.AbhyankarDVR`.
   * Mathlib-only form: `scratch/t-brauer-purity/T2Full.lean` copies the definition verbatim from
     `Leaves.lean` and proves `TBrauerPurity.abhyankarDVR : PkgI2.AbhyankarDVR.{u}`, polymorphic in
     the universe.
   * T2 can therefore move from leaf to glue. §3 describes the proof; it avoids completions.
2. **T15, real place: proved.** `H2TwoClasses (Field.absoluteGaloisGroup ℝ)` is now a theorem over
   the kernel's own definition `PkgI6.H2TwoClasses`
   (`scratch/t-brauer-purity/LocalH2RealKernel.lean`, which imports
   `ZInQKernel.HDecomp.Conductor.I6Base`): `TBrauerPurityK.h2TwoClasses_real`. Hence
   `TBrauerPurityK.localH2CardC_iff : PkgI6.LocalH2CardC ↔ ∀ p [Fact p.Prime],
   PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])`.
3. **T1 (Zariski–Nagata purity) and T14 (Brauer–Hasse–Noether with reciprocity): nothing proved.**
   The finite-place half of T15 is also unproved. §4 explains why: these are deep theorems, and the
   infrastructure they need is missing from Mathlib v4.35 (VERIFIED by grep).
4. **No bridge from Tau Ceti or the Stacks project.** Neither source tree is on this host, and there
   is no network, so the task rule that a bridge counts only if its source compiles here rules them
   out (VERIFIED: searched `~/*`, `~/*/*`).
5. **Statement audit: all five Props are correct as stated** (§2). I found no vacuity, no
   over-strength, and no mismatch with the published statements.

**Recommendations for the announcement.** (i) **T2 is no longer a leaf.** Its bundle field
(`t2 : PkgI2.AbhyankarDVR.{0}`, `Leaves.lean` around line 19154) can be filled with
`TBrauerPurityT2K.abhyankarDVR`, which leaves 55 leaves. (ii) **T15.** Glue uses only the finite-place uniqueness half of T15:
`leafLocalTwo_of_T15` (ZInQKernel/HDecomp/Descent/WP3.lean:231) uses `(hC.1 p).2` only (VERIFIED,
read), and `leafLocalTwo_iff` there shows `LeafLocalTwo` equals that half. T15's real conjunct is now
proved. So T15 can be announced as `∀ p, H2TwoClasses (G_{ℚ_p})`, or more narrowly as glue-descent's
`LeafLocalTwo` (`|H²(G_{ℚ_p}, ℤ/2)| ≤ 2` on cochains), which is a consequence of the published
`Br(ℚ_p)[2] ≅ ℤ/2`.

## 2. Statement audit

**T1, `PkgI2.PurityBranchLocus`.** Hypotheses: `R → S` of finite type, `R` Noetherian, `R_p`
regular, `S_q` a normal domain, `S` quasi-finite at `q` (Mathlib:
`QuasiFinite R (Localization.AtPrime q)`, which for finite type means `q` is isolated in its fibre;
RingTheory/QuasiFinite/Basic.lean:368, VERIFIED), `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every height-one prime `q' ⊆ q`. Conclusion: `Algebra.IsEtaleAt R q` (= `FormallyEtale R S_q`,
Etale/Locus.lean:35, VERIFIED). This matches the ring-theoretic content of Stacks Tag 0BMB
(STANDARD; hypotheses recalled from memory, UNVERIFIED): `O_{X,x}` normal, `O_{S,s}` regular, `f`
quasi-finite at `x`, `dim O_{X,x} = dim O_{S,s} ≥ 1`, and `f` unramified at every specialization
`x' ⇝ x` with `dim O_{X,x'} = 1`. Two points. First, the height of `q' ⊆ q` in `S` equals the
dimension of `O_{X,x'}`. Second, finite type over a Noetherian ring gives finite presentation, so
`FormallyEtale R S_q` is étaleness at `q`. The hypotheses are satisfiable (for example `S = R`), so
the leaf is not vacuous. Correct.

**T2, `PkgI2.AbhyankarDVR`.** Now proved in Lean (§3), so the statement is true and not vacuous. Before proving it, I checked the mathematics as follows. Let
`Q' | Q | 𝔪`, `e = e(Q|𝔪)` with `e ∣ n`, and `m = n/e`. In `D = (S_L)_Q` write `π = uϖᵉ` with `u` a
unit, and put `w = t^m/ϖ`. Then `wᵉ = u`, so `L(w)/L` is unramified above `Q` (because `e` is
invertible). Over `L(w)`, `t` is a root of `X^m − wϖ`, and `wϖ` is a uniformizer at every prime `P`
over `Q`. Hence `e(Q'|P) = m` and `f(Q'|P) = 1`. This is exactly the proved
`ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq`, applied over the DVR `(S_{L(w)})_P`. So
`e(Q'|𝔪) = e·m = n`, and the residue field is separable over `k` by transitivity, using the
tameness of `L`.

Edge cases checked: `t ∈ L` (then `M = L`); `Xⁿ − π` reducible over `L`; `L` already containing an
`n`-th root of `π`. The derived facts the statement silently needs (the tower `R → L → M` commutes,
`M/K` is finite and separable, and `integralClosure R M` is Dedekind) are now Lean theorems. The
conclusion is a consequence of SGA 1 X 3.6 together with "`K(t)/K` is totally ramified of degree
`n`" (STANDARD; locator UNVERIFIED). Correct.

**T14, `PkgI6.BrauerHasse2C`, `PkgI6.BrauerReciprocity2C`.** `ZMod N` carries the discrete topology
(Topology/Instances/ZMod.lean:24, VERIFIED), so the `Continuous` in `IsCocycle2` and
`IsCoboundary2` is the genuine condition (local constancy). The cochain groups are therefore Serre's
continuous-cochain `H²(G, ℤ/2)`. Through `H²(G_K, ℤ/2) = H²(G_K, μ₂) ≅ Br(K)[2]` (Kummer and
Hilbert 90, natural in `K`), the two Props are the 2-torsion of injectivity of
`Br ℚ → ⊕_v Br ℚ_v` and of `∑_v inv_v = 0` (STANDARD). `resC` uses Mathlib's
`Field.absoluteGaloisGroup.map`, which depends on a choice of embedding of algebraic closures.
Being a coboundary is invariant under that choice, because conjugation acts trivially on cohomology.
Correct.

**T15, `PkgI6.LocalH2CardC`.** `H2TwoClasses G` says that a non-trivial class exists and that any
two non-trivial classes differ by a coboundary, i.e. `|H²| = 2`. At `ℚ_p` this is
`Br(ℚ_p)[2] ≅ ℤ/2` (STANDARD). At `ℝ` it is now proved. Correct.

## 3. Lean results

| File | Main declarations | Status |
|---|---|---|
| `LocalH2Real.lean` (Mathlib only; `IsCocycle2`, `IsCoboundary2`, `H2TwoClasses` copied verbatim from I6Base) | `h2TwoClasses_of_card_two` (any discrete group of order 2), `card_absoluteGaloisGroup_real : Nat.card G_ℝ = 2`, `discreteTopology_absoluteGaloisGroup_real`, `h2TwoClasses_real` | compiles, standard axioms |
| `LocalH2RealKernel.lean` (imports `ZInQKernel.HDecomp.Conductor.I6Base`; nothing copied) | `TBrauerPurityK.h2TwoClasses_real : PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℝ)`, `TBrauerPurityK.localH2CardC_iff` | compiles, standard axioms |
| `KummerEtale.lean` | `kummerPair`, `etale_adjoinRoot_X_pow_sub_C` | compiles, standard axioms |
| `KummerUnramified.lean` | `isUnramifiedAt_of_pow_eq`, `ramificationIdx_eq_one_of_pow_eq` | compiles, standard axioms |
| **`T2Kernel.lean`** (imports `ZInQKernel.HDecomp.Objects`) | **`TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}`**, `TBrauerPurityT2K.abhyankarDVR_objBridge : ObjBridge.AbhyankarDVR`, `abhyankarDVR_main`, `exists_pow_mul_eq`, `isSeparable_quotient_trans`, `isSeparable_quotient_of_inertiaDeg_eq_one` | compiles, standard axioms |
| **`T2Full.lean`** (Mathlib only; definition copied verbatim from `Leaves.lean`) | **`TBrauerPurity.abhyankarDVR : PkgI2.AbhyankarDVR.{u}`**, with the same proof as `T2Kernel.lean` | compiles, standard axioms |
| `AbhyankarBricks.lean` | `dvd_ramificationIdx_of_pow_eq`, `abhyankar_isScalarTower_RLM`, `abhyankar_finiteDimensional(_L)`, `abhyankar_isSeparable`, `abhyankar_isDedekindDomain`, `abhyankar_dvd_ramificationIdx`, `finrank_le_of_pow_eq`, `ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq`, `abhyankarDVR_conclusion_of_L_eq_K` | compiles, standard axioms |

How the real place is proved. Every element of `G_ℝ` is `1` or `s`, with `s² = 1`. The cocycle
identity forces `ε(1,z) = ε(x,1) = ε(1,1)`, and a cocycle is a coboundary iff `ε(1,1) = ε(s,s)`
(`isCoboundary2_iff_of_order2`). The class of `ε(x,y) = [x = s ∧ y = s]` is non-trivial, and the
difference of two non-trivial classes is a coboundary (checked by `decide` over `ZMod 2`). For
`G_ℝ` itself: `AlgebraicClosure ℝ ≃ₐ[ℝ] ℂ` via `IsAlgClosure.equiv`, so the finrank is 2 and the
extension is Galois, which gives `Nat.card = 2`. Discreteness comes from
`krullTopology_discreteTopology_of_finiteDimensional`.

How the `L = K` case of T2 is proved. `n ∣ e(Q)` follows from `(π)S = (t)ⁿ` and unique
factorization (`ramificationIdx_eq_normalizedFactors_count`, `normalizedFactors_pow`). Then
`∑_Q e f = rank_R S = [M:K] ≤ n` (`Ideal.sum_ramification_inertia_eq_finrank`, using that `S` is
finite and flat over the Dedekind ring `R`, and `IsIntegralClosure.rank`), so `e = n` and `f = 1`.
Finally `f = 1` gives `⊥ = ⊤` for the residue algebra (`Subalgebra.bot_eq_top_iff_finrank_eq_one`),
hence separability.

How T2 is proved (`abhyankarDVR_main`; global, with no completions or localizations of fields).
Notation: `A₁ = S_L`, `A₃ = S_M`, `Q'` a prime of `A₃` over `𝔪`, `Q = Q' ∩ A₁`, `e = e(Q|𝔪)`, and
`n = e·m` (by tameness).
* (a) `exists_pow_mul_eq` (no CRT needed). Take `ϖ ∈ Q \ Q²` and write `(ϖ) = Q·J₂` with `J₂ ⊄ Q`.
  Pick `b ∈ J₂ᵉ \ Q`. Then `b·π ∈ J₂ᵉ(π) = (ϖᵉ)·J₁`, so `bπ = ϖᵉa`. Moreover `a ∉ Q`, since
  otherwise `π ∈ Q^{e+1}` (by `Ideal.IsPrime.mul_mem_pow`), contradicting `count_Q(π) = e`
  (`ramificationIdx_eq_normalizedFactors_count`).
* (b) Put `w = b tᵐ/ϖ ∈ M`. Then `wᵉ = u := bᵉ⁻¹a ∈ A₁ \ Q`. Let `L₁ = L(w)` and
  `A₂ = integralClosure A₁ L₁`. Then `A₁ → A₂` is unramified at `P = Q' ∩ A₂`
  (`isUnramifiedAt_of_pow_eq`, via the different ideal).
* (c) `e(Q'|P)·f(Q'|P) ≤ [M:L₁] ≤ m`, using Mathlib's deprecated `Ideal.sum_ramification_inertia`
  and the fact that `t^m ∈ L₁`. Applying `Ideal.ramificationIdx_tower` twice, together with
  `ramificationIdx_eq_one`, gives `e(Q'|𝔪) = e·e(Q'|P)`. Since `n ∣ e(Q'|𝔪)`
  (`abhyankar_dvd_ramificationIdx`), `m ∣ e(Q'|P)`. Hence `e(Q'|P) = m`, `f(Q'|P) = 1`, and
  `e(Q'|𝔪) = n`.
* (d) Residue fields. `κ(P)/κ(Q)` is separable because `P` does not divide the different
  (`dvd_differentIdeal_of_not_isSeparable`). `κ(Q')/κ(P)` is separable because `f = 1`. `κ(Q)/k` is
  separable by tameness. Transitivity finishes (`isSeparable_quotient_trans`).

## 4. What remains, with the missing infrastructure (VERIFIED by grep of Mathlib v4.35 unless marked)

T2 is done. Mathlib itself has no notion of tame ramification and no Abhyankar lemma (grep for
"abhyankar", "tamely": no hits in RingTheory); the files here could be upstreamed.

**T1 (deep).** The SGA 1 X 3.4 and Stacks 0BMB proofs reduce, via Zariski's Main Theorem (Mathlib
has `RingTheory/ZariskisMainTheorem.lean`), to a finite map onto a regular local ring. They then
need two things.
* Normal of dimension 2 implies Cohen–Macaulay (Serre's criterion), and Auslander–Buchsbaum gives
  "CM finite over regular implies flat". Mathlib has depth (`RingTheory/Depth/`) and projective
  dimension of regular-sequence quotients, but neither Serre's criterion nor Auslander–Buchsbaum.
* The branch locus of a finite flat map is cut out by the discriminant, and the reduction from
  dimension ≥ 3 to dimension 2 goes through SGA 2-style local Lefschetz or purity arguments. None
  of this is in Mathlib.

Even the dimension-1 case needs "flat + unramified at `q` ⇒ `FormallyEtale R S_q`" for an
essentially-finite-type localization. Mathlib has
`Algebra.Etale.of_formallyUnramified_of_flat` only under finite presentation, plus
`etaleLocus_eq_unramifiedLocus_inter_smoothLocus`. Tau Ceti's dimension ≤ 2 purity and the Stacks
formalization (prereq-survey.md) are not available here.

**T14 and T15 at `ℚ_p` (deep).** Both need class field theory: global for T14, local for T15
(`inv : Br ℚ_p ≅ ℚ/ℤ` or Tate local duality). They also need a Kummer bridge on cochains,
`H²(G_K, ℤ/2) ≅ Br(K)[2]`, which requires crossed-product algebras. Mathlib v4.35 has
`BrauerGroup` (definition only), Hilbert 90 for finite Galois groups
(`RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`), and no crossed products (grep:
no hits). Glue that does not need the literature includes "every continuous `ZMod 2`-cocycle on a
profinite group is inflated from a finite quotient". Tau Ceti's `brLocalization_injective`,
`sumLocalInv_brLocalization_eq_zero` and `h2MuEquivZMod` (prereq-survey.md) are the natural sources
once the Kummer bridge exists.

## 5. Reproduction

```
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
lake env lean scratch/t-brauer-purity/LocalH2Real.lean
lake env lean scratch/t-brauer-purity/LocalH2RealKernel.lean   # needs the ZInQKernel oleans
lake env lean scratch/t-brauer-purity/KummerEtale.lean
lake env lean scratch/t-brauer-purity/KummerUnramified.lean
lake env lean scratch/t-brauer-purity/AbhyankarBricks.lean
lake env lean scratch/t-brauer-purity/T2Full.lean      # about 1 min
lake env lean scratch/t-brauer-purity/T2Kernel.lean    # needs the ZInQKernel oleans
```
Each ends with `#print axioms`, which reports `[propext, Classical.choice, Quot.sound]`.
