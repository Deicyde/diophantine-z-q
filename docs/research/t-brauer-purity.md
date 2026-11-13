# t-brauer-purity: textbook leaves T1, T2, T14, T15

Status: research note (task t-brauer-purity, 2026-11-12). Lean companion: `scratch/t-brauer-purity/`
(results log `log.md`). Base 01267822 (origin/wip/integrate-w34b). No file under `ZInQKernel/`,
`blueprint/`, or another task's notes was edited.

Marks: **VERIFIED** (read in a source named here, computed, or compiled), **STANDARD** (published,
with reference), **SPECULATIVE** (an assessment). There is no network on this host, so theorem numbers
given from memory are **UNVERIFIED**.

## 1. Verdict

None of the four leaves is fully proved. Here is what was proved (all VERIFIED: compiled with
`lake env lean`, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`):

1. **T15, real place: proved.** `H2TwoClasses (Field.absoluteGaloisGroup ℝ)` is now a theorem,
   stated over the kernel's own definition `PkgI6.H2TwoClasses`
   (`scratch/t-brauer-purity/LocalH2RealKernel.lean`, which imports
   `ZInQKernel.HDecomp.Conductor.I6Base`):
   `TBrauerPurityK.h2TwoClasses_real`. Consequently
   `TBrauerPurityK.localH2CardC_iff : PkgI6.LocalH2CardC ↔ ∀ p [Fact p.Prime],
   PkgI6.H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])`. So leaf T15 reduces to its finite-place
   half, and its real conjunct becomes glue.
2. **T2 (Abhyankar, DVR form): the case `L = K` is proved, along with the lower half in general.**
   `scratch/t-brauer-purity/AbhyankarBricks.lean` uses the leaf's instance context verbatim:
   * `abhyankarDVR_conclusion_of_L_eq_K`: the leaf's exact conclusion (`e(Q|𝔪) = n` and a
     separable residue extension, with the leaf's quotient-algebra instance) when `L = K`. In other
     words, adjoining an `n`-th root of a uniformizer, with `n` invertible, is totally ramified with
     `f = 1`. The proof uses `ramificationIdx_eq_and_inertiaDeg_eq_one_of_pow_eq`, which gives
     `e = m` and `f = 1`.
   * `abhyankar_dvd_ramificationIdx`: for general `L`, `n ∣ e(Q|𝔪)` for every prime `Q` of
     `integralClosure R M` over `𝔪`. This is the lower half of the conclusion and needs no
     tameness.
   * `abhyankar_finiteDimensional`, `abhyankar_isSeparable`, `abhyankar_isDedekindDomain`: the
     leaf's hypotheses force `M/K` to be finite and separable, so `integralClosure R M` is a
     Dedekind domain.
   * `dvd_ramificationIdx_of_pow_eq` (general): over a DVR `R` with uniformizer `π`, if `tⁿ = π`
     holds in a Dedekind `R`-algebra `S` with `𝔪S ≠ ⊥`, then `n` divides the ramification index of
     every prime of `S` over `𝔪`.
   * `scratch/t-brauer-purity/KummerUnramified.lean`, `isUnramifiedAt_of_pow_eq` and
     `ramificationIdx_eq_one_of_pow_eq`. Setting: `A` Dedekind, `B` its integral closure in a
     finite separable `L = K(w)`, with `wᵉ = u ∈ A` and `e ≥ 1` invertible. Conclusion: `A → B` is
     unramified, with `e(P) = 1`, at every prime `P` of `B` with `u ∉ P`. The proof uses Mathlib's
     different ideal (`dvd_differentIdeal_iff`, `aeval_derivative_mem_differentIdeal`). This is the
     "unit radicand" step of Abhyankar's lemma in global Dedekind form.
   * `scratch/t-brauer-purity/KummerEtale.lean`, `etale_adjoinRoot_X_pow_sub_C`: for any
     commutative ring `A`, `e ≥ 1` invertible and `u` a unit, `A[X]/(Xᵉ − u)` is étale over `A`
     (a standard étale pair). This is the same step in étale form.
3. **T1 (Zariski–Nagata purity) and T14 (Brauer–Hasse–Noether with reciprocity): nothing proved.**
   The finite-place half of T15 is also unproved. §3 explains why: these are deep theorems, and the
   infrastructure they need is missing from Mathlib v4.35 (VERIFIED by grep).
4. **No bridge from Tau Ceti or the Stacks project.** Neither source tree is on this host, and there
   is no network, so the task rule that a bridge counts only if its source compiles here rules them
   out (VERIFIED: searched `~/*`, `~/*/*`).
5. **Statement audit: all five Props are correct as stated** (§2). I found no vacuity, no
   over-strength, and no mismatch with the published statements.

**Recommendation for the announcement.** Glue uses only the finite-place uniqueness half of T15:
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

**T2, `PkgI2.AbhyankarDVR`.** I checked that the statement is true, not just well-typed. Let
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

## 4. What remains, with the missing infrastructure (VERIFIED by grep of Mathlib v4.35 unless marked)

**T2 (closest to done; SPECULATIVE estimate: 300–500 lines of plumbing on top of §3).** A global
proof that avoids completions and localizations. Notation: `A₁ = S_L`, `A₂ = S_{L(w)}`,
`A₃ = S_M` (integral closures of `R`). Every nonzero prime of each `Aᵢ` lies over `𝔪`.
* (a) Fix `Q'` in `A₃` over `𝔪`, and let `Q = Q' ∩ A₁`, `e = e(Q|𝔪)` (so `e ∣ n`), `m = n/e`.
  Choose `ϖ ∈ A₁` with `(ϖ) = Q`, using CRT in the semilocal Dedekind `A₁`
  (`IsDedekindDomain.exists_forall_sub_mem_ideal`). Then `π = uϖᵉ` with `u ∈ A₁ \ Q`. **Open**:
  ideal arithmetic only.
* (b) Put `w = t^m/ϖ ∈ A₃`, so `wᵉ = u`. Then `A₁ → A₂` is unramified at every prime over `Q`.
  **Proved** (`isUnramifiedAt_of_pow_eq`), once `A₂` is shown to be the integral closure of `A₁` in
  `L(w)` (transitivity of integrality).
* (c) For `P = Q' ∩ A₂`, `e(Q'|P)·f(Q'|P) ≤ [M : L(w)] ≤ m`. This uses
  `Ideal.sum_ramification_inertia_eq_finrank` and `IsIntegralClosure.rank` (a semilocal Dedekind
  `A₂` is a PID), and `M = L(w)(t)` with `t^m = wϖ ∈ L(w)` (as in `finrank_le_of_pow_eq`). The
  divisibility `n ∣ e(Q'|𝔪) = e(Q'|P)·1·e` is **proved** (`abhyankar_dvd_ramificationIdx` together
  with `Ideal.ramificationIdx_tower`, which needs flatness: a torsion-free module over a Dedekind
  domain is flat, an existing instance). It gives `m ∣ e(Q'|P)`, hence `e(Q'|P) = m` and
  `f(Q'|P) = 1`, so `e(Q'|𝔪) = n`.
* (d) Residue fields: `κ(Q') = κ(P)` (`f = 1`), `κ(P)/κ(Q)` is separable by (b)
  (`Algebra.isUnramifiedAt_iff_map_eq`), and `κ(Q)/k` is separable by tameness, so transitivity
  finishes.
* Remaining plumbing: the `Algebra` instances `A₁ → A₂ → A₃` with their scalar towers and
  `LiesOver` instances, and the residue-field towers.

Mathlib has no notion of tame ramification and no Abhyankar lemma (grep for "abhyankar", "tamely":
no hits in RingTheory).

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
```
Each ends with `#print axioms`, which reports `[propext, Classical.choice, Quot.sound]`.
