import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.HoffsteinLuo

/-!
# Lane RC8: Bump–Friedberg–Hoffstein (a twist with a simple zero; a twist with nonzero value)

**Uses in the manuscript (11/5 text).** tex L1984–1992 (`ex:sec7-nonvanishing`, odd case): "Apply
Hoffstein–Luo [hl] in the even case, or Bump–Friedberg–Hoffstein [bfh] in the odd case, to the
actual curve `E^{(q₀)}`. Require their positive discriminant `d` to split at `S ∪ B ∪ {|q₀|}` and at
the conductor primes. Then `q₀d` has the prescribed original classes. ... The BFH clause used in the
odd case is the simple-zero clause." The statement proved there (L1978–1979): "In an odd filter
there is a simple-zero parameter, with no asserted prime-count bound." Appendix tables: BFH and
Hoffstein–Luo "Actual signed-prime twist with trivial character and arbitrary finite splitting
set" (L6791–6793). App F, proof of `ex:app-detector` (L8248–8256): "Apply clause (ii) of
[bfh, pp. 543–544] to its weight-two newform, with every old prime in the splitting set, to obtain
a negative fundamental discriminant `h_*` with `L(E^{(h_*)},1) ≠ 0`. Including two makes `h_*` odd
and excludes the extra-unit fields. Now add the primes of `h_*` to that set and apply clause (i) to
obtain a positive fundamental discriminant `D_w` with `L'(E^{(D_w)},1) ≠ 0`."

**The print** (D. Bump, S. Friedberg and J. Hoffstein, *Nonvanishing theorems for L-functions of
modular forms and their derivatives*, Invent. Math. 102 (1990), 543–618; read in the scan of the
journal pages 543–545). §0 Introduction, p. 543: "Let `M` be a positive integer. If `f` is a
normalized newform for `Γ₀(M)`, then the L-function with gamma factors attached has the form
`Λ(s, f) = (2π)^{-s}Γ(s)M^{s/2}L(s, f)`. It satisfies a functional equation `Λ(s, f) = εΛ(k - s, f)`,
where `ε = ±1` is naturally called the sign in the functional equation. ... If `D` is a fundamental
discriminant, let `χ_D` be the Dirichlet character with conductor `|D|` defined in terms of the
Kronecker symbol by `χ_D(n) = (D/n)`. ... It is known that `χ_D(-1) = sgn(D)`. Let
`L(s, f, χ_D) = ∑ χ_D(n)a(n)n^{-s}`, and let `Λ(s, f, χ_D) = (D²M)^{s/2}(2π)^{-s}Γ(s)L(s, f, χ_D)`.
This has analytic continuation as a function of `s`, and, provided `gcd(M, D) = 1`, satisfies the
functional equation `Λ(s, f, χ_D) = εχ_D(-M)Λ(k - s, f, χ_D)`."
**Theorem** (unnumbered, pp. 543–544). "Let `f` be cuspidal newform of even weight `k` with trivial
character for the group `Γ₀(M)`, and let `S` be a finite set of primes including all those dividing
`M`. Let `ε` denote the sign in the functional equation of `f`.
(i) There exists a quadratic field `ℚ(√D)` with `D` a fundamental discriminant, and `εD < 0`, such
that every prime in `S` splits in `ℚ(√D)`, and `L(s, f, χ_D)` has a simple zero at `s = k/2`.
(ii) There exists a quadratic field `ℚ(√D)` with `D` a fundamental discriminant, and `εD > 0`, such
that every prime in `S` splits in `ℚ(√D)`, and `L(k/2, f, χ_D) ≠ 0`."

The manuscript's "simple-zero clause" is (i). A statement check of clause (ii) against the
project's earlier predicate was posted on the project's issue #14 (verdict: consequence; the
display is existence, not "infinitely many", and gives the all-split local class; no CM or level
restriction); this file states the print itself, not that predicate.

**Use check.** In the odd case the curve `E^{(q₀)}` has root number `ε = -1`, so (i) gives `D` with
`-D < 0`, i.e. a **positive** fundamental discriminant, as the manuscript requires ✓; `S` must contain
the primes of the level (the conductor of `E^{(q₀)}`) ✓ ("and at the conductor primes"); all primes of
`S ∪ B ∪ {|q₀|}` split ✓; `L(s, f, χ_D)` has a simple zero at `s = 1`, which for the curve is
`ord_{s=1} L(E^{(q₀D)}, s) = 1` once `L(s, f, χ_D) = L(E^{(q₀)(D)}, s)` (`TwistDictionary`, GLUE; `D` is
prime to the level because every prime of the level splits) ✓. No prime-count bound is asserted in
the odd case ✓ (BFH gives none). In the App F detector `E` has root number `-1`: clause (ii) gives
`εD > 0`, i.e. `D = h_* < 0` ✓, with `L(E^{(h_*)}, 1) ≠ 0` ✓; `2 ∈ S` makes `h_*` odd (`h_* ≡ 1 mod 8`),
which excludes `ℚ(√-3)` and `ℚ(i)` ✓; clause (i) gives `εD < 0`, i.e. `D = D_w > 0` ✓, and a simple zero
gives `L'(E^{(D_w)}, 1) ≠ 0` ✓. The curve form is `BFHCurve`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 HeckeRing.GL2 Complex

/-- **Bump–Friedberg–Hoffstein, Theorem, clauses (i) and (ii)** (PRINT; Invent. Math. 102 (1990)
543–618, §0, pp. 543–544). For a newform `f` of even weight `k`, trivial character, level `M`,
with sign `ε = newformSign f` in its functional equation, and a finite set `S` of primes containing
every prime dividing `M`:
(i) some fundamental discriminant `D` with `εD < 0`, all primes of `S` split in `ℚ(√D)`, has
`L(s, f, χ_D)` with a simple zero at `s = k/2`;
(ii) some fundamental discriminant `D` with `εD > 0`, all primes of `S` split in `ℚ(√D)`, has
`L(k/2, f, χ_D) ≠ 0`.
Here `L(s, f, χ_D)` is the entire continuation of `∑ χ_D(n) aₙ n^{-s}` from `Re s > k/2 + 1`, and
`εD < 0` is written out for `ε = ±1`. -/
def BFHTheorem : Prop :=
  ∀ (M : ℕ) [NeZero M] (k : ℤ) (f : Newform M k) (hχ : f.χ = 1), 0 < k → Even k →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ M → p ∈ S) →
      (∃ D : ℤ, IsFundamentalDiscriminant D ∧
        (newformSign f hχ = 1 → D < 0) ∧ (newformSign f hχ = -1 → 0 < D) ∧
        (∀ p ∈ S, kronecker D p = 1) ∧
        ∃ F : ℂ → ℂ, IsEntireContinuation (twistCoeff (nfCoeff f) D) ((k : ℝ) / 2 + 1) F ∧
          analyticOrderAt F ((k : ℂ) / 2) = 1) ∧
      (∃ D : ℤ, IsFundamentalDiscriminant D ∧
        (newformSign f hχ = 1 → 0 < D) ∧ (newformSign f hχ = -1 → D < 0) ∧
        (∀ p ∈ S, kronecker D p = 1) ∧
        ∃ F : ℂ → ℂ, IsEntireContinuation (twistCoeff (nfCoeff f) D) ((k : ℝ) / 2 + 1) F ∧
          F ((k : ℂ) / 2) ≠ 0)

/-- **Bump–Friedberg–Hoffstein for an elliptic curve** (PRINT, composite: the form used at tex
L1985–1992 and in the App F detector, over the shared vocabulary `qtwist`, `AnalyticRank`,
`RootNumberAt`). Let `A/ℚ` be an elliptic curve whose `L`-function has the functional equation of
level `N` and sign `w` (so `N` is the conductor and `w` the root number), and let `S` be a finite set
of primes containing every prime dividing `N`. Then
(i) some fundamental discriminant `D` with `wD < 0`, all primes of `S` split in `ℚ(√D)`, has
`ord_{s=1} L(A^{(D)}, s) = 1`;
(ii) some fundamental discriminant `D` with `wD > 0`, all primes of `S` split, has
`ord_{s=1} L(A^{(D)}, s) = 0`.
This is `BFHTheorem` for the newform of `A` (`ModularNewform`), whose level is `N` and whose sign is
`w` (the level and sign of a functional equation of the nonzero `L(A, s)` are unique), with
`TwistDictionary` and `HasseConvergence` (GLUE); `Bridges.lean` proves the derivation. -/
def BFHCurve : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → ∀ (N : ℕ) (w : ℤ), RootNumberAt A N w →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) →
      (∃ D : ℤ, IsFundamentalDiscriminant D ∧ w * D < 0 ∧ (∀ p ∈ S, kronecker D p = 1) ∧
        AnalyticRank (qtwist A D) 1) ∧
      (∃ D : ℤ, IsFundamentalDiscriminant D ∧ 0 < w * D ∧ (∀ p ∈ S, kronecker D p = 1) ∧
        AnalyticRank (qtwist A D) 0)

end ZInQ.Manuscript.RC.PrintsAnalytic
