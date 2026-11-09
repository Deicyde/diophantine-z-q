import Mathlib

/-!
# Partial sums twisted by Dirichlet characters

Notation of plan step 4 (`docs/effective-dirichlet-plan.md`), for a Dirichlet character `χ`
modulo `q` and a residue class `a` modulo `q`:

* `twistedSum χ x = S_χ(x) = Σ_{n ≤ x} χ(n) Λ(n) / n`;
* `classSum a x = S_a(x) = Σ_{n ≤ x, n ≡ a (mod q)} Λ(n) / n`;
* `recipSum χ y = Σ_{m ≤ y} χ(m) / m`;
* `logSum χ x = T(x) = Σ_{n ≤ x} χ(n) log n / n`.

All sums run over `n ∈ Ioc 0 ⌊x⌋₊`, as in `Chebyshev.psi`.
-/

namespace ZInQ.Progressions

open Finset
open ArithmeticFunction hiding log

variable {q : ℕ}

/-- `S_χ(x) = Σ_{n ≤ x} χ(n) Λ(n) / n`. -/
noncomputable def twistedSum (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * Λ n / n

/-- `S_a(x) = Σ_{n ≤ x, n ≡ a (mod q)} Λ(n) / n`. -/
noncomputable def classSum (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊ with ((n : ℕ) : ZMod q) = a, Λ n / n

/-- `Σ_{m ≤ y} χ(m) / m`. -/
noncomputable def recipSum (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  ∑ m ∈ Ioc 0 ⌊y⌋₊, χ m / m

/-- `T(x) = Σ_{n ≤ x} χ(n) log n / n`. -/
noncomputable def logSum (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, χ n * Real.log n / n

lemma classSum_nonneg (a : ZMod q) (x : ℝ) : 0 ≤ classSum a x :=
  sum_nonneg fun _ _ ↦ div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)

end ZInQ.Progressions
