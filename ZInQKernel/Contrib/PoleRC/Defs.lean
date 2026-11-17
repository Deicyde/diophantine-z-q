import Mathlib
import ZInQKernel.Hypotheses.PoleManuscript

/-!
# Theorem 5.2 from Theorem 5.3: the explicit 2-Selmer system of `E_ℓ` and `CR_M`

Fork issue #83 (task pc-from-rc), following `diophantine_zq.tex` Section 5, "The exact descent
reduction" (lines 1019–1074) and the closing paragraph (lines 1107–1121).

* `LocM K ℓ a b`: the Kummer class `(a, b)`, in the manuscript's Kummer coordinates
  `(x + 3ℓ, x − ℓ)` (line 1061), is in the image of `E_ℓ(K)`, written in "x-form" as in
  Route K's `ZInQ.RouteK.Selmer.Loc`: either `a, b` are squares (the class of `O`), or some
  `x ∈ K` makes `(x + 3ℓ)/a`, `(x − ℓ)/b` and `x/(ab)` squares (zero allowed; the three
  two-torsion points give the classes `(ℓ, 1)`, `(3, −ℓ)`, `(3ℓ, −ℓ)`).
* `SelM ℓ`: the explicit 2-Selmer system of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`: pairs of squarefree
  integers whose class is locally in the Kummer image over `ℝ` and every `ℚ_p`.
* `CRM`: the converse input in the form the reduction uses: for `ℓ` in the domain of Theorem 5.3,
  if `#SelM ℓ = 8` (dimension three) and `(β, 1) ∈ SelM ℓ`, the class `(β, 1)` is the class of a
  rational point.
* `SimultaneousConstruction`: the simultaneous construction of `n` and `nθ`
  (lines 1033–1074), which the manuscript attributes to its supplementary files S11–S12.
-/

namespace ZInQ.Manuscript.PoleRC

/-- **The Kummer image of `E_ℓ(K)` in x-form.** For `a, b ≠ 0` in a field `K` of characteristic
not two and `ℓ ≠ 0`, `LocM K ℓ a b` says that the class of `(a, b)` in `(K*/K*²)²` is the image
of a point of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` under the Kummer map in the manuscript's
coordinates `(x + 3ℓ, x − ℓ)` (`diophantine_zq.tex` line 1061): either `a` and `b` are squares
(the point `O`), or there is `x ∈ K` with `(x + 3ℓ)/a`, `(x − ℓ)/b` and `x/(ab)` squares (zero
allowed). The analogue for the congruent number curves is `ZInQ.RouteK.Selmer.Loc`. -/
def LocM (K : Type*) [Field K] (ℓ a b : K) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : K, IsSquare ((x + 3 * ℓ) / a) ∧ IsSquare ((x - ℓ) / b) ∧ IsSquare (x / (a * b))

/-- **The explicit 2-Selmer system of `E_ℓ`** (`diophantine_zq.tex` lines 1033–1074): the pairs
`(a, b)` of squarefree integers (signs allowed) whose class is in the local Kummer image over `ℝ`
and over every `ℚ_p`. Each square class of `ℚ*` is written by its squarefree integer
representative, so this is the textbook `Sel₂(E_ℓ/ℚ) ⊆ H¹(ℚ, E_ℓ[2]) ≅ (ℚ*/ℚ*²)²`
(Silverman X.1.4); its dimension three is `ncard = 8`. Analogue of `ZInQ.RouteK.Selmer.Sel2`. -/
def SelM (ℓ : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ LocM ℝ ℓ ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], LocM ℚ_[p] ℓ ab.1 ab.2}

/-- **`CR_M`: dimension three with the class `(β, 1)` gives a rational point in that class.**
For positive squarefree `ℓ ≡ 11 (mod 12)` (the domain of Theorem 5.3), if the explicit
2-Selmer system of `E_ℓ` has dimension three (`#SelM ℓ = 8`) and contains `(β, 1)`, then
`(β, 1)` is the Kummer class of a rational point of `E_ℓ`.

This is how the manuscript uses Theorem 5.3 (lines 1107–1110: "Applying Theorem 5.3 to both
`n` and `nθ`, Lemma 5.5 gives rank one and finite Sha, hence `Ш[2] = 0`. The Kummer class is then
represented by actual rational points"), together with Lemma 5.4. It is GLUE: it follows from
Theorem 5.3 (`Manuscript.RestrictedConverse`), Lemma 5.4 and Lemma 5.5; see
`ZInQKernel/Contrib/PoleRC/CRM.lean`. -/
def CRM : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (SelM ℓ).ncard = 8 →
    ∀ β : ℤ, (β, 1) ∈ SelM ℓ → LocM ℚ ℓ β 1

/-- **The simultaneous construction** (`diophantine_zq.tex` lines 1033–1074). Let `β, θ` be
positive squarefree with `β ≡ 17`, `θ ≡ 1 (mod 24)`, coprime, each a square modulo every prime of
the other. Then there is `n > 0` with `nθ` squarefree, `n ≡ 11 (mod 12)`, such that the explicit
2-Selmer systems of `E_n` and `E_{nθ}` both have dimension three and contain `(β, 1)`.

ELLIOT: the manuscript attributes this to its supplementary files S11–S12 (lines 1033–1035) and
prints only the matrix conditions (the matrix `K`, `ker K = ⟨1, 1_{supp β}⟩`, `λ ∉ im K`, the
slots, the rank-one correction, the Boolean assignment realized through reciprocity, CRT and
Dirichlet) and the dimension-three count (lines 1061–1074). GLUE (number theory); its proof is
not in Lean. -/
def SimultaneousConstruction : Prop :=
  ∀ β θ : ℕ, Squarefree β → Squarefree θ → β % 24 = 17 → θ % 24 = 1 → Nat.Coprime β θ →
    (∀ p : ℕ, p.Prime → p ∣ θ → IsSquare (β : ZMod p)) →
    (∀ p : ℕ, p.Prime → p ∣ β → IsSquare (θ : ZMod p)) →
    ∃ n : ℕ, 0 < n ∧ Squarefree (n * θ) ∧ n % 12 = 11 ∧
      (SelM n).ncard = 8 ∧ ((β : ℤ), 1) ∈ SelM n ∧
      (SelM (n * θ)).ncard = 8 ∧ ((β : ℤ), 1) ∈ SelM (n * θ)

end ZInQ.Manuscript.PoleRC
