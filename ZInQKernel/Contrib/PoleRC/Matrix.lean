import ZInQKernel.Contrib.PoleRC.Defs

/-!
# The matrix conditions of the simultaneous construction (`diophantine_zq.tex` lines 1036–1074)

For the prime support `q₁, …, q_k` of `ℓ`, with additive Legendre symbols `[a/q] ∈ 𝔽₂`:
`s_i = [−1/q_i]`, `λ_i = [3/q_i]`, `(Kv)_i = Σ_{j ≠ i} [q_j/q_i](v_j + v_i)` (line 1038).
`MatrixConditions ℓ β`: `ker K = ⟨1, 1_{supp β}⟩` (of dimension two) and `λ ∉ im K` (line 1040).

* `DimThreeCount` (GLUE): the matrix conditions give `#SelM ℓ = 8` and `(β, 1) ∈ SelM ℓ`
  (lines 1061–1074).
* `MatrixRealization` (GLUE, ELLIOT: S11–S12): `n` with the matrix conditions for `n` and `nθ`
  (lines 1033–1060).
* `simultaneousConstruction_of`: `SimultaneousConstruction` from the two.
-/

namespace ZInQ.Manuscript.PoleRC

open Classical in
/-- The additive Legendre symbol `[a/q] ∈ 𝔽₂`: `0` if `a` is a square modulo `q`, else `1`. -/
noncomputable def lsym (a : ℤ) (q : ℕ) : ZMod 2 := if IsSquare (a : ZMod q) then 0 else 1

/-- The prime support of `ℓ`, as an index type. -/
abbrev Supp (ℓ : ℕ) := {q // q ∈ ℓ.primeFactors}

/-- The manuscript's matrix `K` (line 1038): `(Kv)_i = Σ_{j ≠ i} [q_j/q_i](v_j + v_i)`. -/
noncomputable def Kmat (ℓ : ℕ) : Matrix (Supp ℓ) (Supp ℓ) (ZMod 2) :=
  fun i j => if i = j then ∑ k ∈ Finset.univ.erase i, lsym (k : ℕ) i else lsym (j : ℕ) i

/-- `λ_i = [3/q_i]` (line 1037). -/
noncomputable def lam (ℓ : ℕ) : Supp ℓ → ZMod 2 := fun i => lsym 3 i

/-- `s_i = [−1/q_i]` (line 1037). -/
noncomputable def sgn (ℓ : ℕ) : Supp ℓ → ZMod 2 := fun i => lsym (-1) i

open Classical in
/-- `1_{supp β}`, the indicator of the primes of `β` in the support of `ℓ`. -/
noncomputable def oneB (ℓ β : ℕ) : Supp ℓ → ZMod 2 := fun i => if (i : ℕ) ∣ β then 1 else 0

/-- **The matrix conditions** (line 1040): `ker K = ⟨1, 1_{supp β}⟩`, of dimension two, and
`λ ∉ im K`. (`K 1 = 0` always.) -/
def MatrixConditions (ℓ β : ℕ) : Prop :=
  oneB ℓ β ≠ 0 ∧ oneB ℓ β ≠ 1 ∧ (Kmat ℓ).mulVec (oneB ℓ β) = 0 ∧
    (∀ v, (Kmat ℓ).mulVec v = 0 → v = 0 ∨ v = 1 ∨ v = oneB ℓ β ∨ v = 1 + oneB ℓ β) ∧
    ∀ u, (Kmat ℓ).mulVec u ≠ lam ℓ

/-- **The dimension-three count** (lines 1061–1074; GLUE). For positive squarefree
`ℓ ≡ 11 (mod 12)` and `β ∣ ℓ` with `β ≡ 1 (mod 8)`, the matrix conditions give
`#SelM ℓ = 8` and `(β, 1) ∈ SelM ℓ`.

The manuscript's argument: a Selmer class with positive second coordinate is
`(3^δ ∏ q_i^{u_i}, ∏ q_i^{v_i})`; the local conditions at the `q_i` and at three give
`Ku + diag(λ)v = δλ`, `(K + diag(s))v = 0`, `(λ + s)ᵗv = 0`, and the matrix conditions force
`v = 0`, `δ = 0`, `u ∈ ker K`: at most eight classes. The class `(β, 1)` is local everywhere
(`β ≡ 1 (mod 8)` is a square at two) and independent of the torsion. The shape of the
representative (no factor `2`, `a > 0`) comes from the local images at two and at the real place,
which the text does not spell out (ELLIOT); see `docs/research/pc-from-rc.md`. -/
def DimThreeCount : Prop :=
  ∀ ℓ β : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → β ∣ ℓ → β % 8 = 1 →
    MatrixConditions ℓ β → (SelM ℓ).ncard = 8 ∧ ((β : ℤ), 1) ∈ SelM ℓ

/-- **The realization of the matrix conditions** (lines 1033–1060; GLUE, ELLIOT). For `β, θ` as
produced by the squareclass bookkeeping, there is `n > 0`, `n ≡ 11 (mod 12)`, `nθ` squarefree,
`β ∣ n`, with the matrix conditions for both `n` and `nθ`.

ELLIOT: the manuscript attributes this to its supplementary files S11–S12 and prints a sketch:
`d − 1` auxiliary prime slots of type `(s, λ) = (0, 0)` and one slot `q₀` of type `(1, 1)`
(`d = ω(β)`), cross-block columns `e_i + e_d`, the rank-one correction `K♯ = K + λaᵗ`, the
nonsingular block `[[D₁, C₁], [C₁ᵗ, 0]]` with `1ᵗD₁1 = 1`, the free `q₀`-symbols toggling the new
diagonal entries for the support of `θ`, and the realization of one Boolean assignment by distinct
auxiliary primes through quadratic reciprocity, the Chinese remainder theorem and Dirichlet's
theorem. Not proved in Lean. -/
def MatrixRealization : Prop :=
  ∀ β θ : ℕ, Squarefree β → Squarefree θ → β % 24 = 17 → θ % 24 = 1 → Nat.Coprime β θ →
    (∀ p : ℕ, p.Prime → p ∣ θ → IsSquare (β : ZMod p)) →
    (∀ p : ℕ, p.Prime → p ∣ β → IsSquare (θ : ZMod p)) →
    ∃ n : ℕ, 0 < n ∧ Squarefree (n * θ) ∧ n % 12 = 11 ∧ β ∣ n ∧
      MatrixConditions n β ∧ MatrixConditions (n * θ) β

/-- **The simultaneous construction from the realization and the dimension-three count.** -/
theorem simultaneousConstruction_of (hR : MatrixRealization) (hD : DimThreeCount) :
    SimultaneousConstruction := by
  intro β θ hβ hθ hβ24 hθ24 hcop hβsq hθsq
  obtain ⟨n, hn, hnθ, hn12, hβn, hMn, hMnθ⟩ := hR β θ hβ hθ hβ24 hθ24 hcop hβsq hθsq
  have hθpos : 0 < θ := by omega
  have hnsf : Squarefree n := Squarefree.of_mul_left hnθ
  have hβ8 : β % 8 = 1 := by omega
  obtain ⟨h1, h2⟩ := hD n β hn hnsf hn12 hβn hβ8 hMn
  obtain ⟨h3, h4⟩ := hD (n * θ) β (Nat.mul_pos hn hθpos) hnθ
    (by rw [Nat.mul_mod, hn12, show θ % 12 = 1 by omega]) (hβn.mul_right θ) hβ8 hMnθ
  exact ⟨n, hn, hnθ, hn12, h1, h2, h3, h4⟩

end ZInQ.Manuscript.PoleRC
