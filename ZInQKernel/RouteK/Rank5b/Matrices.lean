import ZInQKernel.RouteK.Selmer.Prop0
import ZInQKernel.RouteK.Rank5b.Bordered

/-!
# Route K, row 5b: the data `a_ij`, `y_i`, `z_i` and Smith's matrices `L`, `M₁`, `M_5b`

`docs/research/tyz-5b.md`, Notation. For an odd squarefree `n` with prime set `P = n.primeFactors`:

* `a_ij = (p_j/p_i)₊ ∈ 𝔽₂` (`aBit`), `y_i = (−1/p_i)₊` (`yBit`), `z_i = (2/p_i)₊` (`zBit`);
* `L` (Smith's `A`, `Lmat`): `L_ij = a_ij` for `i ≠ j`, `L_ii = Σ_{j≠i} a_ij`;
* `M₁ = [[L + Lᵀ, Lᵀ], [L, D_z]]` (`M1`, indexed by `P ⊕ P`) and
  `M_5b = [[M₁, (0, y)], [(0, y)ᵀ, 0]]` (`M5b`, indexed by `(P ⊕ P) ⊕ Unit`).

The bits are those of the Lean Selmer system: `a_ij = [p_j/p_i]` is the bit `bit p_j p_i` of
`natConfig n`, `y = λ` and `z = μ` (`natConfig_bit_eq_aBit`, `natConfig_lam_eq_yBit`,
`natConfig_mu_eq_zBit`). The matrices are also defined for any configuration `𝒞` (`Config.Lc`,
`Config.M1c`), and `M1 n` is `M1c` of `natConfig n` (`M1_eq_M1c`).

`M₁` is symmetric by its block shape (`M1_transpose`); quadratic reciprocity
(`aBit_add_aBit`) gives the off-diagonal entries `(L + Lᵀ)_ij = y_i y_j` (`Lmat_add_transpose_apply`).
-/

namespace ZInQ.RouteK.Rank5b

open Matrix

/-! ### The configuration-level matrices -/

namespace Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝒞 : RouteK.Config ι)

/-- Smith's matrix `L` of a configuration: `L_xy = [y/x]` for `x ≠ y`, `L_xx = Σ_{y≠x} [y/x]`. -/
def Lc : Matrix ι ι (ZMod 2) := fun x y =>
  if x = y then ∑ z ∈ Finset.univ.erase x, 𝒞.bit z x else 𝒞.bit y x

/-- Smith's matrix `M₁ = [[L + Lᵀ, Lᵀ], [L, D_μ]]` of a configuration. -/
def M1c : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks (Lc 𝒞 + (Lc 𝒞)ᵀ) (Lc 𝒞)ᵀ (Lc 𝒞) (diagonal 𝒞.mu)

/-- Smith's matrix `M_5b`: `M₁` bordered by `(0, λ)`. -/
def M5bc : Matrix ((ι ⊕ ι) ⊕ Unit) ((ι ⊕ ι) ⊕ Unit) (ZMod 2) :=
  border (M1c 𝒞) (Sum.elim 0 𝒞.lam)

theorem M1c_transpose : (M1c 𝒞)ᵀ = M1c 𝒞 := by
  rw [M1c, fromBlocks_transpose, transpose_add, transpose_transpose, add_comm,
    diagonal_transpose]

end Config

/-! ### The data of an odd squarefree number -/

/-- `a_ij = (p_j/p_i)₊`: `0` if `p_j` is a square mod `p_i`, `1` otherwise. -/
noncomputable def aBit (d : ℕ) (i j : d.primeFactors) : ZMod 2 := legBit (i : ℕ) ((j : ℕ) : ℤ)

/-- `y_i = (−1/p_i)₊ = [p_i ≡ 3 (mod 4)]`. -/
noncomputable def yBit (d : ℕ) (i : d.primeFactors) : ZMod 2 := lamBit (i : ℕ)

/-- `z_i = (2/p_i)₊ = [p_i ≡ ±3 (mod 8)]`. -/
noncomputable def zBit (d : ℕ) (i : d.primeFactors) : ZMod 2 := muBit (i : ℕ)

/-- Smith's matrix `L` (his `A`): `L_ij = a_ij` for `i ≠ j`, `L_ii = Σ_{j≠i} a_ij`; its rows sum
to zero. -/
noncomputable def Lmat (d : ℕ) : Matrix d.primeFactors d.primeFactors (ZMod 2) := fun i j =>
  if i = j then ∑ k ∈ Finset.univ.erase i, aBit d i k else aBit d i j

/-- Smith's matrix `M₁ = [[L + Lᵀ, Lᵀ], [L, D_z]]`, indexed by `P ⊕ P`. -/
noncomputable def M1 (d : ℕ) :
    Matrix (d.primeFactors ⊕ d.primeFactors) (d.primeFactors ⊕ d.primeFactors) (ZMod 2) :=
  fromBlocks (Lmat d + (Lmat d)ᵀ) (Lmat d)ᵀ (Lmat d) (diagonal (zBit d))

/-- Smith's matrix of row 5b, `M_5b = [[L + Lᵀ, Lᵀ, 0], [L, D_z, y], [0, yᵀ, 0]]`: `M₁` bordered
by the vector `(0, y)` and a zero corner, indexed by `(P ⊕ P) ⊕ Unit`. -/
noncomputable def M5b (d : ℕ) :
    Matrix ((d.primeFactors ⊕ d.primeFactors) ⊕ Unit)
      ((d.primeFactors ⊕ d.primeFactors) ⊕ Unit) (ZMod 2) :=
  border (M1 d) (Sum.elim 0 (yBit d))

/-- `M₁` is symmetric. -/
theorem M1_transpose (d : ℕ) : (M1 d)ᵀ = M1 d := by
  rw [M1, fromBlocks_transpose, transpose_add, transpose_transpose, add_comm, diagonal_transpose]

/-! ### Agreement with the Lean Selmer system -/

section natConfig

variable {d : ℕ} (hd : Odd d)

/-- `a_ij` is the bit `[p_j/p_i]` of `natConfig d`. -/
theorem natConfig_bit_eq_aBit (i j : d.primeFactors) : (natConfig d hd).bit j i = aBit d i j :=
  rfl

/-- `y = λ`. -/
theorem natConfig_lam_eq_yBit (i : d.primeFactors) : (natConfig d hd).lam i = yBit d i :=
  Selmer.natConfig_lam hd i

/-- `z = μ`. -/
theorem natConfig_mu_eq_zBit (i : d.primeFactors) : (natConfig d hd).mu i = zBit d i :=
  Selmer.natConfig_mu hd i

theorem Lmat_eq_Lc : Lmat d = Config.Lc (natConfig d hd) := rfl

theorem M1_eq_M1c : M1 d = Config.M1c (natConfig d hd) := by
  rw [M1, Config.M1c, ← Lmat_eq_Lc hd]
  congr 2
  funext i
  exact (natConfig_mu_eq_zBit hd i).symm

theorem M5b_eq_M5bc : M5b d = Config.M5bc (natConfig d hd) := by
  rw [M5b, Config.M5bc, ← M1_eq_M1c hd]
  congr 2
  funext i
  exact (natConfig_lam_eq_yBit hd i).symm

include hd in
/-- **Quadratic reciprocity** for the data: `a_ij + a_ji = y_i y_j` for `i ≠ j`. -/
theorem aBit_add_aBit {i j : d.primeFactors} (hij : i ≠ j) :
    aBit d i j + aBit d j i = yBit d i * yBit d j := by
  obtain ⟨hi, hi2⟩ := prime_ne_two_of_mem_primeFactors hd i.2
  obtain ⟨hj, hj2⟩ := prime_ne_two_of_mem_primeFactors hd j.2
  exact legBit_reciprocity hi hj hi2 hj2 fun h => hij (Subtype.ext h)

include hd in
/-- The off-diagonal entries of `L + Lᵀ` are `y_i y_j` (by reciprocity); its diagonal is `0`. -/
theorem Lmat_add_transpose_apply (i j : d.primeFactors) :
    (Lmat d + (Lmat d)ᵀ) i j = if i = j then 0 else yBit d i * yBit d j := by
  simp only [Matrix.add_apply, transpose_apply, Lmat]
  by_cases h : i = j
  · subst h; simp only [ite_true]; exact CharTwo.add_self_eq_zero _
  · simp only [h, Ne.symm h, ite_false]; exact aBit_add_aBit hd h

end natConfig

end ZInQ.RouteK.Rank5b
