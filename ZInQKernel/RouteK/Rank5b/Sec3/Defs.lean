import ZInQKernel.RouteK.Rank5b.Row5b

/-!
# Route K, row 5b, §§2–3: Rédei's `g`, the genus sum `T_5b` and the hypothesis `CertifiedRankTYZ`

`docs/research/tyz-5b.md`, Notation and §2. Everything is a function of the bits `a_ij`, `y_i`,
`z_i` only.

Generic setting: a finite index type `ι` (the primes of `n`), bits `a : ι → ι → 𝔽₂` and
`y z : ι → 𝔽₂`.

* `lapl a U`: the Laplacian of the bits on `U ⊆ ι`, `L_ij = a_ij` (`i ≠ j`), `L_ii = Σ_{k ∈ U, k ≠ i} a_ik`
  (Smith's `A_Rows[U, U]`; `lapl a univ` is `Lmat`);
* `kappa a B ρ = κ_ρ(B) = det L_B[B∖ρ, B∖ρ]`;
* `redeiG a y z B = g(B)`, by Rédei's formulas (tyz-5b Proposition 2.3):
  `g(B) = κ(B)` if `y(B) = 1` and `g(B) = Σ_{ρ∈B} z_ρ κ_ρ(B)` if `y(B) = 0`. For `y(B) = 1`,
  `κ(B)` is the common value of the `κ_ρ(B)` (Lemma 2.2(1), `redeiG_eq_kappa`); the definition writes it
  as `Σ_ρ y_ρ κ_ρ(B)`, which equals it because `Σ_ρ y_ρ = y(B) = 1`, so that no choice of `ρ` is needed;
* `genusSum5b a y z = T_5b`: the sum, over the set partitions `π` of `ι` (Mathlib's `Finpartition`)
  with exactly one block of class 7, exactly one block of class 3 and no block of class 5, of
  `Π_{B∈π} g(B)`. The class of a block `B` is that of `d_B` mod 8: `1, 5, 7, 3` for
  `(y(B), z(B)) = (0,0), (0,1), (1,0), (1,1)`.

For an odd number `d`: `gBit d B` and `T5b d` (classes read off `Π_{p∈B} p mod 8`; `T5b_eq_genusSum5b`
identifies it with `genusSum5b` of the bits), and the hypothesis `CertifiedRankTYZ`.
-/

namespace ZInQ.RouteK.Rank5b

open Matrix

namespace Sec3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Laplacian of the bits `a` on `U`: `L_ij = a_ij` for `i ≠ j`, `L_ii = Σ_{k ∈ U, k ≠ i} a_ik`.
Restricted to `U × U` it is Smith's `A_Rows[U, U]` (tyz-5b Notation, `L_B`). -/
def lapl (a : ι → ι → ZMod 2) (U : Finset ι) : Matrix ι ι (ZMod 2) := fun i j =>
  if i = j then ∑ k ∈ U.erase i, a i k else a i j

/-- `κ_ρ(B) = det L_B[B∖ρ, B∖ρ]` (tyz-5b §2.1, Consequences). -/
noncomputable def kappa (a : ι → ι → ZMod 2) (B : Finset ι) (ρ : ι) : ZMod 2 :=
  ((lapl a B).submatrix (fun x : ↥(B.erase ρ) => (x : ι)) (fun x : ↥(B.erase ρ) => (x : ι))).det

/-- **Rédei's `g`** (tyz-5b Proposition 2.3, as a function of the bits): `g(B) = κ(B)` if
`y(B) = 1` (written `Σ_ρ y_ρ κ_ρ(B)`, see the module docstring), and `g(B) = Σ_{ρ∈B} z_ρ κ_ρ(B)` if
`y(B) = 0`. -/
noncomputable def redeiG (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) (B : Finset ι) : ZMod 2 :=
  if ∑ i ∈ B, y i = 1 then ∑ ρ ∈ B, y ρ * kappa a B ρ else ∑ ρ ∈ B, z ρ * kappa a B ρ

/-- The condition on a set partition in `T_5b`: exactly one block of class 7
(`(y(B), z(B)) = (1, 0)`), exactly one block of class 3 (`(1, 1)`), and no block of class 5
(`(0, 1)`), so all other blocks have class 1. -/
def Admissible5b (y z : ι → ZMod 2) (P : Finpartition (Finset.univ : Finset ι)) : Prop :=
  (P.parts.filter fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 0).card = 1 ∧
  (P.parts.filter fun B => ∑ i ∈ B, y i = 1 ∧ ∑ i ∈ B, z i = 1).card = 1 ∧
  ∀ B ∈ P.parts, ¬(∑ i ∈ B, y i = 0 ∧ ∑ i ∈ B, z i = 1)

instance (y z : ι → ZMod 2) (P : Finpartition (Finset.univ : Finset ι)) :
    Decidable (Admissible5b y z P) := by
  unfold Admissible5b; infer_instance

/-- **The genus sum of row 5b** (tyz-5b Notation): `T_5b = Σ_π Π_{B∈π} g(B)` over the set partitions
`π` of `ι` with one block of class 7, one block of class 3 and all other blocks of class 1. -/
noncomputable def genusSum5b (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset ι),
    if Admissible5b y z P then ∏ B ∈ P.parts, redeiG a y z B else 0

end Sec3

open Sec3

/-! ### The data of an odd number -/

/-- Rédei's `g(B) = #2Cl(ℚ(√−d_B)) mod 2` for a set `B` of primes of `d`, by Rédei's formulas
(tyz-5b Proposition 2.3) in the bits `aBit d`, `yBit d`, `zBit d`. -/
noncomputable def gBit (d : ℕ) (B : Finset d.primeFactors) : ZMod 2 :=
  redeiG (aBit d) (yBit d) (zBit d) B

/-- `d_B = Π_{p ∈ B} p`. -/
def dProd {d : ℕ} (B : Finset d.primeFactors) : ℕ := ∏ p ∈ B, (p : ℕ)

/-- The condition of `T_5b(d)` on a set partition of the primes of `d`, by residues mod 8: exactly
one block `B` with `d_B ≡ 7`, exactly one with `d_B ≡ 3`, and all blocks `≡ 7, 3` or `1 (mod 8)`. -/
def Admissible5bNat (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) : Prop :=
  (P.parts.filter fun B => dProd B % 8 = 7).card = 1 ∧
  (P.parts.filter fun B => dProd B % 8 = 3).card = 1 ∧
  ∀ B ∈ P.parts, dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1

instance (d : ℕ) (P : Finpartition (Finset.univ : Finset d.primeFactors)) :
    Decidable (Admissible5bNat d P) := by
  unfold Admissible5bNat; infer_instance

/-- **The genus sum of row 5b** for `d` (tyz-5b Notation; TYZ's coefficient of `τ(1/2)`, tyz-5b §1.2):
`T_5b(d) = Σ_π Π_{B∈π} g(d_B)` over the set partitions of the primes of `d` into one block with
`d_B ≡ 7`, one block with `d_B ≡ 3` and blocks with `d_B ≡ 1 (mod 8)`. In Smith's notation
`T_5b(d) = Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀) g(d₁) 𝓛(d/d₀d₁)`. -/
noncomputable def T5b (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5bNat d P then ∏ B ∈ P.parts, gBit d B else 0

end ZInQ.RouteK.Rank5b
