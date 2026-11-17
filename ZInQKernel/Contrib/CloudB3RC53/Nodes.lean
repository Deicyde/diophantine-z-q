import ZInQKernel.Contrib.CloudB3RC53.Prints

/-!
# RC53 blueprint: the top-level nodes of the proof of Theorem 5.3

The top-level deduction of Theorem 5.3 (tex L1793–1797, L2593–2602, L5666–5741; restated at
L10862–10935) is:

1. **Root number.** Selmer parity gives `w(E_ℓ) = -1` (`RootNumberNode`, tex L1793–1797), so
   `L(E_ℓ, 1) = 0` (`CentralValueZeroNode`).
2. **Branch 1 / Branch 2** (`BranchPackageNode`, Sections 7–9 and Appendices E–G). Either the
   odd limit symbol is a unit at the empty configuration, and visibility (O.8) at `D = 1` gives
   `ord_{s=1} L(E_ℓ, s) = 1` directly (tex L2587–2592); or there is a final companion `k` with
   `L(E^{(k)}, 1) ≠ 0` and, for every precision `M` and binary dimension `b` chosen as in (5.10),
   the corrected coordinates `ũ_x` (`x ∈ 𝔽₂^b`) with the fixed-field clearing identity (5.9), the
   uniform upper bound `v₂ ũ_x(0) ≤ B` at `x ≠ 0` from (3.9), (3.4), (4.6), (4.7), and the
   base-zero lemma `ex:arith-base-zero`. This package is `FixedFieldPackage`.
3. **Missing address** (`MissingAddressNode`, tex L5666–5735, (5.10)–(5.11)): from the clearing
   identity alone, some `x ≠ 0` has `v₂(ũ_x(0) - ũ_0(0)) ≥ M - 2c`.
4. **Final deduction** (`FinalRankDeductionNode`, tex L5736–5741): if `L'(E/K, 1) ≠ 0` and
   `L(E^{(k)}, 1) ≠ 0`, then `ord_{s=1} L(E, s) = 1`.

The coordinates `ũ_x` live in `Λ[1/2]`, `Λ = ℤ₂[[t]]` (tex L5719–5721), and `f, d` in `𝒪[G]`,
where `𝒪` is the `2`-adic completion of `Λ_{(2)}` (Laurent series `Σ_{i ∈ ℤ} aᵢ tⁱ`, `aᵢ ∈ ℤ₂`,
`aᵢ → 0` as `i → -∞`) and `G = 𝔽₂^b` is the sign group. They are recorded by coefficients:
`CoordData.F g i` is the `tⁱ`-coefficient of the `g`-component of `f`, likewise `D` for `d`, and
`CoordData.u x j` is the `tʲ`-coefficient of `ũ_x`. The sign evaluation at the character `x` is
`signEval F x i = Σ_g (-1)^{⟨x, g⟩} F g i`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower Filter Topology

/-! ### Root number and the central value -/

/-- **Root number `-1`** (tex L1793–1797): for `ℓ` in the domain of Theorem 5.3,
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` gives root number `-1`. Proved from Dokchitser–Dokchitser
Theorem 1.8 (`rootNumberNode_proof`, `Assembly.lean`). -/
def RootNumberNode : Prop :=
  ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → RootNumber (Ecurve ℓ) (-1)

/-- **Root number `-1` forces `L(E, 1) = 0`** (tex L5740–5741, "`w(E) = -1` gives
`ord ≥ 1`"): every entire continuation `F` of `L(E, s)` occurring in a functional equation with
sign `-1` vanishes at `s = 1`. -/
def CentralValueZeroNode : Prop :=
  ∀ E : WeierstrassCurve ℚ, ∀ N : ℕ, 0 < N → ∀ F : ℂ → ℂ,
    (∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N F (2 - s) = (-1 : ℂ) * completedL N F s) →
    F 1 = 0

/-- **The final deduction** (tex L5736–5741, L10930–10935): with root number `-1`,
`L(E^{(k)}, 1) ≠ 0` and `ord_{s=1} L(E,s) L(E^{(k)},s) < 2` (that is, `L'(E/K, 1) ≠ 0` for
`K = ℚ(√k)`), `E` has analytic rank one. -/
def FinalRankDeductionNode : Prop :=
  ∀ (E : WeierstrassCurve ℚ) (k : ℚ), RootNumber E (-1) → AnalyticRank (qtwist E k) 0 →
    ¬ ProductOrderGeTwo E k → AnalyticRankOne E

/-! ### The coordinate data of the fixed-field determinant argument -/

/-- The sign `(-1)^{⟨x, g⟩}` of the character `x ∈ 𝔽₂^b` at `g ∈ G = 𝔽₂^b`. -/
def sgn {b : ℕ} (x g : Fin b → ZMod 2) : ℤ :=
  if (∑ i, x i * g i) = 0 then 1 else -1

/-- The `tⁱ`-coefficient of the sign evaluation at `x` of the group-ring element with
coefficients `F` (`F g i` = the `tⁱ`-coefficient of its `g`-component). -/
def signEval {b : ℕ} (F : (Fin b → ZMod 2) → ℤ → ℤ_[2]) (x : Fin b → ZMod 2) (i : ℤ) : ℤ_[2] :=
  ∑ g, (sgn x g : ℤ_[2]) * F g i

/-- Coefficient data at one precision `M` and binary dimension `b` (tex L5486–5506,
L5666–5735): the `t`-coefficients of `f, d ∈ 𝒪[G]` (by group component) and of the corrected
coordinates `ũ_x ∈ Λ[1/2]`. -/
structure CoordData (b : ℕ) where
  /-- `F g i`: the `tⁱ`-coefficient of the `g`-component of `f = 2^a Δ⁴`. -/
  F : (Fin b → ZMod 2) → ℤ → ℤ_[2]
  /-- `D g i`: the `tⁱ`-coefficient of the `g`-component of `d = η Δ Q`. -/
  D : (Fin b → ZMod 2) → ℤ → ℤ_[2]
  /-- `u x j`: the `tʲ`-coefficient of `ũ_x ∈ Λ[1/2]`; `u x 0 = ũ_x(0)`. -/
  u : (Fin b → ZMod 2) → ℕ → ℚ_[2]

/-- **The clearing identity (5.9)** `f_x ũ_x = d_x` at every character `x`, with `f ∈ 𝒪[G]`
(coefficients tending to `0` at `-∞`) and `ũ_x ∈ Λ[1/2]` (bounded denominators), as a convergent
convolution of coefficients (tex L5491–5496, L5719–5729). -/
def ClearingIdentity {b : ℕ} (C : CoordData b) : Prop :=
  (∀ g, Tendsto (C.F g) atBot (𝓝 0)) ∧
  (∃ e : ℕ, ∀ x j, ‖C.u x j‖ ≤ (2 : ℝ) ^ e) ∧
  ∀ x (n : ℤ), HasSum (fun j : ℕ => (signEval C.F x (n - j) : ℚ_[2]) * C.u x j)
    (signEval C.D x n : ℚ_[2])

/-- **The pole bound** (tex L5500–5502): `L_T = L_T(M)` bounds the negative Laurent support of
every `f_x` modulo `2^M`. -/
def PoleBound {b : ℕ} (C : CoordData b) (LT M : ℕ) : Prop :=
  ∀ x (i : ℤ), i < -(LT : ℤ) → (2 : ℤ_[2]) ^ M ∣ signEval C.F x i

/-- **The base is regular** (tex L5496–5499): `f_0 ∈ Λ` (no negative powers of `t`) and
`c = v₂ f_0(0)`. -/
def BaseRegular {b : ℕ} (C : CoordData b) (c : ℕ) : Prop :=
  (∀ i : ℤ, i < 0 → signEval C.F 0 i = 0) ∧ signEval C.F 0 0 ≠ 0 ∧
    (signEval C.F 0 0).valuation = c

/-- **The uniform upper bound at nonzero addresses** (tex L5730–5733, from (3.9), (3.4), (4.6)
and (4.7)): `v₂ ũ_x(0) ≤ B` for every `x ≠ 0`. -/
def UpperBound {b : ℕ} (C : CoordData b) (B : ℕ) : Prop :=
  ∀ x, x ≠ 0 → (2 : ℝ) ^ (-(B : ℤ)) ≤ ‖C.u x 0‖

/-- **The base-zero conclusion** (Lemma `ex:arith-base-zero`, tex L4321–4373): if
`L'(E/K, 1) = 0`, then `ũ_0(0) = 0`. -/
def BaseZero {b : ℕ} (E : WeierstrassCurve ℚ) (k : ℚ) (C : CoordData b) : Prop :=
  ProductOrderGeTwo E k → C.u 0 0 = 0

/-- **The fixed-field package of the remaining branch** (Branch 2). A final companion `k` with
`L(E^{(k)}, 1) ≠ 0` (tex L2595–2600), constants `B`, `c_det` and a pole bound `L_T(M)` fixed
before the binary dimension (tex L5497–5499, L5655–5662, L5730–5731), and, for every `M, b` as in
(5.10), coefficient data with the clearing identity, the pole bound, a regular base with
`c ≤ c_det`, the upper bound `B` and the base-zero conclusion. -/
structure FixedFieldPackage (E : WeierstrassCurve ℚ) where
  /-- The final companion discriminant `k` (`K = ℚ(√k)`). -/
  k : ℚ
  /-- `L(E^{(k)}, 1) ≠ 0`. -/
  hk : AnalyticRank (qtwist E k) 0
  /-- The upper bound `B` on `v₂ ũ_x(0)`, `x ≠ 0`. -/
  B : ℕ
  /-- `c_det = a + 4(h_K + 2c_E + 2t_K)`. -/
  cdet : ℕ
  /-- `L_T(M) = 16(d_K + 5)M`. -/
  LT : ℕ → ℕ
  /-- For every `M, b` as in (5.10), the coefficient data. -/
  coord : ∀ M b : ℕ, cdet < M → B + 2 * cdet < M → (LT M + 2) * (2 ^ M - 1) < b →
    ∃ (C : CoordData b) (c : ℕ), c ≤ cdet ∧ ClearingIdentity C ∧ PoleBound C (LT M) M ∧
      BaseRegular C c ∧ UpperBound C B ∧ BaseZero E k C

/-- **Branch 1 or the fixed-field package** (Sections 7–9 and Appendices E–G): for `ℓ` in the
domain of Theorem 5.3 with `corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1`, either `E_ℓ` has analytic rank one
(Branch 1: the odd limit symbol is a unit at the empty configuration and (O.8) applies at `D = 1`,
tex L2587–2592, L10258–10273), or the fixed-field package of Branch 2 exists. This node bundles
Elliot's constructions of Sections 7–9 and Appendices E–G; `DAG.md` lists its sub-nodes. -/
def BranchPackageNode : Prop :=
  ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) →
    AnalyticRankOne (Ecurve ℓ) ∨ Nonempty (FixedFieldPackage (Ecurve ℓ))

/-- **The missing-address argument** (Proposition `ex:limits-coefficient-transfer`, tex
L5666–5735, (5.10)–(5.11)): with `M > c_det`, `M > B + 2 c_det`, `b > (L_T + 2)(2^M - 1)`, the
clearing identity, the pole bound and a regular base with `c ≤ c_det`, some nonzero address `x`
has `v₂(ũ_x(0) - ũ_0(0)) ≥ M - 2c`. -/
def MissingAddressNode : Prop :=
  ∀ (b M LT B cdet c : ℕ) (C : CoordData b), cdet < M → B + 2 * cdet < M →
    (LT + 2) * (2 ^ M - 1) < b → c ≤ cdet → ClearingIdentity C → PoleBound C LT M →
    BaseRegular C c →
    ∃ x, x ≠ 0 ∧ ‖C.u x 0 - C.u 0 0‖ ≤ (2 : ℝ) ^ (-((M : ℤ) - 2 * c))

end ZInQ.Contrib.CloudB3RC53
