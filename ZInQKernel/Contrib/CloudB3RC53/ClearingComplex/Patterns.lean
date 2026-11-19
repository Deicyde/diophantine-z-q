import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.Identification

/-!
# E2: the only generic patterns of the remaining complex

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5605–5617: "If `D_x` has the rank-one pattern … If `D_x` is generically acyclic … These are the
only generic patterns in the present family, by central specialization and the central corank-one
bound."

For a block-form complex `D` over `𝒪[G]` (`ClearingComplex.BlockComplex`) and a sign character `x`,
the generic cohomology of `D_x` (over `K = Frac 𝒪`) has dimensions
`h⁰ = m₀ − r₀`, `h¹ = (m₀ + 1 + m₁) − r₁ − r₀`, `h² = (m₁ + 1 + m₂) − r₂ − r₁`, `h³ = m₂ − r₂`,
with `r_i` the rank of the sign-evaluated differential `d^i_x` over `K` (`BlockComplex.hdim`,
rank–nullity).

* `RankOnePattern x`: `(h⁰, h¹, h², h³) = (0, 1, 1, 0)`; `AcyclicPattern x`: all `h^i = 0`.
* `hdim_le_central`: where the Smith blocks are invertible at `x` (`Δ_x ≠ 0`, the hypothesis under
  which `ClearingCoordIdentity` uses the patterns), the generic dimensions are bounded by the
  central ones `(0, 1, 1, 0)` (the central corank-one bound: `H₁, H₂` have rank one in the block
  form, and the Smith blocks keep their full rank `m_i` at `x`);
* `euler_char`: `h⁰ − h¹ + h² − h³ = 0`;
* `patterns_of_det_ne_zero`: hence `RankOnePattern x ∨ AcyclicPattern x` (PROVED);
* `clearingPatterns_of`: RC0's `ClearingPatterns` for the patterns guarded by `Δ_x ≠ 0`, and
  `clearingCoordIdentity_guard_iff`: the coordinate identity for the guarded patterns is
  equivalent to the one for the genuine patterns (PROVED);
* `clearingModelOver_of_identification_E1`: `ClearingModelOver genuinePole` from the single
  identification and E1 alone (E2 is now PROVED).

DEPARTURE (of route, recorded): Elliot argues by specialization of `D_x` to the central fibre
(semicontinuity of rank) and the central corank-one bound. In the Smith block form the central
corank-one bound is built into the shape of `D` (`rank H₁ = rank H₂ = 1`), and "semicontinuity" is
replaced by the full rank of the Smith blocks at `x`, which is exactly `Δ_x ≠ 0`; the patterns are
only used where `Δ_x ≠ 0`. At `Δ_x = 0` no dichotomy is claimed (the guarded `RankOne` holds
vacuously there), and none is used.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData evK sgnChar
  genuinePole)

namespace BlockComplex

variable {O : Type} [CommRing O] {b : ℕ}
  (D : BlockComplex (MonoidAlgebra O (SignGroup b)))

/-! ### The generic cohomology dimensions of `D_x` -/

/-- The sign-evaluated differentials `d^i_x` over `K = Frac 𝒪`. -/
def dx0 (x : Addr b) := D.d0.map (evK (sgnChar x))
/-- `d¹_x` over `K`. -/
def dx1 (x : Addr b) := D.d1.map (evK (sgnChar x))
/-- `d²_x` over `K`. -/
def dx2 (x : Addr b) := D.d2.map (evK (sgnChar x))

/-- **The generic cohomology dimensions of `D_x`** (over `K = Frac 𝒪`; rank–nullity):
`h^i = dim D^i − rank d^i_x − rank d^{i−1}_x`. -/
def hdim (x : Addr b) : ℕ → ℤ
  | 0 => (D.m0 : ℤ) - (D.dx0 x).rank
  | 1 => ((D.m0 + 1 + D.m1 : ℕ) : ℤ) - (D.dx1 x).rank - (D.dx0 x).rank
  | 2 => ((D.m1 + 1 + D.m2 : ℕ) : ℤ) - (D.dx2 x).rank - (D.dx1 x).rank
  | 3 => (D.m2 : ℤ) - (D.dx2 x).rank
  | _ + 4 => 0

/-- **The rank-one pattern** (tex 5605): generic cohomology `(0, 1, 1, 0)`. -/
def RankOnePattern (x : Addr b) : Prop :=
  D.hdim x 0 = 0 ∧ D.hdim x 1 = 1 ∧ D.hdim x 2 = 1 ∧ D.hdim x 3 = 0

/-- **The acyclic pattern** (tex 5613): `D_x` generically acyclic. -/
def AcyclicPattern (x : Addr b) : Prop :=
  ∀ i, D.hdim x i = 0

/-- `d¹_x d⁰_x = 0`. -/
theorem dx1_mul_dx0 (x : Addr b) : D.dx1 x * D.dx0 x = 0 := by
  rw [dx1, dx0, ← Matrix.map_mul, D.d1_d0, Matrix.map_zero _ (map_zero _)]

/-- `d²_x d¹_x = 0`. -/
theorem dx2_mul_dx1 (x : Addr b) : D.dx2 x * D.dx1 x = 0 := by
  rw [dx2, dx1, ← Matrix.map_mul, D.d2_d1, Matrix.map_zero _ (map_zero _)]

/-- **Euler characteristic zero**: `h⁰ − h¹ + h² − h³ = 0`. -/
theorem euler_char (x : Addr b) :
    D.hdim x 0 - D.hdim x 1 + D.hdim x 2 - D.hdim x 3 = 0 := by
  simp only [hdim]; push_cast; ring

/-- The sign-evaluated Smith blocks are submatrices of the sign-evaluated differentials. -/
theorem A0_map (x : Addr b) : D.A0.map (evK (sgnChar x)) = (D.dx0 x).submatrix Sum.inl id := rfl
theorem A1_map (x : Addr b) :
    D.A1.map (evK (sgnChar x)) = (D.dx1 x).submatrix Sum.inl (Sum.inr ∘ Sum.inr) := rfl
theorem A2_map (x : Addr b) :
    D.A2.map (evK (sgnChar x)) = (D.dx2 x).submatrix id (Sum.inr ∘ Sum.inr) := rfl

variable {OL : Type} [CommRing OL] [Algebra Lam OL]

/-- `Δ_x ≠ 0` for the Smith data of `D` gives the invertibility of the three Smith blocks at `x`. -/
theorem dets_of_Δ (A0' : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) Lam)
    (s : (i : ℕ) → Fin (D.mi i) → ℤ_[2]) (s_ne : ∀ i j, s i j ≠ 0)
    (central : ∀ i, (A0' i).map PowerSeries.constantCoeff = Matrix.diagonal (s i)) (x : Addr b)
    (h : evK (sgnChar x) (D.toSmithBlocks (O := OL) A0' s s_ne central).Δ ≠ 0) :
    evK (sgnChar x) D.A0.det ≠ 0 ∧ evK (sgnChar x) D.A1.det ≠ 0 ∧
      evK (sgnChar x) D.A2.det ≠ 0 := by
  simp only [SmithBlocks.Δ, SmithBlocks.δ, toSmithBlocks, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, map_mul, ne_eq] at h
  change evK (sgnChar x) D.A0.det * evK (sgnChar x) D.A1.det * evK (sgnChar x) D.A2.det = 0 →
    False at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h1 => h (by rw [h1]; ring),
    fun h2 => h (by rw [h2]; ring)⟩

variable [IsDomain O]

/-- **The generic dimensions are nonnegative** (`d² = 0`). -/
theorem hdim_nonneg (x : Addr b) (i : ℕ) : 0 ≤ D.hdim x i := by
  have h01 := Matrix.rank_add_rank_le_card_of_mul_eq_zero (D.dx1_mul_dx0 x)
  have h12 := Matrix.rank_add_rank_le_card_of_mul_eq_zero (D.dx2_mul_dx1 x)
  have r0 : (D.dx0 x).rank ≤ D.m0 := (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _)
  have r2 : (D.dx2 x).rank ≤ D.m2 := (Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin _)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h01 h12
  match i with
  | 0 => simp only [hdim]; omega
  | 1 => simp only [hdim]; push_cast; omega
  | 2 => simp only [hdim]; push_cast; omega
  | 3 => simp only [hdim]; omega
  | _ + 4 => simp [hdim]

/-- A square submatrix with nonzero determinant bounds the rank from below. -/
theorem le_rank_of_submatrix {K : Type} [Field K] {r c : Type} [Fintype r] [Fintype c] {k : ℕ}
    (M : Matrix r c K) (f : Fin k → r) (g : Fin k → c) (h : (M.submatrix f g).det ≠ 0) :
    k ≤ M.rank := by
  have := Matrix.rank_of_det_ne_zero h
  rw [Fintype.card_fin] at this
  rw [← this]
  exact Matrix.rank_submatrix_le M f g

/-- **The central bound** `(h⁰, h¹, h², h³) ≤ (0, 1, 1, 0)` where the Smith blocks are invertible at
`x` (and, PROVED, `h⁰ = h³ = 0`). -/
theorem hdim_le_central (x : Addr b) (h0 : evK (sgnChar x) D.A0.det ≠ 0)
    (h1 : evK (sgnChar x) D.A1.det ≠ 0) (h2 : evK (sgnChar x) D.A2.det ≠ 0) :
    D.hdim x 0 = 0 ∧ D.hdim x 1 ≤ 1 ∧ D.hdim x 2 ≤ 1 ∧ D.hdim x 3 = 0 := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, A0_map] at h0
  rw [RingHom.map_det, RingHom.mapMatrix_apply, A1_map] at h1
  rw [RingHom.map_det, RingHom.mapMatrix_apply, A2_map] at h2
  have l0 := le_rank_of_submatrix _ _ _ h0
  have l1 := le_rank_of_submatrix _ _ _ h1
  have l2 := le_rank_of_submatrix _ _ _ h2
  have r0 : (D.dx0 x).rank ≤ D.m0 := (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _)
  have r2 : (D.dx2 x).rank ≤ D.m2 := (Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin _)
  simp only [hdim]; push_cast
  omega

/-- **E2: the only generic patterns** (tex 5615–5617; PROVED): where the Smith blocks are
invertible at `x`, `D_x` has the rank-one pattern or is generically acyclic (central bound,
nonnegativity and `χ = 0`). -/
theorem patterns_of_det_ne_zero (x : Addr b) (h0 : evK (sgnChar x) D.A0.det ≠ 0)
    (h1 : evK (sgnChar x) D.A1.det ≠ 0) (h2 : evK (sgnChar x) D.A2.det ≠ 0) :
    D.RankOnePattern x ∨ D.AcyclicPattern x := by
  obtain ⟨e0, e1, e2, e3⟩ := D.hdim_le_central x h0 h1 h2
  have n1 := D.hdim_nonneg x 1
  have n2 := D.hdim_nonneg x 2
  have hχ := D.euler_char x
  rcases (show D.hdim x 1 = 0 ∨ D.hdim x 1 = 1 by omega) with h | h
  · refine Or.inr fun i => ?_
    match i with
    | 0 => exact e0
    | 1 => exact h
    | 2 => omega
    | 3 => exact e3
    | _ + 4 => rfl
  · exact Or.inl ⟨e0, h, by omega, e3⟩

end BlockComplex

/-! ### RC0's `ClearingPatterns` and the coordinate identity -/

section Guarded

variable {O : Type} [CommRing O] [IsDomain O] [Algebra Lam O] {b : ℕ}

/-- The patterns guarded by `Δ_x ≠ 0`: rank-one means "rank-one where `Δ_x ≠ 0`". -/
def GuardedRankOne (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) (R : Addr b → Prop)
    (x : Addr b) : Prop :=
  evK (sgnChar x) B.Δ ≠ 0 → R x

/-- Acyclic and `Δ_x ≠ 0`. -/
def GuardedAcyclic (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O) (A : Addr b → Prop)
    (x : Addr b) : Prop :=
  evK (sgnChar x) B.Δ ≠ 0 ∧ A x

/-- **The coordinate identity is insensitive to the guard** (PROVED): `ClearingCoordIdentity`
uses the patterns only where `Δ_x ≠ 0`. -/
theorem clearingCoordIdentity_guard_iff (B : SmithBlocks (MonoidAlgebra O (SignGroup b)) O)
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O (SignGroup b)) (a : ℕ) (e : Addr b → ℕ)
    (g : Addr b → Lam) (R A : Addr b → Prop) :
    ClearingCoordIdentity B sd κ ε η a e g (GuardedRankOne B R) (GuardedAcyclic B A) ↔
      ClearingCoordIdentity B sd κ ε η a e g R A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hΔ hR => h1 x hΔ fun _ => hR, fun x hΔ hA => h2 x hΔ ⟨hΔ, hA⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hΔ hR => h1 x hΔ (hR hΔ), fun x hΔ hA => h2 x hΔ hA.2⟩

end Guarded

/-- **E2 for the identified remaining complex: `ClearingPatterns`** (PROVED). -/
theorem clearingPatterns_of {b dK hK cE tK : ℕ} (I : Identification b dK hK cE tK) :
    ClearingPatterns (GuardedRankOne I.B I.D.RankOnePattern)
      (GuardedAcyclic I.B I.D.AcyclicPattern) := by
  intro x
  by_cases hΔ : evK (sgnChar x) I.B.Δ ≠ 0
  · obtain ⟨h0, h1, h2⟩ := I.D.dets_of_Δ I.A0 I.s I.s_ne I.central x hΔ
    rcases I.D.patterns_of_det_ne_zero x h0 h1 h2 with h | h
    · exact Or.inl fun _ => h
    · exact Or.inr ⟨hΔ, h⟩
  · exact Or.inl fun h => absurd h hΔ

/-- **`ClearingModelOver` from the single identification and E1 alone** (PROVED; E2 is
`clearingPatterns_of`): E1 is stated for the genuine generic patterns of the identified complex. -/
theorem clearingModelOver_of_identification_E1 {ℓ : ℕ} (Dd : RCData ℓ) {dK hK cE tK : ℕ}
    (F : Family) (I : Identification F.b dK hK cE tK) (sd : ScalarData I.B)
    (κ ε η : MonoidAlgebra OO (SignGroup F.b))
    (hcoord : ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      ClearingCoordIdentity I.B sd κ ε η 0 e g I.D.RankOnePattern I.D.AcyclicPattern) :
    ClearingModelOver genuinePole Dd dK hK cE tK F :=
  clearingModelOver_of_identification Dd F I sd κ ε η _ _ (clearingPatterns_of I)
    fun e g h => (clearingCoordIdentity_guard_iff _ _ _ _ _ _ _ _ _ _).mpr (hcoord e g h)

/-- **RC0's `ClearingModel` from the single identification and E1** (PROVED). -/
theorem clearingModel_of_E1 {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : Identification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)),
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          ClearingCoordIdentity I.B sd κ ε η 0 e g I.D.RankOnePattern I.D.AcyclicPattern) :
    ClearingModel Dd := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  refine ⟨dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨I, sd, κ, ε, η, hcoord⟩ := hF Co Ce F hFam
  exact clearingModelOver_of_identification_E1 Dd F I sd κ ε η hcoord

/-! ### Non-vacuity: both patterns occur -/

/-- The block complex with no disks and `d¹ = c : H₁ → H₂`. -/
def unitCx {S : Type*} [CommRing S] (c : S) : BlockComplex S where
  m0 := 0
  m1 := 0
  m2 := 0
  d0 := 0
  d1 := fun _ _ => c
  d2 := 0
  d1_d0 := by ext _ j; exact j.elim0
  d2_d1 := by ext i; exact i.elim0

section NonVacuity

variable {O : Type} [CommRing O] [IsDomain O] {b : ℕ}

theorem unitCx_m0 {S : Type*} [CommRing S] (c : S) : (unitCx c).m0 = 0 := rfl
theorem unitCx_m1 {S : Type*} [CommRing S] (c : S) : (unitCx c).m1 = 0 := rfl
theorem unitCx_m2 {S : Type*} [CommRing S] (c : S) : (unitCx c).m2 = 0 := rfl

theorem unitCx_rank0 (c : MonoidAlgebra O (SignGroup b)) (x : Addr b) :
    ((unitCx c).dx0 x).rank = 0 :=
  Nat.le_zero.mp ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _))

theorem unitCx_rank2 (c : MonoidAlgebra O (SignGroup b)) (x : Addr b) :
    ((unitCx c).dx2 x).rank = 0 :=
  Nat.le_zero.mp ((Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin _))

omit [IsDomain O] in
theorem unitCx_rank1 (c : MonoidAlgebra O (SignGroup b)) (x : Addr b) :
    ((unitCx c).dx1 x).rank =
      (Matrix.of fun _ _ => evK (sgnChar x) c :
        Matrix (Fin 0 ⊕ Unit ⊕ Fin 0) (Fin 0 ⊕ Unit ⊕ Fin 0) (FractionRing O)).rank := rfl

/-- **Non-vacuity of the rank-one pattern**: `d¹ = 0 : H₁ → H₂` has generic cohomology
`(0, 1, 1, 0)`. -/
theorem unitCx_zero_rankOne (x : Addr b) :
    (unitCx (0 : MonoidAlgebra O (SignGroup b))).RankOnePattern x := by
  have h0 := unitCx_rank0 (0 : MonoidAlgebra O (SignGroup b)) x
  have h2 := unitCx_rank2 (0 : MonoidAlgebra O (SignGroup b)) x
  have h1 : ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx1 x).rank = 0 := by
    rw [unitCx_rank1, map_zero]
    convert Matrix.rank_zero (R := FractionRing O) (m := Fin 0 ⊕ Unit ⊕ Fin 0)
      (n := Fin 0 ⊕ Unit ⊕ Fin 0) using 2
    ext i j; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ((0 : ℕ) : ℤ) - ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx0 x).rank = 0
    rw [h0]; rfl
  · change ((0 + 1 + 0 : ℕ) : ℤ) - ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx1 x).rank -
      ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx0 x).rank = 1
    rw [h0, h1]; rfl
  · change ((0 + 1 + 0 : ℕ) : ℤ) - ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx2 x).rank -
      ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx1 x).rank = 1
    rw [h2, h1]; rfl
  · change ((0 : ℕ) : ℤ) - ((unitCx (0 : MonoidAlgebra O (SignGroup b))).dx2 x).rank = 0
    rw [h2]; rfl

/-- **Non-vacuity of the acyclic pattern**: `d¹ = 1 : H₁ → H₂` is acyclic. -/
theorem unitCx_one_acyclic (x : Addr b) :
    (unitCx (1 : MonoidAlgebra O (SignGroup b))).AcyclicPattern x := by
  have h1 : ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx1 x).rank = 1 := by
    rw [unitCx_rank1, map_one]
    have : (Matrix.of fun _ _ => (1 : FractionRing O) :
        Matrix (Fin 0 ⊕ Unit ⊕ Fin 0) (Fin 0 ⊕ Unit ⊕ Fin 0) (FractionRing O)) = 1 := by
      ext i j
      have hij : i = j := by
        rcases i with i | i | i
        · exact i.elim0
        · rcases j with j | j | j
          · exact j.elim0
          · rfl
          · exact j.elim0
        · exact i.elim0
      subst hij
      simp
    rw [this, Matrix.rank_one]
    simp
  have h0 := unitCx_rank0 (1 : MonoidAlgebra O (SignGroup b)) x
  have h2 := unitCx_rank2 (1 : MonoidAlgebra O (SignGroup b)) x
  intro i
  match i with
  | 0 =>
    change ((0 : ℕ) : ℤ) - ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx0 x).rank = 0
    rw [h0]; rfl
  | 1 =>
    change ((0 + 1 + 0 : ℕ) : ℤ) - ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx1 x).rank -
      ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx0 x).rank = 0
    rw [h0, h1]; rfl
  | 2 =>
    change ((0 + 1 + 0 : ℕ) : ℤ) - ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx2 x).rank -
      ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx1 x).rank = 0
    rw [h2, h1]; rfl
  | 3 =>
    change ((0 : ℕ) : ℤ) - ((unitCx (1 : MonoidAlgebra O (SignGroup b))).dx2 x).rank = 0
    rw [h2]; rfl
  | _ + 4 => rfl

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
