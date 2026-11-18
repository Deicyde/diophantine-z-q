import ZInQKernel.Contrib.OneProof.RC.Wiring.Clearing
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudgetRank

/-!
# The remaining complex of the determinant clearing and its single identification

Manuscript `diophantine_zq.tex`, Proposition `ex:limits-fixed-field-clearing` and its proof,
tex L5486–5645 (with the new-local cancellation of Lemma `ex:limits-fixed-field-budget`,
tex L5394–5454, and the budget (5.7), tex L5251–5392).

**(1) The block-form complex** (`BlockComplex S`, over any commutative ring `S`; for the clearing
`S = 𝒪[G]`). After the central Smith decomposition (tex 5522–5532) the remaining complex `D` lives
in degrees `0, …, 3` with `D⁰ = E₀`, `D¹ = B₁ ⊕ H₁ ⊕ E₁`, `D² = B₂ ⊕ H₂ ⊕ E₂`, `D³ = B₃`
(`rank E_i = rank B_{i+1} = m_i`, `rank H₁ = rank H₂ = 1`, and `B₀ = H₀ = E₃ = H₃ = 0`). It is recorded
by its three differentials as matrices over these block decompositions, with `d¹d⁰ = 0`,
`d²d¹ = 0`. Its Smith blocks `A_i : E_i → B_{i+1}` are the submatrices `BlockComplex.A0`, `A1`, `A2`
of the actual differentials (tex 5532–5535: "The entries in this definition are the original
entries of `D`").

**(5) The identification** (`Identification b dK hK cE tK`, ONE explicit GLUE input; the
Selmer-complex model of Nekovář, *Selmer complexes*, Astérisque 310, (5.6) and 7.8.8(ii), as the
manuscript cites them, UNVERIFIED; and the new-local cancellation of tex 5394–5454): a block-form
complex `D` over `𝒪[G]` that IS the remaining complex, i.e.
* `aug`: its augmentation is the old complex over `Λ`, whose Smith blocks `A0 i` reduce centrally
  to the nonzero central Smith entries `s i` (tex 5517, 5530–5541: `D_c = D_0 ⊗_Λ ℤ₂`);
* `poles`: at every sign character its differentials are a constant `Λ`-basis change of the Schur
  complements `P_x − Q_x B_x⁻¹ T_x` of one new-local family (`B` with augmentation the block diagonal
  of the new local blocks `A_q`, `det A_q = t^{d_q} v_q + 2w_q`, `d_q ≤ 4`; tex 5437–5454, 5517–5519);
* `budget`: the central complex of its Smith data satisfies the counts used in (5.7): total rank
  `≤ 2d_K + 12`, the exact sequence (5.7d) of `H²` with `H¹_C, H²_C, J, H³_C` of ranks `1, 1` and
  lengths `t_K, h_K, ≤ 2c_E, t_K` (tex 5355–5392).

**(6) Derived (PROVED):** `smithModel_of`, `entryPoles_of`, `budget_of`, and
`clearingModelOver_of_identification`: RC0's `ClearingModelOver genuinePole` follows from the
identification together with the generic patterns (E2, `ClearingPatterns`) and Elliot's
coordinate identity (E1, `ClearingCoordIdentity`), taken here as separate hypotheses;
`clearingModel_of` assembles `ClearingModel`. (E2 is PROVED in `Patterns.lean`; E1b is PROVED for
the Knudsen–Mumford coordinate in `CoordE1b.lean`, leaving E1a `CoordLink`.)

This first version of the identification is superseded by `Identification2`
(`ClearingComplex/NewLocalModel`): it admits an empty new-local family, so
`Identification b 0 0 0 0` is always inhabited (`Consistency.lean`); the content sits in the
coordinate identity E1.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup SmithBlocks ScalarData PoleData aug sgnChar
  genuinePole)

/-! ### (1) The block-form complex -/

/-- **The remaining complex in block form** (tex 5522–5535) over a commutative ring `S`:
`D⁰ = E₀`, `D¹ = B₁ ⊕ H₁ ⊕ E₁`, `D² = B₂ ⊕ H₂ ⊕ E₂`, `D³ = B₃`, with `rank E_i = rank B_{i+1} = m_i`
and `H₁, H₂` of rank one. -/
structure BlockComplex (S : Type*) [CommRing S] where
  /-- `rank E₀ = rank B₁` -/
  m0 : ℕ
  /-- `rank E₁ = rank B₂` -/
  m1 : ℕ
  /-- `rank E₂ = rank B₃` -/
  m2 : ℕ
  /-- `d⁰ : E₀ → B₁ ⊕ H₁ ⊕ E₁` -/
  d0 : Matrix (Fin m0 ⊕ Unit ⊕ Fin m1) (Fin m0) S
  /-- `d¹ : B₁ ⊕ H₁ ⊕ E₁ → B₂ ⊕ H₂ ⊕ E₂` -/
  d1 : Matrix (Fin m1 ⊕ Unit ⊕ Fin m2) (Fin m0 ⊕ Unit ⊕ Fin m1) S
  /-- `d² : B₂ ⊕ H₂ ⊕ E₂ → B₃` -/
  d2 : Matrix (Fin m2) (Fin m1 ⊕ Unit ⊕ Fin m2) S
  d1_d0 : d1 * d0 = 0
  d2_d1 : d2 * d1 = 0

namespace BlockComplex

variable {S : Type*} [CommRing S] (D : BlockComplex S)

/-- `A₀ : E₀ → B₁`, the `(B₁, E₀)` block of `d⁰`. -/
def A0 : Matrix (Fin D.m0) (Fin D.m0) S := fun j k => D.d0 (Sum.inl j) k

/-- `A₁ : E₁ → B₂`, the `(B₂, E₁)` block of `d¹`. -/
def A1 : Matrix (Fin D.m1) (Fin D.m1) S := fun j k => D.d1 (Sum.inl j) (Sum.inr (Sum.inr k))

/-- `A₂ : E₂ → B₃`, the `(B₃, E₂)` block of `d²`. -/
def A2 : Matrix (Fin D.m2) (Fin D.m2) S := fun j k => D.d2 j (Sum.inr (Sum.inr k))

/-- The disk sizes indexed by the source degree (`0` from degree three on). -/
def mi : ℕ → ℕ
  | 0 => D.m0
  | 1 => D.m1
  | 2 => D.m2
  | _ + 3 => 0

/-- The Smith blocks indexed by the source degree. -/
def Ai : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) S
  | 0 => D.A0
  | 1 => D.A1
  | 2 => D.A2
  | _ + 3 => 0

variable {O : Type*} [CommRing O] [Algebra Lam O]

/-- **RC7's Smith data of the block complex** (`SmithBlocks`): the three Smith blocks of the actual
differentials, with augmentation `A0'` over `Λ` reducing centrally to the Smith entries `s`. -/
def toSmithBlocks (A0' : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) Lam)
    (s : (i : ℕ) → Fin (D.mi i) → ℤ_[2]) (s_ne : ∀ i j, s i j ≠ 0)
    (central : ∀ i, (A0' i).map PowerSeries.constantCoeff = Matrix.diagonal (s i)) :
    SmithBlocks S O where
  n := 3
  m := D.mi
  A := D.Ai
  A0 := A0'
  s := s
  s_ne := s_ne
  central := central

end BlockComplex

/-! ### (5) The identification -/

section Identification

variable {b : ℕ}

/-- **A matrix family is a sign-evaluated new-local Schur complement** (tex 5437–5454, 5517–5519):
there are a new-local family `B` over `Λ[G]` (augmentation the block diagonal of new local blocks
`A_q` with `det A_q = t^{d_q} v_q + 2 w_q`, `d_q ≤ 4`), matrices `P, Q, T` over `Λ[G]` and constant
`Λ`-basis changes `U, V` with `M_x = U (P_x − Q_x B_x⁻¹ T_x) V` at every sign character `x` (`·_x` the
sign evaluation, mapped into `𝒪`). -/
def IsNewLocalSchur {r c : Type} (Mx : Addr b → Matrix r c OO) : Prop :=
  ∃ (Q ι : Type) (_ : Fintype Q) (_ : DecidableEq Q) (_ : Fintype ι) (_ : DecidableEq ι)
    (A : Q → Matrix ι ι Lam) (dq : Q → ℕ) (_ : ∀ q, dq q ≤ 4) (v : Q → Lamˣ) (w : Q → Lam)
    (_ : ∀ q, (A q).det = (PowerSeries.X : Lam) ^ dq q * (v q : Lam) + 2 * w q)
    (Bfam : Matrix (ι × Q) (ι × Q) (MonoidAlgebra Lam (SignGroup b)))
    (_ : Bfam.map aug = Matrix.blockDiagonal A)
    (p q' : Type) (_ : Fintype p) (_ : Fintype q')
    (P : Matrix p q' (MonoidAlgebra Lam (SignGroup b)))
    (Qm : Matrix p (ι × Q) (MonoidAlgebra Lam (SignGroup b)))
    (T : Matrix (ι × Q) q' (MonoidAlgebra Lam (SignGroup b))) (U : Matrix r p Lam)
    (V : Matrix q' c Lam),
    ∀ x : Addr b, Mx x = U.map (algebraMap Lam OO) *
      ((P.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO) -
        (Qm.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO) *
          ((Bfam.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO))⁻¹ *
          (T.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO)) *
      V.map (algebraMap Lam OO)

/-- **The counts of (5.7) for the central complex** of Smith data `B` (tex 5355–5392), in the form
of RankCounts' `budget_rank`: total rank `≤ 2d_K + 12`, and the exact sequence (5.7d)
`0 → H²_C → H²(D_c) → J → H³_C → H³(D_c) → 0` with `H¹(D_c) ≅ H¹_C`, ranks one, torsion lengths
`t_K, h_K, t_K` and `ℓ(J) ≤ 2c_E`. -/
def BudgetInputs {S : Type} [CommRing S] (B : SmithBlocks S OO) (dK hK cE tK : ℕ) : Prop :=
  ∃ (fr : ℕ → ℕ)
    (_ : ∑ k : Fin 4, Module.finrank ℤ_[2] (RankCounts.centralCx B fr k) ≤ 2 * dK + 12)
    (H1C H2C J H3C : Type) (_ : AddCommGroup H1C) (_ : Module ℤ_[2] H1C) (_ : AddCommGroup H2C)
    (_ : Module ℤ_[2] H2C) (_ : AddCommGroup J) (_ : Module ℤ_[2] J) (_ : AddCommGroup H3C)
    (_ : Module ℤ_[2] H3C)
    (_ : (RankCounts.centralH B) fr 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] (RankCounts.centralH B) fr 2) (j : (RankCounts.centralH B) fr 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] (RankCounts.centralH B) fr 3),
    (Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧ Function.Exact δ l ∧
      Function.Surjective l) ∧
    Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK ∧ Module.length ℤ_[2] H3C = tK ∧
    Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK ∧ Module.length ℤ_[2] J ≤ 2 * cE ∧
    Module.finrank ℤ_[2] H1C = 1 ∧ Module.finrank ℤ_[2] H2C = 1

/-- **The single identification of the remaining complex** (GLUE; see the module docstring):
a block-form complex `D` over `𝒪[G]`, `G = 𝔽₂^b`, with augmentation the old complex over `Λ`
(Smith blocks `A0` reducing centrally to the Smith entries `s`), sign-evaluated differentials given
by one new-local Schur family, and the (5.7) counts for its central complex.

Superseded by `Identification2` (`ClearingComplex/NewLocalModel`): this first version admits an
empty new-local family, so `Identification b 0 0 0 0` is always inhabited; the content sits in the
coordinate identity E1. -/
structure Identification (b : ℕ) (dK hK cE tK : ℕ) where
  /-- the remaining complex `D` over `𝒪[G]` -/
  D : BlockComplex (MonoidAlgebra OO (SignGroup b))
  /-- the Smith blocks of the old complex over `Λ` -/
  A0 : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) Lam
  /-- the central Smith entries -/
  s : (i : ℕ) → Fin (D.mi i) → ℤ_[2]
  s_ne : ∀ i j, s i j ≠ 0
  central : ∀ i, (A0 i).map PowerSeries.constantCoeff = Matrix.diagonal (s i)
  /-- the augmentation of `D` is the old complex over `Λ` (tex 5517, 5537–5538) -/
  aug_eq : ∀ i, (D.Ai i).map aug = (A0 i).map (algebraMap Lam OO)
  /-- the sign-evaluated differentials are new-local Schur complements (tex 5437–5454, 5517–5519) -/
  poles0 : IsNewLocalSchur (b := b) fun x => D.d0.map (Determinant.signEval (sgnChar x))
  poles1 : IsNewLocalSchur (b := b) fun x => D.d1.map (Determinant.signEval (sgnChar x))
  poles2 : IsNewLocalSchur (b := b) fun x => D.d2.map (Determinant.signEval (sgnChar x))
  /-- the (5.7) counts for the central complex (tex 5355–5392) -/
  budget : BudgetInputs (D.toSmithBlocks (O := OO) A0 s s_ne central) dK hK cE tK

namespace Identification

variable {dK hK cE tK : ℕ} (I : Identification b dK hK cE tK)

/-- RC7's Smith data of the identified remaining complex. -/
def B : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO :=
  I.D.toSmithBlocks I.A0 I.s I.s_ne I.central

/-! ### (6) The derived fields -/

/-- **E3: `ClearingSmithModel`** (PROVED from the identification). -/
theorem smithModel_of : ClearingSmithModel I.B :=
  ⟨by norm_num [B, BlockComplex.toSmithBlocks], I.aug_eq⟩

/-- The entries of a sign-evaluated new-local Schur complement have pole at most `4M` modulo `2^M`
(RC7's PROVED (5.8): `newLocal_family_pole_genuine`, `schur_entry_mem_poleModLE`,
`basisChange_entry_mem_poleModLE`). -/
theorem pole_of_isNewLocalSchur {r c : Type} {Mx : Addr b → Matrix r c OO}
    (h : IsNewLocalSchur Mx) (x : Addr b) (M : ℕ) :
    ∀ j k, Mx x j k ∈ genuinePole.poleModLE M (4 * M) := by
  obtain ⟨Q, ι, _, _, _, _, A, dq, hd, v, w, hdet, Bfam, hB0, p, q', _, _, P, Qm, T, U, V, hM⟩ := h
  have hinv := (Determinant.newLocal_family_pole_genuine A dq hd v w hdet Bfam hB0 (sgnChar x) M).2
  have hschur := genuinePole.schur_entry_mem_poleModLE
    ((P.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO))
    ((Qm.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO))
    ((T.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO))
    ((Bfam.map (Determinant.signEval (sgnChar x))).map (algebraMap Lam OO))
    (fun i j => genuinePole.algebraMap_mem_poleLE _) (fun i j => genuinePole.algebraMap_mem_poleLE _)
    (fun i j => genuinePole.algebraMap_mem_poleLE _) hinv
  intro j k
  rw [hM x]
  exact genuinePole.basisChange_entry_mem_poleModLE U _ V hschur j k

/-- **`ClearingEntryPoles`** (PROVED from the identification and RC7's (5.8)). -/
theorem entryPoles_of : ClearingEntryPoles genuinePole I.B := by
  intro x M i j k
  match i, j, k with
  | 0, j, k =>
    exact pole_of_isNewLocalSchur I.poles0 x M (Sum.inl j) k
  | 1, j, k =>
    exact pole_of_isNewLocalSchur I.poles1 x M (Sum.inl j) (Sum.inr (Sum.inr k))
  | 2, j, k =>
    exact pole_of_isNewLocalSchur I.poles2 x M j (Sum.inr (Sum.inr k))
  | _ + 3, j, _ => exact j.elim0

/-- **`ClearingBudget`** ((5.7); PROVED from the identification's counts by RankCounts'
`budget_rank`). -/
theorem budget_of : ClearingBudget I.B dK hK cE tK := by
  obtain ⟨fr, hrank, H1C, H2C, J, H3C, _, _, _, _, _, _, _, _, e, i, j, δ, l, h57d, ht₁, ht₃, hh,
    hJ, hr₁, hr₂⟩ := I.budget
  exact RankCounts.budget_rank I.B fr (fun i hi hn => by
      change i < 3 at hn
      omega) hrank e i j δ l h57d ht₁ ht₃ hh hJ hr₁ hr₂

end Identification

/-- **`ClearingModelOver` from the identification, the generic patterns (E2) and Elliot's
coordinate identity (E1)** (PROVED). -/
theorem clearingModelOver_of_identification {ℓ : ℕ} (Dd : RCData ℓ) {dK hK cE tK : ℕ}
    (F : Family) (I : Identification F.b dK hK cE tK) (sd : ScalarData I.B)
    (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (RankOne Acyclic : Addr F.b → Prop)
    (hpat : ClearingPatterns RankOne Acyclic)
    (hcoord : ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      ClearingCoordIdentity I.B sd κ ε η 0 e g RankOne Acyclic) :
    ClearingModelOver genuinePole Dd dK hK cE tK F :=
  ⟨I.B, sd, κ, ε, η, RankOne, Acyclic, I.smithModel_of, hpat, hcoord, I.entryPoles_of,
    I.budget_of⟩

/-- **RC0's `ClearingModel` from the single identification plus E1 and E2** (PROVED): constants
fixed before the family and, at every final family, an identification of the remaining complex
together with the generic patterns and the coordinate identity for its Smith data. -/
theorem clearingModel_of {ℓ : ℕ} (Dd : RCData ℓ)
    (h : ∃ dK hK cE tK : ℕ, ∀ Co Ce : ℤ, ∀ F : Family, Dd.FinalFamilyAt Co Ce F →
      ∃ (I : Identification F.b dK hK cE tK) (sd : ScalarData I.B)
        (κ ε η : MonoidAlgebra OO (SignGroup F.b)) (RankOne Acyclic : Addr F.b → Prop),
        ClearingPatterns RankOne Acyclic ∧
        ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
          ClearingCoordIdentity I.B sd κ ε η 0 e g RankOne Acyclic) :
    ClearingModel Dd := by
  obtain ⟨dK, hK, cE, tK, hF⟩ := h
  refine ⟨dK, hK, cE, tK, fun Co Ce F hFam => ?_⟩
  obtain ⟨I, sd, κ, ε, η, RankOne, Acyclic, hpat, hcoord⟩ := hF Co Ce F hFam
  exact clearingModelOver_of_identification Dd F I sd κ ε η RankOne Acyclic hpat hcoord

end Identification

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
