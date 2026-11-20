import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ActualBlocks
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ConstituentCompletion
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.ScopedInventory

/-! A finite inventory for the actual even summands over one finite
extension of the fixed place, before asking for a Galois model. -/

noncomputable section

set_option maxHeartbeats 900000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs EvenBudget EvenExpansion NumberField ModularForm
open ThetaCoeff UpperHalfPlane Wiring IsDedekindDomain HeightOneSpectrum
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53
open scoped MatrixGroups AdicCompletionExtension

/-- The formal list of blocks: the moving block and the unary shells of
this fixed set. -/
abbrev EvenBlock (U : Finset ℕ) := Option ↥(subscripts U)

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}

def evenBlockLevel (P : EvenSource W L τ) {U : Finset ℕ} : EvenBlock U → ℕ
  | none => movingLevel P U
  | some j => maskedLevel P * j.val

def evenBlockSeries (P : EvenSource W L τ) (hS : SupportSpec W) (i : Fin 2)
    {U : Finset ℕ} : EvenBlock U → ℕ → ℂ
  | none => timesTheta (TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff)
  | some j => timesTheta
      (unaryCoeff (evenTypes W.S hS.1).Good (fun p => P.phaseData.η p) i j.val)

/-- An actual expression in normalized newforms and old degrees at the
block's intrinsic level and character. The weights here are complex; the
fields of definition are attached to the columns, before descending the
vector of coordinates. -/
structure CuspBlockExpansion (m : ℕ) (a : ℕ → ℂ) where
  level_ne : m ≠ 0
  χ : DirichletCharacter ℂ m
  columns : Finset (@CuspOldColumn m ⟨level_ne⟩ χ.toUnitHom)
  weight : @CuspOldColumn m ⟨level_ne⟩ χ.toUnitHom → ℂ
  eq_coeff : let _ : NeZero m := ⟨level_ne⟩
    ∀ n, a n = ∑ x ∈ columns, weight x * x.coeff n

namespace CuspBlockExpansion

variable {m : ℕ} {a : ℕ → ℂ} (A : CuspBlockExpansion m a)

def colCoeff (c : ↥A.columns) : ℕ → ℂ :=
  @CuspOldColumn.coeff m ⟨A.level_ne⟩ A.χ.toUnitHom c.val

def colField (c : ↥A.columns) : IntermediateField ℚ ℂ :=
  @CuspOldColumn.field m ⟨A.level_ne⟩ A.χ.toUnitHom c.val

theorem col_numberField (c : ↥A.columns) : NumberField (A.colField c) :=
  @CuspOldColumn.numberField m ⟨A.level_ne⟩ A.χ.toUnitHom c.val

theorem col_coeff_mem (c : ↥A.columns) {n : ℕ} (hn : 0 < n) :
    A.colCoeff c n ∈ A.colField c :=
  @CuspOldColumn.coeff_mem_field m ⟨A.level_ne⟩ A.χ.toUnitHom c.val n hn

end CuspBlockExpansion

variable {P : EvenSource W L τ}

/-- The finite list for each block is unconditional. The character
identities match those in the intrinsic-level statement of evenWeightTwo.
The expression also represents the actual joined form by assembleForm. -/
theorem exists_actual_cuspidal_inventory (hS : SupportSpec W) (i : Fin 2)
    (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    ∃ A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b) (evenBlockSeries P hS i b),
      IsMovingCharacter P U (A none).χ ∧ ∀ j : ↥(subscripts U),
        IsUnaryCharacter P i j.val (A (some j)).χ := by
  classical
  obtain ⟨χB, χJ, fB, fJ, hB, hJ, hmB, hmJ, hcB, hcJ, hqB, hqJ, _⟩ :=
    actual_cuspidal_blocks hS i U hU hodd
  have hmask : maskedLevel P ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne')
  have hmove : movingLevel P U ≠ 0 :=
    mul_ne_zero hmask (Finset.prod_ne_zero_iff.mpr fun p hp => (hU p hp).1.ne_zero)
  have hshell (j : ↥(subscripts U)) : maskedLevel P * j.val ≠ 0 :=
    mul_ne_zero hmask ((mem_subscripts (fun p hp => (hU p hp).1) j.val).mp j.property).1.ne_zero
  have aux (m : ℕ) (hm : m ≠ 0) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ m)
      (f : WeightTwo m) (hmem : f ∈ modFormCharSpace 2 χ.toUnitHom) (hc : f.IsCuspForm)
      (hq : ∀ n, (qExpansion 1 f).coeff n = a n) :
      ∃ A : CuspBlockExpansion m a, A.χ = χ := by
    let _ : NeZero m := ⟨hm⟩
    obtain ⟨g, hg⟩ := hc
    rw [← hg] at hmem hq
    have hm' := (coe_mem_modFormCharSpace_iff 2 χ.toUnitHom g).mp hmem
    obtain ⟨s, w, h⟩ := finite_cuspidal_columns hm'
    exact ⟨⟨hm, χ, s, w, fun n => (hq n).symm.trans (h n)⟩, rfl⟩
  obtain ⟨B, hB'⟩ := aux _ hmove _ χB fB hmB hcB hqB
  have hJ' (j : ↥(subscripts U)) :
      ∃ A : CuspBlockExpansion (evenBlockLevel P (some j))
          (evenBlockSeries P hS i (some j)), A.χ = χJ j :=
    aux _ (hshell j) _ (χJ j) (fJ j) (hmJ j) (hcJ j) (hqJ j)
  choose J hJ' using hJ'
  let A (b : EvenBlock U) : CuspBlockExpansion (evenBlockLevel P b) (evenBlockSeries P hS i b) :=
    match b with
    | none => B
    | some j => J j
  refine ⟨A, ?_, fun j => ?_⟩
  · change IsMovingCharacter P U B.χ
    rwa [hB']
  · change IsUnaryCharacter P i j.val (J j).χ
    rw [hJ']
    exact hJ j

/-- Use one coefficient place for all columns of the finite collection.
Each column is explicitly the image of its exact algebraic Fourier
coefficients in the receiving completion. -/
theorem actual_inventory_at_fixed_place
    (F : IntermediateField ℚ ℂ) [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (hS : SupportSpec W) (i : Fin 2) (U : Finset ℕ)
    (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    ∃ (A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b) (evenBlockSeries P hS i b))
      (E : IntermediateField ℚ ℂ) (_ : NumberField E) (hFE : F ≤ E)
      (w : HeightOneSpectrum (𝓞 E)),
      let _ : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
      ∃ (_ : w.asIdeal.LiesOver v.asIdeal),
        IsMovingCharacter P U (A none).χ ∧
        (∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ) ∧
        FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) ∧
        (∀ b (c : ↥(A b).columns), (A b).colField c ≤ E) ∧
        (∀ b (c : ↥(A b).columns), ∀ n > 0,
          ∃ x : E, constituentComplexEmbedding w (FinitePlace.embedding w x) = (A b).colCoeff c n) ∧
        (∀ x : F, constituentComplexEmbedding w
          (v.adicCompletionExtension F E w (FinitePlace.embedding v x)) = (x : ℂ)) := by
  classical
  obtain ⟨A, hA, hJ⟩ := exists_actual_cuspidal_inventory hS i U hU hodd
  let D := Σ b : EvenBlock U, ↥(A b).columns
  let fields (b : D) := (A b.1).colField b.2
  let _ : ∀ b : D, NumberField (fields b) := fun b => (A b.1).col_numberField b.2
  obtain ⟨E, hE, hFE, hf⟩ := finite_constituent_compositum F fields
  let _ : Algebra F E := (IntermediateField.inclusion hFE).toAlgebra
  obtain ⟨w, hw⟩ := exists_constituent_place (E := E) v
  refine ⟨A, E, hE, hFE, w, hw, hA, hJ, constituent_completion_finite v w,
    fun b c => hf ⟨b, c⟩, fun b c n hn => ?_, fun x => ?_⟩
  · let x : E := ⟨(A b).colCoeff c n, hf ⟨b, c⟩ ((A b).col_coeff_mem c hn)⟩
    exact ⟨x, constituentComplexEmbedding_constituent w x⟩
  · exact constituentComplexEmbedding_fixed w v x

end ZInQ.Manuscript.RC.EvenJoin
