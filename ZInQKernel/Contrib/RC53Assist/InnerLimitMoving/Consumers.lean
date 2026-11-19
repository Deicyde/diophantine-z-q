import ZInQKernel.Contrib.RC53Assist.InnerLimit.Objects
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.FiniteLevel
import ZInQKernel.Contrib.RC53Assist.StageCone.GenuineModel
import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Realization
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate

/-!
# Moving derivative labels and retained Selmer models

A derivative label denotes a sequence of primes. All finite coefficient diagrams
use the same ultrafilter. Matrix limits are taken over the integral coefficient
ring before localization or specialization. The comparison maps below are induced
by the retained cochain maps; no side cohomology equivalence is an input.

The constructions follow the retained finite-diagram lemma and the derivative
local-condition argument in the manuscript, lines 4391–4451 and 4834–4907.
-/

set_option maxHeartbeats 500000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitMoving

open CategoryTheory Filter Topology Matrix Module
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped PowerSeries.WithPiTopology

section MatrixDiagrams

variable {R : Type} [CommRing R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- A retained global, local-condition, and full-local diagram over finite coefficients. -/
structure SelmerDiagramStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) where
  global : ComplexStages I U
  condition : ComplexStages I U
  fullLocal : ComplexStages I U
  restriction : MapStages global fullLocal
  inclusion : MapStages condition fullLocal

/-- The three summands of a Selmer cochain, in global, condition, and shifted-local order. -/
abbrev selmerIndex (D : SelmerDiagramStages I U) (a : ℤ) :=
  Fin (D.global.rank a) ⊕ (Fin (D.condition.rank a) ⊕ Fin (D.fullLocal.rank (a - 1)))

/-- The number of coordinates in the actual Selmer cochain module. -/
def selmerRank (D : SelmerDiagramStages I U) (a : ℤ) : ℕ :=
  D.global.rank a + (D.condition.rank a + D.fullLocal.rank (a - 1))

/-- Concatenation of the three finite coordinate sets. -/
def selmerIndexEquiv (D : SelmerDiagramStages I U) (a : ℤ) :
    selmerIndex D a ≃ Fin (selmerRank D a) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

/-- The differential of the Selmer cone, before taking any limit. -/
def selmerBlock (D : SelmerDiagramStages I U) (i : ℕ) (a b : ℤ) (hab : a + 1 = b) :
    Matrix (selmerIndex D b) (selmerIndex D a) R :=
  Matrix.fromBlocks (D.global.d i a b hab) 0
    (Matrix.fromRows 0 (D.restriction.f i a (b - 1) (by omega)))
    (Matrix.fromBlocks (D.condition.d i a b hab) 0
      (-D.inclusion.f i a (b - 1) (by omega))
      (-D.fullLocal.d i (a - 1) (b - 1) (by omega)))

/-- The same differential on one finite set of coordinates. -/
def selmerStageMatrix (D : SelmerDiagramStages I U) (i : ℕ) (a b : ℤ) (hab : a + 1 = b) :
    Matrix (Fin (selmerRank D b)) (Fin (selmerRank D a)) R :=
  Matrix.reindex (selmerIndexEquiv D b) (selmerIndexEquiv D a) (selmerBlock D i a b hab)

/-- Selmer differentials square to zero at the retained coefficient precision. -/
theorem selmerBlock_square (D : SelmerDiagramStages I U) (a b c : ℤ)
    (hab : a + 1 = b) (hbc : b + 1 = c) :
    ∀ᶠ i in (U : Filter ℕ), ∀ x y,
      (selmerBlock D i b c hbc * selmerBlock D i a b hab) x y ∈ I i := by
  filter_upwards [D.global.square a b c hab hbc, D.condition.square a b c hab hbc,
    D.fullLocal.square (a - 1) (b - 1) (c - 1) (by omega) (by omega),
    D.restriction.comm a b (b - 1) (c - 1) (by omega) hab (by omega) (by omega),
    D.inclusion.comm a b (b - 1) (c - 1) (by omega) hab (by omega) (by omega)]
      with i hG hC hL hres hinc
  intro x y
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  all_goals
    simp only [selmerBlock, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
      add_zero, zero_add, Matrix.neg_apply, neg_mul, mul_neg, neg_neg, neg_zero,
      Finset.sum_neg_distrib]
  · exact hG x y
  · exact (I i).zero_mem
  · exact (I i).zero_mem
  · exact (I i).zero_mem
  · exact hC x y
  · exact (I i).zero_mem
  · simpa only [Matrix.sub_apply, Matrix.mul_apply, sub_eq_add_neg] using hres x y
  · simpa only [Matrix.sub_apply, Matrix.mul_apply, sub_eq_add_neg, neg_add_rev, neg_neg,
      add_comm] using (I i).neg_mem (hinc x y)
  · exact hL x y

/-- The retained finite free Selmer complex is constructed from its three diagrams. -/
def selmerStages (D : SelmerDiagramStages I U) : ComplexStages I U where
  rank := selmerRank D
  low := min D.global.low (min D.condition.low (D.fullLocal.low + 1))
  high := max D.global.high (max D.condition.high (D.fullLocal.high + 1))
  bounded a ha := by
    have hG : D.global.rank a = 0 := D.global.bounded a (by rcases ha with ha | ha <;> omega)
    have hC : D.condition.rank a = 0 := D.condition.bounded a (by rcases ha with ha | ha <;> omega)
    have hL : D.fullLocal.rank (a - 1) = 0 := D.fullLocal.bounded (a - 1) (by rcases ha with ha | ha <;> omega)
    simp only [selmerRank, hG, hC, hL, zero_add]
  d := selmerStageMatrix D
  square a b c hab hbc := (selmerBlock_square D a b c hab hbc).mono fun i hi x y => by
    change (Matrix.reindex (selmerIndexEquiv D c) (selmerIndexEquiv D b) (selmerBlock D i b c hbc) *
      Matrix.reindex (selmerIndexEquiv D b) (selmerIndexEquiv D a) (selmerBlock D i a b hab)) x y ∈ I i
    rw [Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv _ _ _ (selmerIndexEquiv D b).symm]
    exact hi _ _

/-- Splitting concatenated coordinates recovers the three Selmer cochain summands. -/
def selmerCoords (S : Type) [CommRing S] (D : SelmerDiagramStages I U) (a : ℤ) :
    (Fin (selmerRank D a) → S) ≃ₗ[S]
      (Fin (D.global.rank a) → S) × (Fin (D.condition.rank a) → S) ×
        (Fin (D.fullLocal.rank (a - 1)) → S) :=
  (LinearEquiv.funCongrLeft S S (selmerIndexEquiv D a)).trans
    ((LinearEquiv.sumArrowLequivProdArrow _ _ S S).trans
      ((LinearEquiv.refl S _).prodCongr (LinearEquiv.sumArrowLequivProdArrow _ _ S S)))

/-- The splitting reads the global coordinate directly. -/
theorem selmerCoords_global (S : Type) [CommRing S] (D : SelmerDiagramStages I U) (a : ℤ)
    (x : Fin (selmerRank D a) → S) (j : Fin (D.global.rank a)) :
    (selmerCoords S D a x).1 j = x (selmerIndexEquiv D a (Sum.inl j)) := rfl

/-- The splitting reads the local-condition coordinate directly. -/
theorem selmerCoords_condition (S : Type) [CommRing S] (D : SelmerDiagramStages I U) (a : ℤ)
    (x : Fin (selmerRank D a) → S) (j : Fin (D.condition.rank a)) :
    (selmerCoords S D a x).2.1 j = x (selmerIndexEquiv D a (Sum.inr (Sum.inl j))) := rfl

/-- The splitting reads the shifted full-local coordinate directly. -/
theorem selmerCoords_local (S : Type) [CommRing S] (D : SelmerDiagramStages I U) (a : ℤ)
    (x : Fin (selmerRank D a) → S) (j : Fin (D.fullLocal.rank (a - 1))) :
    (selmerCoords S D a x).2.2 j = x (selmerIndexEquiv D a (Sum.inr (Sum.inr j))) := rfl

/-- Splitting a matrix differential gives the literal Selmer differential. -/
theorem selmerCoords_stage_d (D : SelmerDiagramStages I U) (i : ℕ) (a b : ℤ) (hab : a + 1 = b)
    (x : Fin (selmerRank D a) → R) :
    selmerCoords R D b (selmerStageMatrix D i a b hab *ᵥ x) =
      (D.global.d i a b hab *ᵥ (selmerCoords R D a x).1,
        D.condition.d i a b hab *ᵥ (selmerCoords R D a x).2.1,
        D.restriction.f i a (b - 1) (by omega) *ᵥ (selmerCoords R D a x).1 -
          D.inclusion.f i a (b - 1) (by omega) *ᵥ (selmerCoords R D a x).2.1 -
          D.fullLocal.d i (a - 1) (b - 1) (by omega) *ᵥ (selmerCoords R D a x).2.2) := by
  rw [selmerStageMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  apply Prod.ext
  · funext j
    simp only [selmerCoords_global, Function.comp_apply, Equiv.symm_apply_apply,
      selmerBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    rfl
  · apply Prod.ext
    · funext j
      simp only [selmerCoords_condition, Function.comp_apply, Equiv.symm_apply_apply,
        selmerBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromRows_apply_inl, Matrix.zero_apply,
        zero_mul, Finset.sum_const_zero, add_zero, zero_add]
      rfl
    · funext j
      simp only [selmerCoords_local, selmerCoords_global, selmerCoords_condition,
        Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm,
        selmerBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inr,
        Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, Pi.sub_apply]
      abel

end MatrixDiagrams

section ScalarLimits

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {S : Type} [CommRing S]

/-- Scalar extension of the integral matrix limit, also allowing a localized coefficient ring. -/
def scalarComplex (ρ : R →+* S) (C : ComplexStages I U) : GCx S where
  X a := ModuleCat.of S (Fin (C.rank a) → S)
  d a b hab := Matrix.toLin' ((ulimMat U (fun i => C.d i a b hab)).map ρ)
  d_d a b c hab hbc x := by
    have he : (ulimMat U (fun i => C.d i b c hbc)).map ρ *
        (ulimMat U (fun i => C.d i a b hab)).map ρ = 0 := by
      rw [← Matrix.map_mul, differential_product_limit hI hU C a b c hab hbc]
      ext j l
      exact map_zero ρ
    change Matrix.toLin' ((ulimMat U (fun i => C.d i b c hbc)).map ρ)
      (Matrix.toLin' ((ulimMat U (fun i => C.d i a b hab)).map ρ) x) = 0
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, he]
    simp

/-- The scalar extension of a retained cochain map. -/
def scalarMap {C D : ComplexStages I U} (ρ : R →+* S) (F : MapStages C D) :
    GHom (scalarComplex hI hU ρ C) (scalarComplex hI hU ρ D) where
  f a b hab := Matrix.toLin' ((ulimMat U (fun i => F.f i a b hab)).map ρ)
  comm a a' b b' hab ha hb ha'b' x := by
    change (Fin (C.rank a) → S) at x
    have he : ulimMat U (fun i => F.f i a' b' ha'b') * ulimMat U (fun i => C.d i a a' ha) =
        ulimMat U (fun i => D.d i b b' hb) * ulimMat U (fun i => F.f i a b hab) := by
      rw [← ulimMat_mul, ← ulimMat_mul]
      exact ulimMat_eq_of_sub_mem hI hU (F.comm a a' b b' hab ha hb ha'b')
    have hs := congrArg (fun M : Matrix (Fin (D.rank b')) (Fin (C.rank a)) R => M.map ρ) he
    rw [Matrix.map_mul, Matrix.map_mul] at hs
    change Matrix.toLin' ((ulimMat U (fun i => F.f i a' b' ha'b')).map ρ)
      (Matrix.toLin' ((ulimMat U (fun i => C.d i a a' ha)).map ρ) x) =
        Matrix.toLin' ((ulimMat U (fun i => D.d i b b' hb)).map ρ)
          (Matrix.toLin' ((ulimMat U (fun i => F.f i a b hab)).map ρ) x)
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hs, Matrix.toLin'_mul, LinearMap.comp_apply]

/-- The Selmer data of the scalar-extended retained diagram. -/
def scalarSelmerData (ρ : R →+* S) (D : SelmerDiagramStages I U) : SelData S where
  G := scalarComplex hI hU ρ D.global
  U := scalarComplex hI hU ρ D.condition
  L := scalarComplex hI hU ρ D.fullLocal
  res := scalarMap hI hU ρ D.restriction
  ι := scalarMap hI hU ρ D.inclusion

/-- The cone block formed from the specialized integral limits of its retained entries. -/
def scalarSelmerBlock (ρ : R →+* S) (D : SelmerDiagramStages I U) (a b : ℤ) (hab : a + 1 = b) :
    Matrix (selmerIndex D b) (selmerIndex D a) S :=
  Matrix.fromBlocks ((ulimMat U (fun i => D.global.d i a b hab)).map ρ) 0
    (Matrix.fromRows 0 ((ulimMat U (fun i => D.restriction.f i a (b - 1) (by omega))).map ρ))
    (Matrix.fromBlocks ((ulimMat U (fun i => D.condition.d i a b hab)).map ρ) 0
      (-((ulimMat U (fun i => D.inclusion.f i a (b - 1) (by omega))).map ρ))
      (-((ulimMat U (fun i => D.fullLocal.d i (a - 1) (b - 1) (by omega))).map ρ)))

/-- Taking the coefficient limit commutes with forming the actual Selmer differential. -/
theorem scalarSelmerMatrix (ρ : R →+* S) (D : SelmerDiagramStages I U)
    (a b : ℤ) (hab : a + 1 = b) :
    (ulimMat U (fun i => selmerStageMatrix D i a b hab)).map ρ =
      Matrix.reindex (selmerIndexEquiv D b) (selmerIndexEquiv D a)
        (scalarSelmerBlock ρ D a b hab) := by
  ext x y
  simp only [selmerStageMatrix, Matrix.reindex_apply, Matrix.map_apply,
    Matrix.submatrix_apply, ulimMat_apply]
  generalize (selmerIndexEquiv D b).symm x = xb
  generalize (selmerIndexEquiv D a).symm y = ya
  rcases xb with xb | (xb | xb) <;> rcases ya with ya | (ya | ya) <;>
    simp [selmerBlock, scalarSelmerBlock, ulim_zero, ulim_neg, ulimMat_apply]

/-- The canonical coordinate comparison respects every differential after scalar extension. -/
theorem selmerCoords_scalar_d (ρ : R →+* S) (D : SelmerDiagramStages I U)
    (a b : ℤ) (hab : a + 1 = b) (x : Fin (selmerRank D a) → S) :
    selmerCoords S D b ((scalarComplex hI hU ρ (selmerStages D)).d a b hab x) =
      (selCx (scalarSelmerData hI hU ρ D)).d a b hab (selmerCoords S D a x) := by
  change selmerCoords S D b (((ulimMat U (fun i => selmerStageMatrix D i a b hab)).map ρ) *ᵥ x) = _
  rw [scalarSelmerMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  apply Prod.ext
  · funext j
    simp only [selmerCoords_global, Function.comp_apply, Equiv.symm_apply_apply,
      scalarSelmerBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    rfl
  · apply Prod.ext
    · funext j
      simp only [selmerCoords_condition, Function.comp_apply, Equiv.symm_apply_apply,
        scalarSelmerBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromRows_apply_inl, Matrix.zero_apply,
        zero_mul, Finset.sum_const_zero, add_zero, zero_add]
      rfl
    · funext j
      change _ = (((ulimMat U (fun i => D.restriction.f i a (b - 1) (by omega))).map ρ) *ᵥ
        (selmerCoords S D a x).1 -
        ((ulimMat U (fun i => D.inclusion.f i a (b - 1) (by omega))).map ρ) *ᵥ
          (selmerCoords S D a x).2.1 -
        ((ulimMat U (fun i => D.fullLocal.d i (a - 1) (b - 1) (by omega))).map ρ) *ᵥ
          (selmerCoords S D a x).2.2) j
      simp only [selmerCoords_local, selmerCoords_global, selmerCoords_condition,
        Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm,
        scalarSelmerBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inr,
        Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, Pi.sub_apply]
      abel

/-- The limit of the finite free Selmer models is the Selmer complex of the limit diagram. -/
def scalarSelmerIso (ρ : R →+* S) (D : SelmerDiagramStages I U) :
    (scalarComplex hI hU ρ (selmerStages D)).toCC ≅
      (selCx (scalarSelmerData hI hU ρ D)).toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (selmerCoords S D a).toModuleIso)
    (fun a b hab => by
      ext x
      change (Fin (selmerRank D a) → S) at x
      change ((selCx (scalarSelmerData hI hU ρ D)).toCC.d a b).hom (selmerCoords S D a x) =
        selmerCoords S D b (((scalarComplex hI hU ρ (selmerStages D)).toCC.d a b).hom x)
      erw [GCx.toCC_d_hom _ a b hab, GCx.toCC_d_hom _ a b hab]
      exact (selmerCoords_scalar_d hI hU ρ D a b hab x).symm)

/-- The induced homology equivalence is a consequence of that explicit cochain comparison. -/
def scalarSelmerH1Equiv (ρ : R →+* S) (D : SelmerDiagramStages I U) :
    (scalarComplex hI hU ρ (selmerStages D)).toCC.homology 1 ≃ₗ[S]
      (selCx (scalarSelmerData hI hU ρ D)).toCC.homology 1 :=
  ((HomotopyEquiv.ofIso (scalarSelmerIso hI hU ρ D)).toHomologyIso 1).toLinearEquiv

end ScalarLimits

section LocalModels

variable {R : Type} [CommRing R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- The four derivative local conditions, all retaining degree zero. -/
inductive ConditionKind
  | strict
  | finite
  | singular
  | relaxed
  deriving DecidableEq

/-- The degree-one rank of each derivative condition. -/
def conditionDim : ConditionKind → ℕ
  | .strict => 0
  | .finite => 2
  | .singular => 2
  | .relaxed => 4

/-- The ranks of the full retained tame complex. -/
def fullLocalRank : ℤ → ℕ
  | .ofNat 0 => 2
  | .ofNat 1 => 4
  | .ofNat 2 => 2
  | .ofNat (_ + 3) => 0
  | .negSucc _ => 0

/-- The condition has the same rank-two degree-zero term and no degree-two term. -/
def localConditionRank (s : ConditionKind) : ℤ → ℕ
  | .ofNat 0 => 2
  | .ofNat 1 => conditionDim s
  | .ofNat (_ + 2) => 0
  | .negSucc _ => 0

/-- The full local complex at the retained coefficient precision. -/
def fullLocalStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) : ComplexStages I U where
  rank := fullLocalRank
  low := 0
  high := 2
  bounded a ha := by
    rcases a with (_ | _ | _ | a) | a
    · change (0 : ℤ) < 0 ∨ 2 < 0 at ha; omega
    · change (1 : ℤ) < 0 ∨ 2 < 1 at ha; omega
    · change (2 : ℤ) < 0 ∨ 2 < 2 at ha; omega
    · rfl
    · rfl
  d _ _ _ _ := 0
  square _ _ _ _ _ := Eventually.of_forall fun i _ _ => by simp

/-- The four local conditions at finite coefficient precision. -/
def localConditionStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) (s : ConditionKind) : ComplexStages I U where
  rank := localConditionRank s
  low := 0
  high := 1
  bounded a ha := by
    rcases a with (_ | _ | a) | a
    · change (0 : ℤ) < 0 ∨ 1 < 0 at ha; omega
    · change (1 : ℤ) < 0 ∨ 1 < 1 at ha; omega
    · rfl
    · rfl
  d _ _ _ _ := 0
  square _ _ _ _ _ := Eventually.of_forall fun i _ _ => by simp

/-- Finite coordinates are included into the first half of the local coordinate module. -/
def finiteInclusionMatrix (R : Type) [CommRing R] : Matrix (Fin 4) (Fin 2) R :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _) (Matrix.fromRows (1 : Matrix (Fin 2) (Fin 2) R)
    (0 : Matrix (Fin 2) (Fin 2) R))

/-- Singular coordinates are included into the second half. -/
def singularInclusionMatrix (R : Type) [CommRing R] : Matrix (Fin 4) (Fin 2) R :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _) (Matrix.fromRows 0 (1 : Matrix (Fin 2) (Fin 2) R))

/-- The literal local-condition inclusion, including the identity in degree zero. -/
def localInclusionMatrix (R : Type) [CommRing R] (s : ConditionKind) :
    ∀ a, Matrix (Fin (fullLocalRank a)) (Fin (localConditionRank s a)) R
  | .ofNat 0 => (1 : Matrix (Fin 2) (Fin 2) R)
  | .ofNat 1 => match s with
    | .strict => 0
    | .finite => finiteInclusionMatrix R
    | .singular => singularInclusionMatrix R
    | .relaxed => (1 : Matrix (Fin 4) (Fin 4) R)
  | _ => 0

/-- These inclusions form retained cochain maps. -/
def localInclusionStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) (s : ConditionKind) :
    MapStages (localConditionStages I U s) (fullLocalStages I U) where
  f _ a b hab := by subst hab; exact localInclusionMatrix R s a
  comm a a' b b' hab ha hb ha'b' := by
    subst hab ha'b'
    exact Eventually.of_forall fun i x y => by
      change (localInclusionMatrix R s a' *
        (0 : Matrix (Fin (localConditionRank s a')) (Fin (localConditionRank s a)) R) -
        (0 : Matrix (Fin (fullLocalRank a')) (Fin (fullLocalRank a)) R) *
          localInclusionMatrix R s a) x y ∈ I i
      simp only [Matrix.mul_zero, Matrix.zero_mul, sub_self]
      change (0 : R) ∈ I i
      exact (I i).zero_mem

/-- A retained global model with the chosen derivative condition at the moving label. -/
def derivativeDiagram (C : ComplexStages I U) (r : MapStages C (fullLocalStages I U))
    (s : ConditionKind) : SelmerDiagramStages I U where
  global := C
  condition := localConditionStages I U s
  fullLocal := fullLocalStages I U
  restriction := r
  inclusion := localInclusionStages I U s

/-- A rank-four vector splits into its finite and singular rank-two coordinates. -/
def localPairCoords (S : Type) [CommRing S] : (Fin 4 → S) ≃ₗ[S] Coords S :=
  (LinearEquiv.funCongrLeft S S finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) S S)

/-- Coordinates of the full split local complex. -/
def fullLocalCoords (S : Type) [CommRing S] :
    ∀ a, (Fin (fullLocalRank a) → S) ≃ₗ[S] splitLocalTerms S a
  | .ofNat 0 => LinearEquiv.refl S _
  | .ofNat 1 => localPairCoords S
  | .ofNat 2 => LinearEquiv.refl S _
  | .ofNat (_ + 3) => LinearEquiv.ofSubsingleton (Fin 0 → S) PUnit
  | .negSucc _ => LinearEquiv.ofSubsingleton (Fin 0 → S) PUnit

/-- The actual integral coordinate plane of each condition. -/
def conditionPlane (S : Type) [CommRing S] : ConditionKind → Submodule S (Coords S)
  | .strict => ⊥
  | .finite => finiteAxis S
  | .singular => singularAxis S
  | .relaxed => ⊤

/-- The local-condition coordinates are determined by their respective axes. -/
def localConditionCoords (k : Type) [Field k] (s : ConditionKind) :
    ∀ a, (Fin (localConditionRank s a) → k) ≃ₗ[k] conditionTerms (conditionPlane k s) a
  | .ofNat 0 => LinearEquiv.refl k _
  | .ofNat 1 => match s with
    | .strict => LinearEquiv.ofSubsingleton (Fin 0 → k) (⊥ : Submodule k (Coords k))
    | .finite => (finiteAxisEquiv (R := k)).symm
    | .singular => (singularAxisEquiv (R := k)).symm
    | .relaxed => (localPairCoords k).trans (Submodule.topEquiv).symm
  | .ofNat (_ + 2) => LinearEquiv.ofSubsingleton (Fin 0 → k) PUnit
  | .negSucc _ => LinearEquiv.ofSubsingleton (Fin 0 → k) PUnit

end LocalModels

section LocalScalarComparisons

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {S : Type} [CommRing S]

/-- A retained zero differential stays zero after taking the integral limit and changing scalars. -/
theorem scalar_d_zero (ρ : R →+* S) (C : ComplexStages I U)
    (hC : ∀ i a b (hab : a + 1 = b), C.d i a b hab = 0) (a b : ℤ) :
    (scalarComplex hI hU ρ C).toCC.d a b = 0 := by
  by_cases hab : a + 1 = b
  · have hM : (ulimMat U (fun i => C.d i a b hab)).map ρ = 0 := by
      rw [show (fun i => C.d i a b hab) = fun _ => 0 from funext fun i => hC i a b hab,
        ulimMat_zero]
      ext x y
      exact map_zero ρ
    ext x
    change (Fin (C.rank a) → S) at x
    erw [GCx.toCC_d_hom _ a b hab]
    change Matrix.toLin' ((ulimMat U (fun i => C.d i a b hab)).map ρ) x = 0
    rw [hM]
    simp
  · exact (scalarComplex hI hU ρ C).toCC.shape a b hab

/-- The full retained local matrix complex is the author's actual split local complex. -/
def fullLocalScalarIso (ρ : R →+* S) :
    (scalarComplex hI hU ρ (fullLocalStages I U)).toCC ≅ (splitLocalComplex S).toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (fullLocalCoords S a).toModuleIso)
    (fun a b _ => by
      rw [scalar_d_zero hI hU ρ _ (fun _ _ _ _ => rfl), splitLocalComplex_d_zero]
      ext x
      change (0 : splitLocalTerms S b) = fullLocalCoords S b (0 : Fin (fullLocalRank b) → S)
      exact (map_zero (fullLocalCoords S b)).symm)

variable {k : Type} [Field k]

/-- Each finite-coefficient condition specializes to the actual condition in the split limit diagram. -/
def localConditionScalarIso (ρ : R →+* k) (s : ConditionKind) :
    (scalarComplex hI hU ρ (localConditionStages I U s)).toCC ≅
      (conditionComplex (conditionPlane k s)).toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (localConditionCoords k s a).toModuleIso)
    (fun a b _ => by
      rw [scalar_d_zero hI hU ρ _ (fun _ _ _ _ => rfl)]
      have hz : (conditionComplex (conditionPlane k s)).toCC.d a b = 0 := by
        dsimp [GCx.toCC, conditionComplex]
        split_ifs <;> rfl
      rw [hz]
      ext x
      change (0 : conditionTerms (conditionPlane k s) b) =
        localConditionCoords k s b (0 : Fin (localConditionRank s b) → k)
      exact (map_zero (localConditionCoords k s b)).symm)

end LocalScalarComparisons

section LocalCoordinateMaps

variable {R : Type} [CommRing R]

/-- The first coordinate half is exactly the finite inclusion. -/
theorem localPairCoords_finite (x : Fin 2 → R) :
    localPairCoords R (finiteInclusionMatrix R *ᵥ x) = (x, 0) := by
  rw [finiteInclusionMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Matrix.fromRows_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  apply Prod.ext
  · funext j
    change (Sum.elim x (0 : Fin 2 → R))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = x j
    rw [Equiv.symm_apply_apply]
    rfl
  · funext j
    change (Sum.elim x (0 : Fin 2 → R))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = 0
    rw [Equiv.symm_apply_apply]
    rfl

/-- The second coordinate half is exactly the singular inclusion. -/
theorem localPairCoords_singular (x : Fin 2 → R) :
    localPairCoords R (singularInclusionMatrix R *ᵥ x) = (0, x) := by
  rw [singularInclusionMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Matrix.fromRows_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]
  apply Prod.ext
  · funext j
    change (Sum.elim (0 : Fin 2 → R) x)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = 0
    rw [Equiv.symm_apply_apply]
    rfl
  · funext j
    change (Sum.elim (0 : Fin 2 → R) x)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = x j
    rw [Equiv.symm_apply_apply]
    rfl

variable {S : Type} [CommRing S]

/-- Finite-coordinate inclusions commute with every change of coefficients. -/
theorem finiteInclusionMatrix_map (ρ : R →+* S) :
    (finiteInclusionMatrix R).map ρ = finiteInclusionMatrix S := by
  ext a b
  rcases h : (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm a with a | a <;>
    simp [finiteInclusionMatrix, Matrix.reindex_apply, h, Matrix.one_apply]

/-- Singular-coordinate inclusions commute with every change of coefficients. -/
theorem singularInclusionMatrix_map (ρ : R →+* S) :
    (singularInclusionMatrix R).map ρ = singularInclusionMatrix S := by
  ext a b
  rcases h : (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm a with a | a <;>
    simp [singularInclusionMatrix, Matrix.reindex_apply, h, Matrix.one_apply]

/-- Every retained local inclusion commutes with changing coefficients. -/
theorem localInclusionMatrix_map (ρ : R →+* S) (s : ConditionKind) (a : ℤ) :
    (localInclusionMatrix R s a).map ρ = localInclusionMatrix S s a := by
  rcases a with (_ | _ | a) | a
  · change (1 : Matrix (Fin 2) (Fin 2) R).map ρ = 1
    exact Matrix.map_one _ (map_zero ρ) (map_one ρ)
  · cases s
    · ext x y; exact map_zero ρ
    · exact finiteInclusionMatrix_map ρ
    · exact singularInclusionMatrix_map ρ
    · change (1 : Matrix (Fin 4) (Fin 4) R).map ρ = 1
      exact Matrix.map_one _ (map_zero ρ) (map_one ρ)
  · ext x y; exact map_zero ρ
  · ext x y; exact map_zero ρ

variable {k : Type} [Field k]

/-- The coordinate equivalences preserve the actual local-condition inclusions. -/
theorem localInclusion_coordinates (s : ConditionKind) (a : ℤ)
    (x : Fin (localConditionRank s a) → k) :
    fullLocalCoords k a (localInclusionMatrix k s a *ᵥ x) =
      (conditionToLocal (conditionPlane k s)).f a a rfl (localConditionCoords k s a x) := by
  rcases a with (_ | _ | _ | a) | a
  · change (1 : Matrix (Fin 2) (Fin 2) k) *ᵥ x = x
    exact Matrix.one_mulVec x
  · cases s
    · change (Fin 0 → k) at x
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      rfl
    · change localPairCoords k (finiteInclusionMatrix k *ᵥ x) = (x, 0)
      exact localPairCoords_finite x
    · change localPairCoords k (singularInclusionMatrix k *ᵥ x) = (0, x)
      exact localPairCoords_singular x
    · change (Fin 4 → k) at x
      change localPairCoords k ((1 : Matrix (Fin 4) (Fin 4) k) *ᵥ x) = localPairCoords k x
      exact congrArg (localPairCoords k) (Matrix.one_mulVec x)
  · change (Fin 0 → k) at x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    rfl
  · change (_ : PUnit) = _
    exact Subsingleton.elim _ _
  · change (_ : PUnit) = _
    exact Subsingleton.elim _ _

end LocalCoordinateMaps

section CochainComparisons

variable {R : Type} [CommRing R]

/-- Read a genuine cochain map as a relation-indexed map without changing any component. -/
def relationMap {C D : GCx R} (f : C.toCC ⟶ D.toCC) : GHom C D where
  f a b hab := by subst hab; exact (f.f a).hom
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    change C.toCC.X a at x
    have he := congrArg (fun g => g.hom x) (f.comm a a')
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at he
    erw [GCx.toCC_d_hom C a a' ha, GCx.toCC_d_hom D a a' hb] at he
    exact he.symm

/-- Passing back to ordinary cochains recovers the same map. -/
theorem relationMap_toCC {C D : GCx R} (f : C.toCC ⟶ D.toCC) :
    GHom.toCC (relationMap f) = f := by
  ext a x
  rfl

end CochainComparisons

section DerivativeComparisons

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {k : Type} [Field k]

/-- The retained restriction map, in the limiting tame coordinates. -/
def derivativeRestriction (ρ : R →+* k) (C : ComplexStages I U)
    (r : MapStages C (fullLocalStages I U)) : GHom (scalarComplex hI hU ρ C) (splitLocalComplex k) :=
  ghomComp (scalarMap hI hU ρ r) (relationMap (fullLocalScalarIso hI hU ρ).hom)

/-- The actual split local datum with one of the four derivative conditions. -/
def derivativeSideData (ρ : R →+* k) (C : ComplexStages I U)
    (r : MapStages C (fullLocalStages I U)) (s : ConditionKind) : SelData k where
  G := scalarComplex hI hU ρ C
  U := conditionComplex (conditionPlane k s)
  L := splitLocalComplex k
  res := derivativeRestriction hI hU ρ C r
  ι := conditionToLocal (conditionPlane k s)

/-- The retained matrix inclusion becomes precisely the author's actual condition inclusion. -/
theorem derivative_inclusion_square (ρ : R →+* k) (s : ConditionKind) (a : ℤ)
    (x : Fin (localConditionRank s a) → k) :
    fullLocalCoords k a ((scalarMap hI hU ρ (localInclusionStages I U s)).f a a rfl x) =
      (conditionToLocal (conditionPlane k s)).f a a rfl (localConditionCoords k s a x) := by
  change fullLocalCoords k a (((ulimMat U (fun _ => localInclusionMatrix R s a)).map ρ) *ᵥ x) = _
  rw [ulimMat_const, localInclusionMatrix_map]
  exact localInclusion_coordinates s a x

/-- The comparison is a map of the actual Selmer diagrams, with no correction cochain. -/
def derivativeComparisonData (ρ : R →+* k) (C : ComplexStages I U)
    (r : MapStages C (fullLocalStages I U)) (s : ConditionKind) : SupportChangeData k where
  D := scalarSelmerData hI hU ρ (derivativeDiagram C r s)
  Dp := derivativeSideData hI hU ρ C r s
  g := idGHom _
  lam := relationMap (fullLocalScalarIso hI hU ρ).hom
  mu := relationMap (localConditionScalarIso hI hU ρ s).hom
  r := zeroGHom _ _
  hres a b hab x := by
    subst hab
    let y : (splitLocalComplex k).X a :=
      ((relationMap (fullLocalScalarIso hI hU ρ).hom).f a a rfl)
        ((scalarMap hI hU ρ r).f a a rfl x)
    have hz := map_zero ((conditionToLocal (conditionPlane k s)).f a a rfl)
    exact (add_zero y).symm.trans
      (congrArg (fun t : (splitLocalComplex k).X a => y + t) hz.symm)
  hι a b hab x := by
    subst hab
    exact (derivative_inclusion_square hI hU ρ s a x).symm

/-- The forward comparison on the Selmer cone is the product of the canonical coordinate equivalences. -/
theorem derivativeComparison_component (ρ : R →+* k) (C : ComplexStages I U)
    (r : MapStages C (fullLocalStages I U)) (s : ConditionKind) (a : ℤ) :
    (GHom.toCC (supportMap (derivativeComparisonData hI hU ρ C r s))).f a =
      ModuleCat.ofHom ((LinearEquiv.refl k (Fin (C.rank a) → k)).prodCongr
        ((localConditionCoords k s a).prodCongr (fullLocalCoords k (a - 1)))).toLinearMap := by
  ext x
  change (Fin (C.rank a) → k) × (Fin (localConditionRank s a) → k) ×
    (Fin (fullLocalRank (a - 1)) → k) at x
  change (x.1, localConditionCoords k s a x.2.1 + 0,
    fullLocalCoords k (a - 1) x.2.2) =
      (x.1, localConditionCoords k s a x.2.1, fullLocalCoords k (a - 1) x.2.2)
  rw [add_zero]

/-- The actual split Selmer cone is isomorphic to the scalar-extended retained diagram. -/
def derivativeSelmerIso (ρ : R →+* k) (C : ComplexStages I U)
    (r : MapStages C (fullLocalStages I U)) (s : ConditionKind) :
    (selCx (scalarSelmerData hI hU ρ (derivativeDiagram C r s))).toCC ≅
      (selCx (derivativeSideData hI hU ρ C r s)).toCC := by
  let f := GHom.toCC (supportMap (derivativeComparisonData hI hU ρ C r s))
  haveI : ∀ a, IsIso (f.f a) := fun a => by
    dsimp only [f]
    rw [derivativeComparison_component hI hU ρ C r s a]
    change IsIso (((LinearEquiv.refl k (Fin (C.rank a) → k)).prodCongr
      ((localConditionCoords k s a).prodCongr (fullLocalCoords k (a - 1)))).toModuleIso.hom)
    infer_instance
  have hIso : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact @asIso _ _ _ _ f hIso

/-- The side-to-matrix comparison is derived from the actual three-term Selmer cone. -/
def derivativeMatrixIso (ρ : R →+* k) (C : ComplexStages I U)
    (r : MapStages C (fullLocalStages I U)) (s : ConditionKind) :
    (scalarComplex hI hU ρ (selmerStages (derivativeDiagram C r s))).toCC ≅
      (selCx (derivativeSideData hI hU ρ C r s)).toCC :=
  scalarSelmerIso hI hU ρ (derivativeDiagram C r s) ≪≫ derivativeSelmerIso hI hU ρ C r s

end DerivativeComparisons

section CoefficientStages

variable {R : Type} [CommRing R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}

/-- The retained matrices define a genuine complex at this finite coefficient stage. -/
def CoefficientSquaredZero (C : ComplexStages I U) (i : ℕ) : Prop :=
  ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), ∀ x y,
    (C.d i b c hbc * C.d i a b hab) x y ∈ I i

/-- Boundedness lets all differential-square identities hold on one common set of stages. -/
theorem eventually_coefficientSquaredZero (C : ComplexStages I U) :
    ∀ᶠ i in (U : Filter ℕ), CoefficientSquaredZero C i := by
  have hf : ∀ a : Finset.Icc C.low C.high,
      ∀ᶠ i in (U : Filter ℕ), ∀ x y,
        (C.d i (a + 1) (a + 1 + 1) rfl * C.d i a (a + 1) rfl) x y ∈ I i :=
    fun a => C.square a (a + 1) (a + 1 + 1) rfl rfl
  filter_upwards [Filter.eventually_all.mpr hf] with i hi
  intro a b c hab hbc x y
  subst hab hbc
  by_cases ha : a ∈ Finset.Icc C.low C.high
  · exact hi ⟨a, ha⟩ x y
  · have hr : C.rank a = 0 := C.bounded a (by simp only [Finset.mem_Icc] at ha; omega)
    have : IsEmpty (Fin (C.rank a)) := by rw [hr]; infer_instance
    exact isEmptyElim y

/-- The genuine finite-coefficient complex of the retained matrices. -/
def coefficientComplex (C : ComplexStages I U) (i : ℕ) (hC : CoefficientSquaredZero C i) :
    GCx (R ⧸ I i) where
  X a := ModuleCat.of (R ⧸ I i) (Fin (C.rank a) → R ⧸ I i)
  d a b hab := Matrix.toLin' ((C.d i a b hab).map (Ideal.Quotient.mk (I i)))
  d_d a b c hab hbc x := by
    change (Fin (C.rank a) → R ⧸ I i) at x
    have he : (C.d i b c hbc).map (Ideal.Quotient.mk (I i)) *
        (C.d i a b hab).map (Ideal.Quotient.mk (I i)) = 0 := by
      rw [← Matrix.map_mul]
      ext j l
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hC a b c hab hbc j l)
    change Matrix.toLin' ((C.d i b c hbc).map (Ideal.Quotient.mk (I i)))
      (Matrix.toLin' ((C.d i a b hab).map (Ideal.Quotient.mk (I i))) x) = 0
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, he]
    simp

/-- The retained comparison is a genuine cochain map at this coefficient stage. -/
def CoefficientCommutation {C D : ComplexStages I U} (F : MapStages C D) (i : ℕ) : Prop :=
  ∀ a a' b b' (hab : a = b) (ha : a + 1 = a') (hb : b + 1 = b') (ha'b' : a' = b'), ∀ x y,
    (F.f i a' b' ha'b' * C.d i a a' ha - D.d i b b' hb * F.f i a b hab) x y ∈ I i

/-- The same bounded diagram gives a common set on which all comparison identities hold. -/
theorem eventually_coefficientCommutation {C D : ComplexStages I U} (F : MapStages C D) :
    ∀ᶠ i in (U : Filter ℕ), CoefficientCommutation F i := by
  have hf : ∀ a : Finset.Icc C.low C.high,
      ∀ᶠ i in (U : Filter ℕ), ∀ x y,
        (F.f i (a + 1) (a + 1) rfl * C.d i a (a + 1) rfl -
          D.d i a (a + 1) rfl * F.f i a a rfl) x y ∈ I i :=
    fun a => F.comm a (a + 1) a (a + 1) rfl rfl rfl rfl
  filter_upwards [Filter.eventually_all.mpr hf] with i hi
  intro a a' b b' hab ha hb ha'b' x y
  subst hab ha'b' ha
  by_cases ha : a ∈ Finset.Icc C.low C.high
  · exact hi ⟨a, ha⟩ x y
  · have hr : C.rank a = 0 := C.bounded a (by simp only [Finset.mem_Icc] at ha; omega)
    have : IsEmpty (Fin (C.rank a)) := by rw [hr]; infer_instance
    exact isEmptyElim y

/-- Reduction of the retained map is the actual map between its finite-coefficient complexes. -/
def coefficientMap {C D : ComplexStages I U} (F : MapStages C D) (i : ℕ)
    (hC : CoefficientSquaredZero C i) (hD : CoefficientSquaredZero D i)
    (hF : CoefficientCommutation F i) :
    GHom (coefficientComplex C i hC) (coefficientComplex D i hD) where
  f a b hab := Matrix.toLin' ((F.f i a b hab).map (Ideal.Quotient.mk (I i)))
  comm a a' b b' hab ha hb ha'b' x := by
    change (Fin (C.rank a) → R ⧸ I i) at x
    have he : (F.f i a' b' ha'b').map (Ideal.Quotient.mk (I i)) *
        (C.d i a a' ha).map (Ideal.Quotient.mk (I i)) =
      (D.d i b b' hb).map (Ideal.Quotient.mk (I i)) *
        (F.f i a b hab).map (Ideal.Quotient.mk (I i)) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      ext j l
      exact Ideal.Quotient.eq.mpr (hF a a' b b' hab ha hb ha'b' j l)
    change Matrix.toLin' ((F.f i a' b' ha'b').map (Ideal.Quotient.mk (I i)))
      (Matrix.toLin' ((C.d i a a' ha).map (Ideal.Quotient.mk (I i))) x) =
        Matrix.toLin' ((D.d i b b' hb).map (Ideal.Quotient.mk (I i)))
          (Matrix.toLin' ((F.f i a b hab).map (Ideal.Quotient.mk (I i))) x)
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, he, Matrix.toLin'_mul, LinearMap.comp_apply]

end CoefficientStages

section OldConditions

variable {R : Type} [CommRing R]

/-- The product of two relation-indexed complexes, with the product differential. -/
def productComplex (C D : GCx R) : GCx R where
  X a := ModuleCat.of R (C.X a × D.X a)
  d a b hab := (C.d a b hab).prodMap (D.d a b hab)
  d_d a b c hab hbc x := Prod.ext (C.d_d a b c hab hbc x.1) (D.d_d a b c hab hbc x.2)

/-- The product of two actual cochain maps. -/
def productMap {C D E F : GCx R} (f : GHom C D) (g : GHom E F) :
    GHom (productComplex C E) (productComplex D F) where
  f a b hab := (f.f a b hab).prodMap (g.f a b hab)
  comm a a' b b' hab ha hb ha'b' x :=
    Prod.ext (f.comm a a' b b' hab ha hb ha'b' x.1) (g.comm a a' b b' hab ha hb ha'b' x.2)

/-- Two localization maps with a common source, paired as one actual cochain map. -/
def pairedMap {C D E : GCx R} (f : GHom C D) (g : GHom C E) : GHom C (productComplex D E) where
  f a b hab := (f.f a b hab).prod (g.f a b hab)
  comm a a' b b' hab ha hb ha'b' x :=
    Prod.ext (f.comm a a' b b' hab ha hb ha'b' x) (g.comm a a' b b' hab ha hb ha'b' x)

/-- Add one new local condition while retaining the old global and local-condition diagram. -/
def compoundData (D : SelData R) (L : GCx R) (r : GHom D.G L) (V : GCx R) (j : GHom V L) :
    SelData R where
  G := D.G
  U := productComplex D.U V
  L := productComplex D.L L
  res := pairedMap D.res r
  ι := productMap D.ι j

/-- Localization of the old Selmer cone at the new label reads its original global component. -/
def oldRestriction (D : SelData R) (L : GCx R) (r : GHom D.G L) : GHom (selCx D) L where
  f a b hab := r.f a b hab ∘ₗ LinearMap.fst R _ _
  comm a a' b b' hab ha hb ha'b' x := r.comm a a' b b' hab ha hb ha'b' x.1

/-- The new local condition applied to the actual old Selmer cone. -/
def iteratedData (D : SelData R) (L : GCx R) (r : GHom D.G L) (V : GCx R) (j : GHom V L) :
    SelData R where
  G := selCx D
  U := V
  L := L
  res := oldRestriction D L r
  ι := j

/-- Reassociation of old and new Selmer cochains; it does not change any coordinate. -/
def iteratedSelmerCoords (D : SelData R) (L : GCx R) (V : GCx R) (a : ℤ) :
    ((D.G.X a × D.U.X a × D.L.X (a - 1)) × V.X a × L.X (a - 1)) ≃ₗ[R]
      D.G.X a × (D.U.X a × V.X a) × (D.L.X (a - 1) × L.X (a - 1)) where
  toFun x := (x.1.1, (x.1.2.1, x.2.1), (x.1.2.2, x.2.2))
  invFun x := ((x.1, x.2.1.1, x.2.2.1), x.2.1.2, x.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cochain permutation from the iterated cone to the full cone. -/
def iteratedSelmerMap (D : SelData R) (L : GCx R) (r : GHom D.G L) (V : GCx R) (j : GHom V L) :
    GHom (selCx (iteratedData D L r V j)) (selCx (compoundData D L r V j)) where
  f a b hab := by subst hab; exact (iteratedSelmerCoords D L V a).toLinearMap
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    rfl

/-- Its component is exactly the canonical cochain reassociation. -/
theorem iteratedSelmerMap_component (D : SelData R) (L : GCx R) (r : GHom D.G L)
    (V : GCx R) (j : GHom V L) (a : ℤ) :
    (GHom.toCC (iteratedSelmerMap D L r V j)).f a =
      ModuleCat.ofHom (iteratedSelmerCoords D L V a).toLinearMap := rfl

/-- Isolating a new label and retaining the old Selmer cone gives the same full Selmer complex. -/
def iteratedSelmerIso (D : SelData R) (L : GCx R) (r : GHom D.G L) (V : GCx R) (j : GHom V L) :
    (selCx (iteratedData D L r V j)).toCC ≅ (selCx (compoundData D L r V j)).toCC := by
  let f := GHom.toCC (iteratedSelmerMap D L r V j)
  haveI : ∀ a, IsIso (f.f a) := fun a => by
    dsimp only [f]
    rw [iteratedSelmerMap_component]
    change IsIso ((iteratedSelmerCoords D L V a).toModuleIso.hom)
    infer_instance
  have hIso : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact @asIso _ _ _ _ f hIso

/-- Quotient localization of the compound condition is the new-condition quotient alone. -/
def newConditionQuotient (A : GCx R) {V W : GCx R} (q : GHom V W) :
    GHom (productComplex A V) W where
  f a b hab := q.f a b hab ∘ₗ LinearMap.snd R _ _
  comm a a' b b' hab ha hb ha'b' x := q.comm a a' b b' hab ha hb ha'b' x.2

/-- The cochain permutation respects the actual quotient localization. -/
theorem iteratedQuotient_square (D : SelData R) (L : GCx R) (r : GHom D.G L)
    (V : GCx R) (j : GHom V L) (W : GCx R) (q : GHom V W) :
    (iteratedSelmerIso D L r V j).hom ≫
      GHom.toCC (quotMap (compoundData D L r V j) (newConditionQuotient D.U q)) =
        GHom.toCC (quotMap (iteratedData D L r V j) q) := by
  ext a x
  rfl

/-- The induced equivalence on actual Selmer cohomology. -/
def iteratedH1Equiv (D : SelData R) (L : GCx R) (r : GHom D.G L) (V : GCx R) (j : GHom V L) :
    (selCx (iteratedData D L r V j)).toCC.homology 1 ≃ₗ[R]
      (selCx (compoundData D L r V j)).toCC.homology 1 :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) 1).mapIso
    (iteratedSelmerIso D L r V j)).toLinearEquiv

/-- The cohomology comparison preserves localization, not merely dimension. -/
theorem iteratedLocalization_natural (D : SelData R) (L : GCx R) (r : GHom D.G L)
    (V : GCx R) (j : GHom V L) (W : GCx R) (q : GHom V W) :
    HomologicalComplex.homologyMap (iteratedSelmerIso D L r V j).hom 1 ≫
      HomologicalComplex.homologyMap
        (GHom.toCC (quotMap (compoundData D L r V j) (newConditionQuotient D.U q))) 1 =
      HomologicalComplex.homologyMap (GHom.toCC (quotMap (iteratedData D L r V j) q)) 1 := by
  rw [← HomologicalComplex.homologyMap_comp, iteratedQuotient_square]

end OldConditions

section MinimalModels

open ZInQ.Contrib.CloudB3RC53.ResidualTransfer
open ZInQ.Contrib.RC53Assist.StageCone

variable {A : Type} [CommRing A] [IsLocalRing A]

/-- Residual support, balance, and positivity of the specified integral complex. -/
def ResidualTwoTermShape (C : GCx A) : Prop :=
  (∀ i : ℤ, i ≠ 1 → i ≠ 2 →
    finrank (IsLocalRing.ResidueField A) ((resCx C.toCC).homology i) = 0) ∧
  finrank (IsLocalRing.ResidueField A) ((resCx C.toCC).homology 1) =
    finrank (IsLocalRing.ResidueField A) ((resCx C.toCC).homology 2) ∧
  0 < finrank (IsLocalRing.ResidueField A) ((resCx C.toCC).homology 1)

/-- A based minimal model of the specified complex, constructed by unit-disk cancellation. -/
structure BasedTwoTermModel (C : GCx A) where
  model : GCx A
  n : ℕ
  equivalence : HomotopyEquiv C.toCC model.toCC
  b1 : Basis (Fin (n + 1)) A (model.X 1)
  b2 : Basis (Fin (n + 1)) A (model.X 2)
  outside : ∀ i : ℤ, i ≠ 1 → i ≠ 2 → Subsingleton (model.X i)
  minimal : ∀ i j (hij : i + 1 = j) (x : model.X i),
    model.d i j hij x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (model.X j))

/-- The based two-term model is obtained from bounded finite-free data, not a side equivalence input. -/
theorem exists_basedTwoTermModel (C : GCx A)
    (hfree : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hbound : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (C.X i))
    (hshape : ResidualTwoTermShape C) : Nonempty (BasedTwoTermModel C) := by
  obtain ⟨L, ⟨e⟩, hL, hmin, _, hrank⟩ :=
    minimalModelsExist_proof A C.toCC hfree hbound
  let n := finrank (IsLocalRing.ResidueField A) ((resCx C.toCC).homology 1) - 1
  have hn : n + 1 = finrank (IsLocalRing.ResidueField A) ((resCx C.toCC).homology 1) := by
    dsimp only [n]
    exact Nat.sub_add_cancel hshape.2.2
  have h1 : finrank A (L.X 1) = n + 1 := (hrank 1).trans hn.symm
  have h2 : finrank A (L.X 2) = n + 1 := (hrank 2).trans (hshape.2.1.symm.trans hn.symm)
  have hfree1 : Module.Free A (L.X 1) := (hL 1).1
  have hfinite1 : Module.Finite A (L.X 1) := (hL 1).2
  have hfree2 : Module.Free A (L.X 2) := (hL 2).1
  have hfinite2 : Module.Finite A (L.X 2) := (hL 2).2
  have hout : ∀ i : ℤ, i ≠ 1 → i ≠ 2 → Subsingleton (L.X i) := by
    intro i hi1 hi2
    have hfreei : Module.Free A (L.X i) := (hL i).1
    have hfinitei : Module.Finite A (L.X i) := (hL i).2
    apply free_subsingleton_of_finrank_zero (A := A) (L.X i)
    rw [hrank i, hshape.1 i hi1 hi2]
  exact ⟨{
    model := ofCC L
    n := n
    equivalence := e.trans (HomotopyEquiv.ofIso (ofCCToCCIso L).symm)
    b1 := finBasisOfFinrank (A := A) (L.X 1) (n + 1) h1
    b2 := finBasisOfFinrank (A := A) (L.X 2) (n + 1) h2
    outside := hout
    minimal := fun i j _ x => hmin i j x }⟩

/-- Choose the proved minimal model of the specified bounded integral complex. -/
def basedTwoTermModel (C : GCx A)
    (hfree : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hbound : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (C.X i))
    (hshape : ResidualTwoTermShape C) : BasedTwoTermModel C :=
  (exists_basedTwoTermModel C hfree hbound hshape).some

variable {C : GCx A}

/-- The realized map back to the specified integral complex is the actual homotopy inverse. -/
def BasedTwoTermModel.realization (M : BasedTwoTermModel C) : TwoTermRealization C where
  model := M.model
  n := M.n
  b1 := M.b1
  b2 := M.b2
  outside := M.outside
  f := relationMap M.equivalence.inv
  quasiIso := by
    rw [relationMap_toCC]
    exact M.equivalence.quasiIso_inv

/-- The class, functional, and generic coordinate are constructed in that genuine realization. -/
def BasedTwoTermModel.stage (M : BasedTwoTermModel C) {F : Type} [Field F] (ι : A →+* F)
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y, lam (C.d 1 2 rfl y) = 0)
    (hdet : (M.realization.matrix.map ι).det = 0)
    (hadj : (M.realization.matrix.map ι).adjugate ≠ 0) : TwoTermStage ι :=
  stageOfRealization M.realization ι z hz lam hlam hdet hadj

/-- The constructed stage retains the actual class, up to its specified integral boundary. -/
theorem BasedTwoTermModel.stage_class (M : BasedTwoTermModel C) {F : Type} [Field F] (ι : A →+* F)
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y, lam (C.d 1 2 rfl y) = 0)
    (hdet : (M.realization.matrix.map ι).det = 0)
    (hadj : (M.realization.matrix.map ι).adjugate ≠ 0) :
    M.realization.f.f 1 1 rfl
        (M.b1.equivFun.symm (M.stage ι z hz lam hlam hdet hadj).z) =
      z + C.d 0 1 rfl (M.realization.boundaryWitness z hz) :=
  stageOfRealization_class M.realization ι z hz lam hlam hdet hadj

/-- The stage row is the pullback of the specified functional of the actual class. -/
theorem BasedTwoTermModel.stage_functional (M : BasedTwoTermModel C) {F : Type} [Field F]
    (ι : A →+* F) (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y, lam (C.d 1 2 rfl y) = 0)
    (hdet : (M.realization.matrix.map ι).det = 0)
    (hadj : (M.realization.matrix.map ι).adjugate ≠ 0) (x : Fin (M.n + 1) → A) :
    (M.stage ι z hz lam hlam hdet hadj).w ⬝ᵥ x =
      lam (M.realization.f.f 2 2 rfl (M.b2.equivFun.symm x)) :=
  stageOfRealization_functional M.realization ι z hz lam hlam hdet hadj x

/-- Minimality makes the computed stage differential vanish in the actual residue field. -/
theorem BasedTwoTermModel.matrix_residue_zero (M : BasedTwoTermModel C) :
    M.realization.matrix.map (IsLocalRing.residue A) = 0 := by
  have hk : ∀ y : M.model.X 2,
      y ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M.model.X 2)) →
      ∀ i, IsLocalRing.residue A (M.b2.equivFun y i) = 0 := by
    intro y hy i
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha x _
      rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
        (IsLocalRing.residue_eq_zero_iff a).mpr ha, zero_mul]
    · intro x y hx hy
      rw [map_add, Pi.add_apply, map_add, hx, hy, add_zero]
  ext i j
  have he := congrFun (M.realization.matrix_mulVec (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct_single, mul_one] at he
  change IsLocalRing.residue A (M.realization.matrix i j) = 0
  rw [he]
  exact hk _ (M.minimal 1 2 rfl _) i

/-- Scalar extension preserves the actual homotopy equivalence, without a flatness assumption. -/
def BasedTwoTermModel.residualEquivalence (M : BasedTwoTermModel C) :
    HomotopyEquiv (resCx C.toCC) (resCx M.model.toCC) := by
  letI := resF_additive (R := A)
  exact (resF A).mapHomotopyEquiv M.equivalence

/-- Every residual differential of the genuine minimal model is zero. -/
theorem BasedTwoTermModel.residual_d_zero (M : BasedTwoTermModel C) (i j : ℤ) :
    (resCx M.model.toCC).d i j = 0 := by
  apply resF_map_eq_zero
  intro x
  by_cases hij : i + 1 = j
  · change M.model.X i at x
    have he := GCx.toCC_d_hom M.model i j hij x
    exact he.symm ▸ M.minimal i j hij x
  · rw [M.model.toCC.shape i j hij, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- The retained basis identifies the residual degree-one model with its actual coordinate module. -/
def BasedTwoTermModel.residualCoords (M : BasedTwoTermModel C) :
    (resCx M.model.toCC).X 1 ≃ₗ[IsLocalRing.ResidueField A]
      (Fin (M.n + 1) → IsLocalRing.ResidueField A) := by
  letI := (IsLocalRing.residue A).toAlgebra
  exact (M.b1.baseChange (IsLocalRing.ResidueField A)).equivFun

/-- Actual first cohomology of the residual minimal model, in the retained coordinates. -/
def BasedTwoTermModel.residualH1Coords (M : BasedTwoTermModel C) :
    (resCx M.model.toCC).homology 1 ≃ₗ[IsLocalRing.ResidueField A]
      (Fin (M.n + 1) → IsLocalRing.ResidueField A) :=
  (((resCx M.model.toCC).isoHomologyπ 0 1 (by simp) (M.residual_d_zero 0 1)).symm ≪≫
    (resCx M.model.toCC).iCyclesIso 1 2 (by simp) (M.residual_d_zero 1 2)).toLinearEquiv |>.trans M.residualCoords

/-- The two-term consumer fibre has the same coordinates when its computed residue matrix vanishes. -/
def zeroStageH1Coords {F : Type} [Field F] {ι : A →+* F} (S : TwoTermStage ι)
    (hS : S.D.map (IsLocalRing.residue A) = 0) :
    fiberH1 (IsLocalRing.residue A) S ≃ₗ[IsLocalRing.ResidueField A]
      (Fin (S.n + 1) → IsLocalRing.ResidueField A) := by
  let K := twoTermFiberComplex (IsLocalRing.residue A) S
  have hd0 : K.d 0 1 = 0 := rfl
  have hd1 : K.d 1 2 = 0 := by
    change ModuleCat.ofHom ((S.D.map (IsLocalRing.residue A)).mulVecLin) = 0
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (Fin (S.n + 1) → IsLocalRing.ResidueField A) at x
    change (S.D.map (IsLocalRing.residue A)) *ᵥ x = 0
    rw [hS, Matrix.zero_mulVec]
  exact ((K.isoHomologyπ 0 1 (by simp) hd0).symm ≪≫ K.iCyclesIso 1 2 (by simp) hd1).toLinearEquiv

/-- The side-to-stage equivalence is derived from unit-disk cancellation and its retained maps. -/
def BasedTwoTermModel.stageH1Equiv (M : BasedTwoTermModel C) {F : Type} [Field F] (ι : A →+* F)
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y, lam (C.d 1 2 rfl y) = 0)
    (hdet : (M.realization.matrix.map ι).det = 0)
    (hadj : (M.realization.matrix.map ι).adjugate ≠ 0) :
    (resCx C.toCC).homology 1 ≃ₗ[IsLocalRing.ResidueField A]
      fiberH1 (IsLocalRing.residue A) (M.stage ι z hz lam hlam hdet hadj) :=
  ((M.residualEquivalence.toHomologyIso 1).toLinearEquiv.trans M.residualH1Coords).trans
    (zeroStageH1Coords (M.stage ι z hz lam hlam hdet hadj) M.matrix_residue_zero).symm

end MinimalModels

section ScalarCoordinates

open scoped ChangeOfRings

variable {A k : Type} [CommRing A] [CommRing k]

/-- The canonical coordinates of a scalar-extended finite free module. -/
def tensorVectorCoords (ρ : A →+* k) (n : ℕ) :
    (ModuleCat.extendScalars ρ).obj (ModuleCat.of A (Fin n → A)) ≃ₗ[k] (Fin n → k) := by
  letI := ρ.toAlgebra
  exact TensorProduct.piScalarRight A k k (Fin n)

/-- These coordinates are induced by the coefficient map, not by an arbitrary equivalence. -/
theorem tensorVectorCoords_tmul (ρ : A →+* k) (n : ℕ) (s : k) (x : Fin n → A) :
    tensorVectorCoords ρ n (s ⊗ₜ[A, ρ] x) = fun i => ρ (x i) * s := by
  let _ := ρ.toAlgebra
  change TensorProduct.piScalarRight A k k (Fin n) (s ⊗ₜ[A] x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- Coordinates commute with every actual matrix map under scalar extension. -/
theorem tensorMatrix_square (ρ : A →+* k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) A) :
    (ModuleCat.extendScalars ρ).map (ModuleCat.ofHom (Matrix.toLin' M)) ≫
      (tensorVectorCoords ρ m).toModuleIso.hom =
    (tensorVectorCoords ρ n).toModuleIso.hom ≫ ModuleCat.ofHom (Matrix.toLin' (M.map ρ)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (Fin n → A) at x
  change tensorVectorCoords ρ m
      ((ModuleCat.extendScalars ρ).map (ModuleCat.ofHom (Matrix.toLin' M))
        ((1 : k) ⊗ₜ[A, ρ] x)) =
    Matrix.toLin' (M.map ρ) (tensorVectorCoords ρ n ((1 : k) ⊗ₜ[A, ρ] x))
  calc
    _ = tensorVectorCoords ρ m ((1 : k) ⊗ₜ[A, ρ] (M *ᵥ x)) :=
      congrArg (tensorVectorCoords ρ m)
        (ModuleCat.ExtendScalars.map_tmul ρ (ModuleCat.ofHom (Matrix.toLin' M)) 1 x)
    _ = (fun i => ρ ((M *ᵥ x) i) * 1) := tensorVectorCoords_tmul ρ m 1 (M *ᵥ x)
    _ = Matrix.toLin' (M.map ρ) (fun i => ρ (x i) * 1) := by
      simp only [mul_one, Matrix.toLin'_apply]
      funext i
      exact RingHom.map_mulVec ρ M x i
    _ = _ := congrArg (Matrix.toLin' (M.map ρ)) (tensorVectorCoords_tmul ρ n 1 x).symm

/-- Entrywise scalar extension respects composition of coefficient maps. -/
theorem matrix_map_comp {R : Type} [CommRing R] (ρ : R →+* A) (τ : A →+* k)
    {m n : Type} (M : Matrix m n R) :
    (M.map ρ).map τ = M.map (τ.comp ρ) := rfl

end ScalarCoordinates

section ResidualMatrixComparisons

open ZInQ.Contrib.CloudB3RC53.ResidualTransfer
open ZInQ.Contrib.RC53Assist.StageCone

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {A : Type} [CommRing A] [IsLocalRing A]

/-- The residue of the integral matrix limit is the same matrix complex as direct fixed-field specialization. -/
def residualMatrixRelationMap (ρ : R →+* A) (C : ComplexStages I U) :
    GHom (ofCC (resCx (scalarComplex hI hU ρ C).toCC))
      (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) C) where
  f a b hab := by subst hab; exact (tensorVectorCoords (IsLocalRing.residue A) (C.rank a)).toLinearMap
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    have hd : (scalarComplex hI hU ρ C).toCC.d a a' =
        ModuleCat.ofHom (Matrix.toLin' ((ulimMat U (fun i => C.d i a a' ha)).map ρ)) := by
      dsimp only [GCx.toCC]
      rw [dite_eq_left ha]
      rfl
    have he := congrArg (fun f => f.hom x)
      (tensorMatrix_square (IsLocalRing.residue A) ((ulimMat U (fun i => C.d i a a' ha)).map ρ))
    change tensorVectorCoords (IsLocalRing.residue A) (C.rank a')
        ((resF A).map (ModuleCat.ofHom
          (Matrix.toLin' ((ulimMat U (fun i => C.d i a a' ha)).map ρ))) x) =
      Matrix.toLin' (((ulimMat U (fun i => C.d i a a' ha)).map ρ).map (IsLocalRing.residue A))
        (tensorVectorCoords (IsLocalRing.residue A) (C.rank a) x) at he
    change tensorVectorCoords (IsLocalRing.residue A) (C.rank a')
        ((resF A).map ((scalarComplex hI hU ρ C).toCC.d a a') x) =
      Matrix.toLin' ((ulimMat U (fun i => C.d i a a' hb)).map ((IsLocalRing.residue A).comp ρ))
        (tensorVectorCoords (IsLocalRing.residue A) (C.rank a) x)
    rw [hd, ← matrix_map_comp]
    exact he

/-- The explicit matrix comparison before computing cohomology. -/
def residualMatrixMap (ρ : R →+* A) (C : ComplexStages I U) :
    resCx (scalarComplex hI hU ρ C).toCC ⟶
      (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) C).toCC :=
  (ofCCToCCIso _).inv ≫ GHom.toCC (residualMatrixRelationMap hI hU ρ C)

/-- Every component is the canonical scalar-extension coordinate map. -/
theorem residualMatrixMap_component (ρ : R →+* A) (C : ComplexStages I U) (a : ℤ) :
    (residualMatrixMap hI hU ρ C).f a =
      (tensorVectorCoords (IsLocalRing.residue A) (C.rank a)).toModuleIso.hom := by
  ext x
  rfl

/-- Specialization is identified by a genuine cochain isomorphism, without exchanging cohomology and limits. -/
def residualMatrixIso (ρ : R →+* A) (C : ComplexStages I U) :
    resCx (scalarComplex hI hU ρ C).toCC ≅
      (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) C).toCC := by
  let f := residualMatrixMap hI hU ρ C
  haveI : ∀ a, IsIso (f.f a) := fun a => by
    dsimp only [f]
    rw [residualMatrixMap_component]
    exact (tensorVectorCoords (IsLocalRing.residue A) (C.rank a)).toModuleIso.isIso_hom
  have hf : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact @asIso _ _ _ _ f hf

omit [IsLocalRing A] in
/-- Scalar matrix models are degreewise finite free over the localized integral coefficient ring. -/
theorem scalarComplex_finiteFree (ρ : R →+* A) (C : ComplexStages I U) (a : ℤ) :
    Module.Free A ((scalarComplex hI hU ρ C).X a) ∧
      Module.Finite A ((scalarComplex hI hU ρ C).X a) := by
  change Module.Free A (Fin (C.rank a) → A) ∧ Module.Finite A (Fin (C.rank a) → A)
  exact ⟨inferInstance, inferInstance⟩

omit [IsLocalRing A] in
/-- The retained degree bound survives localization and fixed-field specialization. -/
theorem scalarComplex_bounded (ρ : R →+* A) (C : ComplexStages I U) :
    ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton ((scalarComplex hI hU ρ C).X i) := by
  refine ⟨C.low, C.high, fun i hi => ?_⟩
  change Subsingleton (Fin (C.rank i) → A)
  have hr := C.bounded i hi
  rw [hr]
  infer_instance

end ResidualMatrixComparisons


section ArithmeticLabels


open CategoryTheory Filter Topology Matrix Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Uniform
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Contrib.ChebFD.C10 (GQ Qbar IsFrobAt)
open scoped PowerSeries.WithPiTopology

/-- A chosen genuine complex conjugation of the algebraic closure of the rational field. -/
structure RationalConjugation where
  tau : GQ
  embedding : Qbar →ₐ[ℚ] ℂ
  conjugates : ∀ x, embedding (tau x) = star (embedding x)

/-- Complex conjugation has square one as a genuine Galois automorphism. -/
theorem RationalConjugation.square (D : RationalConjugation) : D.tau * D.tau = 1 := by
  apply AlgEquiv.ext
  intro x
  apply D.embedding.injective
  change D.embedding (D.tau (D.tau x)) = D.embedding x
  rw [D.conjugates, D.conjugates, star_star]

/-- The rational Tate Frobenius matrix in integral power-series coefficients. -/
def rationalTateMatrix (E : WeierstrassCurve ℚ) [E.IsElliptic] (g : GQ) :
    Matrix (Fin 2) (Fin 2) Lambda :=
  (tateMatrix E g).map (PowerSeries.C : ℤ_[2] →+* Lambda)

/-- The actual conjugation matrix is an involution. -/
theorem rationalTateMatrix_square (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (D : RationalConjugation) : rationalTateMatrix E D.tau * rationalTateMatrix E D.tau = 1 := by
  rw [rationalTateMatrix, ← Matrix.map_mul, ← tateMatrix_mul, D.square, tateMatrix_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Frobenius orientation comes from the actual Tate representation, not an extra matrix choice. -/
theorem rationalTateMatrix_det_frob (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {g : GQ} {ell : ℕ} (hell : ell ≠ 2) (hF : IsFrobAt g ell) :
    (rationalTateMatrix E g).det = (ell : Lambda) := by
  rw [rationalTateMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    det_tateMatrix, ZInQ.Manuscript.RC.GlueSweep.Tate.det_tateRep_eq_of_isFrobAt E hell hF,
    map_natCast]

/-- The actual twisted coefficient action in a chosen integral basis. -/
def coefficientActionMatrix (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K)
    (alpha : GKS K S →* Lambdaˣ) (b : Basis (Fin 2) Lambda (TLam K S W alpha))
    (g : GKS K S) : Matrix (Fin 2) (Fin 2) Lambda :=
  LinearMap.toMatrix b b (DistribMulAction.toModuleEnd Lambda (TLam K S W alpha) g)

/-- The canonical embedding of the number-field integers into algebraic integers in its algebraic closure. -/
def integersInClosure (K : Type) [Field K] [NumberField K] :
    𝓞 K →+* integralClosure ℤ (AlgebraicClosure K) where
  toFun x := ⟨algebraMap K (AlgebraicClosure K) (x : K),
    x.2.map (IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _x _y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _x _y := Subtype.ext (map_add _ _ _)

/-- Arithmetic Frobenius at a genuine completion, expressed on algebraic integers over its prime. -/
def IsLocalArithmeticFrobenius (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : Gloc K v) : Prop :=
  ∃ Q : Ideal (integralClosure ℤ (AlgebraicClosure K)), Q.IsPrime ∧
    Ideal.comap (integersInClosure K) Q = v.asIdeal ∧
    ∀ x y : integralClosure ℤ (AlgebraicClosure K),
      (y : AlgebraicClosure K) =
        (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from decompMap K v g) (x : AlgebraicClosure K) -
        (x : AlgebraicClosure K) ^ Ideal.absNorm v.asIdeal → y ∈ Q

/-- A moving label carries actual primes and local Frobenius elements at one common retained precision. -/
structure MovingDerivativeLabel (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (K : Type) [Field K] [NumberField K]
    (support : ℕ → Set (HeightOneSpectrum (𝓞 K)))
    (alpha : ∀ i, GKS K (support i) →* Lambdaˣ)
    (D : RationalConjugation) (excluded : ℕ → Finset ℕ)
    (prec : ℕ → ℕ) (U : Ultrafilter ℕ) where
  quadratic : finrank ℚ K = 2
  imaginary : IsEmpty (K →ₐ[ℚ] ℝ)
  ell : ℕ → ℕ
  prime : ∀ i, (ell i).Prime
  avoid : ∀ i, ell i ∉ excluded i
  exclude_two : ∀ i, 2 ∈ excluded i
  frobenius : ℕ → GQ
  frobenius_at : ∀ i, IsFrobAt (frobenius i) (ell i)
  place : ∀ i, Places K (support i)
  place_under : ∀ i, (place i).1.asIdeal.under ℤ = Ideal.span {(ell i : ℤ)}
  residue_size : ∀ i, Ideal.absNorm (place i).1.asIdeal = ell i ^ 2
  local_frobenius : ∀ i, Gloc K (place i).1
  local_frobenius_at : ∀ i, IsLocalArithmeticFrobenius K (place i).1 (local_frobenius i)
  basis : ∀ i, Basis (Fin 2) Lambda (TLam K (support i) (E.baseChange K) (alpha i))
  ell_unit : ℕ → Lambdaˣ
  ell_unit_val : ∀ i, (ell_unit i : Lambda) = (ell i : Lambda)
  ell_precision : ∀ᶠ i in (U : Filter ℕ), (ell i : Lambda) + 1 ∈ stageIdeal (prec i + 1)
  tate_precision : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (rationalTateMatrix E (frobenius i) - rationalTateMatrix E D.tau) a b ∈ stageIdeal (prec i + 1)
  character_precision : ∀ᶠ i in (U : Filter ℕ),
    ((alpha i (locMap K (support i) (place i).1 (local_frobenius i)) : Lambdaˣ) : Lambda) - 1 ∈
      stageIdeal (prec i)
  tate_comparison : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (coefficientActionMatrix K (support i) (E.baseChange K) (alpha i) (basis i)
        (locMap K (support i) (place i).1 (local_frobenius i)) -
      ((alpha i (locMap K (support i) (place i).1 (local_frobenius i)) : Lambdaˣ) : Lambda) •
        (rationalTateMatrix E (frobenius i) * rationalTateMatrix E (frobenius i))) a b ∈ stageIdeal (prec i)

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]
  {K : Type} [Field K] [NumberField K]
  {support : ℕ → Set (HeightOneSpectrum (𝓞 K))}
  {alpha : ∀ i, GKS K (support i) →* Lambdaˣ}
  {D : RationalConjugation} {excluded : ℕ → Finset ℕ} {prec : ℕ → ℕ} {U : Ultrafilter ℕ}

/-- The finite coefficient action includes the scalar character constraint; its triviality is derived. -/
theorem MovingDerivativeLabel.phi_precision
    (L : MovingDerivativeLabel E K support alpha D excluded prec U) :
    ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      (coefficientActionMatrix K (support i) (E.baseChange K) (alpha i) (L.basis i)
        (locMap K (support i) (L.place i).1 (L.local_frobenius i)) - 1) a b ∈ stageIdeal (prec i) := by
  filter_upwards [L.tate_comparison, L.character_precision, L.tate_precision] with i hc ha hT
  let q := Ideal.Quotient.mk (stageIdeal (prec i))
  let F := rationalTateMatrix E (L.frobenius i)
  let J := rationalTateMatrix E D.tau
  let a := ((alpha i (locMap K (support i) (L.place i).1 (L.local_frobenius i)) : Lambdaˣ) : Lambda)
  let Phi := coefficientActionMatrix K (support i) (E.baseChange K) (alpha i) (L.basis i)
    (locMap K (support i) (L.place i).1 (L.local_frobenius i))
  have hF : F.map q = J.map q := by
    ext x y
    exact Ideal.Quotient.eq.mpr (stageIdeal_antitone (Nat.le_succ _) (hT x y))
  have hJ : J.map q * J.map q = 1 := by
    rw [← Matrix.map_mul, rationalTateMatrix_square E D]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hFF : (F * F).map q = 1 := by rw [Matrix.map_mul, hF, hJ]
  have hA : q a = 1 := by
    have he : q a = q 1 := Ideal.Quotient.eq.mpr ha
    simpa using he
  have hPhi : Phi.map q = 1 := by
    ext x y
    have he : q (Phi x y) = q (a * (F * F) x y) := Ideal.Quotient.eq.mpr (hc x y)
    change q (Phi x y) = (1 : Matrix (Fin 2) (Fin 2) (Lambda ⧸ stageIdeal (prec i))) x y
    rw [he, map_mul, hA, one_mul]
    exact congrFun (congrFun hFF x) y
  have hone : (1 : Matrix (Fin 2) (Fin 2) Lambda).map q = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  intro x y
  exact Ideal.Quotient.eq.mp (congrFun (congrFun (hPhi.trans hone.symm) x) y)


end ArithmeticLabels

section LabelConditions


open CategoryTheory Filter Module
open ZInQ.Manuscript.RC.Uniform
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.RC53Assist.InnerLimit

variable {k : Type} [Field k] {B : Type} [DecidableEq B]

/-- Replace exactly one local plane in a fixed finite diagram. -/
def changedPlane (old : B → Submodule k (Coords k)) (q : B)
    (P : Submodule k (Coords k)) (v : B) : Submodule k (Coords k) :=
  if v = q then P else old v

/-- The local conditions of the entire label family. -/
abbrev familyConditions (P : B → Submodule k (Coords k)) : GCx k :=
  piCx fun v => conditionComplex (P v)

/-- Componentwise inclusions retain degree zero at every label. -/
def familyInclusion {P Q : B → Submodule k (Coords k)} (h : ∀ v, P v ≤ Q v) :
    GHom (familyConditions P) (familyConditions Q) :=
  piMap fun v => conditionIncl (h v)

omit [DecidableEq B] in
/-- Every such family inclusion is degreewise injective. -/
theorem familyInclusion_injective {P Q : B → Submodule k (Coords k)} (h : ∀ v, P v ≤ Q v)
    (a : ℤ) : Function.Injective ((familyInclusion h).f a a rfl) := by
  intro x y hxy
  funext v
  exact conditionIncl_injective (h v) a (congrFun hxy v)

/-- Read the actual coordinate at one label. -/
def familyCoordinate (P : B → Submodule k (Coords k)) (q : B) :
    (∀ v, P v) →ₗ[k] Coords k :=
  (P q).subtype ∘ₗ LinearMap.proj q

/-- A degree-one quotient map from the family condition complex. -/
def familyProjectionAt {M : Type} [AddCommGroup M] [Module k M]
    (P : B → Submodule k (Coords k)) (f : (∀ v, P v) →ₗ[k] M) :
    ∀ a, (familyConditions P).X a →ₗ[k] oneTerms k M a
  | .ofNat 1 => f
  | _ => 0

def familyProjection {M : Type} [AddCommGroup M] [Module k M]
    (P : B → Submodule k (Coords k)) (f : (∀ v, P v) →ₗ[k] M) :
    GHom (familyConditions P) (oneComplex k M) where
  f a b hab := by subst hab; exact familyProjectionAt P f a
  comm a a' b b' hab ha hb ha'b' x := by
    subst hab ha'b'
    have hz : (familyConditions P).d a a' ha x = 0 := by
      funext v
      rfl
    rw [hz]
    change familyProjectionAt P f a' 0 = 0
    exact map_zero _

omit [DecidableEq B] in
/-- Inclusions followed by localization are the prescribed local-condition maps. -/
theorem familyInclusion_toLocal {P Q : B → Submodule k (Coords k)} (h : ∀ v, P v ≤ Q v) :
    ghomComp (familyInclusion h) (piMap fun v => conditionToLocal (Q v)) =
      piMap fun v => conditionToLocal (P v) := by
  apply ghom_ext
  intro a u
  funext v
  rcases a with (_ | _ | a) | a <;> rfl

/-- The full Selmer datum of a label family, with the old global object fixed. -/
def familyData (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (P : B → Submodule k (Coords k)) : SelData k :=
  ⟨G, familyConditions P, piCx fun _ : B => splitLocalComplex k, r,
    piMap fun v => conditionToLocal (P v)⟩

/-- The relaxed quotient at the new label, retaining all other conditions. -/
def familyRelaxed (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (old : B → Submodule k (Coords k)) (q : B) : RelaxedLocalization k where
  D := familyData G r (changedPlane old q ⊤)
  Wrel := oneComplex k (Coords k)
  gR := familyProjection (changedPlane old q ⊤) (familyCoordinate (changedPlane old q ⊤) q)
  eR := LinearEquiv.refl k _
  hWrel := oneComplex_concentrated _

/-- The side quotient reads its new-label plane, not an unrelated vector. -/
def familySideCoordinate (old : B → Submodule k (Coords k)) (q : B)
    (P : Submodule k (Coords k)) : (∀ v, changedPlane old q P v) →ₗ[k] P :=
  (familyCoordinate (changedPlane old q P) q).codRestrict P (by
    intro u
    change (u q).1 ∈ P
    simpa [changedPlane] using (u q).2)

/-- Both exact sequences and all plane fields are constructed for the whole moving-label diagram. -/
def familyLiteralSide (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (old : B → Submodule k (Coords k)) (q : B) (P : Submodule k (Coords k))
    (T : Type) [AddCommGroup T] [Module k T] (pi : Coords k →ₗ[k] T)
    (hsur : Function.Surjective pi) (hker : ∀ x, pi x = 0 ↔ x ∈ P) :
    SwitchSide (familyRelaxed G r old q) P where
  U₁ := familyConditions (changedPlane old q P)
  Ustr := familyConditions (changedPlane old q ⊥)
  W₁ := oneComplex k P
  W₂ := oneComplex k T
  f₁ := familyInclusion (by intro v; by_cases hv : v = q <;> simp [changedPlane, hv])
  fs := familyInclusion (by intro v; by_cases hv : v = q <;> simp [changedPlane, hv])
  g₂ := familyProjection (changedPlane old q ⊤)
    (pi ∘ₗ familyCoordinate (changedPlane old q ⊤) q)
  g₁ := familyProjection (changedPlane old q P) (familySideCoordinate old q P)
  i := oneMap P.subtype
  p := oneMap pi
  hfg₂ a u := by
    rcases a with (_ | _ | a) | a
    · rfl
    · change pi ((u q).1) = 0
      apply (hker _).mpr
      simpa [changedPlane] using (u q).2
    · rfl
    · rfl
  f₁_inj := familyInclusion_injective _
  fs_inj := familyInclusion_injective _
  g₂_surj a := by
    rcases a with (_ | _ | a) | a
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · intro y
      obtain ⟨x, hx⟩ := hsur y
      let u : ∀ v, changedPlane old q ⊤ v :=
        Pi.single q ⟨x, by simp [changedPlane]⟩
      refine ⟨u, ?_⟩
      change pi ((u q).1) = y
      dsimp only [u]
      rw [Pi.single_eq_same]
      exact hx
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  g₁_surj a := by
    rcases a with (_ | _ | a) | a
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · intro y
      let u : ∀ v, changedPlane old q P v := Pi.single q ⟨y.1, by simp [changedPlane]⟩
      refine ⟨u, ?_⟩
      apply Subtype.ext
      change (u q).1 = y.1
      dsimp only [u]
      rw [Pi.single_eq_same]
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
    · exact fun y => ⟨0, Subsingleton.elim (α := PUnit) _ _⟩
  ex₂ a u hu := by
    rcases a with (_ | _ | a) | a
    · exact ⟨u, rfl⟩
    · change pi ((u q).1) = 0 at hu
      have hq : (u q).1 ∈ P := (hker _).mp hu
      let x : ∀ v, changedPlane old q P v := fun v => ⟨(u v).1, by
        by_cases hv : v = q
        · subst hv; simpa [changedPlane] using hq
        · simpa [changedPlane, hv] using (u v).2⟩
      refine ⟨x, ?_⟩
      funext v
      exact Subtype.ext rfl
    · exact ⟨0, by change (0 : ∀ _v : B, PUnit) = u; exact Subsingleton.elim _ _⟩
    · exact ⟨0, by change (0 : ∀ _v : B, PUnit) = u; exact Subsingleton.elim _ _⟩
  hfg₁ a u := by
    rcases a with (_ | _ | a) | a
    · rfl
    · apply Subtype.ext
      change (u q).1 = 0
      have hq := (u q).2
      simpa [changedPlane] using hq
    · rfl
    · rfl
  ex₁ a u hu := by
    rcases a with (_ | _ | a) | a
    · exact ⟨u, rfl⟩
    · have hq : (u q).1 = 0 := congrArg Subtype.val hu
      let x : ∀ v, changedPlane old q ⊥ v := fun v => ⟨(u v).1, by
        by_cases hv : v = q
        · subst hv; simp [changedPlane, hq]
        · simpa [changedPlane, hv] using (u v).2⟩
      refine ⟨x, ?_⟩
      funext v
      exact Subtype.ext rfl
    · exact ⟨0, by change (0 : ∀ _v : B, PUnit) = u; exact Subsingleton.elim _ _⟩
    · exact ⟨0, by change (0 : ∀ _v : B, PUnit) = u; exact Subsingleton.elim _ _⟩
  hRF a u := by rcases a with (_ | _ | a) | a <;> rfl
  hpR a u := by rcases a with (_ | _ | a) | a <;> rfl
  hW₁ := oneComplex_concentrated _
  hW₂ := oneComplex_concentrated _
  i_inj := P.injective_subtype
  ip_exact x := by
    change Coords k at x
    change pi x = 0 ↔ ∃ y : P, y.1 = x
    rw [hker]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  hP := Submodule.range_subtype P

/-- The side data is the Selmer datum of precisely the prescribed family of planes. -/
theorem familyLiteralSide_Dside (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (old : B → Submodule k (Coords k)) (q : B) (P : Submodule k (Coords k))
    (T : Type) [AddCommGroup T] [Module k T] (pi : Coords k →ₗ[k] T)
    (hsur : Function.Surjective pi) (hker : ∀ x, pi x = 0 ↔ x ∈ P) :
    (familyLiteralSide G r old q P T pi hsur hker).Dside =
      familyData G r (changedPlane old q P) := by
  unfold SwitchSide.Dside restrictData familyData familyLiteralSide familyRelaxed
  congr 1
  exact familyInclusion_toLocal _

/-- Both switch sides retain the same strict datum, including every old condition. -/
theorem familyLiteralSide_Dstr (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (old : B → Submodule k (Coords k)) (q : B) (P : Submodule k (Coords k))
    (T : Type) [AddCommGroup T] [Module k T] (pi : Coords k →ₗ[k] T)
    (hsur : Function.Surjective pi) (hker : ∀ x, pi x = 0 ↔ x ∈ P) :
    (familyLiteralSide G r old q P T pi hsur hker).Dstr =
      familyData G r (changedPlane old q ⊥) := by
  unfold SwitchSide.Dstr SwitchSide.Dside restrictData familyData familyLiteralSide familyRelaxed
  congr 1
  apply ghom_ext
  intro a u
  funext v
  rcases a with (_ | _ | a) | a <;> rfl

/-- A configuration selects singular conditions exactly at its selected labels. -/
def configurationPlanes (c : Finset B) (v : B) : Submodule k (Coords k) :=
  if v ∈ c then singPlane k (Vec2 k) (Vec2 k) else finPlane k (Vec2 k) (Vec2 k)

/-- The configured Selmer data is fixed by the label family, not chosen to fit a stage. -/
def configurationData (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) : SelData k := familyData G r (configurationPlanes c)

def movingRelaxed (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) (q : B) : QuasiRelaxedLocalization k :=
  (familyRelaxed G r (configurationPlanes c) q).toQuasi

def movingFiniteSide (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) (q : B) : QuasiSwitchSide (movingRelaxed G r c q)
      (finPlane k (Vec2 k) (Vec2 k)) :=
  (familyLiteralSide G r (configurationPlanes c) q (finPlane k (Vec2 k) (Vec2 k))
    (Vec2 k) (LinearMap.snd k _ _) LinearMap.snd_surjective (fun _ => mem_finPlane.symm)).toQuasi

def movingSingularSide (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) (q : B) : QuasiSwitchSide (movingRelaxed G r c q)
      (singPlane k (Vec2 k) (Vec2 k)) :=
  (familyLiteralSide G r (configurationPlanes c) q (singPlane k (Vec2 k) (Vec2 k))
    (Vec2 k) (LinearMap.fst k _ _) LinearMap.fst_surjective (fun _ => mem_singPlane.symm)).toQuasi

/-- The finite side equals the selected old configuration's datum, not just its dimension. -/
theorem movingFiniteSide_Dside (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) (q : B) (hq : q ∉ c) :
    (movingFiniteSide G r c q).Dside = configurationData G r c := by
  change (familyLiteralSide G r (configurationPlanes c) q (finPlane k (Vec2 k) (Vec2 k))
    (Vec2 k) (LinearMap.snd k _ _) LinearMap.snd_surjective (fun _ => mem_finPlane.symm)).Dside = _
  erw [familyLiteralSide_Dside]
  have hP : changedPlane (configurationPlanes (k := k) c) q
      (finPlane k (Vec2 k) (Vec2 k)) = configurationPlanes c := by
    funext v
    by_cases hv : v = q
    · subst hv; simp [changedPlane, configurationPlanes, hq]
    · simp [changedPlane, hv]
  rw [hP]
  rfl

/-- The singular side equals the datum after inserting the same moving label. -/
theorem movingSingularSide_Dside (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) (q : B) :
    (movingSingularSide G r c q).Dside = configurationData G r (insert q c) := by
  change (familyLiteralSide G r (configurationPlanes c) q (singPlane k (Vec2 k) (Vec2 k))
    (Vec2 k) (LinearMap.fst k _ _) LinearMap.fst_surjective (fun _ => mem_singPlane.symm)).Dside = _
  erw [familyLiteralSide_Dside]
  have hP : changedPlane (configurationPlanes (k := k) c) q
      (singPlane k (Vec2 k) (Vec2 k)) = configurationPlanes (insert q c) := by
    funext v
    by_cases hv : v = q
    · subst hv; simp [changedPlane, configurationPlanes]
    · simp [changedPlane, configurationPlanes, hv]
  rw [hP]
  rfl

/-- The strict objects of the two sides agree as Selmer data. -/
theorem movingSides_Dstr (G : GCx k) (r : GHom G (piCx fun _ : B => splitLocalComplex k))
    (c : Finset B) (q : B) :
    (movingFiniteSide G r c q).Dstr = (movingSingularSide G r c q).Dstr := by
  change (familyLiteralSide G r (configurationPlanes c) q (finPlane k (Vec2 k) (Vec2 k))
    (Vec2 k) (LinearMap.snd k _ _) LinearMap.snd_surjective (fun _ => mem_finPlane.symm)).Dstr =
      (familyLiteralSide G r (configurationPlanes c) q (singPlane k (Vec2 k) (Vec2 k))
        (Vec2 k) (LinearMap.fst k _ _) LinearMap.fst_surjective (fun _ => mem_singPlane.symm)).Dstr
  erw [familyLiteralSide_Dstr, familyLiteralSide_Dstr]

/-- The moving-label family uses one fixed configuration rule and the actual starting cochains. -/
def movingSwitchFamily {A : Type} [CommRing A] (G : GCx k)
    (r : GHom G (piCx fun _ : B => splitLocalComplex k)) (c0 : Finset B) (t : A)
    (z : (selCx (configurationData G r c0)).X 1)
    (hz : (selCx (configurationData G r c0)).d 1 2 rfl z = 0)
    (lam : (selCx (configurationData G r c0)).X 2 →ₗ[k] k)
    (hlam : ∀ y, lam ((selCx (configurationData G r c0)).d 1 2 rfl y) = 0) : SwitchFamily k A where
  Config := Finset B
  Prime := B
  actual := c0
  next c q := insert q c
  fibre := configurationData G r
  t := t
  zAct := z
  hzAct := (GCx.toCC_d_hom _ 1 2 rfl z).trans hz
  lamAct := lam
  hlamAct y := by
    have he := GCx.toCC_d_hom (selCx (configurationData G r c0)) 1 2 rfl y
    exact (congrArg lam he).trans (hlam y)


end LabelConditions

section LabelMatrices


variable {R : Type} [CommRing R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  {B : Type} [Fintype B] [DecidableEq B]

/-- Total coordinate rank of a fixed finite label diagram. -/
def labelRank (d : B → ℕ) : ℕ := ∑ v, d v

/-- The finite coordinate set is the disjoint union of the label coordinate sets. -/
def labelIndexEquiv (d : B → ℕ) : (Σ v, Fin (d v)) ≃ Fin (labelRank d) :=
  (Fintype.equivFin _).trans (finCongr (by simp [labelRank, Fintype.card_sigma]))

/-- Concatenated coordinates split into the actual coordinate module at every label. -/
def labelCoords (S : Type) [CommRing S] (d : B → ℕ) :
    (Fin (labelRank d) → S) ≃ₗ[S] (∀ v, Fin (d v) → S) where
  toFun x v a := x (labelIndexEquiv d ⟨v, a⟩)
  invFun x a := x ((labelIndexEquiv d).symm a).1 ((labelIndexEquiv d).symm a).2
  left_inv x := by
    funext a
    exact congrArg x ((labelIndexEquiv d).apply_symm_apply a)
  right_inv x := by
    funext v a
    change x ((labelIndexEquiv d).symm (labelIndexEquiv d ⟨v, a⟩)).1
      ((labelIndexEquiv d).symm (labelIndexEquiv d ⟨v, a⟩)).2 = x v a
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A finite family of retained zero-differential coordinate complexes. -/
def zeroLabelStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ)
    (d : ℤ → B → ℕ) (low high : ℤ)
    (hbound : ∀ a v, a < low ∨ high < a → d a v = 0) : ComplexStages I U where
  rank a := labelRank (d a)
  low := low
  high := high
  bounded a ha := by simp [labelRank, fun v => hbound a v ha]
  d _ _ _ _ := 0
  square _ _ _ _ _ := Eventually.of_forall fun i _ _ => by simp

/-- The full local stage tuple for one fixed finite family of moving labels. -/
def fullLabelStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) : ComplexStages I U :=
  zeroLabelStages I U (fun (a : ℤ) (_v : B) => fullLocalRank a) 0 2 (by
    intro a v ha
    rcases a with (_ | _ | _ | a) | a
    · change (0 : ℤ) < 0 ∨ 2 < 0 at ha; omega
    · change (1 : ℤ) < 0 ∨ 2 < 1 at ha; omega
    · change (2 : ℤ) < 0 ∨ 2 < 2 at ha; omega
    · rfl
    · rfl)

/-- The finite coefficient conditions of one configuration. -/
def conditionLabelStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ)
    (s : B → ConditionKind) : ComplexStages I U :=
  zeroLabelStages I U (fun a v => localConditionRank (s v) a) 0 1 (by
    intro a v ha
    rcases a with (_ | _ | a) | a
    · change (0 : ℤ) < 0 ∨ 1 < 0 at ha; omega
    · change (1 : ℤ) < 0 ∨ 1 < 1 at ha; omega
    · rfl
    · rfl)

/-- Stack the retained localization maps at the actual labels of the same finite diagram. -/
def labelRestrictionStages (C : ComplexStages I U)
    (r : ∀ _v : B, MapStages C (fullLocalStages I U)) : MapStages C (fullLabelStages (B := B) I U) where
  f i a b hab x y :=
    let z := (labelIndexEquiv (fun _v : B => fullLocalRank b)).symm x
    (r z.1).f i a b hab z.2 y
  comm a a' b b' hab ha hb ha'b' := by
    filter_upwards [Filter.eventually_all.mpr (fun v => (r v).comm a a' b b' hab ha hb ha'b')]
      with i hi
    intro x y
    let z := (labelIndexEquiv (fun _v : B => fullLocalRank b')).symm x
    have he := hi z.1 z.2 y
    change ((∑ j : Fin (C.rank a'), (r z.1).f i a' b' ha'b' z.2 j * C.d i a a' ha j y) -
      ∑ j : Fin (fullLocalRank b), (0 : R) * (r z.1).f i a b hab j y) ∈ I i at he
    simp only [zero_mul, Finset.sum_const_zero, sub_zero] at he
    change ((∑ j : Fin (C.rank a'), (r z.1).f i a' b' ha'b' z.2 j * C.d i a a' ha j y) -
      ∑ j : Fin (labelRank (fun _v : B => fullLocalRank b)), (0 : R) *
        (r ((labelIndexEquiv (fun _v : B => fullLocalRank b)).symm j).1).f i a b hab
          ((labelIndexEquiv (fun _v : B => fullLocalRank b)).symm j).2 y) ∈ I i
    simpa only [zero_mul, Finset.sum_const_zero, sub_zero] using he

/-- The finite-stage block-diagonal inclusion of all the actual local conditions. -/
def labelInclusionMatrix (R : Type) [CommRing R] (s : B → ConditionKind) (a : ℤ) :
    Matrix (Fin (labelRank (fun _v : B => fullLocalRank a)))
      (Fin (labelRank (fun v => localConditionRank (s v) a))) R :=
  Matrix.reindex (labelIndexEquiv _) (labelIndexEquiv _)
    (Matrix.blockDiagonal' fun v => localInclusionMatrix R (s v) a)

/-- All condition inclusions belong to that same retained diagram. -/
def labelInclusionStages (I : ℕ → Ideal R) (U : Ultrafilter ℕ) (s : B → ConditionKind) :
    MapStages (conditionLabelStages I U s) (fullLabelStages (B := B) I U) where
  f _i a b hab := by subst hab; exact labelInclusionMatrix R s a
  comm a a' b b' hab ha hb ha'b' := by
    subst hab ha'b'
    exact Eventually.of_forall fun i x y => by
      change ((∑ j : Fin (labelRank (fun v => localConditionRank (s v) a')),
          labelInclusionMatrix R s a' x j * (0 : R)) -
        ∑ j : Fin (labelRank (fun _v : B => fullLocalRank a)),
          (0 : R) * labelInclusionMatrix R s a j y) ∈ I i
      simpa only [mul_zero, zero_mul, Finset.sum_const_zero, sub_self] using (I i).zero_mem

/-- The actual finite-free Selmer diagram of a configuration of moving labels. -/
def labelDiagramStages (C : ComplexStages I U)
    (r : ∀ _v : B, MapStages C (fullLocalStages I U)) (s : B → ConditionKind) :
    SelmerDiagramStages I U :=
  ⟨C, conditionLabelStages I U s, fullLabelStages (B := B) I U,
    labelRestrictionStages C r, labelInclusionStages I U s⟩


end LabelMatrices

section CanonicalConsumers


open ZInQ.Contrib.CloudB3RC53.ResidualTransfer
open ZInQ.Contrib.RC53Assist.StageCone

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {A : Type} [CommRing A] [IsLocalRing A]

/-- The consumer model is computed from the specified finite-free matrix complex. -/
def canonicalMatrixModel (ρ : R →+* A) (C : ComplexStages I U)
    (hshape : ResidualTwoTermShape (scalarComplex hI hU ρ C)) :
    BasedTwoTermModel (scalarComplex hI hU ρ C) :=
  basedTwoTermModel _ (scalarComplex_finiteFree hI hU ρ C)
    (scalarComplex_bounded hI hU ρ C) hshape

/-- Actual class and functional data, together with the generic rank-one degeneracy of the computed model. -/
structure IntegralMatrixStageData (ρ : R →+* A) {F : Type} [Field F]
    (ι : A →+* F) (C : ComplexStages I U) where
  shape : ResidualTwoTermShape (scalarComplex hI hU ρ C)
  z : (scalarComplex hI hU ρ C).X 1
  hz : (scalarComplex hI hU ρ C).d 1 2 rfl z = 0
  lam : (scalarComplex hI hU ρ C).X 2 →ₗ[A] A
  hlam : ∀ y, lam ((scalarComplex hI hU ρ C).d 1 2 rfl y) = 0
  determinant : ((canonicalMatrixModel hI hU ρ C shape).realization.matrix.map ι).det = 0
  adjugate : ((canonicalMatrixModel hI hU ρ C shape).realization.matrix.map ι).adjugate ≠ 0

variable {hI hU} {ρ : R →+* A} {F : Type} [Field F] {ι : A →+* F}
  {C : ComplexStages I U}

/-- The finite stage is not selected by a desired dimension: its class and row are the realized ones. -/
def IntegralMatrixStageData.stage (D : IntegralMatrixStageData hI hU ρ ι C) : TwoTermStage ι :=
  (canonicalMatrixModel hI hU ρ C D.shape).stage ι D.z D.hz D.lam D.hlam
    D.determinant D.adjugate

/-- A derived equivalence from the actual specialized matrix complex to its computed stage. -/
def IntegralMatrixStageData.h1Equiv (D : IntegralMatrixStageData hI hU ρ ι C) :
    (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) C).toCC.homology 1
      ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage :=
  (((HomologicalComplex.homologyFunctor (ModuleCat (IsLocalRing.ResidueField A))
    (ComplexShape.up ℤ) 1).mapIso (residualMatrixIso hI hU ρ C)).toLinearEquiv).symm.trans
      ((canonicalMatrixModel hI hU ρ C D.shape).stageH1Equiv ι D.z D.hz D.lam D.hlam
        D.determinant D.adjugate)

/-- The derivative side-to-stage equivalence factors through actual cochain coordinate maps. -/
def derivativeSideStageEquiv (G : ComplexStages I U) (r : MapStages G (fullLocalStages I U))
    (s : ConditionKind) (D : IntegralMatrixStageData hI hU ρ ι (selmerStages (derivativeDiagram G r s))) :
    (selCx (derivativeSideData hI hU ((IsLocalRing.residue A).comp ρ) G r s)).toCC.homology 1
      ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage :=
  (((HomologicalComplex.homologyFunctor (ModuleCat (IsLocalRing.ResidueField A))
    (ComplexShape.up ℤ) 1).mapIso
      (derivativeMatrixIso hI hU ((IsLocalRing.residue A).comp ρ) G r s)).toLinearEquiv).symm.trans
      D.h1Equiv

end CanonicalConsumers

section LiteralSideComparison

variable {k : Type} [Field k] (G : GCx k) (r : GHom G (splitLocalComplex k))

/-- The literal side and its split Selmer datum agree as cochain data. -/
theorem literalSideData (P : Submodule k (Coords k)) (T : Type) [AddCommGroup T] [Module k T]
    (pi : Coords k →ₗ[k] T) (hsur : Function.Surjective pi) (hker : ∀ x, pi x = 0 ↔ x ∈ P) :
    (literalLimitSide G r P T pi hsur hker).Dside =
      (⟨G, conditionComplex P, splitLocalComplex k, r, conditionToLocal P⟩ : SelData k) := by
  unfold SwitchSide.Dside restrictData literalLimitSide literalLimitRelaxed limitRelaxedData
  congr 1
  apply ghom_ext
  intro a u
  rcases a with (_ | _ | a) | a <;> rfl

end LiteralSideComparison

section DerivedLimitStep

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {A : Type} [CommRing A] [IsLocalRing A] (ρ : R →+* A)
  {F : Type} [Field F] {ι : A →+* F}
  (G : ComplexStages I U) (r : MapStages G (fullLocalStages I U))

/-- The finite quasi side is exactly the side whose matrix model was constructed. -/
theorem finiteSideData_eq :
    (finiteLimitSide (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)).Dside =
        derivativeSideData hI hU ((IsLocalRing.residue A).comp ρ) G r .finite := by
  exact literalSideData (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
    (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)
    (finPlane (IsLocalRing.ResidueField A) (Vec2 (IsLocalRing.ResidueField A))
      (Vec2 (IsLocalRing.ResidueField A))) (Vec2 (IsLocalRing.ResidueField A))
    (LinearMap.snd (IsLocalRing.ResidueField A) _ _) LinearMap.snd_surjective
    (fun _ => mem_finPlane.symm)

/-- The singular quasi side is exactly the other configured matrix Selmer datum. -/
theorem singularSideData_eq :
    (singularLimitSide (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)).Dside =
        derivativeSideData hI hU ((IsLocalRing.residue A).comp ρ) G r .singular := by
  exact literalSideData (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
    (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)
    (singPlane (IsLocalRing.ResidueField A) (Vec2 (IsLocalRing.ResidueField A))
      (Vec2 (IsLocalRing.ResidueField A))) (Vec2 (IsLocalRing.ResidueField A))
    (LinearMap.fst (IsLocalRing.ResidueField A) _ _) LinearMap.fst_surjective
    (fun _ => mem_singPlane.symm)

/-- The finite side-to-stage comparison is derived, not a consumer hypothesis. -/
def finiteSideStageEquiv
    (D : IntegralMatrixStageData hI hU ρ ι (selmerStages (derivativeDiagram G r .finite))) :
    (selCx (finiteLimitSide (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)).Dside).toCC.homology 1
        ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage := by
  rw [finiteSideData_eq]
  exact derivativeSideStageEquiv G r .finite D

/-- The singular side-to-stage comparison uses its own actual complex and minimal model. -/
def singularSideStageEquiv
    (D : IntegralMatrixStageData hI hU ρ ι (selmerStages (derivativeDiagram G r .singular))) :
    (selCx (singularLimitSide (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)).Dside).toCC.homology 1
        ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage := by
  rw [singularSideData_eq]
  exact derivativeSideStageEquiv G r .singular D

/-- Conditional switching with both side comparisons constructed from their specified integral data. -/
def derivedLimitNonquadStep
    (D0 : IntegralMatrixStageData hI hU ρ ι (selmerStages (derivativeDiagram G r .finite)))
    (D1 : IntegralMatrixStageData hI hU ρ ι (selmerStages (derivativeDiagram G r .singular)))
    (ε σ : IsLocalRing.ResidueField A) (J : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField A))
    (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ : J * J = 1)
    (hdual : LimitSwitchDuality (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r) ε σ J hε hσ hJ)
    (hdet : finPlane (IsLocalRing.ResidueField A) (Vec2 (IsLocalRing.ResidueField A))
      (Vec2 (IsLocalRing.ResidueField A)) ≤
        (limitRelaxed (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
          (derivativeRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)).U) :
    QuasiNonquadStep (IsLocalRing.residue A) D0.stage D1.stage :=
  limitNonquadStep _ _ (IsLocalRing.residue A) D0.stage D1.stage ε σ J hε hσ hJ hdual hdet
    (finiteSideStageEquiv hI hU ρ G r D0) (singularSideStageEquiv hI hU ρ G r D1)

end DerivedLimitStep


section RetainedRestrictionComparison

open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Wiring (ResAt)

/-- The integral coordinate index and the local duality coordinate index agree in every degree. -/
def localCoordinateIndex : ∀ a : ℤ, Fin (fullLocalRank a) ≃ lIdx a
  | .ofNat 0 => Equiv.refl _
  | .ofNat 1 => (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm
  | .ofNat 2 => Equiv.refl _
  | .ofNat (_ + 3) => show Fin 0 ≃ Empty from
      { toFun := Fin.elim0, invFun := Empty.elim,
        left_inv := fun i => Fin.elim0 i, right_inv := fun i => Empty.elim i }
  | .negSucc _ => show Fin 0 ≃ Empty from
      { toFun := Fin.elim0, invFun := Empty.elim,
        left_inv := fun i => Fin.elim0 i, right_inv := fun i => Empty.elim i }

/-- The two coordinate conventions have the same underlying local cochain map. -/
theorem localCoordinates_agree {k : Type} [Field k] (a : ℤ) (x : lIdx a → k) :
    fullLocalCoords k a (fun i => x (localCoordinateIndex a i)) = (lCoord k a).symm x := by
  rcases a with (_ | _ | _ | a) | a
  · rfl
  · apply Prod.ext
    · funext j
      change x (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = x (Sum.inl j)
      rw [Equiv.symm_apply_apply]
    · funext j
      change x (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = x (Sum.inr j)
      rw [Equiv.symm_apply_apply]
  · rfl
  · change (_ : PUnit) = _
    exact Subsingleton.elim _ _
  · change (_ : PUnit) = _
    exact Subsingleton.elim _ _

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}

/-- The same retained localization as the duality diagram, in finite-coordinate matrix form. -/
def retainedRestrictionStages (D : RetainedLimitPairingStages U C) :
    MapStages C (fullLocalStages stageIdeal U) where
  f i a b hab := by
    subst hab
    exact (D.res a i).submatrix (localCoordinateIndex a) id
  comm a a' b b' hab ha hb ha'b' := by
    subst hab ha'b' ha
    filter_upwards [D.res_comm a] with i hi
    intro x y
    have he := hi (localCoordinateIndex (a + 1) x) y
    change (∑ j : Fin (C.rank (a + 1)), D.res (a + 1) i
      (localCoordinateIndex (a + 1) x) j * C.d i a (a + 1) rfl j y) ∈ stageIdeal i at he
    change ((∑ j : Fin (C.rank (a + 1)), D.res (a + 1) i
        (localCoordinateIndex (a + 1) x) j * C.d i a (a + 1) rfl j y) -
      ∑ j : Fin (fullLocalRank a), (0 : Lambda) * D.res a i
        (localCoordinateIndex a j) y) ∈ stageIdeal i
    simpa only [zero_mul, Finset.sum_const_zero, sub_zero] using he

/-- Its specialized cochain restriction is precisely the one used by the retained pairing certificate. -/
theorem retainedRestriction_eq (hU : (U : Filter ℕ) ≤ cofinite)
    (D : RetainedLimitPairingStages U C) (P : Ideal Lambda) [P.IsPrime] :
    derivativeRestriction stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C
      (retainedRestrictionStages D) = D.resLimit hU P := by
  apply ghom_ext
  intro a x
  let M : Matrix (lIdx a) (Fin (C.rank a)) (ResAt P) :=
    (ulimMat U (D.res a)).map (algebraMap Lambda (ResAt P))
  change fullLocalCoords (ResAt P) a (M.submatrix (localCoordinateIndex a) id *ᵥ x) = _
  have he : (M.submatrix (localCoordinateIndex a) id *ᵥ x) =
      (fun i => (M *ᵥ x) (localCoordinateIndex a i)) := by
    funext i
    rfl
  rw [he]
  exact localCoordinates_agree a _

end RetainedRestrictionComparison

section FamilyScalarComparisons

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {B : Type} [Fintype B] [DecidableEq B] {k : Type} [Field k]

/-- The full coordinate tuple is split using the fixed finite label indexing. -/
def fullLabelCoords (S : Type) [CommRing S] (a : ℤ) :
    (Fin (labelRank (fun _v : B => fullLocalRank a)) → S) ≃ₗ[S]
      (∀ _v : B, splitLocalTerms S a) :=
  (labelCoords S _).trans (LinearEquiv.piCongrRight fun _v : B => fullLocalCoords S a)

/-- The local conditions use that same label indexing and their actual plane coordinates. -/
def conditionLabelCoords (s : B → ConditionKind) (a : ℤ) :
    (Fin (labelRank (fun v => localConditionRank (s v) a)) → k) ≃ₗ[k]
      (∀ v : B, conditionTerms (conditionPlane k (s v)) a) :=
  (labelCoords k _).trans (LinearEquiv.piCongrRight fun v => localConditionCoords k (s v) a)

/-- Full local matrix stages give the tuple of actual limiting local complexes. -/
def fullLabelScalarIso (ρ : R →+* k) :
    (scalarComplex hI hU ρ (fullLabelStages (B := B) I U)).toCC ≅
      (piCx fun _v : B => splitLocalComplex k).toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (fullLabelCoords k a).toModuleIso)
    (fun a b _ => by
      rw [scalar_d_zero hI hU ρ _ (fun _ _ _ _ => rfl)]
      have hd : (piCx fun _v : B => splitLocalComplex k).toCC.d a b = 0 := by
        by_cases h : a + 1 = b
        · apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext v
          erw [GCx.toCC_d_hom _ a b h]
          rfl
        · exact (piCx fun _v : B => splitLocalComplex k).toCC.shape a b h
      rw [hd]
      ext x
      exact (map_zero (fullLabelCoords k b)).symm)

/-- All configured condition stages give their actual tuple of limiting conditions. -/
def conditionLabelScalarIso (ρ : R →+* k) (s : B → ConditionKind) :
    (scalarComplex hI hU ρ (conditionLabelStages I U s)).toCC ≅
      (piCx fun v => conditionComplex (conditionPlane k (s v))).toCC :=
  HomologicalComplex.Hom.isoOfComponents (fun a => (conditionLabelCoords s a).toModuleIso)
    (fun a b _ => by
      rw [scalar_d_zero hI hU ρ _ (fun _ _ _ _ => rfl)]
      have hd : (piCx fun v => conditionComplex (conditionPlane k (s v))).toCC.d a b = 0 := by
        by_cases h : a + 1 = b
        · apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext v
          erw [GCx.toCC_d_hom _ a b h]
          rfl
        · exact (piCx fun v => conditionComplex (conditionPlane k (s v))).toCC.shape a b h
      rw [hd]
      ext x
      exact (map_zero (conditionLabelCoords s b)).symm)

/-- A diagonal block acts on each label's coordinate module and never changes another label. -/
theorem blockDiagonal_coordinate {d e : B → ℕ}
    (M : ∀ v, Matrix (Fin (d v)) (Fin (e v)) k)
    (x : (Σ v, Fin (e v)) → k) (v : B) (a : Fin (d v)) :
    (Matrix.blockDiagonal' M *ᵥ x) ⟨v, a⟩ = (M v *ᵥ fun j => x ⟨v, j⟩) a := by
  change (∑ z : Σ v, Fin (e v), Matrix.blockDiagonal' M ⟨v, a⟩ z * x z) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single v]
  · simp only [Matrix.blockDiagonal'_apply_eq]
    rfl
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.blockDiagonal'_apply_ne M a j (Ne.symm hw), zero_mul]
  · intro hv
    exact False.elim (hv (Finset.mem_univ v))

omit [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
/-- Changing coefficients respects the entire block-diagonal condition inclusion. -/
theorem labelInclusionMatrix_map (ρ : R →+* k) (s : B → ConditionKind) (a : ℤ) :
    (labelInclusionMatrix R s a).map ρ = labelInclusionMatrix k s a := by
  have hm : (Matrix.blockDiagonal' fun v => localInclusionMatrix R (s v) a).map ρ =
      Matrix.blockDiagonal' fun v => localInclusionMatrix k (s v) a := by
    rw [Matrix.blockDiagonal'_map _ ρ (map_zero ρ)]
    congr 1
    funext v
    exact localInclusionMatrix_map ρ (s v) a
  ext x y
  exact congrFun (congrFun hm ((labelIndexEquiv _).symm x)) ((labelIndexEquiv _).symm y)

/-- The labelwise cochain coordinates preserve every local condition inclusion. -/
theorem labelInclusion_coordinates (s : B → ConditionKind) (a : ℤ)
    (x : Fin (labelRank (fun v => localConditionRank (s v) a)) → k) (v : B) :
    fullLabelCoords k a (labelInclusionMatrix k s a *ᵥ x) v =
      (conditionToLocal (conditionPlane k (s v))).f a a rfl (conditionLabelCoords s a x v) := by
  unfold labelInclusionMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  change fullLocalCoords k a (fun j =>
      (Matrix.blockDiagonal' (fun v => localInclusionMatrix k (s v) a) *ᵥ
        (fun z => x (labelIndexEquiv _ z)))
          ((labelIndexEquiv _).symm (labelIndexEquiv _ ⟨v, j⟩))) = _
  simp only [Equiv.symm_apply_apply]
  have hv : (fun j => (Matrix.blockDiagonal' (fun v => localInclusionMatrix k (s v) a) *ᵥ
      (fun z => x (labelIndexEquiv _ z))) ⟨v, j⟩) =
        localInclusionMatrix k (s v) a *ᵥ (fun j => x (labelIndexEquiv _ ⟨v, j⟩)) := by
    funext j
    exact blockDiagonal_coordinate (d := fun _v : B => fullLocalRank a)
      (e := fun v : B => localConditionRank (s v) a)
      (fun v => localInclusionMatrix k (s v) a)
      (fun z => x (labelIndexEquiv _ z)) v j
  rw [hv]
  exact localInclusion_coordinates (s v) a _

/-- The retained family localization is the canonical tuple of the retained local maps. -/
def labelLimitRestriction (ρ : R →+* k) (G : ComplexStages I U)
    (r : ∀ _v : B, MapStages G (fullLocalStages I U)) :
    GHom (scalarComplex hI hU ρ G) (piCx fun _v : B => splitLocalComplex k) :=
  ghomComp (scalarMap hI hU ρ (labelRestrictionStages G r))
    (relationMap (fullLabelScalarIso hI hU ρ).hom)

/-- Matrix and configured local diagrams are compared before taking cohomology. -/
def labelComparisonData (ρ : R →+* k) (G : ComplexStages I U)
    (r : ∀ _v : B, MapStages G (fullLocalStages I U)) (s : B → ConditionKind) :
    SupportChangeData k where
  D := scalarSelmerData hI hU ρ (labelDiagramStages G r s)
  Dp := familyData (scalarComplex hI hU ρ G) (labelLimitRestriction hI hU ρ G r)
    (fun v => conditionPlane k (s v))
  g := idGHom _
  lam := relationMap (fullLabelScalarIso hI hU ρ).hom
  mu := relationMap (conditionLabelScalarIso hI hU ρ s).hom
  r := zeroGHom _ _
  hres a b hab x := by
    subst hab
    let y := (labelLimitRestriction hI hU ρ G r).f a a rfl x
    exact (add_zero y).symm.trans (congrArg (fun t => y + t) (map_zero _).symm)
  hι a b hab x := by
    subst hab
    funext v
    change (conditionToLocal (conditionPlane k (s v))).f a a rfl
        (conditionLabelCoords s a x v) =
      fullLabelCoords k a ((scalarMap hI hU ρ (labelInclusionStages I U s)).f a a rfl x) v
    change _ = fullLabelCoords k a
      (((ulimMat U (fun _ => labelInclusionMatrix R s a)).map ρ) *ᵥ x) v
    rw [ulimMat_const, labelInclusionMatrix_map]
    exact (labelInclusion_coordinates s a x v).symm

/-- The Selmer comparison is the product of the three canonical cochain coordinate maps. -/
theorem labelComparison_component (ρ : R →+* k) (G : ComplexStages I U)
    (r : ∀ _v : B, MapStages G (fullLocalStages I U)) (s : B → ConditionKind) (a : ℤ) :
    (GHom.toCC (supportMap (labelComparisonData hI hU ρ G r s))).f a =
      ((LinearEquiv.refl k (Fin (G.rank a) → k)).prodCongr
        ((conditionLabelCoords s a).prodCongr (fullLabelCoords k (a - 1)))).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (x.1, conditionLabelCoords s a x.2.1 + 0, fullLabelCoords k (a - 1) x.2.2) = _
  rw [add_zero]
  rfl

/-- The configured Selmer complex is genuinely cochain-isomorphic to its matrix-stage limit. -/
def labelMatrixSideIso (ρ : R →+* k) (G : ComplexStages I U)
    (r : ∀ _v : B, MapStages G (fullLocalStages I U)) (s : B → ConditionKind) :
    (scalarComplex hI hU ρ (selmerStages (labelDiagramStages G r s))).toCC ≅
      (selCx (familyData (scalarComplex hI hU ρ G) (labelLimitRestriction hI hU ρ G r)
        (fun v => conditionPlane k (s v)))).toCC := by
  let f := GHom.toCC (supportMap (labelComparisonData hI hU ρ G r s))
  haveI : ∀ a, IsIso (f.f a) := fun a => by
    dsimp only [f]
    rw [labelComparison_component]
    exact (LinearEquiv.toModuleIso _).isIso_hom
  have hf : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact scalarSelmerIso hI hU ρ (labelDiagramStages G r s) ≪≫ @asIso _ _ _ _ f hf

end FamilyScalarComparisons

section ConfiguredStages

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {B : Type} [Fintype B] [DecidableEq B]
  {A : Type} [CommRing A] [IsLocalRing A] (ρ : R →+* A)
  {F : Type} [Field F] {ι : A →+* F}
  (G : ComplexStages I U) (r : ∀ _v : B, MapStages G (fullLocalStages I U))

/-- A configuration has one fixed rule for its finite and singular conditions. -/
def configurationKinds (c : Finset B) (v : B) : ConditionKind :=
  if v ∈ c then .singular else .finite

omit [Fintype B] in
/-- That rule gives exactly the prescribed configured planes. -/
theorem configurationKinds_planes {k : Type} [Field k] (c : Finset B) :
    (fun v => conditionPlane k (configurationKinds c v)) = configurationPlanes c := by
  funext v
  by_cases hv : v ∈ c <;> simp [configurationKinds, configurationPlanes, conditionPlane, hv] <;> rfl

/-- The selected family's cohomology is identified with the stage derived from its own integral diagram. -/
def configuredSideStageEquiv (c : Finset B)
    (D : IntegralMatrixStageData hI hU ρ ι (selmerStages (labelDiagramStages G r (configurationKinds c)))) :
    (selCx (configurationData (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (labelLimitRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r) c)).toCC.homology 1
        ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage := by
  let e := labelMatrixSideIso hI hU ((IsLocalRing.residue A).comp ρ) G r (configurationKinds c)
  have hp : (selCx (familyData (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (labelLimitRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r)
        (fun v => conditionPlane (IsLocalRing.ResidueField A) (configurationKinds c v)))).toCC.homology 1
      ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage :=
    (((HomologicalComplex.homologyFunctor (ModuleCat (IsLocalRing.ResidueField A))
      (ComplexShape.up ℤ) 1).mapIso e).toLinearEquiv).symm.trans D.h1Equiv
  rw [configurationKinds_planes] at hp
  exact hp

/-- The finite side uses exactly the selected old configuration's constructed stage. -/
def movingFiniteStageEquiv (c : Finset B) (q : B) (hq : q ∉ c)
    (D : IntegralMatrixStageData hI hU ρ ι (selmerStages (labelDiagramStages G r (configurationKinds c)))) :
    (selCx (movingFiniteSide (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (labelLimitRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r) c q).Dside).toCC.homology 1
        ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage := by
  rw [movingFiniteSide_Dside _ _ c q hq]
  exact configuredSideStageEquiv hI hU ρ G r c D

/-- The singular side uses the constructed stage of the inserted configuration. -/
def movingSingularStageEquiv (c : Finset B) (q : B)
    (D : IntegralMatrixStageData hI hU ρ ι
      (selmerStages (labelDiagramStages G r (configurationKinds (insert q c))))) :
    (selCx (movingSingularSide (scalarComplex hI hU ((IsLocalRing.residue A).comp ρ) G)
      (labelLimitRestriction hI hU ((IsLocalRing.residue A).comp ρ) G r) c q).Dside).toCC.homology 1
        ≃ₗ[IsLocalRing.ResidueField A] fiberH1 (IsLocalRing.residue A) D.stage := by
  rw [movingSingularSide_Dside _ _ c q]
  exact configuredSideStageEquiv hI hU ρ G r (insert q c) D

end ConfiguredStages


section PairingTransfer


open Matrix Filter Topology Module NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped PowerSeries.WithPiTopology

section PolynomialPairings

/-- Integral coefficients of the alternating Tate pairing followed by the specified operator. -/
def crossCoefficientMatrix (R : Type) [CommRing R] (e : R) (J : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R := fun a b =>
  if a = 0 then e * J 1 b else -(e * J 0 b)

/-- The degree-one residue convention in finite and singular coordinates. -/
def residueCoefficientMatrix (R : Type) [CommRing R] (e s : R)
    (J : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R
  | .inl _, .inl _ => 0
  | .inl a, .inr b => -(s * crossCoefficientMatrix R e J a b)
  | .inr a, .inl b => -(crossCoefficientMatrix R e J b a)
  | .inr _, .inr _ => 0

variable {k : Type} [Field k]

/-- The integral coefficient formula gives the actual transported cross pairing after specialization. -/
theorem crossCoefficientMatrix_bilin (e : k) (J : Matrix (Fin 2) (Fin 2) k) (x y : Vec2 k) :
    bilinOfMat (crossCoefficientMatrix k e J) x y = crossPairing e J x y := by
  simp [bilinOfMat_apply, crossCoefficientMatrix, dotProduct, Fin.sum_univ_two,
    Matrix.mulVec, crossPairing_apply, weil, LinearMap.mk₂_apply]
  ring

/-- The residue convention is the negative transposed switch pairing, with no sign guessed in the limit. -/
theorem residueCoefficientMatrix_bilin (e s : k) (J : Matrix (Fin 2) (Fin 2) k) (x y : Coords k) :
    bilinOfMat (residueCoefficientMatrix k e s J) (lCoord k 1 x) (lCoord k 1 y) =
      -(switchPairing e s J y x) := by
  change (Sum.elim x.1 x.2) ⬝ᵥ
      ((residueCoefficientMatrix k e s J) *ᵥ (Sum.elim y.1 y.2)) = _
  simp [residueCoefficientMatrix, crossCoefficientMatrix, dotProduct,
    Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    switchPairing, planePairing_apply, crossPairing_apply, weil, LinearMap.mk₂_apply]
  ring

variable {R S : Type} [CommRing R] [CommRing S]

/-- The cross-pairing coefficients are polynomial under coefficient change. -/
theorem crossCoefficientMatrix_map (f : R →+* S) (e : R) (J : Matrix (Fin 2) (Fin 2) R) :
    (crossCoefficientMatrix R e J).map f = crossCoefficientMatrix S (f e) (J.map f) := by
  ext a b
  fin_cases a <;> simp [crossCoefficientMatrix]

/-- The residue coefficients obey the same fixed coefficient map. -/
theorem residueCoefficientMatrix_map (f : R →+* S) (e s : R) (J : Matrix (Fin 2) (Fin 2) R) :
    (residueCoefficientMatrix R e s J).map f =
      residueCoefficientMatrix S (f e) (f s) (J.map f) := by
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [residueCoefficientMatrix, crossCoefficientMatrix]

variable [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]

/-- Cross coefficients commute with the integral matrix limit. -/
theorem crossCoefficientMatrix_limit (U : Ultrafilter ℕ) (e : ℕ → R)
    (J : ℕ → Matrix (Fin 2) (Fin 2) R) :
    ulimMat U (fun i => crossCoefficientMatrix R (e i) (J i)) =
      crossCoefficientMatrix R (ulim U e) (ulimMat U J) := by
  ext a b
  fin_cases a
  · change ulim U (fun i => e i * J i 1 b) = ulim U e * ulim U (fun i => J i 1 b)
    exact ulim_mul U _ _
  · change ulim U (fun i => -(e i * J i 0 b)) = -(ulim U e * ulim U (fun i => J i 0 b))
    rw [ulim_neg, ulim_mul]

/-- The complete degree-one residue formula commutes with that same limit. -/
theorem residueCoefficientMatrix_limit (U : Ultrafilter ℕ) (e s : ℕ → R)
    (J : ℕ → Matrix (Fin 2) (Fin 2) R) :
    ulimMat U (fun i => residueCoefficientMatrix R (e i) (s i) (J i)) =
      residueCoefficientMatrix R (ulim U e) (ulim U s) (ulimMat U J) := by
  ext (a | a) (b | b)
  · exact ulim_const U 0
  · fin_cases a <;>
      simp [ulimMat_apply, residueCoefficientMatrix, crossCoefficientMatrix, ulim_neg, ulim_mul]
  · fin_cases b <;>
      simp [ulimMat_apply, residueCoefficientMatrix, crossCoefficientMatrix, ulim_neg, ulim_mul]
  · exact ulim_const U 0

end PolynomialPairings

section ScalarInverses

variable (U : Ultrafilter ℕ)

/-- A scalar unit at all retained precisions, including its retained inverse. -/
structure RetainedScalarUnit where
  value : ℕ → Lambda
  inverse : ℕ → Lambda
  identity : ∀ᶠ i in (U : Filter ℕ), value i * inverse i - 1 ∈ stageIdeal i

variable {U}

/-- Its value at a fixed height-one specialization is the specialization of the integral limit. -/
def RetainedScalarUnit.at (d : RetainedScalarUnit U) (P : Ideal Lambda) [P.IsPrime] : ResAt P :=
  algebraMap Lambda (ResAt P) (ulim U d.value)

/-- A retained inverse certifies nonvanishing; mere stagewise nonzero scalars would not suffice. -/
theorem RetainedScalarUnit.at_ne_zero (hU : (U : Filter ℕ) ≤ cofinite)
    (d : RetainedScalarUnit U) (P : Ideal Lambda) [P.IsPrime] : d.at P ≠ 0 := by
  exact ((scalar_limit_isUnit stageIdeal_tendsToZero hU d.value d.inverse d.identity).map
    (algebraMap Lambda (ResAt P))).ne_zero

end ScalarInverses

section RetainedResidues

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}
  (D : RetainedLimitPairingStages U C) (J : ℕ → Matrix (Fin 2) (Fin 2) Lambda)

/-- The retained degree-one matrix with its coordinate type made explicit. -/
def localOnePairingMatrix (i : ℕ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Lambda :=
  D.loc 1 1 i

/-- The retained top-degree matrix in the degree-two and degree-zero Tate coordinates. -/
def localTopPairingMatrix (i : ℕ) : Matrix (Fin 2) (Fin 2) Lambda :=
  D.loc 2 0 i

/-- Retained scalar inverses and the finite-stage local cup-product comparisons in the same coordinate diagram. -/
structure RetainedLocalCupStages where
  e0 : RetainedScalarUnit U
  e2 : RetainedScalarUnit U
  e : RetainedScalarUnit U
  s : RetainedScalarUnit U
  residue : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (localOnePairingMatrix D i - residueCoefficientMatrix Lambda (e.value i) (s.value i) (J i)) a b ∈ stageIdeal i
  topPair : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
    (localTopPairingMatrix D i - crossCoefficientMatrix Lambda (e2.value i) (J i)) a b ∈ stageIdeal i

variable {D J} (hU : (U : Filter ℕ) ≤ cofinite) (L : RetainedLocalCupStages D J)
  (P : Ideal Lambda) [P.IsPrime]

include hU L

/-- The finite-stage residue comparison implies the precise degree-one identity of the duality certificate. -/
theorem RetainedLocalCupStages.b11 :
    ∀ x y, (localPairingOfMat (D.locK P)).b11 x y =
      -(switchPairing (L.e.at P) (L.s.at P) ((ulimMat U J).map (algebraMap Lambda (ResAt P))) y x) := by
  have hm := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU L.residue
  rw [residueCoefficientMatrix_limit] at hm
  intro x y
  change bilinOfMat ((ulimMat U (localOnePairingMatrix D)).map (algebraMap Lambda (ResAt P)))
    (lCoord (ResAt P) 1 x) (lCoord (ResAt P) 1 y) = _
  rw [hm, residueCoefficientMatrix_map]
  exact residueCoefficientMatrix_bilin _ _ _ x y

/-- The degree-two/degree-zero adjoint is the transported Tate pairing of the retained scalar. -/
theorem RetainedLocalCupStages.b20 :
    (localPairingOfMat (D.locK P)).b20 =
      crossPairing (L.e2.at P) ((ulimMat U J).map (algebraMap Lambda (ResAt P))) := by
  have hm := ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU L.topPair
  rw [crossCoefficientMatrix_limit] at hm
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change bilinOfMat ((ulimMat U (localTopPairingMatrix D)).map (algebraMap Lambda (ResAt P))) x y = _
  rw [hm, crossCoefficientMatrix_map]
  exact crossCoefficientMatrix_bilin _ _ x y

/-- Perfectness is derived from retained inverse data and the realized involution. -/
theorem RetainedLocalCupStages.b20_bijective
    (hJ : ((ulimMat U J).map (algebraMap Lambda (ResAt P))) *
      ((ulimMat U J).map (algebraMap Lambda (ResAt P))) = 1) :
    Function.Bijective (localPairingOfMat (D.locK P)).b20 := by
  rw [L.b20 hU P]
  exact (crossPairing_isPerfPair (L.e2.at_ne_zero hU P) hJ).bijective_left

/-- The actual retained global certificate now has no local perfectness or scalar-nonzero hypotheses. -/
theorem RetainedLocalCupStages.certificate (E : RetainedGlobalDualityStages D)
    (hJ : ((ulimMat U J).map (algebraMap Lambda (ResAt P))) *
      ((ulimMat U J).map (algebraMap Lambda (ResAt P))) = 1) :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) (L.e.at P) (L.s.at P)
      ((ulimMat U J).map (algebraMap Lambda (ResAt P))) :=
  fibreInnerLimitPairingCertificate_of_retained' hU E P (L.e.at P) (L.s.at P) _
    (L.e.at_ne_zero hU P) (L.s.at_ne_zero hU P) hJ (L.b11 hU P) (L.b20_bijective hU P hJ)

end RetainedResidues

section ActualConjugation

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- The integral matrix of the actual conjugation in the retained Tate basis. -/
def integralConjMatrix : Matrix (Fin 2) (Fin 2) Lambda :=
  (LinearMap.toMatrix (tateBasis (K := K) (S := S) (W := W)) tateBasis
    (conjTate Cn W hW)).map (algebraMap ℤ_[2] Lambda)

/-- Fixed-prime specialization gives exactly the conjugation matrix of the local duality interface. -/
theorem integralConjMatrix_map (P : Ideal Lambda) [P.IsPrime] :
    (integralConjMatrix Cn W hW).map (algebraMap Lambda (ResAt P)) = conjMatrix Cn W hW P := by
  ext a b
  change (algebraMap Lambda (ResAt P)).comp (algebraMap ℤ_[2] Lambda)
      (LinearMap.toMatrix (tateBasis (K := K) (S := S) (W := W)) tateBasis (conjTate Cn W hW) a b) = _
  rw [← IsScalarTower.algebraMap_eq]
  rfl

variable {U : Ultrafilter ℕ} {C : ComplexStages (R := Lambda) stageIdeal U}
  (hU : (U : Filter ℕ) ≤ cofinite) {D : RetainedLimitPairingStages U C}
  (L : RetainedLocalCupStages D (fun _ => integralConjMatrix Cn W hW))
  (P : Ideal Lambda) [P.IsPrime]

include hU

/-- Every retained scalar has a certified nonzero specialization, including the two trace scalars. -/
theorem RetainedLocalCupStages.scalars_ne_zero :
    L.e0.at P ≠ 0 ∧ L.e2.at P ≠ 0 ∧ L.e.at P ≠ 0 ∧ L.s.at P ≠ 0 :=
  ⟨L.e0.at_ne_zero hU P, L.e2.at_ne_zero hU P, L.e.at_ne_zero hU P, L.s.at_ne_zero hU P⟩

/-- The retained residue comparisons produce the actual conjugation certificate, not an unrelated involution. -/
theorem RetainedLocalCupStages.conjCertificate (E : RetainedGlobalDualityStages D) :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P)
      (L.e.at P) (L.s.at P) (conjMatrix Cn W hW P) := by
  have hJ : (ulimMat U (fun _ => integralConjMatrix Cn W hW)).map
      (algebraMap Lambda (ResAt P)) = conjMatrix Cn W hW P := by
    rw [ulimMat_const]
    exact integralConjMatrix_map Cn W hW P
  have hs : ((ulimMat U (fun _ => integralConjMatrix Cn W hW)).map
      (algebraMap Lambda (ResAt P))) * ((ulimMat U (fun _ => integralConjMatrix Cn W hW)).map
        (algebraMap Lambda (ResAt P))) = 1 := by
    rw [hJ]
    exact conjMatrix_mul_self Cn W hW P
  simpa only [hJ] using L.certificate hU P E hs

end ActualConjugation

section TateCoordinateFrames

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W] {U : Ultrafilter ℕ}
  (d : DerivativeMatrices (R := Lambda) stageIdeal U)

/-- A retained change of Tate coordinates, with the actual conjugation intertwining identity. -/
structure RetainedTateFrame where
  changeBasis : (Matrix (Fin 2) (Fin 2) Lambda)ˣ
  conjugation : (changeBasis : Matrix (Fin 2) (Fin 2) Lambda) * d.J =
    integralConjMatrix Cn W hW * (changeBasis : Matrix (Fin 2) (Fin 2) Lambda)

variable {Cn W hW d}

/-- The forward integral coordinate matrix. -/
def RetainedTateFrame.matrix (F : RetainedTateFrame Cn W hW d) : Matrix (Fin 2) (Fin 2) Lambda :=
  F.changeBasis

/-- The retained inverse belongs to the same integral coordinate diagram. -/
def RetainedTateFrame.inverseMatrix (F : RetainedTateFrame Cn W hW d) :
    Matrix (Fin 2) (Fin 2) Lambda :=
  ((F.changeBasis)⁻¹ : (Matrix (Fin 2) (Fin 2) Lambda)ˣ)

/-- The basis change is an actual invertible integral matrix. -/
theorem RetainedTateFrame.right_inverse (F : RetainedTateFrame Cn W hW d) :
    F.matrix * F.inverseMatrix = 1 := by
  change ((F.changeBasis * (F.changeBasis)⁻¹ : (Matrix (Fin 2) (Fin 2) Lambda)ˣ) :
    Matrix (Fin 2) (Fin 2) Lambda) = 1
  rw [mul_inv_cancel, Units.val_one]

/-- The actual rational Frobenius matrices in the retained local Tate coordinates. -/
def RetainedTateFrame.localStages (F : RetainedTateFrame Cn W hW d) (i : ℕ) :
    Matrix (Fin 2) (Fin 2) Lambda := F.matrix * d.rationalFrob i * F.inverseMatrix

/-- The moving Frobenius operators tend to the actual conjugation in those same coordinates. -/
theorem RetainedTateFrame.limit (hU : (U : Filter ℕ) ≤ cofinite)
    (F : RetainedTateFrame Cn W hW d) :
    ulimMat U F.localStages = integralConjMatrix Cn W hW := by
  change ulimMat U (fun i => F.matrix * d.rationalFrob i * F.inverseMatrix) = _
  rw [ulimMat_mul, ulimMat_mul, ulimMat_const, ulimMat_const,
    rationalFrob_limit stageIdeal_tendsToZero hU d]
  rw [show F.matrix * d.J = integralConjMatrix Cn W hW * F.matrix from F.conjugation,
    mul_assoc, F.right_inverse, mul_one]

/-- The finite-stage cup comparison now produces the certificate with the required actual conjugation. -/
theorem RetainedTateFrame.pairingCertificate (hU : (U : Filter ℕ) ≤ cofinite)
    (F : RetainedTateFrame Cn W hW d) {C : ComplexStages (R := Lambda) stageIdeal U}
    {D : RetainedLimitPairingStages U C} (L : RetainedLocalCupStages D F.localStages)
    (E : RetainedGlobalDualityStages D) (P : Ideal Lambda) [P.IsPrime] :
    FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P)
      (L.e.at P) (L.s.at P) (conjMatrix Cn W hW P) := by
  have hJ : (ulimMat U F.localStages).map (algebraMap Lambda (ResAt P)) = conjMatrix Cn W hW P := by
    rw [F.limit hU]
    exact integralConjMatrix_map Cn W hW P
  have hs : ((ulimMat U F.localStages).map (algebraMap Lambda (ResAt P))) *
      ((ulimMat U F.localStages).map (algebraMap Lambda (ResAt P))) = 1 := by
    rw [hJ]
    exact conjMatrix_mul_self Cn W hW P
  simpa only [hJ] using L.certificate hU P E hs

end TateCoordinateFrames


end PairingTransfer

section FixedPrimeConsumers

open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)

variable {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
  (P : Ideal Lambda) [P.IsPrime] {C : ComplexStages (R := Lambda) stageIdeal U}
  (D : RetainedLimitPairingStages U C)

/-- Localization followed by residue is the fixed coefficient specialization, not a stagewise field substitution. -/
theorem localizedResidue_comp :
    (resAt P).comp (algebraMap Lambda (Localization.AtPrime P)) = algebraMap Lambda (ResAt P) :=
  (IsScalarTower.algebraMap_eq Lambda (Localization.AtPrime P) (ResAt P)).symm

variable {F : Type} [Field F] {ι : Localization.AtPrime P →+* F}

/-- The finite side of the actual retained duality diagram has a derived stage equivalence. -/
def fibreFiniteStageEquiv
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .finite))) :
    (selCx (finiteLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) D0.stage := by
  have e := finiteSideStageEquiv stageIdeal_tendsToZero hU
    (algebraMap Lambda (Localization.AtPrime P)) C (retainedRestrictionStages D) D0
  have hr : ((IsLocalRing.residue (Localization.AtPrime P)).comp
      (algebraMap Lambda (Localization.AtPrime P))) = algebraMap Lambda (ResAt P) :=
    localizedResidue_comp P
  rw [hr, retainedRestriction_eq] at e
  exact e

/-- The singular side uses its own computed integral stage in the same retained diagram. -/
def fibreSingularStageEquiv
    (D1 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .singular))) :
    (selCx (singularLimitSide (fibreLimitGlobal U hU P C) (D.resLimit hU P)).Dside).toCC.homology 1
      ≃ₗ[ResAt P] fiberH1 (resAt P) D1.stage := by
  have e := singularSideStageEquiv stageIdeal_tendsToZero hU
    (algebraMap Lambda (Localization.AtPrime P)) C (retainedRestrictionStages D) D1
  have hr : ((IsLocalRing.residue (Localization.AtPrime P)).comp
      (algebraMap Lambda (Localization.AtPrime P))) = algebraMap Lambda (ResAt P) :=
    localizedResidue_comp P
  rw [hr, retainedRestriction_eq] at e
  exact e

/-- The fixed-prime consumer takes actual stage data and the pairing certificate, never side-equivalence hypotheses. -/
def derivedFibreNonquadStep
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .finite)))
    (D1 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .singular)))
    (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ : J * J = 1)
    (H : FibreInnerLimitPairingCertificate U hU P C (D.resLimit hU P) ε σ J)
    (hdet : finPlane (ResAt P) (Vec2 (ResAt P)) (Vec2 (ResAt P)) ≤
      (limitRelaxed (fibreLimitGlobal U hU P C) (D.resLimit hU P)).U) :
    QuasiNonquadStep (resAt P) D0.stage D1.stage :=
  fibreLimitNonquadStep U hU P C (D.resLimit hU P) D0.stage D1.stage ε σ J hε hσ hJ
    (fibreInnerLimitDuality_of_certificate U hU P C (D.resLimit hU P) ε σ J hε hσ hJ H) hdet
    (fibreFiniteStageEquiv hU P D D0) (fibreSingularStageEquiv hU P D D1)

end FixedPrimeConsumers

section ArithmeticConsumer

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.GlueSweep.Tate (torsField)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic] [HasFullTwoTorsion K S W]
  {α : GKS K S →* Lambdaˣ} [IsContChar α]
  {E0 : WeierstrassCurve ℚ} [E0.IsElliptic] {τ : GalQ} {h : ℕ → GalQ}
  {F0 : ℕ → IntermediateField ℚ Qbar} {excl : ℕ → Finset ℕ}

/-- Conditional arithmetic consumer: genuine moving primes, the same retained diagram and old Selmer cocycles,
computed side stages, and the local cup comparison. No side equivalence or self-annihilation is an input. -/
def retainedRealizedFibreNonquadStep
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (P : Ideal Lambda) [P.IsPrime]
    (_hheight : P.height = 1) (_hnotTwo : P ≠ Ideal.span {2})
    (C : ComplexStages (R := Lambda) stageIdeal U) (D : RetainedLimitPairingStages U C)
    (E : RetainedGlobalDualityStages D) (Cn : ActualConj K S) (hW : W.map (Cn.κ : K →+* K) = W)
    (X : RealizedLabel E0 K S W α τ h F0 excl)
    (_hquadratic : Module.finrank ℚ K = 2) (_himaginary : ∃ x : K, Cn.κ x ≠ x)
    (_hresidueDegree : ∀ i, Nat.card (𝓞 K ⧸ (X.label.q i).asIdeal) = (X.primes.ell i) ^ 2)
    (_hprior : ∀ i j, j < i → X.primes.ell j ∈ excl i)
    (hτ2 : τ * τ = 1)
    (hτμ : ∀ (M : ℕ) (ζ : Qbar), ζ ^ (2 ^ M) = 1 → τ ζ = ζ ^ (2 ^ M - 1))
    (hh : ∀ i, ∀ x ∈ torsField E0 i, h i x = x)
    (F : RetainedTateFrame Cn W hW (X.derivative hτ2 hτμ hh U))
    (L : RetainedLocalCupStages D F.localStages)
    (σ : ∀ i, Gloc K (X.label.q i)) (hσ : ∀ i, urRes K (X.label.q i) (σ i) = 1)
    (Δ : GaloisLocalConditions K S Lambda (TLam K S W α))
    (R : SelmerRealization W α Δ P (fibreLimitGlobal U hU P C) (D.resLimit hU P) X.label σ U)
    {T : Type} [Field T] {ι : Localization.AtPrime P →+* T}
    (D0 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .finite)))
    (D1 : IntegralMatrixStageData stageIdeal_tendsToZero hU
      (algebraMap Lambda (Localization.AtPrime P)) ι
        (selmerStages (derivativeDiagram C (retainedRestrictionStages D) .singular)))
    (a b : LinearMap.ker ((fibreLimitGlobal U hU P C).d 1 2 rfl))
    (hdet : (Matrix.of ![limitFrobValue P X.label U (R.toDegreeOne.cocycle a),
      limitFrobValue P X.label U (R.toDegreeOne.cocycle b)]).det ≠ 0) :
    QuasiNonquadStep (resAt P) D0.stage D1.stage :=
  derivedFibreNonquadStep hU P D D0 D1 (L.e.at P) (L.s.at P) (conjMatrix Cn W hW P)
    (L.e.at_ne_zero hU P) (L.s.at_ne_zero hU P) (conjMatrix_mul_self Cn W hW P)
    (F.pairingCertificate hU L E P) (R.toDegreeOne.finPlane_le_U hσ hU a b hdet)

end ArithmeticConsumer

section CoordinateExactSequences

variable {k : Type} [Field k]

/-- Transport a cochain short complex through specified cochain coordinate isomorphisms. -/
def coordinateShortSequence (S : ShortComplex (CochainComplex (ModuleCat k) ℤ))
    {A1 A2 A3 : CochainComplex (ModuleCat k) ℤ}
    (e1 : A1 ≅ S.X₁) (e2 : A2 ≅ S.X₂) (e3 : A3 ≅ S.X₃) :
    ShortComplex (CochainComplex (ModuleCat k) ℤ) :=
  ShortComplex.mk (e1.hom ≫ S.f ≫ e2.inv) (e2.hom ≫ S.g ≫ e3.inv)
    (by simp [Category.assoc])

/-- The coordinate sequence is isomorphic to the specified original sequence as a diagram. -/
def coordinateShortSequenceIso (S : ShortComplex (CochainComplex (ModuleCat k) ℤ))
    {A1 A2 A3 : CochainComplex (ModuleCat k) ℤ}
    (e1 : A1 ≅ S.X₁) (e2 : A2 ≅ S.X₂) (e3 : A3 ≅ S.X₃) :
    coordinateShortSequence S e1 e2 e3 ≅ S :=
  ShortComplex.isoMk e1 e2 e3
    (by simp [coordinateShortSequence, Category.assoc])
    (by simp [coordinateShortSequence, Category.assoc])

/-- Exactness is transported by the actual cochain isomorphism, not postulated for new maps. -/
theorem coordinateShortSequence_shortExact (S : ShortComplex (CochainComplex (ModuleCat k) ℤ))
    {A1 A2 A3 : CochainComplex (ModuleCat k) ℤ}
    (e1 : A1 ≅ S.X₁) (e2 : A2 ≅ S.X₂) (e3 : A3 ≅ S.X₃) (hS : S.ShortExact) :
    (coordinateShortSequence S e1 e2 e3).ShortExact :=
  ShortComplex.shortExact_of_iso (coordinateShortSequenceIso S e1 e2 e3).symm hS

/-- The connecting map commutes with the same cochain coordinate maps. -/
theorem coordinateShortSequence_delta (S : ShortComplex (CochainComplex (ModuleCat k) ℤ))
    {A1 A2 A3 : CochainComplex (ModuleCat k) ℤ}
    (e1 : A1 ≅ S.X₁) (e2 : A2 ≅ S.X₂) (e3 : A3 ≅ S.X₃) (hS : S.ShortExact) :
    (coordinateShortSequence_shortExact S e1 e2 e3 hS).δ 1 2 rfl ≫
      HomologicalComplex.homologyMap e1.hom 2 =
        HomologicalComplex.homologyMap e3.hom 1 ≫ hS.δ 1 2 rfl :=
  HomologicalComplex.HomologySequence.δ_naturality (coordinateShortSequenceIso S e1 e2 e3).hom
    (coordinateShortSequence_shortExact S e1 e2 e3 hS) hS 1 2 rfl

variable (G : GCx k) (r : GHom G (splitLocalComplex k))

/-- The strict/relaxed sequence of the author's actual limiting Selmer complexes. -/
def nativeStrictSequence : ShortComplex (CochainComplex (ModuleCat k) ℤ) :=
  changeSES (limitRelaxed G r).D (strictLimitMap G r) (limitRelaxed G r).gR (strictLimitMap_zero G r)

/-- Its exactness uses the retained degree-zero term and the actual coordinate quotient. -/
theorem nativeStrictSequence_shortExact : (nativeStrictSequence G r).ShortExact :=
  relaxedQuotientNode_proof k (limitRelaxed G r).D (conditionComplex (⊥ : Submodule k (Coords k)))
    (limitRelaxed G r).Wrel (strictLimitMap G r) (limitRelaxed G r).gR (strictLimitMap_zero G r)
      (strictLimitMap_injective G r) (strictLimitQuot_surjective G r) (strictLimitQuot_exact G r)

/-- The connecting map here is the actual limit connecting map, including its convention. -/
theorem nativeStrictSequence_delta :
    (nativeStrictSequence_shortExact G r).δ 1 2 rfl = ModuleCat.ofHom (limitDelta G r) :=
  rfl

end CoordinateExactSequences

section MatrixExactSequence

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] {I : ℕ → Ideal R} {U : Ultrafilter ℕ}
  (hI : IdealsTendToZero I) (hU : (U : Filter ℕ) ≤ cofinite)
  {k : Type} [Field k] (ρ : R →+* k)
  (G : ComplexStages I U) (r : MapStages G (fullLocalStages I U))

/-- The strict matrix model is identified with the strict object in that very exact sequence. -/
def strictMatrixSequenceIso :
    (scalarComplex hI hU ρ (selmerStages (derivativeDiagram G r .strict))).toCC ≅
      (nativeStrictSequence (scalarComplex hI hU ρ G) (derivativeRestriction hI hU ρ G r)).X₁ := by
  have hD : restrictData (limitRelaxed (scalarComplex hI hU ρ G)
      (derivativeRestriction hI hU ρ G r)).D
        (strictLimitMap (scalarComplex hI hU ρ G) (derivativeRestriction hI hU ρ G r)) =
          derivativeSideData hI hU ρ G r .strict :=
    strictLimitMap_Data _ _
  exact derivativeMatrixIso hI hU ρ G r .strict ≪≫
    eqToIso (congrArg (fun D : SelData k => (selCx D).toCC) hD.symm)

/-- The matrix-coordinate strict/relaxed sequence is constructed from the derived cochain maps. -/
def matrixStrictSequence : ShortComplex (CochainComplex (ModuleCat k) ℤ) :=
  coordinateShortSequence
    (nativeStrictSequence (scalarComplex hI hU ρ G) (derivativeRestriction hI hU ρ G r))
    (strictMatrixSequenceIso hI hU ρ G r) (derivativeMatrixIso hI hU ρ G r .relaxed)
    (Iso.refl _)

/-- The constructed matrix-coordinate sequence is short exact. -/
theorem matrixStrictSequence_shortExact : (matrixStrictSequence hI hU ρ G r).ShortExact :=
  coordinateShortSequence_shortExact _ (strictMatrixSequenceIso hI hU ρ G r)
    (derivativeMatrixIso hI hU ρ G r .relaxed) (Iso.refl _)
      (nativeStrictSequence_shortExact _ _)

/-- The genuine matrix-coordinate connecting map carries to the actual limit connecting map. -/
theorem matrixStrictSequence_delta :
    (matrixStrictSequence_shortExact hI hU ρ G r).δ 1 2 rfl ≫
      HomologicalComplex.homologyMap (strictMatrixSequenceIso hI hU ρ G r).hom 2 =
        ModuleCat.ofHom (limitDelta (scalarComplex hI hU ρ G) (derivativeRestriction hI hU ρ G r)) := by
  have he := coordinateShortSequence_delta
    (nativeStrictSequence (scalarComplex hI hU ρ G) (derivativeRestriction hI hU ρ G r))
    (strictMatrixSequenceIso hI hU ρ G r) (derivativeMatrixIso hI hU ρ G r .relaxed)
    (Iso.refl _) (nativeStrictSequence_shortExact _ _)
  simp only [Iso.refl_hom, HomologicalComplex.homologyMap_id, nativeStrictSequence_delta] at he
  exact he.trans (Category.id_comp _)

end MatrixExactSequence

section RetainedOrientation

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.Wiring (ResAt)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {Cn : ActualConj K S} {W : WeierstrassCurve K} {hW : W.map (Cn.κ : K →+* K) = W}
  [W.IsElliptic] [HasFullTwoTorsion K S W] {U : Ultrafilter ℕ}
  {d : DerivativeMatrices (R := Lambda) stageIdeal U}

/-- The retained arithmetic orientation is preserved by the actual change of Tate coordinates. -/
theorem RetainedTateFrame.orientation (F : RetainedTateFrame Cn W hW d) (hd : d.J.det = -1) :
    (integralConjMatrix Cn W hW).det = -1 := by
  have hB : F.matrix.det * F.inverseMatrix.det = 1 := by
    rw [← Matrix.det_mul, F.right_inverse, Matrix.det_one]
  have hC : F.matrix * d.J * F.inverseMatrix = integralConjMatrix Cn W hW := by
    rw [show F.matrix * d.J = integralConjMatrix Cn W hW * F.matrix from F.conjugation,
      mul_assoc, F.right_inverse, mul_one]
  rw [← hC, Matrix.det_mul, Matrix.det_mul, hd]
  calc
    _ = -(F.matrix.det * F.inverseMatrix.det) := by ring
    _ = -1 := by rw [hB]

/-- The fixed-prime conjugation has the same determinant minus one in the certificate's basis. -/
theorem RetainedTateFrame.fibre_orientation (F : RetainedTateFrame Cn W hW d) (hd : d.J.det = -1)
    (P : Ideal Lambda) [P.IsPrime] : (conjMatrix Cn W hW P).det = -1 := by
  rw [← integralConjMatrix_map Cn W hW P]
  have hm := RingHom.map_det (algebraMap Lambda (ResAt P)) (integralConjMatrix Cn W hW)
  rw [F.orientation hd, map_neg, map_one] at hm
  exact hm.symm

end RetainedOrientation

end ZInQ.Contrib.RC53Assist.InnerLimitMoving
