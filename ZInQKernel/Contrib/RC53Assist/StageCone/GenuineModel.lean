import ZInQKernel.Contrib.CloudB3RC53.StageCone.Comparison
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso
import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.MinimalModelsExist
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer

/-!
# Integral stages with a continuous-cochain realization

A two-term model must be linked to the specified continuous-cochain Selmer
complex. The realization below records that link as an integral
quasi-isomorphism. Over a local ring, the proved minimal-model theorem constructs
such a realization from a bounded finite-free presentation whose residual
cohomology is balanced and concentrated in degrees one and two. The initial
presentation and the residual cohomology conditions remain inputs; no existence
statement for them is postulated.

Once that model is supplied, the actual class lifts integrally, with an actual
boundary witness. The actual closed functional pulls back integrally. The
stage matrix, class, functional, and generic coordinate are then constructed.
The final result records the obstruction to using a finite coefficient ring
as a characteristic-zero fraction-field lattice.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.StageCone

open CategoryTheory Matrix Module
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Central

section Lifts

variable {A : Type} [CommRing A] {B C : GCx A}

/-- A degree-one class lifts through an integral quasi-isomorphism, up to a specified boundary. -/
theorem cycle_lift_one (f : GHom B C) (hf : QuasiIso (GHom.toCC f))
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) :
    ∃ (x : B.X 1) (y : C.X 0),
      B.d 1 2 rfl x = 0 ∧ f.f 1 1 rfl x = z + C.d 0 1 rfl y := by
  have hac := coneCx_acyclic_of_quasiIso f hf
  have hc : (coneCx f).d 2 3 rfl ((0, z) : (coneCx f).X 2) = 0 := by
    change (B.d 2 3 rfl 0, f.f 2 2 rfl 0 - C.d 1 2 rfl z) = 0
    simp [hz]
  obtain ⟨⟨x, y⟩, hxy⟩ := hac 1 2 3 rfl rfl ((0, z) : (coneCx f).X 2) hc
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  change B.d 1 2 rfl x = 0 at hx
  change f.f 1 1 rfl x - C.d 0 1 rfl y = z at hy
  exact ⟨x, y, hx, sub_eq_iff_eq_add.mp hy⟩

/-- Degree-two cycles lift integrally as well; this tests the pulled-back functional. -/
theorem cycle_lift_two (f : GHom B C) (hf : QuasiIso (GHom.toCC f))
    (z : C.X 2) (hz : C.d 2 3 rfl z = 0) :
    ∃ (x : B.X 2) (y : C.X 1),
      B.d 2 3 rfl x = 0 ∧ f.f 2 2 rfl x = z + C.d 1 2 rfl y := by
  have hac := coneCx_acyclic_of_quasiIso f hf
  have hc : (coneCx f).d 3 4 rfl ((0, z) : (coneCx f).X 3) = 0 := by
    change (B.d 3 4 rfl 0, f.f 3 3 rfl 0 - C.d 2 3 rfl z) = 0
    simp [hz]
  obtain ⟨⟨x, y⟩, hxy⟩ := hac 2 3 4 rfl rfl ((0, z) : (coneCx f).X 3) hc
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  change B.d 2 3 rfl x = 0 at hx
  change f.f 2 2 rfl x - C.d 1 2 rfl y = z at hy
  exact ⟨x, y, hx, sub_eq_iff_eq_add.mp hy⟩

end Lifts

section Coordinates

variable {A : Type} [CommRing A] {n : ℕ}

/-- Coordinates of a functional in the standard basis. -/
def functionalRow (f : (Fin n → A) →ₗ[A] A) : Fin n → A :=
  fun j => f (Pi.single j 1)

theorem functionalRow_dot (f : (Fin n → A) →ₗ[A] A) (x : Fin n → A) :
    functionalRow f ⬝ᵥ x = f x := by
  conv_rhs => rw [pi_eq_sum_univ x]
  simp only [map_sum, map_smul, smul_eq_mul, functionalRow, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  have hs : (fun k : Fin n => if j = k then (1 : A) else 0) = Pi.single j 1 := by
    funext k
    by_cases hk : j = k
    · subst k; simp
    · simp [hk, Ne.symm hk]
  rw [hs, mul_comm]

/-- Scalar extension preserves a matrix cycle. -/
theorem map_cycle {F : Type} [CommRing F] (ι : A →+* F)
    (D : Matrix (Fin n) (Fin n) A) (z : Fin n → A) (hz : D *ᵥ z = 0) :
    D.map ι *ᵥ (fun j => ι (z j)) = 0 := by
  funext j
  change (D.map ι *ᵥ (ι ∘ z)) j = 0
  rw [← RingHom.map_mulVec, hz]
  exact map_zero ι

/-- Scalar extension preserves a closed matrix functional. -/
theorem map_closedRow {F : Type} [CommRing F] (ι : A →+* F)
    (D : Matrix (Fin n) (Fin n) A) (w : Fin n → A) (hw : w ᵥ* D = 0) :
    (fun j => ι (w j)) ᵥ* D.map ι = 0 := by
  funext j
  change ((ι ∘ w) ᵥ* D.map ι) j = 0
  rw [← RingHom.map_vecMul, hw]
  exact map_zero ι

theorem map_vector_ne_zero {F : Type} [CommRing F] (ι : A →+* F)
    (hι : Function.Injective ι) {z : Fin n → A} (hz : z ≠ 0) :
    (fun j => ι (z j)) ≠ 0 := by
  intro h0
  apply hz
  funext j
  apply hι
  simpa using congrFun h0 j

theorem coordinate_ne_zero {F : Type} [Field F] {D : Matrix (Fin n) (Fin n) F}
    {z w : Fin n → F} {u : F} (hu : IsClassFunctionalCoord D z w u)
    (hz : z ≠ 0) (hw : w ≠ 0) : u ≠ 0 := by
  have hz' : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hw' : ∃ j, w j ≠ 0 := by
    by_contra h
    apply hw
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨i, hi⟩ := hz'
  obtain ⟨j, hj⟩ := hw'
  intro h0
  have he := congrFun (congrFun hu i) j
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, h0, zero_mul] at he
  exact (mul_ne_zero hi hj) he

end Coordinates

section Realization

variable {A : Type} [CommRing A] (C : GCx A)

/-- A based two-term integral model of a specified complex, not unconstrained Selmer data. -/
structure TwoTermRealization where
  model : GCx A
  n : ℕ
  b1 : Basis (Fin (n + 1)) A (model.X 1)
  b2 : Basis (Fin (n + 1)) A (model.X 2)
  outside : ∀ j : ℤ, j ≠ 1 → j ≠ 2 → Subsingleton (model.X j)
  f : GHom model C
  quasiIso : QuasiIso (GHom.toCC f)

variable {C} (R : TwoTermRealization C)

/-- The differential in the retained integral bases. -/
def TwoTermRealization.dVec : (Fin (R.n + 1) → A) →ₗ[A] (Fin (R.n + 1) → A) :=
  R.b2.equivFun.toLinearMap ∘ₗ R.model.d 1 2 rfl ∘ₗ R.b1.equivFun.symm.toLinearMap

def TwoTermRealization.matrix : Matrix (Fin (R.n + 1)) (Fin (R.n + 1)) A :=
  LinearMap.toMatrix' R.dVec

theorem TwoTermRealization.matrix_mulVec (x : Fin (R.n + 1) → A) :
    R.matrix *ᵥ x = R.dVec x := by
  change Matrix.toLin' (LinearMap.toMatrix' R.dVec) x = _
  rw [Matrix.toLin'_toMatrix']

def TwoTermRealization.liftedClass (z : C.X 1) (hz : C.d 1 2 rfl z = 0) : R.model.X 1 :=
  (cycle_lift_one R.f R.quasiIso z hz).choose

def TwoTermRealization.boundaryWitness (z : C.X 1) (hz : C.d 1 2 rfl z = 0) : C.X 0 :=
  (cycle_lift_one R.f R.quasiIso z hz).choose_spec.choose

theorem TwoTermRealization.liftedClass_closed (z : C.X 1) (hz : C.d 1 2 rfl z = 0) :
    R.model.d 1 2 rfl (R.liftedClass z hz) = 0 :=
  (cycle_lift_one R.f R.quasiIso z hz).choose_spec.choose_spec.1

theorem TwoTermRealization.liftedClass_image (z : C.X 1) (hz : C.d 1 2 rfl z = 0) :
    R.f.f 1 1 rfl (R.liftedClass z hz) = z + C.d 0 1 rfl (R.boundaryWitness z hz) :=
  (cycle_lift_one R.f R.quasiIso z hz).choose_spec.choose_spec.2

def TwoTermRealization.classVec (z : C.X 1) (hz : C.d 1 2 rfl z = 0) : Fin (R.n + 1) → A :=
  R.b1.equivFun (R.liftedClass z hz)

/-- Pull back the specified actual functional, with no normalization change. -/
def TwoTermRealization.functional (lam : C.X 2 →ₗ[A] A) : (Fin (R.n + 1) → A) →ₗ[A] A :=
  lam ∘ₗ R.f.f 2 2 rfl ∘ₗ R.b2.equivFun.symm.toLinearMap

def TwoTermRealization.row (lam : C.X 2 →ₗ[A] A) : Fin (R.n + 1) → A :=
  functionalRow (R.functional lam)

theorem TwoTermRealization.classVec_closed (z : C.X 1) (hz : C.d 1 2 rfl z = 0) :
    R.matrix *ᵥ R.classVec z hz = 0 := by
  rw [R.matrix_mulVec]
  change R.b2.equivFun (R.model.d 1 2 rfl
    (R.b1.equivFun.symm (R.b1.equivFun (R.liftedClass z hz)))) = 0
  rw [LinearEquiv.symm_apply_apply, R.liftedClass_closed, map_zero]

theorem TwoTermRealization.functional_closed (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y : C.X 1, lam (C.d 1 2 rfl y) = 0) (x : Fin (R.n + 1) → A) :
    R.functional lam (R.matrix *ᵥ x) = 0 := by
  rw [R.matrix_mulVec]
  dsimp only [TwoTermRealization.functional, TwoTermRealization.dVec,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply, R.f.comm 1 2 1 2 rfl rfl rfl rfl]
  exact hlam _

theorem TwoTermRealization.row_closed (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y : C.X 1, lam (C.d 1 2 rfl y) = 0) : R.row lam ᵥ* R.matrix = 0 := by
  funext j
  have he := R.functional_closed lam hlam (Pi.single j 1)
  rw [← functionalRow_dot, dotProduct_mulVec, dotProduct_single, mul_one] at he
  exact he

/-- Construct the stage, including its generic coordinate, from the realized actual class
and functional. The generic rank-one condition is supplied as determinant and adjugate data. -/
def stageOfRealization {F : Type} [Field F] (ι : A →+* F)
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y : C.X 1, lam (C.d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0) :
    TwoTermStage ι :=
  let hzA := R.classVec_closed z hz
  let hwA := R.row_closed lam hlam
  let hu := exists_isClassFunctionalCoord hdet hadj
    (map_cycle ι R.matrix (R.classVec z hz) hzA)
    (map_closedRow ι R.matrix (R.row lam) hwA)
  { n := R.n
    D := R.matrix
    z := R.classVec z hz
    w := R.row lam
    u := hu.choose
    hz := hzA
    hw := hwA
    hu := hu.choose_spec }

/-- The constructed class represents the specified actual class, with the retained boundary. -/
theorem stageOfRealization_class {F : Type} [Field F] (ι : A →+* F)
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y : C.X 1, lam (C.d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0) :
    R.f.f 1 1 rfl (R.b1.equivFun.symm (stageOfRealization R ι z hz lam hlam hdet hadj).z) =
      z + C.d 0 1 rfl (R.boundaryWitness z hz) := by
  change R.f.f 1 1 rfl (R.b1.equivFun.symm (R.b1.equivFun (R.liftedClass z hz))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact R.liftedClass_image z hz

/-- Evaluation of the constructed row is evaluation of the actual functional on the realization. -/
theorem stageOfRealization_functional {F : Type} [Field F] (ι : A →+* F)
    (z : C.X 1) (hz : C.d 1 2 rfl z = 0) (lam : C.X 2 →ₗ[A] A)
    (hlam : ∀ y : C.X 1, lam (C.d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0)
    (x : Fin (R.n + 1) → A) :
    (stageOfRealization R ι z hz lam hlam hdet hadj).w ⬝ᵥ x =
      lam (R.f.f 2 2 rfl (R.b2.equivFun.symm x)) :=
  functionalRow_dot (R.functional lam) x

/-- A nonboundary actual class and a functional nonzero on actual cycles give a nonzero
stage coordinate. This is derived, not another coordinate hypothesis. -/
theorem stageOfRealization_ne_zero {F : Type} [Field F] (ι : A →+* F)
    (hι : Function.Injective ι) (z : C.X 1) (hz : C.d 1 2 rfl z = 0)
    (lam : C.X 2 →ₗ[A] A) (hlam : ∀ y : C.X 1, lam (C.d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0)
    (hznb : ∀ y : C.X 0, C.d 0 1 rfl y ≠ z)
    (hlne : ∃ x : C.X 2, C.d 2 3 rfl x = 0 ∧ lam x ≠ 0) :
    (stageOfRealization R ι z hz lam hlam hdet hadj).u ≠ 0 := by
  have hzL : R.liftedClass z hz ≠ 0 := by
    intro h0
    have he := R.liftedClass_image z hz
    rw [h0, map_zero] at he
    apply hznb (-R.boundaryWitness z hz)
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left he.symm).symm
  have hzv : R.classVec z hz ≠ 0 := by
    intro h0
    apply hzL
    exact R.b1.equivFun.injective (h0.trans (map_zero _).symm)
  have hwv : R.row lam ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hxl⟩ := hlne
    obtain ⟨y, b, _, hy⟩ := cycle_lift_two R.f R.quasiIso x hx
    have he : R.functional lam (R.b2.equivFun y) = lam x := by
      dsimp only [TwoTermRealization.functional, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_apply, hy, map_add, hlam b, add_zero]
    have he0 : R.functional lam (R.b2.equivFun y) = 0 := by
      rw [← functionalRow_dot]
      change R.row lam ⬝ᵥ R.b2.equivFun y = 0
      rw [h0, zero_dotProduct]
    exact hxl (he.symm.trans he0)
  exact coordinate_ne_zero (stageOfRealization R ι z hz lam hlam hdet hadj).hu
    (map_vector_ne_zero ι hι hzv) (map_vector_ne_zero ι hι hwv)

end Realization

section MinimalRealization

open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.ResidualTransfer

variable {A : Type} [CommRing A]

/-- A finite free module of rank zero vanishes. -/
theorem free_subsingleton_of_finrank_zero [Nontrivial A]
    (V : Type) [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (hV : Module.finrank A V = 0) : Subsingleton V := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A V) = 0 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hV]
  have : IsEmpty (Module.Free.ChooseBasisIndex A V) := Fintype.card_eq_zero_iff.mp hcard
  exact (Module.Free.chooseBasis A V).repr.subsingleton

/-- Retain a finite basis, reindexed by its specified rank. -/
def finBasisOfFinrank [Nontrivial A]
    (V : Type) [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (n : ℕ) (hV : Module.finrank A V = n) : Basis (Fin n) A V :=
  (Module.Free.chooseBasis A V).reindex
    ((Fintype.equivFin (Module.Free.ChooseBasisIndex A V)).trans
      (finCongr ((Module.finrank_eq_card_chooseBasisIndex A V).symm.trans hV)))

/-- Recover the Mathlib complex after passage to relation-indexed differentials. -/
def ofCCToCCIso (K : CochainComplex (ModuleCat.{0} A) ℤ) : (ofCC K).toCC ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    ext x
    exact (GCx.toCC_d_hom (ofCC K) i j hij x).symm)

/-- Conversion of a map from a Mathlib presentation preserves quasi-isomorphy. -/
theorem ofCCHom_quasiIso {K : CochainComplex (ModuleCat.{0} A) ℤ} {C : GCx A}
    (f : K ⟶ C.toCC) (hf : QuasiIso f) : QuasiIso (GHom.toCC (ofCCHom f)) := by
  have := hf
  have he : GHom.toCC (ofCCHom f) = (ofCCToCCIso K).hom ≫ f := by
    ext i x
    rfl
  rw [he]
  infer_instance

/-- Construct a based minimal two-term realization from a bounded finite-free presentation.

The residual support and equal positive ranks force the minimal model to have
only degrees one and two. The presentation map is to the specified complex,
which may be its full continuous-cochain model, not to an unrelated Selmer datum.
The specified rank and integral minimality are retained in the conclusion.
The minimal-model existence used here is proved by integral unit-disk cancellation. -/
theorem exists_twoTermRealization_of_boundedFree [IsLocalRing A]
    (C : GCx A) (K : CochainComplex (ModuleCat.{0} A) ℤ)
    (hfree : ∀ i, Module.Free A (K.X i) ∧ Module.Finite A (K.X i))
    (hbd : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (K.X i))
    (f : K ⟶ C.toCC) (hf : QuasiIso f) (n : ℕ)
    (hres : ∀ i : ℤ, Module.finrank (IsLocalRing.ResidueField A) ((resCx K).homology i) =
      if i = 1 ∨ i = 2 then n + 1 else 0) :
    ∃ R : TwoTermRealization C, R.n = n ∧
      ∀ (i j : ℤ) (hij : i + 1 = j) (x : R.model.X i),
        R.model.d i j hij x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (R.model.X j)) := by
  obtain ⟨L, ⟨e⟩, hfreeL, hminL, _, hrank⟩ := minimalModelsExist_proof A K hfree hbd
  have hfree1 : Module.Free A (L.X 1) := (hfreeL 1).1
  have hfinite1 : Module.Finite A (L.X 1) := (hfreeL 1).2
  have hfree2 : Module.Free A (L.X 2) := (hfreeL 2).1
  have hfinite2 : Module.Finite A (L.X 2) := (hfreeL 2).2
  change ∀ i, Module.finrank A (L.X i) =
    Module.finrank (IsLocalRing.ResidueField A) ((resCx K).homology i) at hrank
  have h1 : Module.finrank A (L.X 1) = n + 1 := by
    rw [hrank 1, hres 1]
    simp
  have h2 : Module.finrank A (L.X 2) = n + 1 := by
    rw [hrank 2, hres 2]
    simp
  have hout : ∀ i : ℤ, i ≠ 1 → i ≠ 2 → Subsingleton (L.X i) := by
    intro i hi1 hi2
    have hfreei : Module.Free A (L.X i) := (hfreeL i).1
    have hfinitei : Module.Finite A (L.X i) := (hfreeL i).2
    apply free_subsingleton_of_finrank_zero (A := A) (L.X i)
    rw [hrank i, hres i]
    simp [hi1, hi2]
  have := hf
  have hq : QuasiIso (e.inv ≫ f) := inferInstance
  let T : TwoTermRealization C := {
    model := ofCC L
    n := n
    b1 := finBasisOfFinrank (A := A) (L.X 1) (n + 1) h1
    b2 := finBasisOfFinrank (A := A) (L.X 2) (n + 1) h2
    outside := hout
    f := ofCCHom (e.inv ≫ f)
    quasiIso := ofCCHom_quasiIso (e.inv ≫ f) hq }
  refine ⟨T, rfl, ?_⟩
  intro i j hij x
  exact hminL i j x

end MinimalRealization

section Genuine

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex

variable (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
variable (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul A M]
  [ContinuousSMul (GKS K S) M]

/-- Realizations of the specified continuous-cochain Selmer complex over the coefficient ring. -/
abbrev GenuineTwoTermRealization (Delta : GaloisLocalConditions K S A M) :=
  TwoTermRealization (selCx (galoisSelData K S A M Delta))

/-- The actual integral stage constructor, specialized to genuine Galois Selmer data.
Existence of the realized bounded model and its generic rank-one condition remain open inputs. -/
def genuineStage {F : Type} [Field F] (ι : A →+* F)
    (Delta : GaloisLocalConditions K S A M) (R : GenuineTwoTermRealization K S A M Delta)
    (z : (selCx (galoisSelData K S A M Delta)).X 1)
    (hz : (selCx (galoisSelData K S A M Delta)).d 1 2 rfl z = 0)
    (lam : (selCx (galoisSelData K S A M Delta)).X 2 →ₗ[A] A)
    (hlam : ∀ y, lam ((selCx (galoisSelData K S A M Delta)).d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0) :
    TwoTermStage ι :=
  stageOfRealization R ι z hz lam hlam hdet hadj

end Genuine

section FiniteCoefficients

open ZInQ.Manuscript.RC.HeegnerAlgebra

/-- Finite coefficient stages are not characteristic-zero integral fraction-field lattices. -/
theorem isEmpty_ringHom_acoef_charZero (i : ℕ) (F : Type) [Field F] [CharZero F] :
    IsEmpty (Acoef i →+* F) := by
  constructor
  intro f
  have hz : ((2 ^ i : ℕ) : Acoef i) = 0 := by
    rw [← map_natCast (algebraMap (ZMod (2 ^ i)) (Acoef i))]
    simp
  have hF : ((2 ^ i : ℕ) : F) = 0 := by
    rw [← map_natCast f, hz, map_zero]
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero i (by decide : (2 : ℕ) ≠ 0))) hF

end FiniteCoefficients

set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true

end ZInQ.Contrib.RC53Assist.StageCone
