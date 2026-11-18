import ZInQKernel.Contrib.RC53Assist.StageCone.GenuineModel
import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.PrimitiveKernel
import ZInQKernel.Contrib.RC53Assist.StageCone.CommonFactor
import ZInQKernel.Contrib.RC53Assist.StageCone.IntegralLattice

/-!
# Primitive kernel vectors and regularity for retained Selmer classes

The continuous-cochain Selmer cone, its specified integral class, and its
specified functional are retained throughout. A primitive kernel vector is
chosen separately, solely for residue-field detection. The nonvanishing input
is that the specified actual cycle is not a boundary, as required for the
nonzero actual class in the height-one regularity argument, lines 4992–4995
and 5137–5157. Minimality alone does not imply this input.

A bounded finite-free presentation constructs the minimal realization.
The paired representative comes from an integral orthogonal lift of the same
actual class and the specified Selmer cup product and trace. Explicit
successors, actual-class comparison maps, and local-image geometry then
construct the height-one switching data and its regularity conclusion.
The arithmetic construction of those inputs is not asserted here.

The determinant comparison retains the common strict factor, as in lines
4900–4906 and 5148–5152. Its being common suffices for coordinate steps;
its being unit-valued is the additional condition for the two individual
integral-unit comparisons. No additional arithmetic proposition is postulated.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.StagePrimitive

open CategoryTheory Matrix Module NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Contrib.CloudB3RC53.StageCone
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.StageCone
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Uniform
open ZInQ.Manuscript.RC.Uniform.QuadraticCase

section RetainedClass

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (A : Type) [CommRing A]
  (M : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul A M]
  [ContinuousSMul (GKS K S) M]
  (Delta : GaloisLocalConditions K S A M)

/-- The retained coordinate vector is nonzero exactly when the specified
actual Selmer class is nonzero in degree-one cohomology. -/
theorem genuineClassVec_ne_zero_iff
    (R : GenuineTwoTermRealization K S A M Delta)
    (z : (selCx (galoisSelData K S A M Delta)).X 1)
    (hz : (selCx (galoisSelData K S A M Delta)).d 1 2 rfl z = 0) :
    R.classVec z hz ≠ 0 ↔
      ∀ y : (selCx (galoisSelData K S A M Delta)).X 0,
        (selCx (galoisSelData K S A M Delta)).d 0 1 rfl y ≠ z := by
  let C := selCx (galoisSelData K S A M Delta)
  constructor
  · intro hv y hy
    have hc : (coneCx R.f).d 1 2 rfl
        ((R.liftedClass z hz, y + R.boundaryWitness z hz) : (coneCx R.f).X 1) = 0 := by
      change (R.model.d 1 2 rfl (R.liftedClass z hz),
        R.f.f 1 1 rfl (R.liftedClass z hz) -
          C.d 0 1 rfl (y + R.boundaryWitness z hz)) = 0
      rw [R.liftedClass_closed, R.liftedClass_image, map_add, hy]
      simp [C]
    obtain ⟨⟨a, b⟩, hab⟩ := (coneCx_acyclic_of_quasiIso R.f R.quasiIso)
      0 1 2 rfl rfl _ hc
    have ha := congrArg Prod.fst hab
    change R.model.d 0 1 rfl a = R.liftedClass z hz at ha
    have ha0 : a = 0 := (R.outside 0 (by decide) (by decide)).elim a 0
    have hx0 : R.liftedClass z hz = 0 := by
      rw [ha0, map_zero] at ha
      exact ha.symm
    apply hv
    change R.b1.equivFun (R.liftedClass z hz) = 0
    rw [hx0, map_zero]
  · intro hnb hv
    have hx0 : R.liftedClass z hz = 0 :=
      R.b1.equivFun.injective (hv.trans (map_zero _).symm)
    have he := R.liftedClass_image z hz
    rw [hx0, map_zero] at he
    apply hnb (-R.boundaryWitness z hz)
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left he.symm).symm

/-- A nonboundary actual class in a two-term integral realization is not
torsion: no nonzero scalar multiple is an actual boundary. -/
theorem genuineClass_not_torsion_boundary [IsDomain A]
    (R : GenuineTwoTermRealization K S A M Delta)
    (z : (selCx (galoisSelData K S A M Delta)).X 1)
    (hz : (selCx (galoisSelData K S A M Delta)).d 1 2 rfl z = 0)
    (hnb : ∀ y : (selCx (galoisSelData K S A M Delta)).X 0,
      (selCx (galoisSelData K S A M Delta)).d 0 1 rfl y ≠ z)
    (a : A) (ha : a ≠ 0) (y : (selCx (galoisSelData K S A M Delta)).X 0) :
    (selCx (galoisSelData K S A M Delta)).d 0 1 rfl y ≠ a • z := by
  let C := selCx (galoisSelData K S A M Delta)
  intro hy
  have hc : (coneCx R.f).d 1 2 rfl
      ((a • R.liftedClass z hz, y + a • R.boundaryWitness z hz) : (coneCx R.f).X 1) = 0 := by
    change (R.model.d 1 2 rfl (a • R.liftedClass z hz),
      R.f.f 1 1 rfl (a • R.liftedClass z hz) -
        C.d 0 1 rfl (y + a • R.boundaryWitness z hz)) = 0
    rw [map_smul, R.liftedClass_closed, smul_zero, map_smul,
      R.liftedClass_image, map_add, map_smul, hy, smul_add]
    simp [C]
  obtain ⟨⟨b, c⟩, hbc⟩ := (coneCx_acyclic_of_quasiIso R.f R.quasiIso)
    0 1 2 rfl rfl _ hc
  have hb := congrArg Prod.fst hbc
  change R.model.d 0 1 rfl b = a • R.liftedClass z hz at hb
  have hb0 : b = 0 := (R.outside 0 (by decide) (by decide)).elim b 0
  rw [hb0, map_zero] at hb
  have hv0 : a • R.classVec z hz = 0 := by
    change a • R.b1.equivFun (R.liftedClass z hz) = 0
    rw [← map_smul, ← hb, map_zero]
  apply (genuineClassVec_ne_zero_iff K S A M Delta R z hz).2 hnb
  funext i
  have hi := congrFun hv0 i
  change a * R.classVec z hz i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left ha

/-- In the zero-class branch the genuine coordinate vanishes, so no
primitive-kernel witness or switching process is needed for regularity. -/
theorem genuineStage_coordinate_zero_of_boundary {F : Type} [Field F]
    (ι : A →+* F) (R : GenuineTwoTermRealization K S A M Delta)
    (z : (selCx (galoisSelData K S A M Delta)).X 1)
    (hz : (selCx (galoisSelData K S A M Delta)).d 1 2 rfl z = 0)
    (lam : (selCx (galoisSelData K S A M Delta)).X 2 →ₗ[A] A)
    (hlam : ∀ y, lam ((selCx (galoisSelData K S A M Delta)).d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0)
    (y : (selCx (galoisSelData K S A M Delta)).X 0)
    (hy : (selCx (galoisSelData K S A M Delta)).d 0 1 rfl y = z) :
    (genuineStage K S A M ι Delta R z hz lam hlam hdet hadj).u = 0 := by
  let T := genuineStage K S A M ι Delta R z hz lam hlam hdet hadj
  have hz0 : T.z = 0 := by
    change R.classVec z hz = 0
    by_contra h
    exact (genuineClassVec_ne_zero_iff K S A M Delta R z hz).1 h y hy
  have hu0 : ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
      (T.D.map ι) (fun i => ι (T.z i)) (fun i => ι (T.w i)) 0 := by
    unfold ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord
    ext i j
    simp [hz0, vecMulVec]
  exact ZInQ.Manuscript.RC.Central.isClassFunctionalCoord_unique hadj T.hu hu0

variable {F k : Type} [Field F] [Field k] [IsDomain A] [IsDiscreteValuationRing A]

/-- Saturation supplies the primitive-kernel field for the genuine stage,
without altering the actual class or its functional. -/
theorem genuineStage_primitiveKernel (ι : A →+* F) (hι : Function.Injective ι)
    (ρ : A →+* k) (R : GenuineTwoTermRealization K S A M Delta)
    (z : (selCx (galoisSelData K S A M Delta)).X 1)
    (hz : (selCx (galoisSelData K S A M Delta)).d 1 2 rfl z = 0)
    (lam : (selCx (galoisSelData K S A M Delta)).X 2 →ₗ[A] A)
    (hlam : ∀ y, lam ((selCx (galoisSelData K S A M Delta)).d 1 2 rfl y) = 0)
    (hdet : (R.matrix.map ι).det = 0) (hadj : (R.matrix.map ι).adjugate ≠ 0)
    (hnb : ∀ y : (selCx (galoisSelData K S A M Delta)).X 0,
      (selCx (galoisSelData K S A M Delta)).d 0 1 rfl y ≠ z) :
    Nonempty (PrimitiveKernelVector
      (genuineStage K S A M ι Delta R z hz lam hlam hdet hadj) ρ) := by
  apply exists_primitiveKernelVector hι ρ
  have hv := (genuineClassVec_ne_zero_iff K S A M Delta R z hz).2 hnb
  by_contra h
  push Not at h
  apply hv
  funext i
  exact h i

end RetainedClass

section MinimalPresentation

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (A : Type) [CommRing A] [IsLocalRing A]
  (M : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul A M]
  [ContinuousSMul (GKS K S) M]
  (Delta : GaloisLocalConditions K S A M)

/-- A bounded finite-free presentation of the specified continuous-cochain
Selmer cone. No two-term realization or regular coordinate is an input. -/
structure GenuinePresentation where
  complex : CochainComplex (ModuleCat.{0} A) ℤ
  finite_free : ∀ i, Module.Free A (complex.X i) ∧ Module.Finite A (complex.X i)
  bounded : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → Subsingleton (complex.X i)
  comparison : complex ⟶ (selCx (galoisSelData K S A M Delta)).toCC
  quasiIso : QuasiIso comparison
  n : ℕ
  residual : ∀ i : ℤ,
    Module.finrank (IsLocalRing.ResidueField A)
      ((ZInQ.Contrib.CloudB3RC53.ResidualTransfer.resCx complex).homology i) =
        if i = 1 ∨ i = 2 then n + 1 else 0

variable {K S A M Delta}

/-- Choose the minimal realization proved to exist by integral unit-disk
cancellation, with the comparison still to the specified Selmer cone. -/
def GenuinePresentation.realization (P : GenuinePresentation K S A M Delta) :
    GenuineTwoTermRealization K S A M Delta :=
  (exists_twoTermRealization_of_boundedFree
    (selCx (galoisSelData K S A M Delta)) P.complex P.finite_free
    P.bounded P.comparison P.quasiIso P.n P.residual).choose

/-- The selected realization retains the residual rank and integral minimality. -/
theorem GenuinePresentation.realization_spec (P : GenuinePresentation K S A M Delta) :
    P.realization.n = P.n ∧
      ∀ (i j : ℤ) (hij : i + 1 = j) (x : P.realization.model.X i),
        P.realization.model.d i j hij x ∈
          IsLocalRing.maximalIdeal A • (⊤ : Submodule A (P.realization.model.X j)) :=
  (exists_twoTermRealization_of_boundedFree
    (selCx (galoisSelData K S A M Delta)) P.complex P.finite_free
    P.bounded P.comparison P.quasiIso P.n P.residual).choose_spec

/-- The differential of the selected genuine minimal realization vanishes
under every residue map killing the maximal ideal. -/
theorem GenuinePresentation.matrix_residue_zero {k : Type} [Field k]
    (P : GenuinePresentation K S A M Delta) (ρ : A →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) :
    P.realization.matrix.map ρ = 0 := by
  let R := P.realization
  have hk : ∀ (y : R.model.X 2),
      y ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (R.model.X 2)) →
        ∀ i, ρ (R.b2.equivFun y i) = 0 := by
    intro y hy i
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha x _
      rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, hρ a ha, zero_mul]
    · intro x y hx hy
      rw [map_add, Pi.add_apply, map_add, hx, hy, add_zero]
  ext i j
  have he := congrFun (R.matrix_mulVec (Pi.single j 1)) i
  simp only [mulVec, dotProduct_single, mul_one] at he
  change ρ (R.matrix i j) = 0
  rw [he]
  exact hk _ (P.realization_spec.2 1 2 rfl _) i

end MinimalPresentation

section PairedRepresentative

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (A : Type) [CommRing A]
  (M N : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul A M]
  [ContinuousSMul (GKS K S) M]
  [AddCommGroup N] [Module A N]
  [DistribMulAction (GKS K S) N] [SMulCommClass (GKS K S) A N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul A N]
  [ContinuousSMul (GKS K S) N]
  (Delta : GaloisLocalConditions K S A M)
  (z : (selCx (galoisSelData K S A M Delta)).X 1)

/-- An integral representative of the functional of the same actual class.
The conjugate and orthogonal complexes are specified continuous-cochain
Selmer cones. The integral orthogonal lift, cup product, trace, and generic
nondegeneracy are arithmetic inputs, not arbitrary closed functionals.
The final field is generic nondegeneracy modulo torsion, expressed on actual
cycles and boundaries. -/
structure RetainedIntegralPairing where
  orthogonalConditions : GaloisLocalConditions K S A N
  conjugateConditions : GaloisLocalConditions K S A N
  conjugation : GHom (selCx (galoisSelData K S A M Delta))
    (selCx (galoisSelData K S A N conjugateConditions))
  conjugation_quasiIso : QuasiIso (GHom.toCC conjugation)
  comparison : GHom (selCx (galoisSelData K S A N orthogonalConditions))
    (selCx (galoisSelData K S A N conjugateConditions))
  comparison_quasiIso : QuasiIso (GHom.toCC comparison)
  orthogonalClass : (selCx (galoisSelData K S A N orthogonalConditions)).X 1
  orthogonal_closed :
    (selCx (galoisSelData K S A N orthogonalConditions)).d 1 2 rfl orthogonalClass = 0
  boundary : (selCx (galoisSelData K S A N conjugateConditions)).X 0
  lift_image : comparison.f 1 1 rfl orthogonalClass = conjugation.f 1 1 rfl z +
    (selCx (galoisSelData K S A N conjugateConditions)).d 0 1 rfl boundary
  pairing : SelPairData (galoisSelData K S A M Delta)
    (galoisSelData K S A N orthogonalConditions)
  trace : (coneCx pairing.resE).X 3 →ₗ[A] A
  trace_closed : ∀ x, trace ((coneCx pairing.resE).d 2 3 rfl x) = 0
  generic_nondegenerate :
    ∀ y : (selCx (galoisSelData K S A N orthogonalConditions)).X 1,
      (selCx (galoisSelData K S A N orthogonalConditions)).d 1 2 rfl y = 0 →
      (∀ w : (selCx (galoisSelData K S A M Delta)).X 2,
        (selCx (galoisSelData K S A M Delta)).d 2 3 rfl w = 0 →
          traceComp (selPair pairing) trace 2 1 rfl w y = 0) →
      ∃ a : A, a ≠ 0 ∧
        ∃ b : (selCx (galoisSelData K S A N orthogonalConditions)).X 0,
          (selCx (galoisSelData K S A N orthogonalConditions)).d 0 1 rfl b = a • y

variable {K S A M N Delta z}

/-- Pair with the retained orthogonal lift of the same actual class. -/
def RetainedIntegralPairing.functional
    (P : RetainedIntegralPairing K S A M N Delta z) :
    (selCx (galoisSelData K S A M Delta)).X 2 →ₗ[A] A :=
  (traceComp (selPair P.pairing) P.trace 2 1 rfl).flip P.orthogonalClass

/-- The specified paired representative is closed integrally. -/
theorem RetainedIntegralPairing.functional_closed
    (P : RetainedIntegralPairing K S A M N Delta z) :
    ∀ y, P.functional ((selCx (galoisSelData K S A M Delta)).d 1 2 rfl y) = 0 := by
  intro y
  have h := (selPair P.pairing).leib 1 2 1 2 2 3 rfl rfl rfl rfl y P.orthogonalClass
  have h0 := P.trace_closed ((selPair P.pairing).P 1 1 2 rfl y P.orthogonalClass)
  rw [h] at h0
  change P.trace ((selPair P.pairing).P 2 1 3 rfl
    ((selCx (galoisSelData K S A M Delta)).d 1 2 rfl y) P.orthogonalClass) = 0
  simpa only [P.orthogonal_closed, map_zero, smul_zero, add_zero] using h0

/-- Generic nondegeneracy detects the transported actual class. Its paired
functional is nonzero on actual degree-two cycles; no coordinate-nonvanishing
hypothesis is used. -/
theorem RetainedIntegralPairing.functional_nonzero_on_cycles [IsDomain A]
    (P : RetainedIntegralPairing K S A M N Delta z)
    (R : GenuineTwoTermRealization K S A M Delta)
    (hz : (selCx (galoisSelData K S A M Delta)).d 1 2 rfl z = 0)
    (hnb : ∀ y : (selCx (galoisSelData K S A M Delta)).X 0,
      (selCx (galoisSelData K S A M Delta)).d 0 1 rfl y ≠ z) :
    ∃ w : (selCx (galoisSelData K S A M Delta)).X 2,
      (selCx (galoisSelData K S A M Delta)).d 2 3 rfl w = 0 ∧ P.functional w ≠ 0 := by
  by_contra h
  push Not at h
  have hkill : ∀ w : (selCx (galoisSelData K S A M Delta)).X 2,
      (selCx (galoisSelData K S A M Delta)).d 2 3 rfl w = 0 →
        traceComp (selPair P.pairing) P.trace 2 1 rfl w P.orthogonalClass = 0 := h
  obtain ⟨a, ha, b, hb⟩ := P.generic_nondegenerate P.orthogonalClass P.orthogonal_closed hkill
  let C := selCx (galoisSelData K S A M Delta)
  let Ct := selCx (galoisSelData K S A N P.conjugateConditions)
  let y := P.comparison.f 0 0 rfl b - a • P.boundary
  have hy : Ct.d 0 1 rfl y = a • P.conjugation.f 1 1 rfl z := by
    dsimp only [y]
    rw [map_sub, map_smul, ← P.comparison.comm 0 1 0 1 rfl rfl rfl rfl,
      hb, map_smul, P.lift_image, smul_add]
    abel
  have hc : (coneCx P.conjugation).d 1 2 rfl
      ((a • z, y) : (coneCx P.conjugation).X 1) = 0 := by
    change (C.d 1 2 rfl (a • z), P.conjugation.f 1 1 rfl (a • z) - Ct.d 0 1 rfl y) = 0
    rw [map_smul, hz, smul_zero, map_smul, hy, sub_self]
    rfl
  obtain ⟨⟨x, t⟩, hxt⟩ := (coneCx_acyclic_of_quasiIso
    P.conjugation P.conjugation_quasiIso) 0 1 2 rfl rfl _ hc
  have hx := congrArg Prod.fst hxt
  change C.d 0 1 rfl x = a • z at hx
  exact genuineClass_not_torsion_boundary K S A M Delta R z hz hnb a ha x hx

end PairedRepresentative

section GenuineStages

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (A : Type) [CommRing A] [IsLocalRing A]
  (M N : Type) [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul A M]
  [ContinuousSMul (GKS K S) M]
  [AddCommGroup N] [Module A N]
  [DistribMulAction (GKS K S) N] [SMulCommClass (GKS K S) A N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul A N]
  [ContinuousSMul (GKS K S) N]
  {F : Type} [Field F] (ι : A →+* F)

/-- Genuine integral configuration data. The minimal model is constructed
from the bounded presentation. The class is a specified actual nonboundary,
and the functional is constructed from its retained orthogonal lift. Neither
a primitive vector, a regular coordinate, nor a switching process is an input. -/
structure GenuineStageData where
  conditions : GaloisLocalConditions K S A M
  presentation : GenuinePresentation K S A M conditions
  actualClass : (selCx (galoisSelData K S A M conditions)).X 1
  class_closed : (selCx (galoisSelData K S A M conditions)).d 1 2 rfl actualClass = 0
  class_nonboundary : ∀ y : (selCx (galoisSelData K S A M conditions)).X 0,
    (selCx (galoisSelData K S A M conditions)).d 0 1 rfl y ≠ actualClass
  paired : RetainedIntegralPairing K S A M N conditions actualClass
  generic_det : (presentation.realization.matrix.map ι).det = 0
  generic_adj : (presentation.realization.matrix.map ι).adjugate ≠ 0

variable {K S A M N ι}

/-- The genuine stage, retaining the actual class and its actual paired
representative in the minimal realization. -/
def GenuineStageData.stage (G : GenuineStageData K S A M N ι) : TwoTermStage ι :=
  genuineStage K S A M ι G.conditions G.presentation.realization
    G.actualClass G.class_closed G.paired.functional G.paired.functional_closed
    G.generic_det G.generic_adj

/-- The stage still represents the specified actual class, with its original
boundary witness; the primitive kernel vector is not substituted for it. -/
theorem GenuineStageData.retains_class (G : GenuineStageData K S A M N ι) :
    G.presentation.realization.f.f 1 1 rfl
      (G.presentation.realization.b1.equivFun.symm G.stage.z) =
      G.actualClass + (selCx (galoisSelData K S A M G.conditions)).d 0 1 rfl
        (G.presentation.realization.boundaryWitness G.actualClass G.class_closed) :=
  stageOfRealization_class G.presentation.realization ι G.actualClass G.class_closed
    G.paired.functional G.paired.functional_closed G.generic_det G.generic_adj

/-- The stage row evaluates the paired functional of the same actual class,
not a functional attached to the chosen primitive vector. -/
theorem GenuineStageData.retains_functional (G : GenuineStageData K S A M N ι)
    (x : Fin (G.stage.n + 1) → A) :
    G.stage.w ⬝ᵥ x = G.paired.functional
      (G.presentation.realization.f.f 2 2 rfl
        (G.presentation.realization.b2.equivFun.symm x)) :=
  stageOfRealization_functional G.presentation.realization ι G.actualClass G.class_closed
    G.paired.functional G.paired.functional_closed G.generic_det G.generic_adj x

/-- The nonzero genuine class and the retained pairing force a nonzero generic
coordinate. This is proved from actual cycles, not included as a stage field. -/
theorem GenuineStageData.coord_ne_zero [IsDomain A]
    (G : GenuineStageData K S A M N ι) (hι : Function.Injective ι) : G.stage.u ≠ 0 :=
  stageOfRealization_ne_zero G.presentation.realization ι hι G.actualClass G.class_closed
    G.paired.functional G.paired.functional_closed G.generic_det G.generic_adj
    G.class_nonboundary
    (G.paired.functional_nonzero_on_cycles G.presentation.realization
      G.class_closed G.class_nonboundary)

/-- Minimality identifies the computed residue-fibre dimension with the rank
obtained from the genuine bounded presentation. -/
theorem GenuineStageData.fiberDim_eq {k : Type} [Field k]
    (G : GenuineStageData K S A M N ι) (ρ : A →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) :
    G.stage.fiberDim ρ = G.presentation.n + 1 := by
  have hD : G.stage.D.map ρ = 0 := G.presentation.matrix_residue_zero ρ hρ
  have hd : (G.stage.D.map ρ).mulVecLin = 0 := by
    apply LinearMap.ext
    intro x
    rw [mulVecLin_apply, hD, zero_mulVec]
    rfl
  rw [TwoTermStage.fiberDim, hd, LinearMap.ker_zero,
    finrank_top, finrank_fin_fun]
  exact congrArg (fun n => n + 1) G.presentation.realization_spec.1

/-- The computed fibre dimension is the degree-one residual cohomology
of the bounded presentation of the specified continuous-cochain cone. -/
theorem GenuineStageData.fiberDim_residualHomology (G : GenuineStageData K S A M N ι) :
    G.stage.fiberDim (IsLocalRing.residue A) =
      Module.finrank (IsLocalRing.ResidueField A)
        ((ZInQ.Contrib.CloudB3RC53.ResidualTransfer.resCx G.presentation.complex).homology 1) := by
  rw [G.fiberDim_eq (IsLocalRing.residue A)
    (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx), G.presentation.residual 1]
  simp

/-- A genuine minimal stage with residual rank one has an integral coordinate
without any switch hypothesis. This is the actual terminal case. -/
theorem GenuineStageData.terminal_regular {k : Type} [Field k]
    (G : GenuineStageData K S A M N ι) (hι : Function.Injective ι) (ρ : A →+* k)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (hn : G.presentation.n = 0) :
    ∃ a : A, ι a = G.stage.u := by
  apply TwoTermStage.coord_integral_of_fiberDim_one hι ρ hρ G.stage
  rw [G.fiberDim_eq ρ hρ, hn]

/-- An integral localization on the specified actual degree-one cycles,
killing actual boundaries. Its matrix is derived in the retained realization;
it is not an independent vector attached to an abstract stage. -/
structure GenuineLocalization (G : GenuineStageData K S A M N ι) where
  onCochains : (selCx (galoisSelData K S A M G.conditions)).X 1 →ₗ[A] (Fin 2 → A)
  kills_boundaries : ∀ y,
    onCochains ((selCx (galoisSelData K S A M G.conditions)).d 0 1 rfl y) = 0

variable {G : GenuineStageData K S A M N ι}

/-- Express the specified actual localization in the retained degree-one basis. -/
def GenuineLocalization.vectorMap (L : GenuineLocalization G) :
    (Fin (G.stage.n + 1) → A) →ₗ[A] (Fin 2 → A) :=
  L.onCochains ∘ₗ G.presentation.realization.f.f 1 1 rfl ∘ₗ
    G.presentation.realization.b1.equivFun.symm.toLinearMap

def GenuineLocalization.matrix (L : GenuineLocalization G) :
    Matrix (Fin 2) (Fin (G.stage.n + 1)) A := LinearMap.toMatrix' L.vectorMap

def GenuineLocalization.genericVector (L : GenuineLocalization G) : Fin 2 → F :=
  fun i => ι (L.onCochains G.actualClass i)

/-- The localization matrix is the matrix of the actual cochain map. -/
theorem GenuineLocalization.matrix_mulVec (L : GenuineLocalization G)
    (x : Fin (G.stage.n + 1) → A) : L.matrix *ᵥ x = L.vectorMap x := by
  change Matrix.toLin' (LinearMap.toMatrix' L.vectorMap) x = _
  rw [Matrix.toLin'_toMatrix']

/-- The retained stage vector has exactly the localization of the specified
actual class, since its retained error is an actual boundary. -/
theorem GenuineLocalization.class_identity (L : GenuineLocalization G) :
    L.matrix *ᵥ G.stage.z = L.onCochains G.actualClass := by
  rw [L.matrix_mulVec]
  change L.onCochains (G.presentation.realization.f.f 1 1 rfl
    (G.presentation.realization.b1.equivFun.symm G.stage.z)) = _
  rw [G.retains_class, map_add, L.kills_boundaries, add_zero]

/-- The conjugation involution on the computed residual degree-one cohomology
of the genuine stage. Its identification with arithmetic conjugation remains
part of the supplied local and coefficient comparisons. -/
structure GenuineSigns {k : Type} [Field k]
    (G : GenuineStageData K S A M N ι) (ρ : A →+* k) where
  tau : (LinearMap.ker (G.stage.D.map ρ).mulVecLin) →ₗ[k]
    (LinearMap.ker (G.stage.D.map ρ).mulVecLin)
  involutive : Function.Involutive tau
  two_ne_zero : (2 : k) ≠ 0

variable {k : Type} [Field k] {ρ : A →+* k}

/-- The positive cohomology eigenspace of the specified involution. -/
def GenuineSigns.plus (X : GenuineSigns G ρ) := LinearMap.ker (X.tau - LinearMap.id)

/-- The negative cohomology eigenspace of the specified involution. -/
def GenuineSigns.minus (X : GenuineSigns G ρ) := LinearMap.ker (X.tau + LinearMap.id)

/-- The cohomology signs are complementary because two is invertible.
No sign-dimension equality is assumed. -/
theorem GenuineSigns.isCompl (X : GenuineSigns G ρ) : IsCompl X.plus X.minus := by
  unfold GenuineSigns.plus GenuineSigns.minus
  constructor
  · rw [Submodule.disjoint_def]
    intro v hp hm
    rw [LinearMap.mem_ker] at hp hm
    change X.tau v - v = 0 at hp
    change X.tau v + v = 0 at hm
    rw [sub_eq_zero] at hp
    rw [hp, ← two_smul k v] at hm
    exact (smul_eq_zero.mp hm).resolve_left X.two_ne_zero
  · rw [codisjoint_iff]
    apply top_unique
    intro v _
    apply Submodule.mem_sup.mpr
    refine ⟨(2 : k)⁻¹ • (v + X.tau v), ?_, (2 : k)⁻¹ • (v - X.tau v), ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      change X.tau ((2 : k)⁻¹ • (v + X.tau v)) - (2 : k)⁻¹ • (v + X.tau v) = 0
      rw [map_smul, map_add, X.involutive v]
      module
    · rw [LinearMap.mem_ker]
      change X.tau ((2 : k)⁻¹ • (v - X.tau v)) + (2 : k)⁻¹ • (v - X.tau v) = 0
      rw [map_smul, map_sub, X.involutive v]
      module
    · rw [← smul_add]
      have he : (v + X.tau v) + (v - X.tau v) = (2 : k) • v := by module
      rw [he, smul_smul, inv_mul_cancel₀ X.two_ne_zero, one_smul]

/-- The sign dimensions sum to the computed genuine residue-fibre dimension. -/
theorem GenuineSigns.sign_sum (X : GenuineSigns G ρ) :
    finrank k X.plus + finrank k X.minus = G.stage.fiberDim ρ :=
  Submodule.finrank_add_eq_of_isCompl X.isCompl

end GenuineStages

section DVRStages

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {A : Type} [CommRing A]
  [IsDomain A] [IsDiscreteValuationRing A]
  {M N : Type} [AddCommGroup M] [Module A M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) A M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul A M]
  [ContinuousSMul (GKS K S) M]
  [AddCommGroup N] [Module A N]
  [DistribMulAction (GKS K S) N] [SMulCommClass (GKS K S) A N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul A N]
  [ContinuousSMul (GKS K S) N]
  {F k : Type} [Field F] [Field k] {ι : A →+* F}

/-- Supply the primitive-kernel witness by saturation of the genuine model's
kernel, applied to its retained actual class. -/
def GenuineStageData.primitiveKernel (G : GenuineStageData K S A M N ι)
    (hι : Function.Injective ι) (ρ : A →+* k) : PrimitiveKernelVector G.stage ρ :=
  (genuineStage_primitiveKernel K S A M G.conditions ι hι ρ G.presentation.realization
    G.actualClass G.class_closed G.paired.functional G.paired.functional_closed
    G.generic_det G.generic_adj G.class_nonboundary).some

/-- Residue-field detection of the chosen primitive kernel vector implies
nonzero generic localization of the same actual Selmer class. -/
theorem GenuineLocalization.detects_actual {G : GenuineStageData K S A M N ι}
    (L : GenuineLocalization G) (hι : Function.Injective ι) (ρ : A →+* k)
    (hL : L.matrix.map ρ *ᵥ
      (fun i => ρ ((G.primitiveKernel hι ρ).v i)) ≠ 0) : L.genericVector ≠ 0 := by
  have h := localization_ne_zero_of_primitiveKernel hι (G.primitiveKernel hι ρ) L.matrix hL
  have he : L.matrix.map ι *ᵥ (fun i => ι (G.stage.z i)) = L.genericVector := by
    ext i
    change (L.matrix.map ι *ᵥ (ι ∘ G.stage.z)) i = ι (L.onCochains G.actualClass i)
    rw [← RingHom.map_mulVec, L.class_identity]
  rw [he] at h
  exact h

/-- The actual-class determinant comparison of one specified genuine switch.
The local vector is the localization of the retained actual class. Detection
is on its separately constructed primitive kernel vector. The common strict
factor and its two unit normalizations are retained, including all torsion.
These geometric comparisons are inputs; no integral coordinate or coordinate
relation is assumed. -/
structure GenuineSwitchComparison (hι : Function.Injective ι) (ρ : A →+* k)
    (G G' : GenuineStageData K S A M N ι) where
  epsilon : F
  epsilon_ne_zero : epsilon ≠ 0
  sigma : F
  sigma_sq : sigma * sigma = 1
  J : Matrix (Fin 2) (Fin 2) F
  J_sq : J * J = 1
  J_det : J.det = -1
  localization : GenuineLocalization G
  detects_primitive : localization.matrix.map ρ *ᵥ
    (fun i => ρ ((G.primitiveKernel hι ρ).v i)) ≠ 0
  oldMap : StageMap G.stage (oldMat epsilon localization.genericVector)
    localization.genericVector (Pi.single 0 1)
  newMap : StageMap G'.stage (newMat epsilon sigma J localization.genericVector)
    (J *ᵥ localization.genericVector) (Pi.single 1 1)
  strictFactor : F
  oldUnit : Aˣ
  newUnit : Aˣ
  old_factor : normalizedConeTorsion oldMap
    (oldMat_hz epsilon localization.genericVector)
    (oldMat_hl epsilon localization.genericVector) = strictFactor * ι oldUnit
  new_factor : normalizedConeTorsion newMap
    (newMat_hz epsilon sigma J localization.genericVector)
    (newMat_hl epsilon sigma J localization.genericVector) = strictFactor * ι newUnit

variable {hι : Function.Injective ι} {ρ : A →+* k}
  {G G' : GenuineStageData K S A M N ι}

/-- The common strict determinant factor gives the existing coordinate-step
consumer for the two specified genuine stages. Nonzero localizations and
coordinates are derived from their actual classes and paired representatives. -/
def GenuineSwitchComparison.toCoordStep (C : GenuineSwitchComparison hι ρ G G') :
    CoordStep ι G.stage.u G'.stage.u :=
  coordStep_of_commonFactor C.oldMap C.newMap C.epsilon_ne_zero C.sigma_sq C.J_sq C.J_det
    (C.localization.detects_actual hι ρ C.detects_primitive)
    (G.coord_ne_zero hι) G.generic_adj (G'.coord_ne_zero hι) G'.generic_adj
    C.strictFactor C.oldUnit C.newUnit C.old_factor C.new_factor

/-- The individual old comparison is unit-valued exactly when the retained
common strict factor is unit-valued. Commonality is not replaced by a unit
assumption. -/
theorem GenuineSwitchComparison.oldIntegralUnit_iff
    (C : GenuineSwitchComparison hι ρ G G') :
    C.oldMap.IntegralUnit
        (oldMat_hz C.epsilon C.localization.genericVector)
        (oldMat_hl C.epsilon C.localization.genericVector) ↔
      ∃ c : Aˣ, C.strictFactor = ι c := by
  rw [integralUnit_iff_normalized]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u * C.oldUnit⁻¹, ?_⟩
    calc
      C.strictFactor =
          (C.strictFactor * ι (C.oldUnit : A)) * ι ((C.oldUnit⁻¹ : Aˣ) : A) := by
        rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
      _ = ι (u : A) * ι ((C.oldUnit⁻¹ : Aˣ) : A) := by rw [← C.old_factor, hu]
      _ = ι ((u * C.oldUnit⁻¹ : Aˣ) : A) := by rw [Units.val_mul, map_mul]
  · rintro ⟨c, hc⟩
    refine ⟨c * C.oldUnit, ?_⟩
    rw [C.old_factor, hc, Units.val_mul, map_mul]

/-- The literal two individual integral-unit comparisons require precisely
the extra unit-valued strict-factor certificate. The regularity construction
uses only the common-factor comparison and does not assert this stronger
certificate. -/
theorem GenuineSwitchComparison.stageConeComparison_iff
    (C : GenuineSwitchComparison hι ρ G G') :
    StageConeComparison G.stage G'.stage C.epsilon C.sigma C.J C.localization.genericVector ↔
      ∃ c : Aˣ, C.strictFactor = ι c := by
  constructor
  · intro H
    have hv := C.localization.detects_actual hι ρ C.detects_primitive
    have hlink := stageModelLink_old C.epsilon_ne_zero hv
      (G.coord_ne_zero hι) G.generic_adj H.1
    have hu := (stageModelLink_iff C.oldMap
      (oldMat_hz C.epsilon C.localization.genericVector)
      (oldMat_hl C.epsilon C.localization.genericVector)
      (G.coord_ne_zero hι) G.generic_adj
      (oldMat_coord C.epsilon_ne_zero C.localization.genericVector)
      (neg_ne_zero.mpr (inv_ne_zero C.epsilon_ne_zero))
      (oldMat_adjugate_ne_zero C.epsilon_ne_zero hv)).1 hlink
    exact C.oldIntegralUnit_iff.1 hu
  · intro H
    refine ⟨⟨C.oldMap, C.oldIntegralUnit_iff.2 H⟩, C.newMap, ?_⟩
    apply (integralUnit_iff_normalized C.newMap _ _).2
    obtain ⟨c, hc⟩ := H
    refine ⟨c * C.newUnit, ?_⟩
    rw [C.new_factor, hc, Units.val_mul, map_mul]

/-- The quadratic character condition and its genuine cohomology involutions.
The two dimensions are computed from eigenspaces, not supplied as numbers. -/
structure GenuineSignFamily {I : Type} (ρ : A →+* k)
    (family : I → GenuineStageData K S A M N ι) where
  quadratic : Prop
  involutions : quadratic → ∀ i, GenuineSigns (family i) ρ

variable {I : Type} {family : I → GenuineStageData K S A M N ι}

/-- The positive cohomology dimension at a quadratic specialization. -/
def GenuineSignFamily.sp (T : GenuineSignFamily ρ family) (i : I) : ℕ := by
  classical
  exact if hq : T.quadratic then finrank k (T.involutions hq i).plus else 0

/-- The negative cohomology dimension at a quadratic specialization. -/
def GenuineSignFamily.sm (T : GenuineSignFamily ρ family) (i : I) : ℕ := by
  classical
  exact if hq : T.quadratic then finrank k (T.involutions hq i).minus else 0

/-- The sign-sum field follows from the genuine cohomology involutions. -/
theorem GenuineSignFamily.sign_sum (T : GenuineSignFamily ρ family) (hq : T.quadratic) (i : I) :
    T.sp i + T.sm i = (family i).stage.fiberDim ρ := by
  classical
  simpa only [GenuineSignFamily.sp, GenuineSignFamily.sm, dite_eq_left hq] using
    (T.involutions hq i).sign_sum

/-- Explicit successors and local-image geometry for a family of specified
genuine configurations. A successor comes with its actual-class determinant
comparison and the geometric dimension witnesses. There are no free
existential coordinates, no dimension-drop assumptions, and no regularity
or primitive-vector fields in these inputs. -/
structure GenuineSwitchSystem (hι : Function.Injective ι) (ρ : A →+* k)
    (family : I → GenuineStageData K S A M N ι) where
  signs : GenuineSignFamily ρ family
  mixedNext : ∀ i,
    (¬ signs.quadratic ∨ (0 < signs.sp i ∧ 0 < signs.sm i)) →
    1 < (family i).stage.fiberDim ρ → I
  mixedComparison : ∀ i hm hd,
    GenuineSwitchComparison hι ρ (family i) (family (mixedNext i hm hd))
  mixedQuadratic : ∀ i hm hd, signs.quadratic →
    QuadMixedDims (k := k) (signs.sp i) (signs.sm i)
      (signs.sp (mixedNext i hm hd)) (signs.sm (mixedNext i hm hd))
  mixedNonquadratic : ∀ i hm hd, ¬ signs.quadratic →
    NonquadDims (k := k) ((family i).stage.fiberDim ρ)
      ((family (mixedNext i hm hd)).stage.fiberDim ρ)
  singleNext : ∀ i, signs.quadratic → ¬ (0 < signs.sp i ∧ 0 < signs.sm i) →
    1 < (family i).stage.fiberDim ρ → I
  singleComparison : ∀ i hq hn hd,
    GenuineSwitchComparison hι ρ (family i) (family (singleNext i hq hn hd))
  singleDimensions : ∀ i hq hn hd,
    QuadSingleDims (k := k) ((family i).stage.fiberDim ρ)
        (signs.sp (singleNext i hq hn hd)) (signs.sm (singleNext i hq hn hd)) ⊕
      QuadSingleDims (k := k) ((family i).stage.fiberDim ρ)
        (signs.sm (singleNext i hq hn hd)) (signs.sp (singleNext i hq hn hd))

/-- Construct all height-one switching fields for the specified genuine
family. The primitive-kernel field is supplied by saturation of the retained
actual class. Coordinate steps retain the common strict torsion factor. -/
def GenuineSwitchSystem.toData (X : GenuineSwitchSystem hι ρ family) :
    HeightOneSwitchDataPK ι ρ where
  Stage := I
  stage i := (family i).stage
  quadratic := X.signs.quadratic
  sp := X.signs.sp
  sm := X.signs.sm
  sign_sum := X.signs.sign_sum
  primitiveKernel i := ⟨(family i).primitiveKernel hι ρ⟩
  switch_mixed i hm hd :=
    ⟨X.mixedNext i hm hd, ⟨(X.mixedComparison i hm hd).toCoordStep⟩,
      (fun hq => ⟨X.mixedQuadratic i hm hd hq⟩),
      (fun hn => ⟨X.mixedNonquadratic i hm hd hn⟩)⟩
  switch_single := by
    intro i hq hn hd
    let j := X.singleNext i hq hn hd
    let C := X.singleComparison i hq hn hd
    rcases X.singleDimensions i hq hn hd with Q | Q
    · exact ⟨j, X.signs.sp j, X.signs.sm j, ⟨C.toCoordStep⟩, ⟨Q⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨j, X.signs.sm j, X.signs.sp j, ⟨C.toCoordStep⟩, ⟨Q⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- Every coordinate of the specified genuine family is integral once its
actual switch comparisons and local-image geometry have been supplied. The
conclusion is about the constructed genuine stages, not arbitrary process
coordinates. -/
theorem GenuineSwitchSystem.regular (X : GenuineSwitchSystem hι ρ family)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (i : I) :
    ∃ a : A, ι a = (family i).stage.u :=
  regular_of_switchDataPK hι hρ X.toData i

end DVRStages

/-- Every height-one localization of the genuine Iwasawa algebra is a DVR.
The proof uses the proved factorization of height-one primes and the standard
local-ring criterion with principal maximal ideal. -/
theorem lambdaAtPrime_dvr (P : Ideal Lambda) [P.IsPrime] (hp : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  obtain ⟨p, _, hP⟩ := (height_eq_one_iff_exists_prime P).1 hp
  have : P.IsPrincipal := by
    rw [hP]
    infer_instance
  have hm : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    infer_instance
  have hnf := IsLocalization.AtPrime.not_isField Lambda
    (Ideal.ne_bot_of_height_eq_one hp) (Localization.AtPrime P)
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 1 5).mpr hm

section HeightOnePrime

variable (P : Ideal Lambda) [P.IsPrime] (hp : P.height = 1)
  {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {M N : Type} [AddCommGroup M] [Module (Localization.AtPrime P) M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (Localization.AtPrime P) M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul (Localization.AtPrime P) M]
  [ContinuousSMul (GKS K S) M]
  [AddCommGroup N] [Module (Localization.AtPrime P) N]
  [DistribMulAction (GKS K S) N] [SMulCommClass (GKS K S) (Localization.AtPrime P) N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul (Localization.AtPrime P) N]
  [ContinuousSMul (GKS K S) N]
  {I : Type}
  (family : I → GenuineStageData K S (Localization.AtPrime P) M N (toFracAt P))

/-- Height-one regularity for the specified genuine stages over the actual
localization of the Iwasawa algebra. The DVR instance is proved, rather than
supplied as an arithmetic hypothesis. -/
theorem regularAtPrime_of_genuineSwitches
    (X : letI : IsDiscreteValuationRing (Localization.AtPrime P) := lambdaAtPrime_dvr P hp
      GenuineSwitchSystem (toFracAt_injective P)
        (IsLocalRing.residue (Localization.AtPrime P)) family)
    (i : I) : RegularAtPrime P (family i).stage.u := by
  let : IsDiscreteValuationRing (Localization.AtPrime P) := lambdaAtPrime_dvr P hp
  obtain ⟨a, ha⟩ := X.regular (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx) i
  exact ⟨a, ha⟩

/-- Supply the existing process consumer with the actual coordinate of a
specified genuine starting stage. No free starting coordinate or process
existence assumption is used. -/
theorem exists_process_of_genuineSwitches
    (X : letI : IsDiscreteValuationRing (Localization.AtPrime P) := lambdaAtPrime_dvr P hp
      GenuineSwitchSystem (toFracAt_injective P)
        (IsLocalRing.residue (Localization.AtPrime P)) family)
    (i : I) :
    ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (i₀ : Pr.Stage),
      Pr.coord i₀ = (family i).stage.u := by
  let : IsDiscreteValuationRing (Localization.AtPrime P) := lambdaAtPrime_dvr P hp
  exact exists_process_of_switchDataPK P (family i).stage.u X.toData i rfl

end HeightOnePrime

end ZInQ.Contrib.RC53Assist.StagePrimitive
