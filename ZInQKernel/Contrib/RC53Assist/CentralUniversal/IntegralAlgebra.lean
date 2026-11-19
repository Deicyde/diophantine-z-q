import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Integral and divisible coordinates of a finitely generated two-adic module

The coordinates in this file come from a basis of the quotient by torsion.
The same basis supplies both rational coordinates and coordinates after tensoring
with the divisible module. Torsion is killed by tensoring with either coefficient
module; no finiteness of a Tate--Shafarevich group is used.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Manuscript.RC53Assist.CentralUniversal

open ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC.BaseZeroLimit
open scoped TensorProduct

/-- The integral lattice in the field of two-adic numbers. -/
def integralLattice : Submodule ℤ_[2] ℚ_[2] where
  carrier := (PadicInt.subring 2).carrier
  zero_mem' := (PadicInt.subring 2).zero_mem
  add_mem' := (PadicInt.subring 2).add_mem
  smul_mem' a x hx := by
    change ‖(a : ℚ_[2]) * x‖ ≤ 1
    exact norm_mul_le_one a.2 hx

/-- The divisible quotient carries its natural two-adic integral scalar action. -/
instance q2z2Module : Module ℤ_[2] Q2Z2 :=
  inferInstanceAs (Module ℤ_[2] (ℚ_[2] ⧸ integralLattice))

/-- The quotient of the field by its integral lattice. -/
def divisibleQuotient : ℚ_[2] →ₗ[ℤ_[2]] Q2Z2 := integralLattice.mkQ

/-- The scalar inclusion, regarded as a linear map. -/
def integralInclusion : ℤ_[2] →ₗ[ℤ_[2]] ℚ_[2] := Algebra.linearMap ℤ_[2] ℚ_[2]

/-- The coefficient sequence is exact. -/
theorem coefficient_exact : Function.Exact integralInclusion divisibleQuotient := by
  intro x
  constructor
  · intro hx
    have hx' : ‖x‖ ≤ 1 := (mk_eq_zero_iff x).mp hx
    exact ⟨Padic.lift x hx', PadicInt.coe_lift hx'⟩
  · rintro ⟨a, rfl⟩
    exact (mk_eq_zero_iff (a : ℚ_[2])).mpr a.2

/-- The quotient map is surjective. -/
theorem divisibleQuotient_surjective : Function.Surjective divisibleQuotient :=
  Submodule.mkQ_surjective integralLattice

/-- Multiplication by a nonzero integral scalar is surjective on the divisible quotient. -/
theorem divisible_smul_surjective (a : ℤ_[2]) (ha : a ≠ 0) :
    Function.Surjective (fun d : Q2Z2 => a • d) := by
  intro d
  obtain ⟨q, rfl⟩ := divisibleQuotient_surjective d
  refine ⟨divisibleQuotient (q / (a : ℚ_[2])), ?_⟩
  change a • divisibleQuotient (q / (a : ℚ_[2])) = divisibleQuotient q
  rw [← divisibleQuotient.map_smul]
  change divisibleQuotient ((a : ℚ_[2]) * (q / (a : ℚ_[2]))) = divisibleQuotient q
  rw [mul_div_cancel₀ q (PadicInt.coe_ne_zero.mpr ha)]

section Modules

variable (M : Type) [AddCommGroup M] [Module ℤ_[2] M]

/-- Rationalization of an integral module. -/
def rationalUnit : M →ₗ[ℤ_[2]] ℚ_[2] ⊗[ℤ_[2]] M :=
  TensorProduct.mk ℤ_[2] ℚ_[2] M 1

/-- Rationalization is localization at the nonzero integral scalars. -/
instance rationalUnit_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ_[2]) (rationalUnit M) := by
  unfold rationalUnit
  infer_instance

/-- Rationalization kills exactly the torsion submodule. -/
theorem rationalUnit_ker : LinearMap.ker (rationalUnit M) = Submodule.torsion ℤ_[2] M := by
  ext x
  exact IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[2]) (rationalUnit M)

/-- The free quotient of the integral module. -/
abbrev FreePart := M ⧸ Submodule.torsion ℤ_[2] M

/-- Pure rational tensors with an integral torsion element vanish. -/
theorem rational_tmul_torsion (q : ℚ_[2]) (x : M) (hx : x ∈ Submodule.torsion ℤ_[2] M) :
    q ⊗ₜ[ℤ_[2]] x = 0 := by
  obtain ⟨a, ha⟩ := hx
  change a.1 • x = 0 at ha
  have hae : a.1 • (q / (a.1 : ℚ_[2])) = q := by
    change (a.1 : ℚ_[2]) * (q / (a.1 : ℚ_[2])) = q
    exact mul_div_cancel₀ q (PadicInt.coe_ne_zero.mpr (nonZeroDivisors.coe_ne_zero a))
  rw [← hae, TensorProduct.smul_tmul, ha, TensorProduct.tmul_zero]

/-- Pure divisible tensors with an integral torsion element vanish. -/
theorem divisible_tmul_torsion (d : Q2Z2) (x : M) (hx : x ∈ Submodule.torsion ℤ_[2] M) :
    d ⊗ₜ[ℤ_[2]] x = 0 := by
  obtain ⟨a, ha⟩ := hx
  change a.1 • x = 0 at ha
  obtain ⟨e, he⟩ := divisible_smul_surjective a.1
    (nonZeroDivisors.coe_ne_zero a) d
  change a.1 • e = d at he
  rw [← he, TensorProduct.smul_tmul, ha, TensorProduct.tmul_zero]

/-- Tensoring the torsion quotient with rational coefficients is bijective. -/
theorem rational_freePart_bijective : Function.Bijective
    ((Submodule.torsion ℤ_[2] M).mkQ.baseChange ℚ_[2]) := by
  constructor
  · change Function.Injective ((Submodule.torsion ℤ_[2] M).mkQ.lTensor ℚ_[2])
    rw [← LinearMap.ker_eq_bot, lTensor_mkQ]
    apply LinearMap.range_eq_bot.mpr
    ext q x
    exact rational_tmul_torsion M q x.1 x.2
  · exact LinearMap.baseChange_surjective ℚ_[2] (Submodule.mkQ_surjective _)

/-- Tensoring the torsion quotient with divisible coefficients is bijective. -/
theorem divisible_freePart_bijective : Function.Bijective
    ((Submodule.torsion ℤ_[2] M).mkQ.lTensor Q2Z2) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, lTensor_mkQ]
    apply LinearMap.range_eq_bot.mpr
    ext d x
    exact divisible_tmul_torsion M d x.1 x.2
  · exact LinearMap.lTensor_surjective Q2Z2 (Submodule.mkQ_surjective _)

/-- The rationalized torsion quotient, induced by the actual quotient map. -/
def rationalFreePartEquiv :
    ℚ_[2] ⊗[ℤ_[2]] M ≃ₗ[ℚ_[2]] ℚ_[2] ⊗[ℤ_[2]] FreePart M :=
  LinearEquiv.ofBijective _ (rational_freePart_bijective M)

/-- The divisible tensor of the torsion quotient, induced by the actual quotient map. -/
def divisibleFreePartEquiv :
    Q2Z2 ⊗[ℤ_[2]] M ≃ₗ[ℤ_[2]] Q2Z2 ⊗[ℤ_[2]] FreePart M :=
  LinearEquiv.ofBijective _ (divisible_freePart_bijective M)

/-- Tensoring the coefficient inclusion has precisely the integral lattice as its image. -/
theorem coefficientTensor_range :
    LinearMap.range (integralInclusion.rTensor M) = LinearMap.range (rationalUnit M) := by
  have hmap : integralInclusion.rTensor M =
      (rationalUnit M).comp (TensorProduct.lid ℤ_[2] M).toLinearMap := by
    apply TensorProduct.ext'
    intro a x
    change (a : ℚ_[2]) ⊗ₜ[ℤ_[2]] x = (1 : ℚ_[2]) ⊗ₜ[ℤ_[2]] (a • x)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp [Algebra.smul_def]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨TensorProduct.lid ℤ_[2] M t, (LinearMap.congr_fun hmap t).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(TensorProduct.lid ℤ_[2] M).symm x, ?_⟩
    rw [hmap]
    simp

/-- The quotient of rationalization by the integral image is the divisible tensor product. -/
def tensorQuotientEquiv :
    (ℚ_[2] ⊗[ℤ_[2]] M ⧸ LinearMap.range (rationalUnit M)) ≃ₗ[ℤ_[2]]
      Q2Z2 ⊗[ℤ_[2]] M :=
  (Submodule.quotEquivOfEq _ _ (coefficientTensor_range M).symm).trans
    (rTensor.equiv M coefficient_exact divisibleQuotient_surjective)

/-- On pure tensors the quotient isomorphism is the coefficient quotient. -/
theorem tensorQuotientEquiv_mk_tmul (q : ℚ_[2]) (x : M) :
    tensorQuotientEquiv M (Submodule.Quotient.mk (q ⊗ₜ[ℤ_[2]] x)) =
      divisibleQuotient q ⊗ₜ[ℤ_[2]] x := by
  rfl

variable {N : Type} [AddCommGroup N] [Module ℤ_[2] N]

/-- A map out of rationalization killing the integral image induces a divisible-tensor map. -/
def universalTensorMap (v : ℚ_[2] ⊗[ℤ_[2]] M →ₗ[ℤ_[2]] N)
    (hv : ∀ x, v (rationalUnit M x) = 0) : Q2Z2 ⊗[ℤ_[2]] M →ₗ[ℤ_[2]] N :=
  ((LinearMap.range (rationalUnit M)).liftQ v (by
    rintro z ⟨x, rfl⟩
    exact hv x)).comp (tensorQuotientEquiv M).symm.toLinearMap

/-- The induced map is uniquely determined by the coefficient-quotient formula. -/
theorem universalTensorMap_tmul (v : ℚ_[2] ⊗[ℤ_[2]] M →ₗ[ℤ_[2]] N)
    (hv : ∀ x, v (rationalUnit M x) = 0) (q : ℚ_[2]) (x : M) :
    universalTensorMap M v hv (divisibleQuotient q ⊗ₜ[ℤ_[2]] x) = v (q ⊗ₜ[ℤ_[2]] x) := by
  rw [← tensorQuotientEquiv_mk_tmul M q x]
  simp [universalTensorMap]

/-- On rationalization classes, the induced map is the original map. -/
theorem universalTensorMap_quotient (v : ℚ_[2] ⊗[ℤ_[2]] M →ₗ[ℤ_[2]] N)
    (hv : ∀ x, v (rationalUnit M x) = 0) (z : ℚ_[2] ⊗[ℤ_[2]] M) :
    universalTensorMap M v hv (tensorQuotientEquiv M (Submodule.Quotient.mk z)) = v z := by
  simp [universalTensorMap]

/-- Exactness at rational cohomology makes the universal-coefficient map injective. -/
theorem universalTensorMap_injective (v : ℚ_[2] ⊗[ℤ_[2]] M →ₗ[ℤ_[2]] N)
    (hv : ∀ x, v (rationalUnit M x) = 0)
    (hex : LinearMap.ker v = LinearMap.range (rationalUnit M)) :
    Function.Injective (universalTensorMap M v hv) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (LinearMap.range (rationalUnit M))
    ((tensorQuotientEquiv M).symm x)
  have hvz : v z = 0 := by
    simpa [universalTensorMap, ← hz] using hx
  have hz0 : (Submodule.Quotient.mk z :
      ℚ_[2] ⊗[ℤ_[2]] M ⧸ LinearMap.range (rationalUnit M)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (hex ▸ hvz)
  apply (tensorQuotientEquiv M).symm.injective
  calc
    (tensorQuotientEquiv M).symm x = Submodule.Quotient.mk z := hz.symm
    _ = 0 := hz0
    _ = (tensorQuotientEquiv M).symm 0 := (map_zero _).symm

variable [Module.Finite ℤ_[2] M]

/-- The integral free rank, fixed by the genuine module. -/
abbrev freeRank : ℕ := Module.finrank ℤ_[2] (FreePart M)

/-- A basis of the actual integral quotient by torsion. -/
def freePartBasis : Module.Basis (Fin (freeRank M)) ℤ_[2] (FreePart M) :=
  Module.finBasis ℤ_[2] (FreePart M)

/-- Rational coordinates induced by the integral free-part basis. -/
def rationalCoordinates : ℚ_[2] ⊗[ℤ_[2]] M ≃ₗ[ℚ_[2]] (Fin (freeRank M) → ℚ_[2]) :=
  (rationalFreePartEquiv M).trans
    ((LinearEquiv.baseChange ℤ_[2] ℚ_[2] (FreePart M)
      (Fin (freeRank M) → ℤ_[2]) (freePartBasis M).equivFun).trans
      (TensorProduct.piScalarRight ℤ_[2] ℚ_[2] ℚ_[2] (Fin (freeRank M))))

/-- Divisible coordinates induced by the very same integral free-part basis. -/
def divisibleCoordinates : Q2Z2 ⊗[ℤ_[2]] M ≃ₗ[ℤ_[2]] (Fin (freeRank M) → Q2Z2) :=
  (divisibleFreePartEquiv M).trans
    ((TensorProduct.congr (LinearEquiv.refl ℤ_[2] Q2Z2) (freePartBasis M).equivFun).trans
      (TensorProduct.piScalarRight ℤ_[2] ℤ_[2] Q2Z2 (Fin (freeRank M))))

/-- Rational coordinates of a pure tensor, in the actual integral basis. -/
theorem rationalCoordinates_tmul (q : ℚ_[2]) (x : M) (i : Fin (freeRank M)) :
    rationalCoordinates M (q ⊗ₜ[ℤ_[2]] x) i =
      ((freePartBasis M).equivFun ((Submodule.torsion ℤ_[2] M).mkQ x) i : ℚ_[2]) * q := by
  rfl

/-- Divisible coordinates of a pure tensor, in that same basis. -/
theorem divisibleCoordinates_tmul (d : Q2Z2) (x : M) (i : Fin (freeRank M)) :
    divisibleCoordinates M (d ⊗ₜ[ℤ_[2]] x) i =
      (freePartBasis M).equivFun ((Submodule.torsion ℤ_[2] M).mkQ x) i • d := by
  rfl

/-- A fixed power of two kills the entire torsion of a finitely generated integral module. -/
theorem finite_torsion_two_power : ∃ n : ℕ,
    ∀ x ∈ Submodule.torsion ℤ_[2] M, (2 ^ n : ℕ) • x = 0 := by
  let T := Submodule.torsion ℤ_[2] M
  have : Module.Finite ℤ_[2] T := inferInstance
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (R := ℤ_[2]) (M := T) (Submodule.torsion_isTorsion (R := ℤ_[2]) (M := M))
  have hane : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha0
  refine ⟨a.valuation, fun x hx => ?_⟩
  have hx0 : a • x = 0 := congrArg Subtype.val
    (Submodule.mem_annihilator.mp ha (⟨x, hx⟩ : T) Submodule.mem_top)
  let u : ℤ_[2]ˣ := PadicInt.unitCoeff hane
  have hu : ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * a = (2 : ℤ_[2]) ^ a.valuation := by
    calc
      ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * a =
          ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((u : ℤ_[2]) * (2 : ℤ_[2]) ^ a.valuation) :=
        congrArg (((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ·) (PadicInt.unitCoeff_spec hane)
      _ = (2 : ℤ_[2]) ^ a.valuation := by simp [← mul_assoc]
  have hpow : (2 : ℤ_[2]) ^ a.valuation • x = 0 := by
    calc
      (2 : ℤ_[2]) ^ a.valuation • x =
          ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) • (a • x) := by rw [← mul_smul, hu]
      _ = 0 := by rw [hx0, smul_zero]
  have hnat : ((2 ^ a.valuation : ℕ) : ℤ_[2]) • x = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow
  rwa [Nat.cast_smul_eq_nsmul] at hnat

end Modules

section AdditiveTransport

open ZInQ.Manuscript.RC53Assist.CentralSelmer

variable {A B D A' B' : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
  [AddCommGroup A'] [AddCommGroup B']

/-- Exactness is transported by specified additive equivalences on the first two terms. -/
theorem exact_transport_addEquiv (f : A →+ B) (g : B →+ D)
    (eA : A' ≃+ A) (eB : B ≃+ B') (hex : Function.Exact f g) :
    Function.Exact (eB.toAddMonoidHom.comp (f.comp eA.toAddMonoidHom))
      (g.comp eB.symm.toAddMonoidHom) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hex (eB.symm y)).mp hy
    refine ⟨eA.symm x, ?_⟩
    change eB (f (eA (eA.symm x))) = y
    rw [AddEquiv.apply_symm_apply, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    change g (eB.symm y) = 0
    change eB (f (eA x)) = y at hx
    rw [← hx, AddEquiv.symm_apply_apply]
    exact (hex (f (eA x))).mpr ⟨eA x, rfl⟩

/-- A specified cokernel annihilator is preserved by those same equivalences. -/
theorem coker_transport_addEquiv (f : A →+ B) (eA : A' ≃+ A) (eB : B ≃+ B')
    (n : ℕ) (hc : ∀ y : B, ∃ x : A, f x = n • y) :
    ∀ y : B', ∃ x : A', (eB.toAddMonoidHom.comp (f.comp eA.toAddMonoidHom)) x = n • y := by
  intro y
  obtain ⟨x, hx⟩ := hc (eB.symm y)
  refine ⟨eA.symm x, ?_⟩
  change eB (f (eA (eA.symm x))) = n • y
  rw [AddEquiv.apply_symm_apply, hx, map_nsmul, AddEquiv.apply_symm_apply]

end AdditiveTransport

end ZInQ.Manuscript.RC53Assist.CentralUniversal
