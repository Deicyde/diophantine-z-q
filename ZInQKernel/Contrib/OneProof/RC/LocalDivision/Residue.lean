import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Order
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.LocallyConstant.Basic

/-! Reduction modulo the division uniformizer, and the Frobenius action
(tex 8551–8559). The coordinate proofs are provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalDivision

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic residue algebra, with generator of square `-1`. -/
abbrev ResidueQuad (p : ℕ) := QuadraticAlgebra (ZMod p) (-1) 0

/-- Coefficient reduction on scalars and on the first imaginary coordinate.
The other two coordinates disappear modulo the uniformizer. -/
noncomputable def quadReduction : IntegralD p →+* ResidueQuad p where
  toFun x := ⟨PadicInt.toZMod x.re, PadicInt.toZMod x.imI⟩
  map_zero' := by ext <;> exact map_zero PadicInt.toZMod
  map_one' := by ext; exact map_one PadicInt.toZMod; exact map_zero PadicInt.toZMod
  map_add' x y := by
    ext
    · exact map_add PadicInt.toZMod x.re y.re
    · exact map_add PadicInt.toZMod x.imI y.imI
  map_mul' x y := by
    rcases x with ⟨a,b,c,d⟩
    rcases y with ⟨e,f,g,h⟩
    rw [QuaternionAlgebra.mk_mul_mk]
    ext
    · change PadicInt.toZMod
        (a*e + (-1)*b*f + (-(p : ℤ_[p]))*c*g + 0 * (-(p : ℤ_[p]))*c*h -
          (-1) * (-(p : ℤ_[p]))*d*h) = _
      simp
    · change PadicInt.toZMod
        (a*f + b*e + 0*b*f - (-(p : ℤ_[p]))*c*h + (-(p : ℤ_[p]))*d*g) = _
      simp

theorem quadReduction_surj : Function.Surjective (quadReduction (p := p)) := by
  intro x
  obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) x.re
  obtain ⟨b, hb⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) x.im
  exact ⟨⟨a, b, 0, 0⟩, QuadraticAlgebra.ext ha hb⟩

/-- The integral element `j`. -/
noncomputable def integralJ : IntegralD p := ⟨0, 0, 1, 0⟩

theorem quadReduction_zero_iff (x : IntegralD p) :
    quadReduction x = 0 ↔ ∃ y : IntegralD p, x = integralJ * y := by
  constructor
  · intro h
    have ha : PadicInt.toZMod x.re = 0 := congrArg QuadraticAlgebra.re h
    have hb : PadicInt.toZMod x.imI = 0 := congrArg QuadraticAlgebra.im h
    obtain ⟨a, ha⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp ((padic_red_eq_zero_iff _).mp ha)
    obtain ⟨b, hb⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp ((padic_red_eq_zero_iff _).mp hb)
    refine ⟨⟨x.imJ, -x.imK, -a, b⟩, ?_⟩
    rcases x with ⟨r,s,t,u⟩
    rw [integralJ, QuaternionAlgebra.mk_mul_mk]
    apply QuaternionAlgebra.ext <;> dsimp at ha hb ⊢ <;> simp [ha, hb]
  · rintro ⟨y, rfl⟩
    rw [map_mul]
    have h : quadReduction (integralJ : IntegralD p) = 0 :=
      QuadraticAlgebra.ext (map_zero _) (map_zero _)
    rw [h, zero_mul]

private theorem padicReduction_locallyConstant :
    IsLocallyConstant (PadicInt.toZMod : ℤ_[p] → ZMod p) := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro a
  have he : (PadicInt.toZMod : ℤ_[p] → ZMod p) ⁻¹' {PadicInt.toZMod a} =
      Metric.ball a 1 := by
    ext b
    change PadicInt.toZMod b = PadicInt.toZMod a ↔ dist b a < 1
    rw [← sub_eq_zero, ← map_sub, padic_red_eq_zero_iff, dist_eq_norm]
  rw [he]
  exact Metric.isOpen_ball

variable [Fact (p % 4 = 3)]

local instance : Fact (¬ IsSquare (-1 : ZMod p)) := ⟨neg_one_nonsquare Fact.out⟩

/-- This choice fixes the coordinate of the trace-zero line in `GaloisField p 2`. -/
noncomputable def residueEquiv : ResidueQuad p ≃ₐ[ZMod p] GaloisField p 2 :=
  GaloisField.algEquivGaloisField p 2
    (by rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
      QuadraticAlgebra.finrank_eq_two])

noncomputable def red : order p →+* GaloisField p 2 :=
  residueEquiv.toRingHom.comp (quadReduction.comp orderEquiv.symm.toRingHom)

theorem red_surj : Function.Surjective (red (p := p)) :=
  residueEquiv.surjective.comp (quadReduction_surj.comp orderEquiv.symm.surjective)

theorem red_ker_maximal : (RingHom.ker (red (p := p))).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective red red_surj

/-- The first isomorphism theorem identifies the quotient by `j𝒪`. -/
noncomputable def residueQuotientEquiv :
    order p ⧸ RingHom.ker (red (p := p)) ≃+* GaloisField p 2 :=
  red.quotientKerEquivOfSurjective red_surj

noncomputable def beta : GaloisField p 2 :=
  residueEquiv (QuadraticAlgebra.omega : ResidueQuad p)

theorem red_i : red (orderEquiv (⟨0, 1, 0, 0⟩ : IntegralD p)) = beta := by
  change residueEquiv (quadReduction (orderEquiv.symm (orderEquiv _))) = _
  rw [AlgEquiv.symm_apply_apply, beta]
  exact congrArg residueEquiv (QuadraticAlgebra.ext (map_zero _) (map_one _))

theorem beta_sq : (beta : GaloisField p 2) ^ 2 = -1 := by
  rw [beta, ← map_pow, QuadraticAlgebra.omega_pow_two_eq_add]
  simp

theorem beta_ne_zero : (beta : GaloisField p 2) ≠ 0 := by
  intro h
  have := beta_sq (p := p)
  rw [h, zero_pow (by decide : 2 ≠ 0)] at this
  exact (neg_ne_zero.mpr one_ne_zero) this.symm

theorem beta_frobenius : (beta : GaloisField p 2) ^ p = -beta := by
  have h₄ : (beta : GaloisField p 2) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, beta_sq]
    simp
  have h₃ : (beta : GaloisField p 2) ^ 3 = -beta := by
    rw [show 3 = 2 + 1 by decide, pow_add, beta_sq, pow_one, neg_one_mul]
  have hp := (Fact.out : p % 4 = 3)
  calc
    (beta : GaloisField p 2) ^ p = beta ^ (4 * (p / 4) + 3) :=
      congrArg (fun n : ℕ => (beta : GaloisField p 2) ^ n) (by omega)
    _ = -beta := by rw [pow_add, pow_mul, h₄, h₃, one_pow, one_mul]

theorem red_apply (x : order p) :
    red x = algebraMap (ZMod p) (GaloisField p 2) (PadicInt.toZMod (orderEquiv.symm x).re) +
      algebraMap (ZMod p) (GaloisField p 2) (PadicInt.toZMod (orderEquiv.symm x).imI) * beta := by
  change residueEquiv (⟨_, _⟩ : ResidueQuad p) = _
  rw [QuadraticAlgebra.mk_eq_add_smul_omega, Algebra.smul_def, map_add, map_mul,
    AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

theorem red_scalar (a : ℤ_[p]) :
    red (algebraMap ℤ_[p] (order p) a) =
      algebraMap (ZMod p) (GaloisField p 2) (PadicInt.toZMod a) := by
  rw [red_apply, AlgEquiv.commutes]
  simp [QuaternionAlgebra.algebraMap_eq]

theorem red_locallyConstant : IsLocallyConstant (red (p := p)) := by
  have h := orderCoord_continuous (p := p)
  exact ((padicReduction_locallyConstant.comp_continuous h.fst).prodMk
    (padicReduction_locallyConstant.comp_continuous h.snd.fst)).comp
      (fun ab => residueEquiv (⟨ab.1, ab.2⟩ : ResidueQuad p))

theorem red_eq_zero_iff (x : order p) :
    red x = 0 ↔ PadicInt.toZMod (orderEquiv.symm x).re = 0 ∧
      PadicInt.toZMod (orderEquiv.symm x).imI = 0 := by
  change residueEquiv (⟨_, _⟩ : ResidueQuad p) = 0 ↔ _
  rw [← map_zero residueEquiv, EmbeddingLike.apply_eq_iff_eq, QuadraticAlgebra.ext_iff]
  rfl

theorem red_ker_j (x : order p) :
    red x = 0 ↔ ∃ y : order p, x = orderEquiv integralJ * y := by
  change residueEquiv (quadReduction (orderEquiv.symm x)) = 0 ↔ _
  rw [← map_zero residueEquiv, EmbeddingLike.apply_eq_iff_eq, quadReduction_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨orderEquiv y, by rw [← map_mul, ← hy, AlgEquiv.apply_symm_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨orderEquiv.symm y, by rw [map_mul, AlgEquiv.symm_apply_apply]⟩

/-- Norm modulo `p` is the sum of the squares of the first two residues. -/
theorem integralNorm_red (x : order p) :
    PadicInt.toZMod (integralNorm x) =
      PadicInt.toZMod (orderEquiv.symm x).re ^ 2 +
        PadicInt.toZMod (orderEquiv.symm x).imI ^ 2 := by
  have hz : integralNorm x =
      (orderEquiv.symm x).re ^ 2 + (orderEquiv.symm x).imI ^ 2 +
        (p : ℤ_[p]) * ((orderEquiv.symm x).imJ ^ 2 + (orderEquiv.symm x).imK ^ 2) := by
    apply Subtype.ext
    change nrd x.val = _
    rw [← includeIntegral_symm x, nrd_formula]
    rfl
  rw [hz]
  simp

theorem red_nonunit (x : order p) : red x = 0 ↔ ¬ IsUnit x := by
  rw [red_eq_zero_iff, ← residue_sum_sq_eq_zero (Fact.out : p % 4 = 3),
    ← integralNorm_red, padic_red_eq_zero_iff, orderUnit_iff_norm]
  change ‖nrd x.val‖ < 1 ↔ _
  have h := (mem_order_iff_nrd _).mp x.property
  exact ⟨ne_of_lt, lt_of_le_of_ne h⟩

theorem trace_line (x : order p) (hx : tr x.val = 0) :
    ∃ t : ZMod p, red x = algebraMap (ZMod p) (GaloisField p 2) t * beta := by
  rw [tr_apply, ← includeIntegral_symm x] at hx
  have h : ((orderEquiv.symm x).re : ℚ_[p]) = 0 :=
    (mul_eq_zero.mp hx).resolve_left (by norm_num)
  refine ⟨PadicInt.toZMod (orderEquiv.symm x).imI, ?_⟩
  rw [red_apply, PadicInt.coe_eq_zero.mp h, map_zero, map_zero, zero_add]

/-- The element `j` viewed as a unit in the division algebra. -/
noncomputable def j : D p := includeIntegral integralJ

omit [Fact (p % 4 = 3)] in
theorem nrd_j : nrd (j : D p) = (p : ℚ_[p]) := by
  rw [nrd_formula]
  change (0 : ℚ_[p]) ^ 2 + 0 ^ 2 + p * (1 ^ 2 + 0 ^ 2) = p
  simp

noncomputable def uniformizer : (D p)ˣ :=
  unitOfNonzero j (by intro h; have he := congrArg QuaternionAlgebra.imJ h; change (1 : ℚ_[p]) = 0 at he; exact one_ne_zero he)

theorem uniformizer_norm : (nrd (uniformizer : (D p)ˣ).val).valuation = 1 := by
  change (nrd (j : D p)).valuation = 1
  rw [nrd_j, Padic.valuation_p]

private noncomputable def conjugateInOrder (u : (D p)ˣ) (x : order p) : order p :=
  ⟨(↑u⁻¹ : D p) * x.val * (u : D p),
    (mem_order_iff_nrd _).mpr (by rw [nrd_conj]; exact (mem_order_iff_nrd _).mp x.property)⟩

private theorem conjugateInOrder_inverse (u : (D p)ˣ) :
    Function.LeftInverse (conjugateInOrder u⁻¹) (conjugateInOrder u) := by
  intro x
  apply Subtype.ext
  change (↑u⁻¹⁻¹ : D p) * ((↑u⁻¹ : D p) * x.val * (u : D p)) * (↑u⁻¹ : D p) = x.val
  simp only [inv_inv, mul_assoc, Units.mul_inv, mul_one,
    ← mul_assoc (u : D p) (↑u⁻¹ : D p) x.val, one_mul]

/-- Inverse conjugation by `j` acts on the order. -/
noncomputable def uniformizerOrder : order p ≃+* order p where
  toFun := conjugateInOrder uniformizer
  invFun := conjugateInOrder uniformizer⁻¹
  left_inv := conjugateInOrder_inverse uniformizer
  right_inv := by
    intro x
    simpa only [inv_inv] using conjugateInOrder_inverse (uniformizer (p := p))⁻¹ x
  map_mul' x y := by
    apply Subtype.ext
    let u : (D p)ˣ := uniformizer
    change (↑u⁻¹ : D p) * (x.val * y.val) * (u : D p) =
      ((↑u⁻¹ : D p) * x.val * (u : D p)) * ((↑u⁻¹ : D p) * y.val * (u : D p))
    simp only [mul_assoc, ← mul_assoc (u : D p) (↑u⁻¹ : D p), Units.mul_inv, one_mul]
  map_add' x y := by
    apply Subtype.ext
    let u : (D p)ˣ := uniformizer
    change (↑u⁻¹ : D p) * (x.val + y.val) * (u : D p) =
      ((↑u⁻¹ : D p) * x.val * (u : D p)) + ((↑u⁻¹ : D p) * y.val * (u : D p))
    rw [mul_add, add_mul]

theorem uniformizer_conj (x : order p) :
    (uniformizerOrder x).val = (↑(uniformizer (p := p))⁻¹ : D p) * x.val *
      (uniformizer : (D p)ˣ).val := rfl

/-- On integral coordinates conjugation fixes the scalar and `j`
and negates the other two coordinates. -/
theorem uniformizer_coords (x : order p) :
    orderEquiv.symm (uniformizerOrder x) =
      ⟨(orderEquiv.symm x).re, -(orderEquiv.symm x).imI,
        (orderEquiv.symm x).imJ, -(orderEquiv.symm x).imK⟩ := by
  apply includeIntegral_injective
  rw [includeIntegral_symm, uniformizer_conj]
  let a := orderEquiv.symm x
  let y : D p := includeIntegral (⟨a.re, -a.imI, a.imJ, -a.imK⟩ : IntegralD p)
  let u : (D p)ˣ := uniformizer
  change (↑u⁻¹ : D p) * x.val * (u : D p) = y
  have hy : (j : D p) * y = x.val * j := by
    have he : x.val = includeIntegral a := (includeIntegral_symm x).symm
    rw [he]
    change (⟨0,0,1,0⟩ : D p) * ⟨a.re,-(a.imI : ℚ_[p]),a.imJ,-(a.imK : ℚ_[p])⟩ =
      ⟨a.re,a.imI,a.imJ,a.imK⟩ * ⟨0,0,1,0⟩
    rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.mk_mul_mk]
    congr 1 <;> ring
  have hh := congrArg (fun z : D p => (↑u⁻¹ : D p) * z) hy
  change (↑u⁻¹ : D p) * ((u : D p) * y) =
    (↑u⁻¹ : D p) * (x.val * (u : D p)) at hh
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using hh.symm

theorem uniformizer_frobenius (x : order p) :
    red (uniformizerOrder x) = red x ^ p := by
  rw [red_apply (uniformizerOrder x), uniformizer_coords, red_apply x, add_pow_char, mul_pow]
  simp only [← map_pow (algebraMap (ZMod p) (GaloisField p 2)), ZMod.pow_card, beta_frobenius]
  rw [map_neg, map_neg, neg_mul, mul_neg]

#print axioms quadReduction_surj
#print axioms quadReduction_zero_iff
#print axioms padicReduction_locallyConstant
#print axioms residueQuotientEquiv
#print axioms red_surj
#print axioms red_ker_maximal
#print axioms red_i
#print axioms beta_sq
#print axioms beta_ne_zero
#print axioms beta_frobenius
#print axioms red_apply
#print axioms red_scalar
#print axioms red_locallyConstant
#print axioms red_eq_zero_iff
#print axioms red_ker_j
#print axioms integralNorm_red
#print axioms red_nonunit
#print axioms trace_line
#print axioms nrd_j
#print axioms uniformizer_norm
#print axioms conjugateInOrder_inverse
#print axioms uniformizer_conj
#print axioms uniformizer_coords
#print axioms uniformizer_frobenius

end ZInQ.Manuscript.RC.LocalDivision
