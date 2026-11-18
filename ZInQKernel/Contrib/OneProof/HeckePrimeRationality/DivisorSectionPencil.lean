import Mathlib.Data.Finsupp.Order
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# A pencil theorem for pole-bounded section spaces

The section spaces are subspaces of an actual field extension, cut out by
integer local orders. A pair with no common zero supplies the pencil kernel
by division in that field. Riemann--Roch dimensions are independent geometric
inputs, not multiplication-surjectivity assumptions. Instantiation on a
particular curve, and identification with analytic modular forms, are
separate obligations.
-/

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

namespace ZInQ.Contrib.HeckePrimeRationality.SectionMultiplication

variable {K F X : Type*} [Field K] [Field F] [Algebra K F]

/-- Integer orders on nonzero functions, trivial on the coefficient field. -/
structure LocalOrders (K F X : Type*) [Field K] [Field F] [Algebra K F] where
  ord : X → F → ℤ
  add_lower : ∀ x f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
    min (ord x f) (ord x g) ≤ ord x (f + g)
  mul_order : ∀ x f g, f ≠ 0 → g ≠ 0 → ord x (f * g) = ord x f + ord x g
  constant_order : ∀ (x : X) (c : K), c ≠ 0 → ord x (algebraMap K F c) = 0

namespace LocalOrders

variable (v : LocalOrders K F X)

/-- A function is a section of a divisor precisely when its poles obey its bounds. -/
def sectionSpace (D : X →₀ ℤ) : Submodule K F where
  carrier := {f | f = 0 ∨ ∀ x, -D x ≤ v.ord x f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases hf with rfl | hf
    · simpa using hg
    rcases hg with rfl | hg
    · simpa using (Or.inr hf : f = 0 ∨ ∀ x, -D x ≤ v.ord x f)
    by_cases hf0 : f = 0
    · subst f; simpa using (Or.inr hg : g = 0 ∨ ∀ x, -D x ≤ v.ord x g)
    by_cases hg0 : g = 0
    · subst g
      change f + 0 = 0 ∨ ∀ x, -D x ≤ v.ord x (f + 0)
      right
      simpa only [add_zero] using hf
    by_cases hsum : f + g = 0
    · exact Or.inl hsum
    · exact Or.inr fun x => (le_min (hf x) (hg x)).trans (v.add_lower x f g hf0 hg0 hsum)
  smul_mem' := by
    intro c f hf
    by_cases hc : c = 0
    · subst c; simp
    rcases hf with rfl | hf
    · simp
    by_cases hf0 : f = 0
    · subst f; simp
    right
    intro x
    rw [Algebra.smul_def, v.mul_order x _ _ ((map_ne_zero (algebraMap K F)).mpr hc) hf0,
      v.constant_order x c hc, zero_add]
    exact hf x

@[simp] theorem mem_sectionSpace (D : X →₀ ℤ) (f : F) :
    f ∈ v.sectionSpace D ↔ f = 0 ∨ ∀ x, -D x ≤ v.ord x f := Iff.rfl

theorem order_neg (x : X) {f : F} (hf : f ≠ 0) : v.ord x (-f) = v.ord x f := by
  have hm : algebraMap K F (-1) = (-1 : F) := by simp
  rw [← neg_one_mul f, ← hm, v.mul_order x _ _ (by simpa using (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))) hf,
    v.constant_order x (-1) (neg_ne_zero.mpr one_ne_zero), zero_add]

theorem section_mul_mem (D E : X →₀ ℤ) {f g : F}
    (hf : f ∈ v.sectionSpace D) (hg : g ∈ v.sectionSpace E) : f * g ∈ v.sectionSpace (D + E) := by
  by_cases hf0 : f = 0
  · subst f; simp
  by_cases hg0 : g = 0
  · subst g; simp
  right
  intro x
  rw [v.mul_order x f g hf0 hg0]
  have hfx := (hf.resolve_left hf0) x
  have hgx := (hg.resolve_left hg0) x
  simp only [Finsupp.add_apply]
  linarith

/-- Actual multiplication of two pole-bounded sections. -/
def sectionMul (D E : X →₀ ℤ) :
    v.sectionSpace D →ₗ[K] v.sectionSpace E →ₗ[K] v.sectionSpace (D + E) where
  toFun f :=
    { toFun := fun g => ⟨f.1 * g.1, v.section_mul_mem D E f.2 g.2⟩
      map_add' := by intro g h; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro c g; apply Subtype.ext; exact mul_smul_comm _ _ _ }
  map_add' := by
    intro f g
    ext h
    exact add_mul _ _ _
  map_smul' := by
    intro c f
    ext g
    exact smul_mul_assoc _ _ _

/-- The genuine tensor multiplication map on these section spaces. -/
def sectionTensorMul (D E : X →₀ ℤ) :
    v.sectionSpace D ⊗[K] v.sectionSpace E →ₗ[K] v.sectionSpace (D + E) :=
  TensorProduct.lift (v.sectionMul D E)

@[simp] theorem sectionTensorMul_tmul (D E : X →₀ ℤ)
    (f : v.sectionSpace D) (g : v.sectionSpace E) :
    (v.sectionTensorMul D E (f ⊗ₜ[K] g) : F) = f.1 * g.1 := rfl

/-- No common zero, written directly in terms of the actual orders and divisor. -/
def IsPencil (D : X →₀ ℤ) (a b : v.sectionSpace D) : Prop :=
  a.1 ≠ 0 ∧ b.1 ≠ 0 ∧ ∀ x, min (v.ord x a.1) (v.ord x b.1) = -D x

/-- Multiplication by a section of D carries sections of E-D to sections of E. -/
theorem pencil_factor_mem (D E : X →₀ ℤ) (a : v.sectionSpace D)
    (h : v.sectionSpace (E - D)) : a.1 * h.1 ∈ v.sectionSpace E := by
  have hm := v.section_mul_mem D (E - D) a.2 h.2
  have hd : D + (E - D) = E := by abel
  rw [hd] at hm
  exact hm

/-- The actual pencil map sends (f,g) to af+bg. -/
def pencilMap (D E : X →₀ ℤ) (a b : v.sectionSpace D) :
    (v.sectionSpace E × v.sectionSpace E) →ₗ[K] v.sectionSpace (D + E) where
  toFun fg := v.sectionMul D E a fg.1 + v.sectionMul D E b fg.2
  map_add' := by intro f g; ext; simp [sectionMul]; ring
  map_smul' := by intro c f; ext; simp [sectionMul, smul_add]

/-- The Koszul relation is constructed inside the actual field. -/
def pencilRelation (D E : X →₀ ℤ) (a b : v.sectionSpace D) :
    v.sectionSpace (E - D) →ₗ[K] (v.sectionSpace E × v.sectionSpace E) where
  toFun h := (⟨b.1 * h.1, v.pencil_factor_mem D E b h⟩,
    -⟨a.1 * h.1, v.pencil_factor_mem D E a h⟩)
  map_add' := by intro h i; ext <;> simp <;> ring
  map_smul' := by intro c h; ext <;> simp [mul_smul_comm]

theorem pencilRelation_injective (D E : X →₀ ℤ) (a b : v.sectionSpace D) (hb : b.1 ≠ 0) :
    Function.Injective (v.pencilRelation D E a b) := by
  intro h i he
  apply Subtype.ext
  have hx : b.1 * h.1 = b.1 * i.1 := congrArg (fun p => (p.1 : F)) he
  exact mul_left_cancel₀ hb hx

/-- A kernel relation has a pole-bounded quotient; no section-surjectivity premise is used. -/
theorem pencil_quotient_mem (D E : X →₀ ℤ) (a b : v.sectionSpace D)
    (hp : v.IsPencil D a b) (fg : v.sectionSpace E × v.sectionSpace E)
    (he : a.1 * fg.1.1 + b.1 * fg.2.1 = 0) :
    fg.1.1 / b.1 ∈ v.sectionSpace (E - D) := by
  by_cases hf : fg.1.1 = 0
  · left; rw [hf, zero_div]
  have hq : fg.1.1 / b.1 ≠ 0 := div_ne_zero hf hp.2.1
  have h0 : b.1 * (fg.1.1 / b.1) = fg.1.1 := mul_div_cancel₀ _ hp.2.1
  have h1 : -(a.1 * (fg.1.1 / b.1)) = fg.2.1 := by
    apply mul_left_cancel₀ hp.2.1
    rw [mul_neg, ← mul_assoc, mul_comm b.1 a.1, mul_assoc, h0]
    linear_combination -he
  have hg : fg.2.1 ≠ 0 := by rw [← h1]; exact neg_ne_zero.mpr (mul_ne_zero hp.1 hq)
  right
  intro x
  have hfbound := (fg.1.2.resolve_left hf) x
  have hgbound := (fg.2.2.resolve_left hg) x
  rw [← h0, v.mul_order x _ _ hp.2.1 hq] at hfbound
  rw [← h1, v.order_neg x (mul_ne_zero hp.1 hq), v.mul_order x _ _ hp.1 hq] at hgbound
  have hbnd : -E x ≤ min (v.ord x a.1) (v.ord x b.1) + v.ord x (fg.1.1 / b.1) := by
    rcases le_total (v.ord x a.1) (v.ord x b.1) with h | h
    · rw [min_eq_left h]; exact hgbound
    · rw [min_eq_right h]; exact hfbound
  rw [hp.2.2 x] at hbnd
  simp only [Finsupp.sub_apply]
  linarith

/-- The pencil kernel is exactly the explicitly constructed Koszul relation space. -/
theorem range_pencilRelation_eq_ker (D E : X →₀ ℤ) (a b : v.sectionSpace D)
    (hp : v.IsPencil D a b) :
    LinearMap.range (v.pencilRelation D E a b) = LinearMap.ker (v.pencilMap D E a b) := by
  ext fg
  constructor
  · rintro ⟨h,rfl⟩
    apply Subtype.ext
    change a.1 * (b.1 * h.1) + b.1 * -(a.1 * h.1) = 0
    ring
  · intro hfg
    have he : a.1 * fg.1.1 + b.1 * fg.2.1 = 0 := congrArg Subtype.val hfg
    let h : v.sectionSpace (E - D) := ⟨fg.1.1 / b.1, v.pencil_quotient_mem D E a b hp fg he⟩
    refine ⟨h,?_⟩
    apply Prod.ext
    · apply Subtype.ext; exact mul_div_cancel₀ _ hp.2.1
    · apply Subtype.ext
      change -(a.1 * (fg.1.1 / b.1)) = fg.2.1
      apply mul_left_cancel₀ hp.2.1
      rw [mul_neg, ← mul_assoc, mul_comm b.1 a.1, mul_assoc, mul_div_cancel₀ _ hp.2.1]
      linear_combination -he

/-- The dimension of the kernel is derived from the explicit quotient relation. -/
theorem pencilMap_finrank_ker (D E : X →₀ ℤ) (a b : v.sectionSpace D)
    (hp : v.IsPencil D a b) [FiniteDimensional K (v.sectionSpace (E - D))] :
    Module.finrank K (LinearMap.ker (v.pencilMap D E a b)) =
      Module.finrank K (v.sectionSpace (E - D)) := by
  rw [← v.range_pencilRelation_eq_ker D E a b hp]
  exact LinearMap.finrank_range_of_inj (v.pencilRelation_injective D E a b hp.2.1)

/-- A pencil plus the independent section dimensions forces actual tensor multiplication onto. -/
theorem sectionTensorMul_surjective_of_pencil_dimensions (D E : X →₀ ℤ)
    (a b : v.sectionSpace D) (hp : v.IsPencil D a b)
    [FiniteDimensional K (v.sectionSpace E)]
    [FiniteDimensional K (v.sectionSpace (E - D))]
    [FiniteDimensional K (v.sectionSpace (D + E))]
    (hdim : 2 * Module.finrank K (v.sectionSpace E) =
      Module.finrank K (v.sectionSpace (D + E)) +
        Module.finrank K (v.sectionSpace (E - D))) :
    Function.Surjective (v.sectionTensorMul D E) := by
  have hr := LinearMap.finrank_range_add_finrank_ker (v.pencilMap D E a b)
  rw [v.pencilMap_finrank_ker D E a b hp, Module.finrank_prod] at hr
  have heq : Module.finrank K (LinearMap.range (v.pencilMap D E a b)) =
      Module.finrank K (v.sectionSpace (D + E)) := by omega
  have honto : Function.Surjective (v.pencilMap D E a b) :=
    LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq heq)
  intro f
  obtain ⟨fg,hfg⟩ := honto f
  refine ⟨a ⊗ₜ[K] fg.1 + b ⊗ₜ[K] fg.2, ?_⟩
  change ((v.sectionMul D E) a) fg.1 + ((v.sectionMul D E) b) fg.2 = f at hfg
  simpa only [map_add, sectionTensorMul, TensorProduct.lift.tmul] using hfg

/-- The nonspecial Riemann--Roch dimension formula, retained as an explicit geometric input. -/
def RRDimensions (degree : (X →₀ ℤ) →+ ℤ) (genus : ℕ) : Prop :=
  ∀ D, 2 * (genus : ℤ) - 2 < degree D →
    (Module.finrank K (v.sectionSpace D) : ℤ) = degree D + 1 - genus

/-- Basepoint-free pencil multiplication when the degree of E-D is nonspecial. -/
theorem sectionTensorMul_surjective_of_RR (degree : (X →₀ ℤ) →+ ℤ) (genus : ℕ)
    (hfinite : ∀ D, FiniteDimensional K (v.sectionSpace D))
    (hRR : v.RRDimensions degree genus) (D E : X →₀ ℤ)
    (hD : 0 ≤ degree D) (hgap : 2 * (genus : ℤ) - 2 < degree (E - D))
    (a b : v.sectionSpace D) (hp : v.IsPencil D a b) :
    Function.Surjective (v.sectionTensorMul D E) := by
  letI := hfinite E
  letI := hfinite (E - D)
  letI := hfinite (D + E)
  have hE : 2 * (genus : ℤ) - 2 < degree E := by
    rw [map_sub] at hgap
    linarith
  have hDE : 2 * (genus : ℤ) - 2 < degree (D + E) := by
    rw [map_add]
    linarith
  have rE := hRR E hE
  have rED := hRR (E - D) hgap
  have rDE := hRR (D + E) hDE
  simp only [map_sub, map_add] at rED rDE
  apply v.sectionTensorMul_surjective_of_pencil_dimensions D E a b hp
  have hdim : (2 : ℤ) * (Module.finrank K (v.sectionSpace E) : ℤ) =
      (Module.finrank K (v.sectionSpace (D + E)) : ℤ) +
        (Module.finrank K (v.sectionSpace (E - D)) : ℤ) := by linarith
  exact_mod_cast hdim

/-- A concrete higher-power consequence, with the geometric pencil hypothesis visible. -/
theorem higher_power_multiplication_of_RR_gap (degree : (X →₀ ℤ) →+ ℤ) (genus : ℕ)
    (hfinite : ∀ D, FiniteDimensional K (v.sectionSpace D))
    (hRR : v.RRDimensions degree genus) (L : X →₀ ℤ)
    (hdegree : (genus : ℤ) + 1 ≤ degree L)
    (i j : ℕ) (hij : i + 2 ≤ j)
    (a b : v.sectionSpace (i • L)) (hp : v.IsPencil (i • L) a b) :
    Function.Surjective (v.sectionTensorMul (i • L) (j • L)) := by
  apply v.sectionTensorMul_surjective_of_RR degree genus hfinite hRR (i • L) (j • L) ?_ ?_ a b hp
  · simp only [map_nsmul, nsmul_eq_mul]
    have hi : (0 : ℤ) ≤ i := Int.natCast_nonneg i
    have hg : (0 : ℤ) ≤ genus := Int.natCast_nonneg genus
    exact mul_nonneg hi (by omega)
  · simp only [map_sub, map_nsmul, nsmul_eq_mul]
    have hgap : (i : ℤ) + 2 ≤ j := by exact_mod_cast hij
    have hg : (0 : ℤ) ≤ genus := Int.natCast_nonneg genus
    have hd : 1 ≤ degree L := by omega
    nlinarith

end LocalOrders
end ZInQ.Contrib.HeckePrimeRationality.SectionMultiplication
