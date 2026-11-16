/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Injective
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

/-!
# W13 dictionary D3/D4, part 3: multiplication by `3` is surjective (hence dominant)

`act (toΛ 3)` is the FLT scheme morphism `schemeNsmul 3`, using `act_add` and `act_one`. Over a field
of characteristic `0`, `3` is a unit. The FLT source theorem
`RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension` (with
`exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing`) makes it étale, so it is universally
open (Mathlib `UniversallyOpen.of_flat`). It is universally closed (`A → Spec K` proper). Its image
is therefore clopen and nonempty in the connected (integral) scheme `A`, so it is surjective.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudB2Shimura.Dictionary

variable {K : Type} [Field K] (u : FLTL3 K)

lemma act_add_eq (x y : ↥Λ) :
    u.1.act (x + y) = (u.1.L.mul u.1.f ⟨u.1.act x, u.1.act_over x⟩ ⟨u.1.act y, u.1.act_over y⟩).1 := by
  have hp : ∀ z : ↥Λ, CerednikDrinfeld.QM.pushPt (u.1.act z) (u.1.act_over z)
      (⟨𝟙 u.1.A, Category.id_comp _⟩ : SchemeHomOver u.1.f u.1.f) = ⟨u.1.act z, u.1.act_over z⟩ :=
    fun z => Subtype.ext (Category.id_comp _)
  have := u.1.act_add x y u.1.f ⟨𝟙 u.1.A, Category.id_comp _⟩
  rw [hp, hp, hp] at this
  exact congrArg Subtype.val this

lemma act_three_eq : u.1.act (toΛ 3) = u.1.L.schemeNsmul 3 := by
  have h3 : toΛ 3 = toΛ 1 + toΛ 1 + toΛ 1 := by
    rw [← toΛ_add, ← toΛ_add]; norm_num
  have h1 : (⟨u.1.act (toΛ 1), u.1.act_over (toΛ 1)⟩ : SchemeHomOver u.1.f u.1.f) =
      GoodReductionJacobian.RelativeGroupLaw.idPoint :=
    Subtype.ext (u.1.act_one _)
  have h2 : (⟨u.1.act (toΛ 1 + toΛ 1), u.1.act_over _⟩ : SchemeHomOver u.1.f u.1.f) =
      u.1.L.mul u.1.f GoodReductionJacobian.RelativeGroupLaw.idPoint
        GoodReductionJacobian.RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    change u.1.act (toΛ 1 + toΛ 1) = _
    rw [act_add_eq, h1]
  rw [h3, act_add_eq, h1, h2]
  unfold GoodReductionJacobian.RelativeGroupLaw.schemeNsmul
  simp only [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ,
    GoodReductionJacobian.RelativeGroupLaw.nsmul_zero, u.1.L.one_mul]

/-- **Multiplication by `3` on `A` is dominant** (indeed surjective). -/
theorem isDominant_act_three [CharZero K] (h : AbVarProps u.1) : IsDominant (u.1.act (toΛ 3)) := by
  haveI : Smooth u.1.f := h.2.1
  haveI : IsProper u.1.f := h.1
  haveI := isIntegral_A u h
  obtain ⟨d, hd⟩ := u.1.L.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  haveI := hd
  have hunit : IsUnit ((3 : ℕ) : K) := (Nat.cast_ne_zero.mpr (by norm_num)).isUnit
  haveI : Etale (u.1.L.schemeNsmul 3) :=
    u.1.L.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension u.1.comm d 3 hunit
  rw [act_three_eq]
  haveI : UniversallyClosed (u.1.L.schemeNsmul 3 ≫ u.1.f) := by
    rw [u.1.L.schemeNsmul_over]; infer_instance
  haveI : UniversallyClosed (u.1.L.schemeNsmul 3) :=
    UniversallyClosed.of_comp_of_isSeparated _ u.1.f
  haveI : Surjective (u.1.L.schemeNsmul 3) := by
    constructor
    have hclopen : IsClopen (Set.range (u.1.L.schemeNsmul 3).base) :=
      ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
    have hne : (Set.range (u.1.L.schemeNsmul 3).base).Nonempty :=
      ⟨_, ⟨u.2.P.1.base (Classical.arbitrary _), rfl⟩⟩
    rw [← Set.range_eq_univ]
    exact hclopen.eq_univ hne
  infer_instance

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D34
