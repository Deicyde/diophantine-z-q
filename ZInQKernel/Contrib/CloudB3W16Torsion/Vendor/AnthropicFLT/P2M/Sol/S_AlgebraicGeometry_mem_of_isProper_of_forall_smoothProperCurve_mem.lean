/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mCurveConnect

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))

noncomputable abbrev pt (p : Spec (CommRingCat.of k) ⟶ Y) : Y := p (IsLocalRing.closedPoint k)

theorem isClosed_pt [LocallyOfFiniteType y] (p : Spec (CommRingCat.of k) ⟶ Y) (hp : p ≫ y = 𝟙 _) :
    IsClosed ({pt p} : Set Y) :=
  ((pointEquivClosedPoint y) ⟨p, hp⟩).2

def CurveStable (S : Set (Spec (CommRingCat.of k) ⟶ Y)) : Prop :=
  ∀ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [IsIntegral C] (ψ : C ⟶ Y), ψ ≫ y = c →
    ∀ p q : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ → q ≫ c = 𝟙 _ → p ≫ ψ ∈ S → q ≫ ψ ∈ S

section Link

variable {U : Y.Opens} (hU : IsAffineOpen U)

omit [IsAlgClosed k] in

noncomputable def algHomK : CommRingCat.of k ⟶ Γ(Y, U) := Spec.preimage (hU.fromSpec ≫ y)

omit [IsAlgClosed k] in
theorem spec_map_algHomK : Spec.map (algHomK y hU) = hU.fromSpec ≫ y := Spec.map_preimage _

omit [IsAlgClosed k] in

@[reducible] noncomputable def algK : Algebra k Γ(Y, U) := (algHomK y hU).hom.toAlgebra

omit [IsAlgClosed k] in
theorem finiteType_algK [LocallyOfFiniteType y] : @Algebra.FiniteType k Γ(Y, U) _ _ (algK y hU) := by
  have h : LocallyOfFiniteType (Spec.map (algHomK y hU)) := by
    rw [spec_map_algHomK]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h

include hU in

theorem link [IsProper y] [IsIntegral Y] (S : Set (Spec (CommRingCat.of k) ⟶ Y)) (hS : CurveStable y S)
    (p q : Spec (CommRingCat.of k) ⟶ Y) (hp : p ≫ y = 𝟙 _) (hq : q ≫ y = 𝟙 _)
    (hpU : pt p ∈ U) (hqU : pt q ∈ U) (hpS : p ∈ S) : q ∈ S := by
  classical
  by_cases hpq : pt p = pt q
  · have : p = q := ext_of_apply_closedPoint_eq y hp hq hpq
    exact this ▸ hpS
  letI : Algebra k Γ(Y, U) := algK y hU
  haveI : Algebra.FiniteType k Γ(Y, U) := finiteType_algK y hU
  haveI : Nonempty U := ⟨⟨pt p, hpU⟩⟩

  set 𝔪p : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨pt p, hpU⟩).asIdeal with h𝔪p
  set 𝔪q : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨pt q, hqU⟩).asIdeal with h𝔪q
  haveI hmp : 𝔪p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨pt p, hpU⟩ (isClosed_pt y p hp)
  haveI hmq : 𝔪q.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨pt q, hqU⟩ (isClosed_pt y q hq)
  have hne : 𝔪p ≠ 𝔪q := by
    intro h
    apply hpq
    have h' : hU.primeIdealOf ⟨pt p, hpU⟩ = hU.primeIdealOf ⟨pt q, hqU⟩ := PrimeSpectrum.ext h
    have := hU.fromSpec_primeIdealOf ⟨pt p, hpU⟩
    rw [h', hU.fromSpec_primeIdealOf] at this
    exact this.symm

  have hbot : (⊥ : Ideal Γ(Y, U)) ≠ 𝔪p := by
    intro hb
    have hbm : (⊥ : Ideal Γ(Y, U)).IsMaximal := hb ▸ hmp
    have h1 : 𝔪q = ⊥ := (hbm.eq_of_le hmq.ne_top bot_le).symm
    exact hne (hb.symm.trans h1.symm)
  have hdim : 1 ≤ ringKrullDim Γ(Y, U) := by
    rw [ringKrullDim, Order.one_le_krullDim_iff]
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, hU.primeIdealOf ⟨pt p, hpU⟩, ?_⟩
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    exact lt_of_le_of_ne bot_le hbot
  obtain ⟨P, hP, hP0, hP1, hdimP⟩ :=
    Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one k hdim 𝔪p 𝔪q
  haveI := hP

  set B : Type u := Γ(Y, U) ⧸ P with hB
  let mkHom : Γ(Y, U) ⟶ CommRingCat.of B := CommRingCat.ofHom (Ideal.Quotient.mk P)
  let φ : Spec (CommRingCat.of B) ⟶ Y := Spec.map mkHom ≫ hU.fromSpec
  have halg : CommRingCat.ofHom (algebraMap k B) = algHomK y hU ≫ mkHom := by
    ext r; rfl
  have hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [halg, Spec.map_comp]
    simp only [φ, Category.assoc, spec_map_algHomK]
  obtain ⟨C, c, _, _, _, ψ, hψ, hpts⟩ :=
    exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one y B hdimP φ hφ
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

  have key : ∀ (r : Spec (CommRingCat.of k) ⟶ Y) (hr : r ≫ y = 𝟙 _) (hrU : pt r ∈ U),
      P ≤ (hU.primeIdealOf ⟨pt r, hrU⟩).asIdeal →
      ∃ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) = 𝟙 _ ∧ a ≫ φ = r := by
    intro r hr hrU hPr
    set 𝔪 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨pt r, hrU⟩).asIdeal with h𝔪
    haveI hmr : 𝔪.IsMaximal :=
      hU.primeIdealOf_isMaximal_of_isClosed ⟨pt r, hrU⟩ (isClosed_pt y r hr)
    have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ 𝔪 := by rw [Ideal.mk_ker]; exact hPr
    have hprime : (𝔪.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hmax : (𝔪.map (Ideal.Quotient.mk P)).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective hmr with h | h
      · exact absurd h hprime.ne_top
      · exact h
    let xB : Spec (CommRingCat.of B) := ⟨𝔪.map (Ideal.Quotient.mk P), hprime⟩
    have hxB : IsClosed ({xB} : Set (Spec (CommRingCat.of B))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal xB).mpr hmax
    have hcomap : Spec.map mkHom xB = hU.primeIdealOf ⟨pt r, hrU⟩ := by
      rw [Spec.map_apply]
      apply PrimeSpectrum.ext
      change Ideal.comap (Ideal.Quotient.mk P) (𝔪.map (Ideal.Quotient.mk P)) = 𝔪
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left]
      rw [← RingHom.ker_eq_comap_bot]; exact hker
    refine ⟨pointOfClosedPoint _ xB hxB, pointOfClosedPoint_comp _ _ _, ?_⟩
    apply ext_of_apply_closedPoint_eq y _ hr
    · change φ (pointOfClosedPoint _ xB hxB (IsLocalRing.closedPoint k)) = pt r
      rw [pointOfClosedPoint_apply]
      change hU.fromSpec (Spec.map mkHom xB) = pt r
      rw [hcomap, hU.fromSpec_primeIdealOf]
    · rw [Category.assoc, hφ, pointOfClosedPoint_comp]
  obtain ⟨ap, hap, hapφ⟩ := key p hp hpU hP0
  obtain ⟨aq, haq, haqφ⟩ := key q hq hqU hP1
  obtain ⟨cp, hcp, hcpψ⟩ := hpts ap hap
  obtain ⟨cq, hcq, hcqψ⟩ := hpts aq haq
  have h1 : cp ≫ ψ ∈ S := by rw [hcpψ, hapφ]; exact hpS
  have h2 := hS C c ψ hψ cp cq hcp hcq h1
  rwa [hcqψ, haqφ] at h2

end Link

theorem main [IsProper y] [IsIntegral Y]
    (S : Set (Spec (CommRingCat.of k) ⟶ Y))
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _) (h₀ : y₀ ∈ S)
    (hS : CurveStable y S)
    (y₁ : Spec (CommRingCat.of k) ⟶ Y) (hy₁ : y₁ ≫ y = 𝟙 _) : y₁ ∈ S := by
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace y

  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (pt y₀)) isOpen_univ
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hx₁, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (pt y₁)) isOpen_univ

  have hne : ((U₀ : Set Y) ∩ (U₁ : Set Y)).Nonempty :=
    nonempty_preirreducible_inter U₀.isOpen U₁.isOpen ⟨_, hx₀⟩ ⟨_, hx₁⟩
  obtain ⟨w, ⟨hw₀, hw₁⟩, hw⟩ :=
    nonempty_inter_closedPoints hne (U₀.isOpen.inter U₁.isOpen).isLocallyClosed
  set yw : Spec (CommRingCat.of k) ⟶ Y := pointOfClosedPoint y w hw with hyw_def
  have hyw : yw ≫ y = 𝟙 _ := pointOfClosedPoint_comp y w hw
  have hptw : pt yw = w := pointOfClosedPoint_apply y w hw _
  have hwS : yw ∈ S := link y hU₀ S hS y₀ yw hy₀ hyw hx₀ (hptw ▸ hw₀) h₀
  exact link y hU₁ S hS yw y₁ hyw hy₁ (hptw ▸ hw₁) hx₁ hwS

end P2mCurveConnect

open P2mCurveConnect in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] [IsIntegral Y]
    (S : Set (Spec (CommRingCat.of k) ⟶ Y))
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ y = 𝟙 _) (h₀ : y₀ ∈ S)
    (hS : ∀ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
      [SmoothOfRelativeDimension 1 c] [IsIntegral C] (ψ : C ⟶ Y), ψ ≫ y = c →
      ∀ p q : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ → q ≫ c = 𝟙 _ → p ≫ ψ ∈ S → q ≫ ψ ∈ S)
    (y₁ : Spec (CommRingCat.of k) ⟶ Y) (hy₁ : y₁ ≫ y = 𝟙 _) : y₁ ∈ S :=
  P2mCurveConnect.main y S y₀ hy₀ h₀ hS y₁ hy₁
