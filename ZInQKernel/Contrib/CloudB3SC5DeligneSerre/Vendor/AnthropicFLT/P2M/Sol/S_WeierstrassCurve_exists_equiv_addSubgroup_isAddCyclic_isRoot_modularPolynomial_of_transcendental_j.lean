/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j (git blob f322a3889b094910389176f02d8eac1365ccff97, sha256 7421d0fb9844b63119a1ff56381f34e96b459fea2170f0448fa8be7f57c25901).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j

open ModularCurve WeierstrassCurve Polynomial IntermediateField

namespace P2MKcKIV

universe u v

theorem separable_fibre (K : Type u) [Field K] {F : Type v} [Field F] [Algebra K F]
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (hNK : (N : K) ≠ 0)
    (x : F) (hx : Transcendental K x) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x)).Separable := by

  set φ : Polynomial K →+* F := (Polynomial.aeval (R := K) x).toRingHom with hφ
  have hφinj : Function.Injective φ := transcendental_iff_injective.1 hx
  have hφ0 : nonZeroDivisors (Polynomial K) ≤ (nonZeroDivisors F).comap φ := fun p hp =>
    mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hφinj (h.trans (map_zero φ).symm)))
  set ψ : RatFunc K →+* F := RatFunc.liftRingHom φ hφ0
  have hsep := (data.separable_map_ratFunc_of_natCast_ne_zero K N hNK).map (f := ψ)
  rw [Polynomial.map_map, Polynomial.map_map] at hsep
  convert hsep using 2
  refine Polynomial.ringHom_ext ?_ ?_
  · intro n
    simp [ψ, φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    change x = ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
    rw [RatFunc.liftRingHom_algebraMap]
    simp [φ]

theorem mem_range_of_fixed {Ω : Type u} [Field Ω] {M : Type v} [Field M] [Algebra Ω M]
    [IsAlgClosure Ω M] (α : M) (p : Polynomial Ω) (hsep : p.Separable)
    (hroot : (p.map (algebraMap Ω M)).IsRoot α)
    (hfix : ∀ τ : M ≃ₐ[Ω] M, τ α = α) : α ∈ Set.range (algebraMap Ω M) := by
  haveI : IsAlgClosed M := IsAlgClosure.isAlgClosed Ω
  haveI : Algebra.IsAlgebraic Ω M := IsAlgClosure.isAlgebraic
  haveI : Normal Ω M := ⟨fun x => IsAlgClosed.splits _⟩
  have hint : IsIntegral Ω α := Algebra.IsIntegral.isIntegral α

  have hmin_dvd : minpoly Ω α ∣ p := minpoly.dvd Ω α (by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hroot)
  have hmin_sep : (minpoly Ω α).Separable := hsep.of_dvd hmin_dvd

  have hroots : ∀ β : M, (minpoly Ω α).map (algebraMap Ω M) |>.IsRoot β → β = α := by
    intro β hβ

    have hβ' : β ∈ ((minpoly Ω α).map (algebraMap Ω M)).roots :=
      (Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).2 hβ
    let f₀ : Ω⟮α⟯ →ₐ[Ω] M :=
      (IntermediateField.algHomAdjoinIntegralEquiv Ω hint).symm ⟨β, hβ'⟩
    have hf₀ : f₀ (IntermediateField.AdjoinSimple.gen Ω α) = β :=
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen Ω hint _

    let f₁ : M →ₐ[Ω] M := f₀.liftNormal M
    let τ : M ≃ₐ[Ω] M := AlgEquiv.ofBijective f₁ (Algebra.IsAlgebraic.algHom_bijective f₁)
    have hτ : τ α = β := by
      change f₁ α = β
      have := AlgHom.liftNormal_commutes f₀ M (IntermediateField.AdjoinSimple.gen Ω α)
      rw [IntermediateField.AdjoinSimple.algebraMap_gen] at this
      change f₁ α = algebraMap M M (f₀ _) at this
      rw [this, hf₀]; rfl
    rw [← hτ, hfix τ]

  have hsplit : ((minpoly Ω α).map (algebraMap Ω M)).Splits := IsAlgClosed.splits _
  have hcard : ((minpoly Ω α).map (algebraMap Ω M)).roots.card = (minpoly Ω α).natDegree := by
    rw [← Polynomial.natDegree_map (algebraMap Ω M)]
    exact (Polynomial.splits_iff_card_roots.1 hsplit)
  have hnodup : ((minpoly Ω α).map (algebraMap Ω M)).roots.Nodup :=
    Polynomial.nodup_roots hmin_sep.map
  have hall : ∀ b ∈ ((minpoly Ω α).map (algebraMap Ω M)).roots, b = α := fun β hβ =>
    hroots β ((Polynomial.mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hint))).1 hβ)
  have hrep := Multiset.eq_replicate_card.2 hall
  have hle : ((minpoly Ω α).map (algebraMap Ω M)).roots.card ≤ 1 := by
    classical
    have hc := (Multiset.nodup_iff_count_le_one.1 hnodup) α
    rw [hrep, Multiset.count_replicate_self] at hc
    exact hc
  have hdeg : (minpoly Ω α).natDegree = 1 := by
    have h1 : 0 < (minpoly Ω α).natDegree := minpoly.natDegree_pos hint
    omega

  have := minpoly.mem_range_of_degree_eq_one Ω α (by
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hdeg]; rfl)
  exact this

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k M : Type*} [Field k] [Field M] [Algebra k M]
    [IsAlgClosed M] [DecidableEq M] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : M) ≠ 0) :
    Nat.card {Q : (E.baseChange M).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := M) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem nsmul_eq_zero_of_mem {A : Type*} [AddCommGroup A] {H : AddSubgroup A} {N : ℕ}
    (hH : Nat.card H = N) {P : A} (hP : P ∈ H) : N • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH] at this
  exact congrArg Subtype.val this

end P2MKcKIV

open P2MKcKIV in
universe u v in
theorem solution (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra k Ω]
    (hN : (N : k) ≠ 0) (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Θ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω)
          (algebraMap k Ω E.j))).IsRoot y},
      ∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Θ H').1 : Ω) = σ (Θ H).1 := by
  classical

  let M := AlgebraicClosure Ω
  let ι : Ω →ₐ[k] M := IsScalarTower.toAlgHom k Ω M
  have hιalg : ∀ x : Ω, ι x = algebraMap Ω M x := fun x => rfl
  have hιinj : Function.Injective ι := (algebraMap Ω M).injective
  let ιp : (E.baseChange Ω).toAffine.Point →+ (E.baseChange M).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map ι
  have hιp : Function.Injective ιp := WeierstrassCurve.Affine.Point.map_injective ι

  letI : Algebra K Ω := ((algebraMap k Ω).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K Ω M := AlgebraicClosure.instIsScalarTower Ω
  haveI : IsScalarTower K k M := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K Ω M, IsScalarTower.algebraMap_apply k Ω M]
    rfl
  have hNK : (N : K) ≠ 0 := fun h => hN (by simpa using congrArg (algebraMap K k) h)
  have hNΩ : (N : Ω) ≠ 0 := fun h => hN ((algebraMap k Ω).injective (by simpa using h))
  have hNM : (N : M) ≠ 0 := fun h => hNΩ ((algebraMap Ω M).injective (by simpa using h))

  set x : Ω := algebraMap k Ω E.j with hx
  set pΩ : Polynomial Ω := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x) with hpΩ
  have hxT : Transcendental K x := (transcendental_algebraMap_iff (algebraMap k Ω).injective).2 hE
  have hsep : pΩ.Separable := separable_fibre K N data hNK x hxT
  haveI instEM : (E.baseChange M).IsElliptic :=
    show (E.map (algebraMap k M)).IsElliptic from inferInstance
  have hjM : (E.baseChange M).j = algebraMap Ω M x := by
    change (E.map (algebraMap k M)).j = _
    rw [WeierstrassCurve.map_j, hx, ← IsScalarTower.algebraMap_apply]
  have hEM : Transcendental K (E.baseChange M).j := by
    rw [hjM]
    exact (transcendental_algebraMap_iff (algebraMap Ω M).injective).2 hxT
  have hpM : pΩ.map (algebraMap Ω M) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom M) (E.baseChange M).j) := by
    rw [hpΩ, Polynomial.map_map, hjM]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp

  set F : AddSubgroup (E.baseChange M).toAffine.Point → M :=
    fun H => (E.baseChange M).cyclicQuotientJ H N with hF
  have hbij := WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
    K N data M hNM (E.baseChange M) hEM
  rw [← hpM] at hbij

  have htorM := natCard_torsion_of_isAlgClosed (M := M) E N hNM
  have hhit : ∀ Q : (E.baseChange M).toAffine.Point, N • Q = 0 → ∃ P, N • P = 0 ∧ ιp P = Q :=
    exists_eq_of_nsmul_eq_zero ιp hιp N hfull htorM

  have hmapS : ∀ H : AddSubgroup (E.baseChange Ω).toAffine.Point,
      IsAddCyclic H ∧ Nat.card H = N → IsAddCyclic (H.map ιp) ∧ Nat.card (H.map ιp) = N := by
    intro H ⟨hc, hcard⟩
    let e := H.equivMapOfInjective ιp hιp
    exact ⟨isAddCyclic_of_surjective e e.surjective, by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm⟩
  have hcomapS : ∀ H' : AddSubgroup (E.baseChange M).toAffine.Point,
      IsAddCyclic H' ∧ Nat.card H' = N →
        (H'.comap ιp).map ιp = H' ∧ IsAddCyclic (H'.comap ιp) ∧ Nat.card (H'.comap ιp) = N := by
    intro H' ⟨hc, hcard⟩
    have hle : H' ≤ ιp.range := fun Q hQ => by
      obtain ⟨P, -, hP⟩ := hhit Q (nsmul_eq_zero_of_mem hcard hQ)
      exact ⟨P, hP⟩
    have hmap : (H'.comap ιp).map ιp = H' := by
      rw [AddSubgroup.map_comap_eq, inf_eq_right.2 hle]
    let e := (H'.comap ιp).equivMapOfInjective ιp hιp
    have e' : (H'.comap ιp) ≃+ H' := e.trans (AddEquiv.addSubgroupCongr hmap)
    exact ⟨hmap, isAddCyclic_of_surjective e'.symm e'.symm.surjective,
      by rw [← hcard]; exact Nat.card_congr e'.toEquiv⟩

  have hfixed : ∀ (H : AddSubgroup (E.baseChange Ω).toAffine.Point) (τ : M ≃ₐ[Ω] M),
      τ (F (H.map ιp)) = F (H.map ιp) := by
    intro H τ
    let τk : M →ₐ[k] M := (τ : M →ₐ[Ω] M).restrictScalars k
    have hnat := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E τk (H.map ιp) N
    have hcomp : τk.comp ι = ι := by
      ext y
      change τ (ι y) = ι y
      rw [hιalg]; exact τ.commutes y
    have hHH : (H.map ιp).map (WeierstrassCurve.Affine.Point.map τk) = H.map ιp := by
      rw [AddSubgroup.map_map]
      congr 1
      ext P
      change WeierstrassCurve.Affine.Point.map τk (WeierstrassCurve.Affine.Point.map ι P) = _
      rw [WeierstrassCurve.Affine.Point.map_map, hcomp]
    rw [hHH] at hnat
    exact hnat.symm

  have hdesc : ∀ H : AddSubgroup (E.baseChange Ω).toAffine.Point, IsAddCyclic H ∧ Nat.card H = N →
      ∃ y : Ω, pΩ.IsRoot y ∧ algebraMap Ω M y = F (H.map ιp) := by
    intro H hH
    have hroot : (pΩ.map (algebraMap Ω M)).IsRoot (F (H.map ιp)) := hbij.mapsTo (hmapS H hH)
    obtain ⟨y, hy⟩ := mem_range_of_fixed (F (H.map ιp)) pΩ hsep hroot (hfixed H)
    refine ⟨y, ?_, hy⟩
    rw [← hy, Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom,
      map_eq_zero_iff _ (algebraMap Ω M).injective] at hroot
    exact hroot

  let Θ₀ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
      {y : Ω // pΩ.IsRoot y} := fun H => ⟨(hdesc H.1 H.2).choose, (hdesc H.1 H.2).choose_spec.1⟩
  have hΘ₀ : ∀ H, algebraMap Ω M (Θ₀ H).1 = F (H.1.map ιp) := fun H => (hdesc H.1 H.2).choose_spec.2
  have hinj : Function.Injective Θ₀ := by
    intro H₁ H₂ h
    have h' := congrArg (fun y : {y : Ω // pΩ.IsRoot y} => algebraMap Ω M y.1) h
    simp only [hΘ₀] at h'
    have := hbij.injOn (hmapS _ H₁.2) (hmapS _ H₂.2) h'
    exact Subtype.ext (AddSubgroup.map_injective hιp this)
  have hsurj : Function.Surjective Θ₀ := by
    rintro ⟨y, hy⟩
    have hyM : (pΩ.map (algebraMap Ω M)).IsRoot (algebraMap Ω M y) := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom, hy.eq_zero, map_zero]
    obtain ⟨H', hH', hFy⟩ := hbij.surjOn hyM
    obtain ⟨hmap, hc, hcard⟩ := hcomapS H' hH'
    refine ⟨⟨H'.comap ιp, hc, hcard⟩, Subtype.ext ((algebraMap Ω M).injective ?_)⟩
    rw [hΘ₀]
    change F ((H'.comap ιp).map ιp) = _
    rw [hmap]
    exact hFy
  refine ⟨Equiv.ofBijective Θ₀ ⟨hinj, hsurj⟩, ?_⟩

  intro σ H H' hH'
  change (Θ₀ H').1 = σ (Θ₀ H).1
  apply (algebraMap Ω M).injective

  let σM : M ≃+* M := IsAlgClosure.equivOfEquiv M M (σ : Ω ≃+* Ω)
  have hσM : ∀ y : Ω, σM (algebraMap Ω M y) = algebraMap Ω M (σ y) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap M M (σ : Ω ≃+* Ω) y
  let σk : M ≃ₐ[k] M := AlgEquiv.ofRingEquiv (f := σM) fun c => by
    rw [IsScalarTower.algebraMap_apply k Ω M, hσM, AlgEquiv.commutes]
  have hnat := WeierstrassCurve.cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed E
    (σk : M →ₐ[k] M) (H.1.map ιp) N
  have hcomp : (σk : M →ₐ[k] M).comp ι = ι.comp (σ : Ω →ₐ[k] Ω) := by
    ext y
    exact hσM y
  have hHH : (H.1.map ιp).map (WeierstrassCurve.Affine.Point.map (σk : M →ₐ[k] M)) =
      H'.1.map ιp := by
    rw [hH', AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext P
    change WeierstrassCurve.Affine.Point.map (σk : M →ₐ[k] M) (WeierstrassCurve.Affine.Point.map ι P)
      = WeierstrassCurve.Affine.Point.map ι (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P)
    rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map, hcomp]
  have e1 : F (H'.1.map ιp) = σk (F (H.1.map ιp)) := by rw [← hHH]; exact hnat
  rw [hΘ₀ H', e1, ← hΘ₀ H]
  exact hσM _
