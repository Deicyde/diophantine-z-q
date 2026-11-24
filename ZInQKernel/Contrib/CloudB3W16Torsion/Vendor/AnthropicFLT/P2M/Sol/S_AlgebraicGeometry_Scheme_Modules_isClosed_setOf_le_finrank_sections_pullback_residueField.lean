/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace P2mSemicontH0

section FibreDim

variable {R : Type u} [CommRing R]

noncomputable abbrev fibreDim (Q : Type u) [AddCommGroup Q] [Module R Q]
    (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] Q)

variable {Q : Type u} [AddCommGroup Q] [Module R Q]

noncomputable def baseChangeCokerEquiv {P : Type u} [AddCommGroup P] [Module R P]
    (φ : P →ₗ[R] Q) (A : Type u) [CommRing A] [Algebra R A] :
    ((A ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange A)) ≃ₗ[A]
      A ⊗[R] (Q ⧸ LinearMap.range φ) := by
  have hex : Function.Exact φ (LinearMap.range φ).mkQ := LinearMap.exact_map_mkQ_range φ
  have hsurj : Function.Surjective (LinearMap.range φ).mkQ := Submodule.mkQ_surjective _
  have hexA : Function.Exact (φ.baseChange A) ((LinearMap.range φ).mkQ.baseChange A) := by
    have h := lTensor_exact A hex hsurj
    rwa [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
  exact hexA.linearEquivOfSurjective (LinearMap.baseChange_surjective A hsurj)

theorem fibreDim_le_card {ι : Type u} [Fintype ι] (φ : (ι → R) →ₗ[R] Q) (𝔮 : PrimeSpectrum R)
    (h : Subsingleton (𝔮.asIdeal.ResidueField ⊗[R] (Q ⧸ LinearMap.range φ))) :
    fibreDim Q 𝔮 ≤ Fintype.card ι := by
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => 𝔮.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔮.asIdeal.zero_mem))⟩⟩
  set K := 𝔮.asIdeal.ResidueField
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [← Submodule.Quotient.subsingleton_iff]
    exact (baseChangeCokerEquiv φ K).toEquiv.subsingleton
  have hsurj : Function.Surjective (φ.baseChange K) := LinearMap.range_eq_top.mp hrange
  calc fibreDim Q 𝔮 ≤ Module.finrank K (K ⊗[R] (ι → R)) :=
        LinearMap.finrank_le_finrank_of_surjective hsurj
    _ = Fintype.card ι := by
        rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card]

theorem exists_family_card_eq (𝔭 : PrimeSpectrum R) [Module.Finite R Q] :
    ∃ (ι : Type u) (_ : Fintype ι) (q : ι → Q),
      Fintype.card ι = fibreDim Q 𝔭 ∧
        Subsingleton (𝔭.asIdeal.ResidueField ⊗[R]
          (Q ⧸ LinearMap.range (Fintype.linearCombination R q))) := by
  set K := 𝔭.asIdeal.ResidueField

  have hspan : Submodule.span K (Set.range (TensorProduct.mk R K Q 1)) = ⊤ := by
    have h := (Submodule.baseChange_eq_span (p := (⊤ : Submodule R Q)) (A := K)).symm.trans
      (Submodule.baseChange_top (R := R) (M := Q) (A := K))
    rwa [Submodule.map_coe, Submodule.top_coe, Set.image_univ] at h
  obtain ⟨ι, a, -, hspan', hli⟩ := exists_linearIndependent' (K := K) (TensorProduct.mk R K Q 1)
  rw [hspan] at hspan'
  let b : Module.Basis ι K (K ⊗[R] Q) := Module.Basis.mk hli hspan'.ge
  haveI : IsNoetherian K (K ⊗[R] Q) := IsNoetherian.iff_fg.2 inferInstance
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  refine ⟨ι, inferInstance, a, (Module.finrank_eq_card_basis b).symm, ?_⟩
  classical
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R a
  have hrange : LinearMap.range (φ.baseChange K) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨1 ⊗ₜ[R] Pi.single i 1, ?_⟩
    rw [LinearMap.baseChange_tmul, Module.Basis.coe_mk]
    change (1 : K) ⊗ₜ[R] φ (Pi.single i 1) = (1 : K) ⊗ₜ[R] a i
    rw [Fintype.linearCombination_apply_single, one_smul]
  haveI : Subsingleton ((K ⊗[R] Q) ⧸ LinearMap.range (φ.baseChange K)) :=
    Submodule.Quotient.subsingleton_iff.mpr hrange
  exact (baseChangeCokerEquiv φ K).symm.toEquiv.subsingleton

theorem isClosed_setOf_le_fibreDim [Module.Finite R Q] (m : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | m ≤ fibreDim Q 𝔭} := by
  rw [← isOpen_compl_iff]
  have hset : {𝔭 : PrimeSpectrum R | m ≤ fibreDim Q 𝔭}ᶜ = {𝔭 | fibreDim Q 𝔭 < m} := by
    ext 𝔭; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  rw [hset, isOpen_iff_forall_mem_open]
  intro 𝔭 h𝔭
  obtain ⟨ι, _, q, hcard, hsub⟩ := exists_family_card_eq (Q := Q) 𝔭
  set φ : (ι → R) →ₗ[R] Q := Fintype.linearCombination R q
  let Q' := Q ⧸ LinearMap.range φ
  refine ⟨(Module.support R Q')ᶜ, ?_, Module.isClosed_support.isOpen_compl, ?_⟩
  · intro 𝔮 h𝔮
    have h𝔮' : Subsingleton (𝔮.asIdeal.ResidueField ⊗[R] Q') := by
      rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
        not_nontrivial_iff_subsingleton] at h𝔮
      exact h𝔮
    calc fibreDim Q 𝔮 ≤ Fintype.card ι := fibreDim_le_card φ 𝔮 h𝔮'
      _ = fibreDim Q 𝔭 := hcard
      _ < m := h𝔭
  · rw [Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
    exact hsub

end FibreDim

section TwoTerm

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)

theorem fibreH0_add_finrank (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 + Module.finrank R G.C1 =
      Module.finrank R G.C0 + fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := by
  haveI : Nontrivial R := ⟨⟨0, 1, fun h => 𝔭.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ 𝔭.asIdeal.zero_mem))⟩⟩
  set K := 𝔭.asIdeal.ResidueField
  set dK := G.d.baseChange K
  have h1 : Module.finrank K (LinearMap.range dK) + Module.finrank K (LinearMap.ker dK) =
      Module.finrank K (K ⊗[R] G.C0) := LinearMap.finrank_range_add_finrank_ker dK
  have h2 : Module.finrank K (K ⊗[R] G.C0) = Module.finrank R G.C0 := Module.finrank_baseChange
  have h3 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) +
      Module.finrank K (LinearMap.range dK) = Module.finrank K (K ⊗[R] G.C1) :=
    Submodule.finrank_quotient_add_finrank _
  have h4 : Module.finrank K (K ⊗[R] G.C1) = Module.finrank R G.C1 := Module.finrank_baseChange
  have h5 : Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range dK) =
      fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭 := (baseChangeCokerEquiv G.d K).finrank_eq
  have h0 : G.fibreH0 𝔭 = Module.finrank K (LinearMap.ker dK) := rfl
  omega

theorem isClosed_setOf_le_fibreH0 (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} := by
  have hset : {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} =
      {𝔭 | n + Module.finrank R G.C1 - Module.finrank R G.C0 ≤
        fibreDim (G.C1 ⧸ LinearMap.range G.d) 𝔭} := by
    ext 𝔭
    simp only [Set.mem_setOf_eq]
    have := fibreH0_add_finrank G 𝔭
    omega
  rw [hset]
  exact isClosed_setOf_le_fibreDim _

end TwoTerm

section Cover

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

end Cover

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    OModulePresheaf.res_res]
  exact add_neg_cancel _

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

def H0Equiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    (OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] Γ(M, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  (LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩).symm

end H0

section Main
open AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤)} := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := coverOfCompact X
  obtain ⟨G, ι0, ι1, comm, hbij⟩ :=
    OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules f M htriv 𝒰

  have key : ∀ 𝔭 : PrimeSpectrum R,
      (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤))
        = G.fibreH0 𝔭 := by
    intro 𝔭
    let K := 𝔭.asIdeal.ResidueField
    let p₁ := Limits.pullback.fst f (specMap R K)
    let p₂ := Limits.pullback.snd f (specMap R K)
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ ((Scheme.Modules.pullback p₁).obj M) ⊤
    obtain ⟨⟨⟨e1⟩, -⟩, -⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial f 𝒰 M htriv K
    let e2 := H0Equiv p₂ ((Scheme.Modules.pullback p₁).obj M) (𝒰.baseChange f K)
    let e3 := LinearEquiv.ofBijective
      (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm K) (hbij K)
    exact (e2.symm.trans (e1.trans e3.symm)).finrank_eq
  have hset : {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback (Limits.pullback.fst f (specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤)}
      = {𝔭 | n ≤ G.fibreH0 𝔭} := by
    ext 𝔭
    simp only [Set.mem_setOf_eq]
    rw [← key 𝔭]
  rw [hset]
  exact isClosed_setOf_le_fibreH0 G n

end Main

end P2mSemicontH0

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      n ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤)} :=
  P2mSemicontH0.main f M htriv n
