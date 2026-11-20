/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
p2m_open "TopologicalSpace Opposite Polynomial AlgebraicGeometry.Polynomial"

namespace P2mDegLead

open AlgebraicGeometry.OModulePresheaf

section Chi

variable {R : Type u} [CommRing R]

theorem eulerChar_eq_of_equiv {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (F' : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (hcard : Fintype.card K.ι = Fintype.card K'.ι)
    (h0 : Nonempty (F.H0 K ≃ₗ[R] F'.H0 K')) (hs : ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F'.HSucc K' i)) :
    F.eulerChar K = F'.eulerChar K' := by
  have h : ∀ i, F.cechFinrank K i = F'.cechFinrank K' i := by
    intro i
    cases i with
    | zero => obtain ⟨e⟩ := h0; exact e.finrank_eq
    | succ j => obtain ⟨e⟩ := hs j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def, hcard]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π') (X : V.Modules)
    (K : V.OrderedAffineCover) : (ofModules π X).eulerChar K = (ofModules π' X).eulerChar K := by
  subst h; rfl

theorem isQuasicoherent_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π') (X : V.Modules)
    (hq : (ofModules π' X).IsQuasicoherent) : (ofModules π X).IsQuasicoherent := by
  subst h; exact hq

end Chi

section PushUnit

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem preimage_eq_bot (U : V.Opens) (hU : (U : Set V) = ∅) : ι ⁻¹ᵁ U = ⊥ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hz
  have : ι.base z ∈ (U : Set V) := hz
  rw [hU] at this
  exact this

theorem subsingleton_sections_of_eq_bot (W : Z.Opens) (h : W = ⊥) : Subsingleton Γ(Z, W) := by
  subst h
  infer_instance

theorem supportedIn_top : (pushforwardUnit π ι).SupportedIn ⊤ := fun U hU =>
  subsingleton_sections_of_eq_bot (ι ⁻¹ᵁ U.1)
    (preimage_eq_bot ι U.1 (by simpa [Closeds.coe_top, Set.inter_univ] using hU))

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  show Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

theorem isCoherent [IsFinite ι] : (pushforwardUnit π ι).IsCoherent := by
  intro U
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := by
    ext a; exact appLE_rfl_apply ι U.1 a
  letI : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hfin' : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact hfin
    exact this
  exact hfin'

theorem loc_core [IsAffineHom ι] (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens) (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  haveI : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y = Z.presheaf.map (homOfLE hle).op y := fun y => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1)) (x : Γ(Z, ι ⁻¹ᵁ V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  show ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U f)).op y) := by
  show Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le ι U f))]

theorem isQuasicoherent [IsAffineHom ι] : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    rw [res_eq, smul_basicOpen]
    show Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
      Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
        (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x)
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hy
  · intro y hy
    rw [res_eq] at hy
    obtain ⟨n, hn⟩ := h2 y hy
    refine ⟨n, ?_⟩
    rw [smul_top]
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) * (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hn

end PushUnit

section Rank

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem finrank_comp_iso {X Y Y' : Scheme.{u}} (g : X ⟶ Y) [Flat g] [IsFinite g] (e : Y ≅ Y') (z : Y') :
    Scheme.Hom.finrank (g ≫ e.hom) z = Scheme.Hom.finrank g (e.inv.base z) := by
  have sq : IsPullback (𝟙 X) (g ≫ e.hom) g e.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z

theorem rankAtStalk_pushforwardUnit_obj [IsFinite ι] [Flat ι] (U : V.affineOpens) (r : ℕ)
    (hr : ∀ y : V, Scheme.Hom.finrank ι y = r) (𝔭 : PrimeSpectrum Γ(V, U.1)) :
    Module.rankAtStalk (R := Γ(V, U.1)) ((pushforwardUnit π ι).obj U.1) 𝔭 = r := by
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := Scheme.Hom.appLE_eq_app ι
  letI alg : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  haveI : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact IsFinite.finite_app ι U.1 U.2
    exact this
  haveI : Module.Flat Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) (f := ι) inferInstance U ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩ le_rfl
    exact this
  have key := Scheme.Hom.finrank_SpecMap_algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) 𝔭
  have hmap : CommRingCat.ofHom (algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1)) = ι.app U.1 := by
    rw [← heq]; rfl
  rw [hmap] at key

  have hU : IsAffineOpen U.1 := U.2
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have hnat : Spec.map (ι.app U.1) = hW.isoSpec.inv ≫ ((ι ∣_ U.1) ≫ hU.isoSpec.hom) := by
    rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  have hfr : Scheme.Hom.finrank (Spec.map (ι.app U.1)) 𝔭 = r := by
    rw [hnat, Scheme.Hom.finrank_comp_left_of_isIso, finrank_comp_iso,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict ι U.1).flip]
    exact hr _
  rw [hfr] at key
  exact key.symm

end Rank

section Setup

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

theorem krullDim_top_le (g : ℕ) [SmoothOfRelativeDimension g f] :
    topologicalKrullDim ((⊤ : Closeds A) : Set A) ≤ g :=
  (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g)

theorem exists_chart_prime [IsIntegral A] [Nonempty A] (𝒦 : A.OrderedAffineCover) :
    ∃ (U₀ : A.affineOpens) (𝔭 : PrimeSpectrum Γ(A, U₀.1)), (∃ i, U₀.1 = 𝒦.U i) ∧ 𝔭.asIdeal = ⊥ := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  have ha : a ∈ (⊤ : A.Opens) := trivial
  rw [← 𝒦.iSup_eq_top, Opens.mem_iSup] at ha
  obtain ⟨i, hi⟩ := ha
  haveI : Nonempty (𝒦.U i) := ⟨⟨a, hi⟩⟩
  exact ⟨⟨𝒦.U i, 𝒦.isAffineOpen i⟩, ⟨⊥, Ideal.isPrime_bot⟩, ⟨i, rfl⟩, rfl⟩

end Setup

section Chain

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem isInvertible_tensorPow {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (n : ℕ) :
    Scheme.Modules.IsInvertible (𝓛.tensorPowFLT n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unitFLT A
  | succ n ih => exact ih.tensor h𝓛

variable [IsSeparated f] (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f) [IsAffineHom γ.1]

include h𝓛 in

theorem eulerChar_twist_eq (m : ℕ) :
    ((pushforwardUnit f γ.1).twist (𝓛.tensorPowFLT m)).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 := by
  have hN : Scheme.Modules.IsInvertible (𝓛.tensorPowFLT m) := isInvertible_tensorPow h𝓛 m

  have e1 : ((pushforwardUnit f γ.1).twist (𝓛.tensorPowFLT m)).eulerChar 𝒦 =
      (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar (𝒦.comap γ.1) := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit f γ.1 𝒦 (𝓛.tensorPowFLT m) hN.1
    exact (eulerChar_eq_of_equiv (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)))
      ((pushforwardUnit f γ.1).twist (𝓛.tensorPowFLT m)) (𝒦.comap γ.1) 𝒦 rfl h0 hs).symm

  have e2 := eulerChar_ofModules_congr γ.2 ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)) (𝒦.comap γ.1)

  have hq : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial f _ (hN.pullback γ.1).1
  have e3 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar (𝒦.comap γ.1) =
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar 𝒦 := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f
      ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)) hq (𝒦.comap γ.1) 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)))
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))) (𝒦.comap γ.1) 𝒦 rfl h0 hs

  have e4 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso γ.1 𝓛 m
    obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso f e 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)))
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)) 𝒦 𝒦 rfl h0 hs
  rw [e1, e2, e3, e4]

end Chain

section Main

variable (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]
  (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f)
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
      L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
  (p q : Polynomial ℚ)
  (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
  (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPowFLT m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ))

include hA hγ hp hq h𝓛 in
theorem main : p.coeff g = (L.endDegree γ : ℚ) * q.coeff g := by
  classical
  haveI := hA.proper
  haveI := hA.smooth
  haveI : ConnectedSpace A := connectedSpace hA
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  by_cases hfin : IsFinite (L.endKerStr γ)
  swap
  ·
    rw [L.endDegree_of_not_isFinite γ hfin, Nat.cast_zero, zero_mul]
    exact RelativeGroupLaw.coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq K f L hA g 𝒦
      𝓛 h𝓛 γ hγ hfin p hp

  haveI := hfin
  haveI : IsFinite γ.1 := RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L γ hγ
  haveI : Flat γ.1 := AbelianSchemePropertyBundle.flat_of_isFinite K hA γ
  obtain ⟨-, -, hrank⟩ := RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat K f L γ

  set G : OModulePresheaf f := pushforwardUnit f γ.1 with hG
  have hGc : G.IsCoherent := isCoherent f γ.1
  have hGq : G.IsQuasicoherent := isQuasicoherent f γ.1
  have hGs : G.SupportedIn ⊤ := supportedIn_top f γ.1

  obtain ⟨p', -, hp'⟩ := exists_polynomial_forall_eulerChar_twist_tensorPow_eq f 𝒦 G hGc hGq ⊤ hGs g
    (krullDim_top_le (f := f) g) 𝓛 h𝓛.1

  have hpp : p' = p := by
    refine Polynomial.eq_of_infinite_eval_eq p' p
      ((Set.infinite_range_of_injective Nat.cast_injective).mono ?_)
    rintro _ ⟨m, rfl⟩
    show p'.eval (m : ℚ) = p.eval (m : ℚ)
    rw [← hp' m, ← hp m, hG, eulerChar_twist_eq f 𝒦 𝓛 h𝓛 γ m]

  obtain ⟨U₀, 𝔭, -, h𝔭⟩ := exists_chart_prime (A := A) 𝒦
  have hlead := coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq f 𝒦 𝓛 h𝓛.1 g
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g) q hq G hGc hGq p' hp' U₀ 𝔭 h𝔭
  have hrk : Module.rankAtStalk (R := Γ(A, U₀.1)) (G.obj U₀.1) 𝔭 = L.endDegree γ :=
    rankAtStalk_pushforwardUnit_obj f γ.1 U₀ (L.endDegree γ) (fun y => (hrank y).symm) 𝔭
  rw [← hpp, hlead, hrk]

end Main

end P2mDegLead

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (p q : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
        (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
    (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPowFLT m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ)) :
    p.coeff g = (L.endDegree γ : ℚ) * q.coeff g :=
  P2mDegLead.main K f L hA g 𝒦 𝓛 h𝓛 γ hγ p q hp hq

end S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq
end P2MW

