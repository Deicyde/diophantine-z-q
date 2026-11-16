/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Module_Flat_isOpen_setOf_flat_localization_atPrime
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Module_Flat_isOpen_setOf_flat_localization_atPrime

open TensorProduct

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

namespace OpenFlatLocus

section Tors

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (S : Submonoid B) (Bs : Type*) [CommRing Bs] [Algebra B Bs] [Algebra A Bs]
  [IsScalarTower A B Bs] [IsLocalization S Bs]
variable {Y' Y : Type*} [AddCommGroup Y'] [Module A Y'] [AddCommGroup Y] [Module A Y]
  (f : Y' →ₗ[A] Y)

def K : Submodule B (B ⊗[A] Y') := LinearMap.ker (AlgebraTensorModule.lTensor B B f)

lemma mem_K (k : B ⊗[A] Y') : k ∈ K f ↔ LinearMap.lTensor B f k = 0 := by
  simp [K, LinearMap.mem_ker]

theorem injective_lTensor_iff :
    Function.Injective (LinearMap.lTensor Bs f) ↔ ∀ k ∈ K (B := B) f, ∃ s ∈ S, s • k = 0 := by
  let g : B →ₗ[B] Bs := Algebra.linearMap B Bs
  haveI : IsLocalizedModule S g := inferInstance
  let GX := AlgebraTensorModule.rTensor A Y' g
  let GY := AlgebraTensorModule.rTensor A Y g
  haveI hX : IsLocalizedModule S GX := inferInstance
  haveI hY : IsLocalizedModule S GY := inferInstance
  have hmap : IsLocalizedModule.map S GX GY (AlgebraTensorModule.lTensor B B f) =
      AlgebraTensorModule.lTensor B Bs f := IsLocalizedModule.map_lTensor B S f g
  constructor
  · intro hinj k hk
    rw [mem_K] at hk
    have h1 : AlgebraTensorModule.lTensor B Bs f (GX k) = 0 := by
      rw [← hmap, IsLocalizedModule.map_apply, AlgebraTensorModule.coe_lTensor, hk, map_zero]
    rw [AlgebraTensorModule.coe_lTensor] at h1
    have h2 : GX k = 0 := hinj (by rw [h1, map_zero])
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S GX).mp h2
    exact ⟨s, s.2, hs⟩
  · intro htors
    refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    obtain ⟨⟨k, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S GX z
    simp only [Function.uncurry_apply_pair] at hz ⊢
    have h1 : IsLocalizedModule.mk' GY (AlgebraTensorModule.lTensor B B f k) s = 0 := by
      rw [← IsLocalizedModule.map_mk' S GX GY, hmap, AlgebraTensorModule.coe_lTensor, hz]
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.mk'_eq_zero' GY s).mp h1
    have h2 : s'.1 • k ∈ K (B := B) f := by
      rw [mem_K, ← AlgebraTensorModule.coe_lTensor (A := B), map_smul]
      exact hs'
    obtain ⟨s'', hs''S, hs''⟩ := htors _ h2
    rw [IsLocalizedModule.mk'_eq_zero' GX s]
    refine ⟨⟨s'', hs''S⟩ * s', ?_⟩
    rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact hs''

lemma injective_rTensor_iff : Function.Injective (LinearMap.rTensor Bs f) ↔
    Function.Injective (LinearMap.lTensor Bs f) := by
  have : LinearMap.rTensor Bs f =
      (TensorProduct.comm A Bs Y).toLinearMap ∘ₗ LinearMap.lTensor Bs f ∘ₗ
        (TensorProduct.comm A Y' Bs).toLinearMap := by
    ext; simp
  rw [this]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp]

end Tors

section FlatIff

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

def Tors (Q : PrimeSpectrum B) {Y' Y : Type*} [AddCommGroup Y'] [Module A Y'] [AddCommGroup Y]
    [Module A Y] (f : Y' →ₗ[A] Y) : Prop :=
  ∀ k ∈ K (B := B) f, ∃ s ∈ Q.asIdeal.primeCompl, s • k = 0

lemma Tors.mono {Q Q' : PrimeSpectrum B} (h : Q'.asIdeal ≤ Q.asIdeal) {Y' Y : Type*}
    [AddCommGroup Y'] [Module A Y'] [AddCommGroup Y] [Module A Y] {f : Y' →ₗ[A] Y}
    (hQ : Tors Q f) : Tors Q' f := fun k hk => by
  obtain ⟨s, hs, hsk⟩ := hQ k hk
  exact ⟨s, fun h' => hs (h h'), hsk⟩

theorem tors_of_flat (Q : PrimeSpectrum B) [Module.Flat A (Localization.AtPrime Q.asIdeal)]
    {Y' Y : Type*} [AddCommGroup Y'] [Module A Y'] [AddCommGroup Y] [Module A Y]
    (f : Y' →ₗ[A] Y) (hf : Function.Injective f) : Tors Q f :=
  (injective_lTensor_iff Q.asIdeal.primeCompl (Localization.AtPrime Q.asIdeal) f).mp
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)

theorem flat_of_tors [IsNoetherianRing A] [IsNoetherianRing B] (Q : PrimeSpectrum B)
    (p : Ideal A) (hp : Q.asIdeal.comap (algebraMap A B) = p)
    (hQ : Tors (A := A) (Y' := ↥p) (Y := A) Q p.subtype) :
    Module.Flat A (Localization.AtPrime Q.asIdeal) := by
  have hinj : Function.Injective (LinearMap.lTensor (Localization.AtPrime Q.asIdeal) p.subtype) :=
    (injective_lTensor_iff Q.asIdeal.primeCompl (Localization.AtPrime Q.asIdeal) p.subtype).mpr hQ
  rw [← injective_rTensor_iff] at hinj
  refine Module.flat_of_comap_maximalIdeal_rTensor_injective
    (S := Localization.AtPrime Q.asIdeal) p ?_ hinj
  rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime Q.asIdeal), ← Ideal.comap_comap]
  have h := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime Q.asIdeal) Q.asIdeal
  rw [Ideal.under] at h
  rw [h, hp]

theorem flat_of_le [IsNoetherianRing A] [IsNoetherianRing B] {Q Q' : PrimeSpectrum B}
    (h : Q'.asIdeal ≤ Q.asIdeal) [Module.Flat A (Localization.AtPrime Q.asIdeal)] :
    Module.Flat A (Localization.AtPrime Q'.asIdeal) :=
  flat_of_tors Q' (Q'.asIdeal.comap (algebraMap A B)) rfl
    ((tors_of_flat (Y' := ↥(Q'.asIdeal.comap (algebraMap A B))) (Y := A) Q
      (Q'.asIdeal.comap (algebraMap A B)).subtype Subtype.val_injective).mono h)

end FlatIff

section Nagata

variable {B : Type*} [CommRing B] [IsNoetherianRing B]

theorem isOpen_of_nagata (U : Set (PrimeSpectrum B))
    (hgen : ∀ Q Q' : PrimeSpectrum B, Q'.asIdeal ≤ Q.asIdeal → Q ∈ U → Q' ∈ U)
    (hnbhd : ∀ Q ∈ U, ∃ g : B, g ∉ Q.asIdeal ∧
      ∀ Q' : PrimeSpectrum B, Q.asIdeal ≤ Q'.asIdeal → g ∉ Q'.asIdeal → Q' ∈ U) :
    IsOpen U := by
  classical

  rw [← isClosed_compl_iff]
  set Z := Uᶜ with hZ
  set J := PrimeSpectrum.vanishingIdeal Z with hJ
  have hZsub : Z ⊆ PrimeSpectrum.zeroLocus (J : Set B) :=
    PrimeSpectrum.subset_zeroLocus_vanishingIdeal Z
  have hJle : ∀ x ∈ PrimeSpectrum.zeroLocus (J : Set B), J ≤ x.asIdeal := fun x hx =>
    (PrimeSpectrum.mem_zeroLocus x J).mp hx
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B J

  have hmin : ∀ q (hq : q ∈ J.minimalPrimes), (⟨q, hq.1.1⟩ : PrimeSpectrum B) ∈ Z := by
    intro q hq
    by_contra hqZ
    have hqU : (⟨q, hq.1.1⟩ : PrimeSpectrum B) ∈ U := Set.notMem_compl_iff.mp hqZ
    obtain ⟨g, hgq, hg⟩ := hnbhd _ hqU
    let others : Finset (Ideal B) := hfin.toFinset.erase q

    have hprod : (others.prod id) * (q ⊔ Ideal.span {g}) ≤ J := by
      intro b hb
      rw [hJ, PrimeSpectrum.mem_vanishingIdeal]
      intro x hxZ
      obtain ⟨q', hq', hq'x⟩ := Ideal.exists_minimalPrimes_le (hJle x (hZsub hxZ))
      by_cases hqq' : q' = q
      · subst hqq'
        have hgx : g ∈ x.asIdeal := by
          by_contra hgx
          exact hxZ (hg x hq'x hgx)
        have hle : (others.prod id) * (q' ⊔ Ideal.span {g}) ≤ x.asIdeal :=
          Ideal.mul_le_right.trans (sup_le hq'x ((Ideal.span_singleton_le_iff_mem _).mpr hgx))
        exact hle hb
      · have hmem : q' ∈ others := Finset.mem_erase.mpr ⟨hqq', hfin.mem_toFinset.mpr hq'⟩
        have hle : (others.prod id) * (q ⊔ Ideal.span {g}) ≤ x.asIdeal :=
          Ideal.mul_le_left.trans
            ((Ideal.prod_le_inf.trans (Finset.inf_le (f := id) hmem)).trans hq'x)
        exact hle hb
    have hqJ : J ≤ q := hq.1.2
    rcases hq.1.1.mul_le.mp (hprod.trans hqJ) with h | h
    · obtain ⟨q', hq'mem, hq'le⟩ := (Ideal.IsPrime.prod_le hq.1.1).mp h
      obtain ⟨hne, hq'min⟩ := Finset.mem_erase.mp hq'mem
      have hq'min' : q' ∈ J.minimalPrimes := hfin.mem_toFinset.mp hq'min
      have hqq' : q ≤ q' := hq.2 ⟨hq'min'.1.1, hq'min'.1.2⟩ hq'le
      exact hne (le_antisymm hq'le hqq')
    · exact hgq (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))

  have hZeq : Z = PrimeSpectrum.zeroLocus (J : Set B) := by
    refine subset_antisymm hZsub fun x hx => ?_
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (hJle x hx)
    by_contra hxZ
    have hxU : x ∈ U := Set.notMem_compl_iff.mp hxZ
    exact hmin q hq (hgen x ⟨q, hq.1.1⟩ hqx hxU)
  rw [hZeq]
  exact PrimeSpectrum.isClosed_zeroLocus _

end Nagata

section Fibre

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem exists_uniform_killer {N : Type*} [AddCommGroup N] [Module B N] (S : Submonoid B)
    (K : Submodule B N) (hK : K.FG) (h : ∀ k ∈ K, ∃ s ∈ S, s • k = 0) :
    ∃ s ∈ S, ∀ k ∈ K, s • k = 0 := by
  classical
  obtain ⟨t, rfl⟩ := hK
  induction t using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun k hk => by simp_all⟩
  | insert x t hx ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := ih (fun k hk => h k (Submodule.span_mono (by simp) hk))
    obtain ⟨s₂, hs₂, h₂⟩ := h x (Submodule.subset_span (by simp))
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, fun k hk => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hk
    obtain ⟨c, z, hz, rfl⟩ := hk
    rw [smul_add, mul_smul, smul_comm s₂ c x, h₂, smul_zero, smul_zero, zero_add, mul_comm, mul_smul,
      h₁ z hz, smul_zero]

section FibreAway

variable (p : Ideal A) (a : A)

-- [port] local notation `A'` removed (build-time syntax); its uses below are expanded to `(A ⧸ p)`
-- [port] local notation `C` removed (build-time syntax); its uses below are expanded to `((A ⧸ p) ⊗[A] B)`
-- [port] local notation `Ba` removed (build-time syntax); its uses below are expanded to `(Localization.Away (algebraMap A B a))`
-- [port] local notation `F` removed (build-time syntax); its uses below are expanded to `((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a))`

set_option maxHeartbeats 6400000 in

theorem flat_fibre_away
    (hflat : Module.Flat (A ⧸ p) (Localization (Submonoid.powers
      (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a))))) :
    Module.Flat (A ⧸ p) ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) := by
  set c : ((A ⧸ p) ⊗[A] B) := algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a) with hc
  have hc' : c = (1 : (A ⧸ p)) ⊗ₜ algebraMap A B a := by
    rw [hc, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

  let ψ₀ : ((A ⧸ p) ⊗[A] B) →ₐ[(A ⧸ p)] ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) := Algebra.TensorProduct.map (AlgHom.id (A ⧸ p) (A ⧸ p)) (IsScalarTower.toAlgHom A B (Localization.Away (algebraMap A B a)))
  have hψ₀ : ∀ (x : (A ⧸ p)) (b : B), ψ₀ (x ⊗ₜ b) = x ⊗ₜ algebraMap B (Localization.Away (algebraMap A B a)) b := fun x b => by
    simp only [ψ₀, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  have hu : IsUnit (algebraMap B (Localization.Away (algebraMap A B a)) (algebraMap A B a)) :=
    IsLocalization.Away.algebraMap_isUnit (algebraMap A B a)
  have hunit : ∀ y : Submonoid.powers c, IsUnit (ψ₀ y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    rw [hc', hψ₀]
    exact hu.map (Algebra.TensorProduct.includeRight (R := A) (A := (A ⧸ p)) (B := (Localization.Away (algebraMap A B a))))
  let φ : Localization (Submonoid.powers c) →ₐ[(A ⧸ p)] ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers c) (f := ψ₀) hunit
  have hφ : ∀ x : ((A ⧸ p) ⊗[A] B), φ (algebraMap ((A ⧸ p) ⊗[A] B) _ x) = ψ₀ x := fun x => by
    simp only [φ, IsLocalization.liftAlgHom_apply]
    exact IsLocalization.lift_eq (M := Submonoid.powers c) _ x

  let θ₀ : B →ₐ[A] Localization (Submonoid.powers c) :=
    (IsScalarTower.toAlgHom A ((A ⧸ p) ⊗[A] B) _).comp
      ((Algebra.TensorProduct.includeRight (R := A) (A := (A ⧸ p)) (B := B)).restrictScalars A)
  have hθ₀ : ∀ b, θ₀ b = algebraMap ((A ⧸ p) ⊗[A] B) (Localization (Submonoid.powers c)) ((1 : (A ⧸ p)) ⊗ₜ b) :=
    fun b => rfl
  have hunit' : ∀ y : Submonoid.powers (algebraMap A B a), IsUnit (θ₀ y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n ?_
    rw [hθ₀, ← hc']
    exact IsLocalization.Away.algebraMap_isUnit c
  let θ : (Localization.Away (algebraMap A B a)) →ₐ[A] Localization (Submonoid.powers c) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap A B a)) (f := θ₀) hunit'
  have hθ : ∀ b, θ (algebraMap B (Localization.Away (algebraMap A B a)) b) = θ₀ b := fun b => by
    simp only [θ, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl
  let χ : ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) →ₐ[(A ⧸ p)] Localization (Submonoid.powers c) :=
    Algebra.TensorProduct.lift (Algebra.ofId (A ⧸ p) _) θ (fun _ _ => Commute.all _ _)
  have hχ : ∀ (x : (A ⧸ p)) (y : (Localization.Away (algebraMap A B a))), χ (x ⊗ₜ y) = algebraMap (A ⧸ p) _ x * θ y := fun x y => by
    simp only [χ, Algebra.TensorProduct.lift_tmul]
    rfl

  have hχψ : ∀ x : ((A ⧸ p) ⊗[A] B), χ (ψ₀ x) = algebraMap ((A ⧸ p) ⊗[A] B) _ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hψ₀, hχ, hθ, hθ₀, ← Algebra.smul_def]
      have hxb : (x ⊗ₜ[A] b : ((A ⧸ p) ⊗[A] B)) = x • ((1 : (A ⧸ p)) ⊗ₜ[A] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hxb, ← Algebra.linearMap_apply ((A ⧸ p) ⊗[A] B) (Localization (Submonoid.powers c)),
        ← Algebra.linearMap_apply ((A ⧸ p) ⊗[A] B) (Localization (Submonoid.powers c)), LinearMap.map_smul_of_tower]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have h1 : ∀ z, χ (φ z) = z := by
    intro z
    have key : (χ.toRingHom.comp φ.toRingHom).comp (algebraMap ((A ⧸ p) ⊗[A] B) _) =
        (RingHom.id _).comp (algebraMap ((A ⧸ p) ⊗[A] B) (Localization (Submonoid.powers c))) := by
      ext x
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [hφ, hχψ]
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [hφ, hχψ]
    have h := IsLocalization.ringHom_ext (Submonoid.powers c) key
    exact congrArg (fun f : _ →+* _ => f z) h

  have h2 : ∀ y : ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)), φ (χ y) = y := by
    intro y
    have key : (φ.restrictScalars A).comp (χ.restrictScalars A) = AlgHom.id A ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) := by
      refine Algebra.TensorProduct.ext ?_ ?_
      · ext x
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeLeft_apply, AlgHom.coe_id, id_eq]
        rw [hχ, map_one, mul_one, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
      · refine IsLocalization.algHom_ext (Submonoid.powers (algebraMap A B a)) ?_
        ext b
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, AlgHom.coe_id, id_eq]
        change φ (χ ((1 : (A ⧸ p)) ⊗ₜ algebraMap B (Localization.Away (algebraMap A B a)) b)) = (1 : (A ⧸ p)) ⊗ₜ algebraMap B (Localization.Away (algebraMap A B a)) b
        rw [hχ, map_one, one_mul, hθ, hθ₀, hφ, hψ₀]
    exact congrArg (fun f : ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) →ₐ[A] ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) => f y) key
  let e : Localization (Submonoid.powers c) ≃ₗ[(A ⧸ p)] ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) :=
    { φ.toLinearMap with
      invFun := χ
      left_inv := h1
      right_inv := h2 }
  exact Module.Flat.of_linearEquiv e.symm

set_option maxHeartbeats 3200000 in

theorem injective_lTensor_away (X : Ideal (A ⧸ p)) [Module.Flat (A ⧸ p) ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a))] :
    Function.Injective (LinearMap.lTensor (Localization.Away (algebraMap A B a)) (X.subtype.restrictScalars A)) := by
  rw [← injective_rTensor_iff (Localization.Away (algebraMap A B a))]

  let eX := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ p) (A ⧸ p) (↥X) (Localization.Away (algebraMap A B a))
  let eA := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ p) (A ⧸ p) (A ⧸ p) (Localization.Away (algebraMap A B a))
  let f : (↥X) ⊗[A] (Localization.Away (algebraMap A B a)) →ₗ[(A ⧸ p)] (A ⧸ p) ⊗[A] (Localization.Away (algebraMap A B a)) := TensorProduct.AlgebraTensorModule.map X.subtype LinearMap.id
  have hf : (f : (↥X) ⊗[A] (Localization.Away (algebraMap A B a)) → (A ⧸ p) ⊗[A] (Localization.Away (algebraMap A B a))) = LinearMap.rTensor (Localization.Away (algebraMap A B a)) (X.subtype.restrictScalars A) := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [f]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsq : f ∘ₗ eX.toLinearMap = eA.toLinearMap ∘ₗ LinearMap.rTensor ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) X.subtype := by
    refine TensorProduct.ext' fun x y => ?_
    induction y using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | tmul a' b =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
        LinearMap.rTensor_tmul]
      erw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.map_tmul]
      rw [LinearMap.id_apply, map_smul, Submodule.subtype_apply]
    | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
  have hinj : Function.Injective (LinearMap.rTensor ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) X.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ X.injective_subtype
  have h2 : Function.Injective (f ∘ₗ eX.toLinearMap) := by
    rw [hsq]
    exact eA.injective.comp hinj
  rw [← hf]
  exact (Function.Injective.of_comp_iff' f eX.bijective).mp h2

end FibreAway

section Step

variable [IsNoetherianRing A] [Algebra.FiniteType A B]

set_option maxHeartbeats 6400000 in

theorem fibre_step (Q : PrimeSpectrum B) [Module.Flat A (Localization.AtPrime Q.asIdeal)] :
    ∃ g : B, g ∉ Q.asIdeal ∧ ∀ Q' : PrimeSpectrum B, Q.asIdeal ≤ Q'.asIdeal → g ∉ Q'.asIdeal →
      Module.Flat A (Localization.AtPrime Q'.asIdeal) := by
  classical
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  set p : Ideal A := Q.asIdeal.comap (algebraMap A B) with hpdef
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _

  have htors : Tors (A := A) (Y' := ↥p) (Y := A) Q p.subtype :=
    tors_of_flat (Y' := ↥p) (Y := A) Q p.subtype p.injective_subtype
  have hKfg : (K (B := B) (p.subtype)).FG := IsNoetherian.noetherian _
  obtain ⟨b, hbQ, hb⟩ := exists_uniform_killer Q.asIdeal.primeCompl (K (B := B) p.subtype) hKfg htors

  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  obtain ⟨abar, habar, hflat⟩ := Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    (A := A ⧸ p) (B := (A ⧸ p) ⊗[A] B) (M := (A ⧸ p) ⊗[A] B)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
  have hap : a ∉ p := fun h => habar (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have haQ : algebraMap A B a ∉ Q.asIdeal := hap
  haveI hF : Module.Flat (A ⧸ p) ((A ⧸ p) ⊗[A] Localization.Away (algebraMap A B a)) := by
    refine flat_fibre_away p a ?_
    exact Module.Flat.of_linearEquiv
      ((TensorProduct.rid ((A ⧸ p) ⊗[A] B) (Localization (Submonoid.powers
        (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a))))).restrictScalars (A ⧸ p)).symm
  refine ⟨algebraMap A B a * b, fun h => (Q.2.mem_or_mem h).elim haQ hbQ, fun Q' hQQ' hg => ?_⟩
  have haQ' : algebraMap A B a ∉ Q'.asIdeal := fun h => hg (Q'.asIdeal.mul_mem_right b h)
  have hbQ' : b ∉ Q'.asIdeal := fun h => hg (Q'.asIdeal.mul_mem_left _ h)
  set p' : Ideal A := Q'.asIdeal.comap (algebraMap A B) with hp'def
  have hpp' : p ≤ p' := Ideal.comap_mono hQQ'
  refine flat_of_tors Q' p' rfl fun k hk => ?_

  let X : Ideal (A ⧸ p) := p'.map (Ideal.Quotient.mk p)
  let π : ↥p' →ₗ[A] ↥X :=
    { toFun := fun x => ⟨Ideal.Quotient.mk p x, Ideal.mem_map_of_mem _ x.2⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (by
        simp only [SetLike.val_smul, smul_eq_mul, RingHom.id_apply, map_mul]
        rfl) }
  let ι : ↥p →ₗ[A] ↥p' := Submodule.inclusion hpp'
  let j : ↥X →ₗ[A] (A ⧸ p) := X.subtype.restrictScalars A
  have hexact : Function.Exact ι π := by
    intro x
    constructor
    · intro hx
      have hx' : Ideal.Quotient.mk p (x : A) = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, Ideal.Quotient.eq_zero_iff_mem.mp hx'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr z.2)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective).mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hjπ : j ∘ₗ π = (Ideal.Quotient.mkₐ A p).toLinearMap ∘ₗ p'.subtype := by ext; rfl
  have hιsub : p'.subtype ∘ₗ ι = p.subtype := by ext; rfl

  have hk0 : LinearMap.lTensor B p'.subtype k = 0 := (mem_K _ k).mp hk
  have hkbar : LinearMap.lTensor B π k ∈ K (B := B) j := by
    rw [mem_K, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hjπ, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hk0, map_zero]

  have hinj := injective_lTensor_away (B := B) p a X
  obtain ⟨s, ⟨n, rfl⟩, hs⟩ := (injective_lTensor_iff (Submonoid.powers (algebraMap A B a))
    (Localization.Away (algebraMap A B a)) j).mp hinj _ hkbar

  have h3 : LinearMap.lTensor B π ((algebraMap A B a ^ n) • k) = 0 := by
    rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B), map_smul,
      TensorProduct.AlgebraTensorModule.coe_lTensor, hs]
  obtain ⟨y, hy⟩ := (lTensor_exact B hexact hπsurj _).mp h3
  have hyK : y ∈ K (B := B) p.subtype := by
    rw [mem_K, ← hιsub, LinearMap.lTensor_comp, LinearMap.comp_apply, hy,
      ← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B), map_smul,
      TensorProduct.AlgebraTensorModule.coe_lTensor, hk0, smul_zero]
  have hby : b • y = 0 := hb y hyK
  refine ⟨b * algebraMap A B a ^ n, ?_, ?_⟩
  · intro hmem
    rcases Q'.2.mem_or_mem hmem with h | h
    · exact hbQ' h
    · exact haQ' (Q'.2.mem_of_pow_mem n h)
  · rw [mul_smul, ← hy, ← TensorProduct.AlgebraTensorModule.coe_lTensor (A := B), ← map_smul, hby,
      map_zero]

end Step

end Fibre

theorem isOpen_flatLocus {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine isOpen_of_nagata _ (fun Q Q' h hQ => ?_) (fun Q hQ => ?_)
  · haveI : Module.Flat A (Localization.AtPrime Q.asIdeal) := hQ
    exact flat_of_le h
  · haveI : Module.Flat A (Localization.AtPrime Q.asIdeal) := hQ
    exact fibre_step Q

end OpenFlatLocus

end

theorem solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} :=
  OpenFlatLocus.isOpen_flatLocus
