import RayProof2

/-! # rayclass-cft, Part P3: the core argument (one imaginary quadratic field `k`) -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

variable {k : Type} [Field k] [NumberField k]

/-- `q̂` on principal ideles is `q`. -/
theorem qHatU_unitEmbedding (q : k →ₐ[ℚ] LeafQM.B) (c : kˣ) :
    ((qHatU q (IdeleGroup.unitEmbedding (𝓞 k) k c) : BAQˣ) : BAQ) = bEmb (q c) := by
  show qHat q ((IdeleGroup.toFiniteIdele (𝓞 k) k (IdeleGroup.unitEmbedding (𝓞 k) k c) :
    FiniteAdeleRing (𝓞 k) k)) = bEmb (q c)
  rw [IdeleGroup.toFiniteIdele_unitEmbedding, FiniteAdeleRing.unitEmbedding_apply, qHat_algebraMap]

/-- `nrd q(c) > 0` at a CM point (`ι(q(c))` is a real matrix with a non-real eigenvector). -/
theorem nrd_pos_of_cm (q : k →ₐ[ℚ] LeafQM.B) (κ : k →+* ℂ) (τ : UpperHalfPlane)
    (h : IsCMPoint q κ τ) (c : kˣ) : 0 < ShimuraGlue.nrdQ ℚ (q c) := by
  have hne : ShimuraGlue.nrdQ ℚ (q c) ≠ 0 :=
    nrd_ne_zero_of_mul (x := q c) (y := q ↑c⁻¹) (by rw [← map_mul, Units.mul_inv, map_one])
  have hdet := det_pos_of_eig τ.im_pos.ne' (h c) (by rw [det_iota]; exact_mod_cast hne)
  rw [det_iota] at hdet
  exact_mod_cast hdet

/-- **The core argument.** Let `Ψ` satisfy the Deligne body, `𝒪̂^×` have class number one, `k` be
imaginary quadratic with `QHatIntegral k`, and `y` a `ℚ̄`-point such that at every representative
`(τ, u)`, `u ∈ 𝒪̂^×`, of `ιC^* y` there is an embedding `q : k → B` with `q(𝒪_k) ⊆ 𝒪` and CM point `τ`.
Then `ℚ(y)` embeds into the ray class field of `k` of conductor `3`. -/
theorem embed_core {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (hb : DeligneBodyAt Y Φ Ψ)
    (hCN : ClassNumberOneB) (k : Type) [Field k] [NumberField k] [IsTotallyComplex k]
    (hk : Module.finrank ℚ k = 2) (hI : QHatIntegral k) (y : fieldPt Qbar ⟶ Y)
    (hcm : ∀ (τ : UpperHalfPlane) (u : BAQˣ), u ∈ OhatU → Ψ τ u = fieldMap ιC ≫ y →
      ∃ (q : k →ₐ[ℚ] LeafQM.B) (κ₀ : k →+* ℂ), (∀ x : 𝓞 k, InO (q x)) ∧ IsCMPoint q κ₀ τ) :
    Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (ShimuraGlue.Ray.mod3 k)) := by
  obtain ⟨hsurj, hfib, -, -, ε, δ, hrec⟩ := hb
  -- (a) a representative `(τ, u)` of `ιC^* y` with `u ∈ 𝒪̂^×` (class number one)
  obtain ⟨τ₀, g, hτ₀⟩ := hsurj (fieldMap ιC ≫ y)
  obtain ⟨γ, hγ, u, hu, hg⟩ := exists_pos_decomp hCN g
  let τ := (iotaGL (binv γ) (nrd_binv_pos hγ).ne') • τ₀
  have hτu : Ψ τ u = fieldMap ιC ≫ y := by
    rw [← hτ₀]; exact ((hfib τ₀ g τ u).2 (dcRel_of_decomp hγ τ₀ hg)).symm
  -- (b) the CM data at `τ`
  obtain ⟨q, κ₀, hqO, hcmτ⟩ := hcm τ u hu hτu
  -- (c) the reflex embedding in the convention `δ`
  let κ : k →+* ℂ := if δ then κ₀ else (starRingEnd ℂ).comp κ₀
  have hκκ : (if δ then κ else (starRingEnd ℂ).comp κ) = κ₀ := by
    cases δ <;> ext a <;> simp [κ]
  -- (d) the ray class field `L` and an embedding `j : L → ℚ̄` over `κ`
  let L := rayClassField (ShimuraGlue.Ray.mod3 k)
  letI : Algebra k ℂ := κ.toAlgebra
  let j' : L →ₐ[k] ℂ := IsAlgClosed.lift
  have hj' : (j' : L →+* ℂ).comp (algebraMap k L) = κ := by
    ext a; exact j'.commutes a
  obtain ⟨j, hj⟩ := exists_lift_ringHom (L := L) (j' : L →+* ℂ)
  let jA : L →ₐ[ℚ] Qbar := j.toRatAlgHom
  let F : IntermediateField ℚ Qbar := jA.fieldRange
  -- (e) every `σ ∈ Gal(ℚ̄/F)` fixes `y`
  have hfix : ∀ σ ∈ F.fixingSubgroup,
      Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y.left = y.left := by
    intro σ hσ
    obtain ⟨σC, hσC⟩ := exists_ringEquiv_extend (ιC : Qbar →+* ℂ) σ.toRingEquiv
    have hσC' : ∀ a, σC (ιC a) = ιC (σ a) := fun a => hσC a
    have hσF : ∀ x : L, σ (j x) = j x := fun x =>
      (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ (j x) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    have hσL : ∀ x : L, σC (j' x) = j' x := fun x => by
      rw [show j' x = (j' : L →+* ℂ) x from rfl, ← hj, hσC', hσF]
    have hσκ : ∀ a : k, σC (κ a) = κ a := fun a => by
      have e : (j' : L →+* ℂ) (algebraMap k L a) = κ a := congrArg (fun f => f a) hj'
      have := hσL (algebraMap k L a)
      rw [show j' (algebraMap k L a) = (j' : L →+* ℂ) (algebraMap k L a) from rfl, e] at this
      exact this
    obtain ⟨s, hs⟩ := exists_artinCondC κ σC hσκ
    -- the Artin symbol of `s` is trivial on `L`
    have hart : ideleClassArtinMap k L (QuotientGroup.mk s) = 1 := by
      refine AlgEquiv.ext fun x => ?_
      apply (j' : L →+* ℂ).injective
      rw [AlgEquiv.one_apply, ← hs L (j' : L →+* ℂ) hj' x]
      exact hσL x
    have hray : ((s : IdeleGroup (𝓞 k) k) : IdeleClassGroup (𝓞 k) k) ∈
        raySubgroup (ShimuraGlue.Ray.mod3 k) := by
      have hker : (QuotientGroup.mk s : IdeleClassGroup (𝓞 k) k) ∈ (ideleClassArtinMap k L).ker := hart
      rw [ker_ideleClassArtinMap, range_ideleClassNormMap_rayClassField] at hker
      exact hker
    rw [mk_mem_raySubgroup_iff] at hray
    obtain ⟨s₀, hs₀, z, ⟨c, rfl⟩, hsz⟩ := Subgroup.mem_sup.1 hray
    -- Shimura's reciprocity law at `(τ, u)`
    have h4 := hrec k hk κ q τ (by rw [hκκ]; exact hcmτ) σC s hs u
    let c' : kˣ := c ^ (ε : ℤ)
    have hsε : s ^ (ε : ℤ) = IdeleGroup.unitEmbedding (𝓞 k) k c' * s₀ ^ (ε : ℤ) := by
      rw [← hsz, mul_zpow, map_zpow, mul_comm]
    have hX : qHatU q s ^ (ε : ℤ) * u = qHatU q (IdeleGroup.unitEmbedding (𝓞 k) k c') * u *
        (u⁻¹ * qHatU q (s₀ ^ (ε : ℤ)) * u) := by
      rw [← map_zpow, hsε, map_mul]; group
    have hk3 : u⁻¹ * qHatU q (s₀ ^ (ε : ℤ)) * u ∈ K3Q :=
      conj_mem_K3Q hu (hI q hqO _ (Subgroup.zpow_mem _ hs₀ _))
    have hdc : DCRel τ u τ (qHatU q s ^ (ε : ℤ) * u) := by
      refine dcRel_fix (nrd_pos_of_cm q κ₀ τ hcmτ c') τ (hcmτ c') u _ _ hk3 ?_
      rw [hX, Units.val_mul, Units.val_mul, qHatU_unitEmbedding]
    have hΨ : galPt σC (Ψ τ u) = Ψ τ u := by
      rw [h4]; exact ((hfib τ u τ _).2 hdc).symm
    rw [hτu, galPt_fieldMap y σ σC hσC'] at hΨ
    have h5 := congrArg CommaMorphism.left (fieldMap_ιC_inj hΨ)
    exact h5
  -- (f) `ℚ(y) ⊆ F ≅ L`
  have hle : residueImage (X := Y.left) y.left ≤ F := residueImage_le y.left F hfix
  exact ⟨((AlgEquiv.ofInjectiveField jA).symm.toAlgHom.comp
    (IntermediateField.inclusion hle)).toRingHom⟩

end RayClassCFT
