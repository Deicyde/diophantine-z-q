import Mathlib

noncomputable section

namespace ZInQ.Contrib.G9.RankOnePeriod

open Module

section Coordinates

variable {K B G V I : Type*} [Field K] [Field B] [Algebra K B] [AddCommGroup V]
  [Module K V] [Fintype I]

/-- In a comparison basis of equivariant maps, all coefficients of an equivariant map are fixed. -/
theorem finrank_equivariantHom_of_basis
    (S : Set G) (a : G → B →+* B) (r : G → V →ₗ[K] V)
    (hr : ∀ g, Function.Surjective (r g))
    (D : Submodule K (V →ₗ[K] B)) (F : Submodule K B) [FiniteDimensional K F]
    (hD : ∀ f : V →ₗ[K] B, f ∈ D ↔ ∀ g ∈ S, ∀ v, f (r g v) = a g (f v))
    (hF : ∀ z : B, z ∈ F ↔ ∀ g ∈ S, a g z = z)
    (b : Basis I B (V →ₗ[K] B)) (hb : ∀ i, b i ∈ D) :
    finrank K D = Fintype.card I * finrank K F := by
  classical
  have mem_iff (f : V →ₗ[K] B) : f ∈ D ↔ ∀ i, b.equivFun f i ∈ F := by
    let c := b.equivFun f
    have he : (∑ i, c i • b i) = f := b.sum_equivFun f
    constructor
    · intro hf i
      apply (hF _).2
      intro g hg
      have heq : ∑ j, (a g (c j) - c j) • b j = 0 := by
        ext v
        obtain ⟨u, rfl⟩ := hr g v
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
          sub_mul, Finset.sum_sub_distrib]
        apply sub_eq_zero.mpr
        have h := (hD _).1 hf g hg u
        rw [← he] at h
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul] at h
        simpa only [← (hD _).1 (hb _) g hg] using h.symm
      exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp b.linearIndependent _ heq i)
    · intro hf
      apply (hD _).2
      intro g hg v
      rw [← he]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul]
      exact Finset.sum_congr rfl fun i _ => by
        rw [(hD _).1 (hb i) g hg, (hF _).1 (hf i) g hg]
  let inc : (I → F) →ₗ[K] (I → B) := F.subtype.compLeft I
  let fromCoeffs : (I → F) →ₗ[K] (V →ₗ[K] B) :=
    (b.equivFun.symm.toLinearMap.restrictScalars K).comp inc
  have hfrom (d : I → F) : fromCoeffs d ∈ D := by
    apply (mem_iff _).2
    intro i
    change b.equivFun (b.equivFun.symm (inc d)) i ∈ F
    rw [LinearEquiv.apply_symm_apply]
    exact (d i).2
  let e := fromCoeffs.codRestrict D hfrom
  have he : Function.Bijective e := by
    constructor
    · intro u v huv
      have h := congrArg (fun z : D => b.equivFun z.1) huv
      change b.equivFun (b.equivFun.symm (inc u)) = b.equivFun (b.equivFun.symm (inc v)) at h
      simp only [LinearEquiv.apply_symm_apply] at h
      funext i
      exact Subtype.ext (congrFun h i)
    · intro f
      let d : I → F := fun i => ⟨b.equivFun f.1 i, (mem_iff _).1 f.2 i⟩
      refine ⟨d, Subtype.ext ?_⟩
      change b.equivFun.symm (b.equivFun f.1) = f.1
      exact b.equivFun.symm_apply_apply _
  rw [← (LinearEquiv.ofBijective e he).finrank_eq, Module.finrank_pi_fintype]
  simp

end Coordinates

section EmbeddingBasis

variable {K E B V : Type*} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
  [IsGalois K E] [Field B] [Algebra K B] [AddCommGroup V] [Module K V]

open scoped Classical in
/-- The distinct coefficient embeddings, rescaled by arbitrary nonzero factors, form a basis. -/
theorem exists_scaledEmbeddings_basis
    (ι : E →ₐ[K] B) (e : V ≃ₗ[K] E) (d : (E ≃ₐ[K] E) → B)
    (hd : ∀ τ, d τ ≠ 0) :
    ∃ b : Basis (E ≃ₐ[K] E) B (V →ₗ[K] B),
      ∀ τ v, b τ v = d τ * ι (τ (e v)) := by
  let embed : (E ≃ₐ[K] E) → E →ₐ[K] B := fun τ => ι.comp τ.toAlgHom
  have hinj : Function.Injective embed := by
    intro τ η h
    ext x
    apply ι.injective
    exact DFunLike.congr_fun h x
  let q := (LinearEquiv.congrLeft B B e).symm
  have hli : LinearIndependent B (fun τ => q (embed τ).toLinearMap) :=
    ((linearIndependent_toLinearMap K E B).comp embed hinj).map' q.toLinearMap q.ker
  let w : (E ≃ₐ[K] E) → Bˣ := fun τ => Units.mk0 (d τ) (hd τ)
  have hw := hli.units_smul w
  let a : (E ≃ₐ[K] E) → (V →ₗ[K] B) := fun τ => (w τ : B) • q (embed τ).toLinearMap
  have hfin : Fintype.card (E ≃ₐ[K] E) = finrank B (V →ₗ[K] B) := by
    let z := (Module.finBasis K E).constr (M' := B) B
    rw [← q.finrank_eq, ← z.finrank_eq, Module.finrank_fin_fun,
      ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let b := Basis.mk hw (hw.span_eq_top_of_card_eq_finrank hfin).ge
  refine ⟨b, fun τ v => ?_⟩
  rw [show b τ = a τ from congrFun (Basis.coe_mk hw (hw.span_eq_top_of_card_eq_finrank hfin).ge) τ]
  rfl

end EmbeddingBasis

end ZInQ.Contrib.G9.RankOnePeriod
