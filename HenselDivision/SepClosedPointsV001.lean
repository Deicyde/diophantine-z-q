import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.FieldTheory.IsSepClosed

/-!
# Points of étale schemes over a separably closed field

Let `k` be a separably closed field and `Ω ⊇ k` any field extension (for instance an algebraic
closure). For an étale `k`-algebra `A`, every `k`-algebra map `A → Ω` factors uniquely through
`k`: its kernel `𝔭` is maximal (`A` is artinian), `A/𝔭` is separable over `k`
(`Algebra.FormallyEtale` over a field), hence equal to `k`. Scheme form: for `X → Spec k` étale,
`X(k) → X(Ω)` is bijective, and relatively, for `f : X → Y` étale and `b : Spec k → Y`, every
`Ω`-point of `X` over `b` comes from a unique `k`-point over `b`.

For the special fibre of a group scheme over a strictly henselian local ring (separably closed
residue field) and an étale torsion scheme, this identifies residue-field torsion points with
geometric torsion points over an algebraic closure of the residue field.
-/

open CategoryTheory AlgebraicGeometry Limits IsLocalRing

namespace HenselDivision

universe u

/-- **Algebraic core.** -/
theorem etale_sepClosed_existsUnique_lift {k : Type u} [Field k] [IsSepClosed k]
    {A : Type u} [CommRing A] [Algebra k A] [Algebra.Etale k A]
    {Ω : Type u} [Field Ω] [Algebra k Ω] (φ : A →ₐ[k] Ω) :
    ∃! ψ : A →ₐ[k] k, (Algebra.ofId k Ω).comp ψ = φ := by
  let p : Ideal A := RingHom.ker φ
  have : p.IsPrime := RingHom.ker_isPrime φ
  have : Module.Finite k A := Algebra.FormallyUnramified.finite_of_free k A
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  have hsurj : Function.Surjective (algebraMap k (A ⧸ p)) :=
    IsSepClosed.algebraMap_surjective k (A ⧸ p)
  have hbij : Function.Bijective (Algebra.ofId k (A ⧸ p)) :=
    ⟨(algebraMap k (A ⧸ p)).injective, hsurj⟩
  let e : k ≃ₐ[k] A ⧸ p := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ p)) hbij
  let ψ : A →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k p)
  let φbar : A ⧸ p →ₐ[k] Ω := Ideal.kerLiftAlg φ
  have hex : (Algebra.ofId k Ω).comp ψ = φ := by
    ext a
    have h1 : φbar (Ideal.Quotient.mk p a) = φ a := Ideal.kerLiftAlg_mk φ a
    have h2 : Ideal.Quotient.mk p a = e (ψ a) := by
      simp [ψ]
    rw [AlgHom.comp_apply, ← h1, h2, AlgEquiv.ofBijective_apply, Algebra.ofId_apply,
      Algebra.ofId_apply, AlgHom.commutes]
  refine ⟨ψ, hex, ?_⟩
  intro ψ' hψ'
  ext a
  apply (algebraMap k Ω).injective
  have := AlgHom.congr_fun (hψ'.trans hex.symm) a
  simpa using this

lemma isLocalHom_ofHom_algebraMap_field (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] :
    IsLocalHom (CommRingCat.ofHom (algebraMap k Ω)).hom := by
  refine ⟨fun a ha => isUnit_iff_ne_zero.mpr ?_⟩
  rintro rfl
  simp at ha

/-- **Points of an étale `k`-scheme with values in a field extension are `k`-rational.** -/
theorem etale_sepClosed_point_existsUnique {k : Type u} [Field k] [IsSepClosed k]
    {Ω : Type u} [Field Ω] [Algebra k Ω] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Etale p] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃! y : Spec (CommRingCat.of k) ⟶ X,
      y ≫ p = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ y = x := by
  have : IsLocalHom (CommRingCat.ofHom (algebraMap k Ω)).hom :=
    isLocalHom_ofHom_algebraMap_field k Ω
  have hπpt : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) (closedPoint (CommRingCat.of Ω)) =
      closedPoint (CommRingCat.of k) := Spec_closedPoint
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (closedPoint (CommRingCat.of Ω)))) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have hrange : ∀ {T : CommRingCat.{u}} [IsLocalRing T] (f : Spec T ⟶ X),
      f (closedPoint T) ∈ U → Set.range f ⊆ Set.range hU.fromSpec := by
    intro T _ f hf
    rintro _ ⟨y, rfl⟩
    rw [hU.range_fromSpec]
    have hy : y ∈ f ⁻¹ᵁ U := by
      rw [Scheme.preimage_eq_top_of_closedPoint_mem f hf]; trivial
    exact hy
  let θ : CommRingCat.of k ⟶ Γ(X, U) := Spec.preimage (hU.fromSpec ≫ p)
  have hθ : Spec.map θ = hU.fromSpec ≫ p := Spec.map_preimage _
  have hθe : θ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hθ]; infer_instance
  letI : Algebra k Γ(X, U) := θ.hom.toAlgebra
  have : Algebra.Etale k Γ(X, U) := hθe
  let x' : Spec (CommRingCat.of Ω) ⟶ Spec Γ(X, U) :=
    IsOpenImmersion.lift hU.fromSpec x (hrange x hxU)
  have hx' : x' ≫ hU.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let ψ0 : Γ(X, U) ⟶ CommRingCat.of Ω := Spec.preimage x'
  have hψ0 : Spec.map ψ0 = x' := Spec.map_preimage _
  have hcompat : θ ≫ ψ0 = CommRingCat.ofHom (algebraMap k Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ0, hθ, ← Category.assoc, hx', hx]
  let φ : Γ(X, U) →ₐ[k] Ω :=
    { ψ0.hom with
      commutes' := fun r => by
        have h := congrArg (fun h => h.hom r) hcompat
        exact h }
  obtain ⟨ψ, hψ, huniq⟩ := etale_sepClosed_existsUnique_lift (k := k) (A := Γ(X, U)) φ
  let ψc : Γ(X, U) ⟶ CommRingCat.of k := CommRingCat.ofHom ψ.toRingHom
  have hθψ : θ ≫ ψc = 𝟙 _ := by
    apply CommRingCat.hom_ext
    ext r
    exact ψ.commutes r
  have hψres : ψc ≫ CommRingCat.ofHom (algebraMap k Ω) = ψ0 := by
    apply CommRingCat.hom_ext
    ext a
    exact AlgHom.congr_fun hψ a
  refine ⟨Spec.map ψc ≫ hU.fromSpec, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp, hθψ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψres, hψ0, hx']
  · rintro y ⟨hy1, hy2⟩
    have key : y (closedPoint (CommRingCat.of k)) = x (closedPoint (CommRingCat.of Ω)) := by
      have h0 := Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) y
        (closedPoint (CommRingCat.of Ω))
      rw [hy2] at h0
      have e := congrArg y hπpt
      exact e.symm.trans h0.symm
    have hypt : y (closedPoint (CommRingCat.of k)) ∈ U := by
      rw [key]; exact hxU
    let y' := IsOpenImmersion.lift hU.fromSpec y (hrange y hypt)
    have hy' : y' ≫ hU.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
    let φ0 : Γ(X, U) ⟶ CommRingCat.of k := Spec.preimage y'
    have hφ0 : Spec.map φ0 = y' := Spec.map_preimage _
    have hθφ0 : θ ≫ φ0 = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ0, hθ, ← Category.assoc, hy', hy1, Spec.map_id]
    have hres0 : φ0 ≫ CommRingCat.ofHom (algebraMap k Ω) = ψ0 := by
      apply Spec.map_injective
      rw [Spec.map_comp, hψ0, hφ0]
      apply (cancel_mono hU.fromSpec).mp
      rw [Category.assoc, hy', hx']
      exact hy2
    let φ0a : Γ(X, U) →ₐ[k] k :=
      { φ0.hom with
        commutes' := fun r => by
          have h := congrArg (fun h => h.hom r) hθφ0
          exact h }
    have hφ0a : (Algebra.ofId k Ω).comp φ0a = φ := by
      ext a
      have h := congrArg (fun h => h.hom a) hres0
      exact h
    have heq : φ0a = ψ := huniq φ0a hφ0a
    have hφ0c : φ0 = ψc := by
      apply CommRingCat.hom_ext
      ext a
      exact AlgHom.congr_fun heq a
    rw [← hy', ← hφ0, hφ0c]

/-- **Relative form.** `f : X → Y` étale, `b : Spec k → Y`, `k` separably closed, `Ω ⊇ k`: every
`Ω`-point of `X` over `b` comes from a unique `k`-point of `X` over `b`. -/
theorem etale_sepClosed_relative_point_existsUnique {k : Type u} [Field k] [IsSepClosed k]
    {Ω : Type u} [Field Ω] [Algebra k Ω] {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (b : Spec (CommRingCat.of k) ⟶ Y) (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ b) :
    ∃! y : Spec (CommRingCat.of k) ⟶ X,
      y ≫ f = b ∧ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ y = x := by
  have : Etale (pullback.snd f b) :=
    MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback f b) ‹Etale f›
  let x₁ : Spec (CommRingCat.of Ω) ⟶ pullback f b :=
    pullback.lift x (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) hx
  have hx₁ : x₁ ≫ pullback.snd f b = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) :=
    pullback.lift_snd _ _ _
  obtain ⟨s, ⟨hs1, hs2⟩, huniq⟩ := etale_sepClosed_point_existsUnique (pullback.snd f b) x₁ hx₁
  refine ⟨s ≫ pullback.fst f b, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]
  · rw [← Category.assoc, hs2, pullback.lift_fst]
  · rintro y ⟨hy1, hy2⟩
    let t : Spec (CommRingCat.of k) ⟶ pullback f b :=
      pullback.lift y (𝟙 _) (by rw [hy1, Category.id_comp])
    have ht1 : t ≫ pullback.snd f b = 𝟙 _ := pullback.lift_snd _ _ _
    have ht2 : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ t = x₁ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hy2]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
    have := huniq t ⟨ht1, ht2⟩
    rw [← this, pullback.lift_fst]

end HenselDivision

#check @HenselDivision.etale_sepClosed_existsUnique_lift
#check @HenselDivision.etale_sepClosed_point_existsUnique
#check @HenselDivision.etale_sepClosed_relative_point_existsUnique
#print axioms HenselDivision.etale_sepClosed_existsUnique_lift
#print axioms HenselDivision.etale_sepClosed_point_existsUnique
#print axioms HenselDivision.etale_sepClosed_relative_point_existsUnique
