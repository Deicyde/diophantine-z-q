import Mathlib

namespace ZInQ.GRIsogDeg

open AlgebraicGeometry CategoryTheory Limits

universe u

theorem card_points_le_finrank {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsIntegral Y]
    {Ω : Type u} [Field Ω] (y₀ : Spec (.of Ω) ⟶ Y) (hy₀ : ∀ z, y₀ z = genericPoint Y)
    (hring : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
      [Module.Finite R S] (ψ₀ : R →+* Ω), Function.Injective ψ₀ → ∀ p : PrimeSpectrum R,
      p.asIdeal = ⊥ → Finite {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ∧
      Nat.card {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≤ Module.rankAtStalk S p) :
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y₀} ∧
    Nat.card {x : Spec (.of Ω) ⟶ X // x ≫ f = y₀} ≤ f.finrank (genericPoint Y) := by
  set η := genericPoint Y with hη
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx η
  let R := 𝒰.X i
  let u : Spec R ⟶ Y := 𝒰.f i
  have ht : u (𝒰.covers η).choose = η := (𝒰.covers η).choose_spec
  set t := (𝒰.covers η).choose with htdef
  have hrange : Set.range y₀ ⊆ Set.range u := by
    rintro _ ⟨z, rfl⟩; exact ⟨t, by rw [ht, hy₀]⟩
  let y₀' : Spec (.of Ω) ⟶ Spec R := IsOpenImmersion.lift u y₀ hrange
  have hfac : y₀' ≫ u = y₀ := IsOpenImmersion.lift_fac _ _ _
  let f' : pullback f u ⟶ Spec R := pullback.snd f u
  haveI : IsAffine (pullback f u) := isAffine_of_isAffineHom f'
  -- points of `X` over `y₀` are points of `pullback f u` over `y₀'`
  let toP : {x : Spec (.of Ω) ⟶ X // x ≫ f = y₀} →
      {x' : Spec (.of Ω) ⟶ pullback f u // x' ≫ f' = y₀'} := fun x =>
    ⟨pullback.lift x.1 y₀' (by rw [hfac, x.2]), pullback.lift_snd _ _ _⟩
  have htoP : Function.Injective toP := fun a b h => Subtype.ext (by
    have := congrArg (fun x' => x'.1 ≫ pullback.fst f u) h
    simpa [toP] using this)
  -- the ring map of `y₀'`
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ CommRingCat.of Ω, Spec.map φ = y₀' :=
    ⟨Spec.preimage y₀', Spec.map_preimage _⟩
  let R' := Γ(Spec R, ⊤)
  let S' := Γ(pullback f u, ⊤)
  let ψ₀ : R' →+* Ω := ((Scheme.ΓSpecIso R).hom ≫ φ).hom
  letI : Algebra R' S' := f'.appTop.hom.toAlgebra
  haveI : Module.Finite R' S' := f'.finite_appTop
  let toR : {x' : Spec (.of Ω) ⟶ pullback f u // x' ≫ f' = y₀'} →
      {ψ : S' →+* Ω // ψ.comp (algebraMap R' S') = ψ₀} := fun x' =>
    ⟨(x'.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom).hom, by
      have h1 : f'.appTop ≫ x'.1.appTop = y₀'.appTop := by
        rw [← Scheme.Hom.comp_appTop, x'.2]
      have h2 : f'.appTop ≫ x'.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom =
          (Scheme.ΓSpecIso R).hom ≫ φ := by
        rw [← Category.assoc, h1, ← hφ, Scheme.ΓSpecIso_naturality]
      exact congrArg CommRingCat.Hom.hom h2⟩
  have htoR : Function.Injective toR := fun a b h => Subtype.ext (by
    have h' : a.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom =
        b.1.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom :=
      CommRingCat.hom_ext (congrArg Subtype.val h)
    exact ext_of_isAffine ((cancel_mono _).mp h'))
  -- the point `p` of `Spec R'` under the generic point is the kernel of `ψ₀`, and it is `⊥`
  haveI : Nonempty (Spec R) := ⟨t⟩
  haveI : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion u
  let z₀ : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hz : y₀' z₀ = t := u.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hfac, hy₀, ht])
  set p : PrimeSpectrum R' := (Spec R).isoSpec.hom t with hpdef
  have hp_ker : p.asIdeal = RingHom.ker ψ₀ := by
    rw [hpdef, ← hz, ← hφ, Scheme.isoSpec_Spec_hom, ← Scheme.Hom.comp_apply, ← Spec.map_comp,
      Spec.map_apply]
    change Ideal.comap ψ₀ z₀.asIdeal = _
    rw [show z₀.asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
    rfl
  have hp_bot : p.asIdeal = ⊥ := by
    let q : PrimeSpectrum R' := ⟨⊥, Ideal.isPrime_bot⟩
    have hgen : ∀ s : Spec R, t ⤳ s := fun s =>
      (u.isOpenEmbedding.toIsInducing.specializes_iff).mp (by
        rw [ht]; exact (genericPoint_spec Y).specializes (Set.mem_univ _))
    have hpq : p ⤳ (Spec R).isoSpec.hom ((Spec R).isoSpec.inv q) :=
      (hgen _).map (Spec R).isoSpec.hom.continuous
    have e : (Spec R).isoSpec.hom ((Spec R).isoSpec.inv q) = q :=
      Scheme.inv_hom_apply (Spec R).isoSpec (q : Spec R')
    rw [e] at hpq
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes p q).mpr hpq)
  have hψ₀ : Function.Injective ψ₀ :=
    (RingHom.injective_iff_ker_eq_bot ψ₀).mpr (hp_ker ▸ hp_bot)
  obtain ⟨hfin, hcard⟩ := hring (S := S') ψ₀ hψ₀ p hp_bot
  have hfinP : Finite {x' : Spec (.of Ω) ⟶ pullback f u // x' ≫ f' = y₀'} :=
    Finite.of_injective _ htoR
  refine ⟨Finite.of_injective _ htoP, ?_⟩
  calc Nat.card {x : Spec (.of Ω) ⟶ X // x ≫ f = y₀}
      ≤ Nat.card {x' : Spec (.of Ω) ⟶ pullback f u // x' ≫ f' = y₀'} :=
        Nat.card_le_card_of_injective _ htoP
    _ ≤ Nat.card {ψ : S' →+* Ω // ψ.comp (algebraMap R' S') = ψ₀} :=
        Nat.card_le_card_of_injective _ htoR
    _ ≤ Module.rankAtStalk S' p := hcard
    _ = f.finrank η := rfl

end ZInQ.GRIsogDeg
