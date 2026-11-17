import ZInQKernel.HDecomp.Faltings.Leaves
import Mathlib
namespace ZInQ.GRIsogDeg

open TensorProduct

/-- Ring-level count: `S` finite over the domain `R`, `ψ₀ : R → Ω` injective into a field.
The ring maps `S → Ω` over `ψ₀` are finitely many, at most the rank of `S` at the zero prime. -/
theorem card_ringHom_le_rankAtStalk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Finite R S] {Ω : Type*} [Field Ω]
    (ψ₀ : R →+* Ω) (hψ₀ : Function.Injective ψ₀) (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    Finite {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ∧
    Nat.card {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≤ Module.rankAtStalk S p := by
  obtain ⟨P, hP⟩ := p
  dsimp only at hp
  subst hp
  let Rp := Localization.AtPrime (⊥ : Ideal R)
  have : IsFractionRing R Rp := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal R).primeCompl)
  letI : Algebra R Ω := ψ₀.toAlgebra
  have hunit : ∀ y : (⊥ : Ideal R).primeCompl, IsUnit (ψ₀ y) := fun y => by
    have hy : (y : R) ≠ 0 := fun h => y.2 (by rw [h]; exact Ideal.zero_mem _)
    exact ((map_ne_zero_iff ψ₀ hψ₀).mpr hy).isUnit
  let ψp : Rp →+* Ω := IsLocalization.lift hunit
  letI : Algebra Rp Ω := ψp.toAlgebra
  haveI : IsScalarTower R Rp Ω := IsScalarTower.of_algebraMap_eq fun r => by
    change ψ₀ r = ψp (algebraMap R Rp r)
    exact (IsLocalization.lift_eq hunit r).symm
  haveI : Module.Free Rp (Rp ⊗[R] S) := by
    let _ : Field Rp := IsFractionRing.toField R
    exact Module.Free.of_divisionRing _ _
  let toA : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} → (S →ₐ[R] Ω) := fun ψ =>
    AlgHom.mk ψ.1 (fun r => congrArg (fun g : R →+* Ω => g r) ψ.2)
  let e₁ : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≃ (S →ₐ[R] Ω) :=
    { toFun := toA
      invFun := fun f => ⟨f.toRingHom, RingHom.ext fun r => f.commutes r⟩
      left_inv := fun ψ => rfl
      right_inv := fun f => rfl }
  let e := e₁.trans (AlgHom.liftEquiv R Rp S Ω)
  have hfin : Finite (Rp ⊗[R] S →ₐ[Rp] Ω) := inferInstance
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Module.rankAtStalk_eq_finrank_tensorProduct]
  exact card_algHom_le_finrank Rp (Rp ⊗[R] S) Ω

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

section AbVar

open MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.DefFaltings (IsIsogeny isogDeg ptObj)
open PkgI3 (AbVar)

variable {K : Type} [Field K]

/-- An abelian variety is an integral scheme (geometrically integral over a field). -/
theorem isIntegral_left (A : AbVar K) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

/-- **The degree of `φ` as a finite morphism**: Mathlib's rank `Scheme.Hom.finrank` of `φ` (the rank
of `φ_* 𝒪_A` over `𝒪_B`, "sometimes also called the degree of a morphism", Stacks 02KA) at the
generic point of `B`. There the stalk of `B` is the function field `K(B)`, so for an isogeny this
is `[K(A) : K(B)]`, the degree of the dominant finite morphism `φ`, with no flatness needed. -/
noncomputable def finDeg {A B : AbVar K} (φ : A.X ⟶ B.X) : ℕ :=
  haveI := isIntegral_left B
  φ.left.finrank (genericPoint B.X.left)

/-- **`# ker φ(K̄) ≤ deg φ`** for every isogeny of abelian varieties over any field `K`
(the number of geometric points of the kernel is the separable degree). -/
theorem isogDeg_le_finDeg {A B : AbVar K} (φ : A.X ⟶ B.X) (hφ : IsIsogeny φ) :
    isogDeg φ ≤ finDeg φ := by
  haveI := isIntegral_left A
  haveI := isIntegral_left B
  obtain ⟨hmon, hfin, hsurj⟩ := hφ
  set ηA := genericPoint A.X.left
  let κ := A.X.left.residueField ηA
  let Ω := AlgebraicClosure κ
  let ξ₀ : Spec (.of Ω) ⟶ A.X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫ A.X.left.fromSpecResidueField ηA
  have hξ : ∀ z, ξ₀ z = ηA := fun z => by
    simp only [ξ₀, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hφη : φ.left ηA = genericPoint B.X.left := by
    have h1 := (genericPoint_spec A.X.left).image φ.left.continuous
    rw [Set.image_univ_of_surjective hsurj.surj, closure_univ] at h1
    exact h1.eq (genericPoint_spec B.X.left)
  have hy : ∀ z, (ξ₀ ≫ φ.left) z = genericPoint B.X.left := fun z => by
    rw [Scheme.Hom.comp_apply, hξ, hφη]
  -- `Ω` as a `K`-algebra, and the geometric generic point `ξ` as a `K`-point of `A`
  let σ : CommRingCat.of K ⟶ CommRingCat.of Ω := Spec.preimage (ξ₀ ≫ A.X.hom)
  letI : Algebra K Ω := σ.hom.toAlgebra
  let ξ : ptObj K Ω ⟶ A.X := Over.homMk ξ₀ (by
    change ξ₀ ≫ A.X.hom = Spec.map (CommRingCat.ofHom σ.hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
  -- an embedding `K̄ → Ω` over `K`
  let emb : AlgebraicClosure K →ₐ[K] Ω := IsAlgClosed.lift
  let embo : ptObj K Ω ⟶ ptObj K (AlgebraicClosure K) :=
    Over.homMk (Spec.map (CommRingCat.ofHom emb.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom emb.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω))
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact emb.commutes x)
  have hepi : Epi (Spec.map (CommRingCat.ofHom emb.toRingHom)) := by
    haveI : Flat (Spec.map (CommRingCat.ofHom emb.toRingHom)) := by
      rw [Flat.SpecMap_iff]
      exact RingHom.Flat.of_isField (Field.toIsField _) _
    haveI : Surjective (Spec.map (CommRingCat.ofHom emb.toRingHom)) :=
      ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  haveI := hmon
  haveI := hfin
  -- translation of `ξ` by the kernel points
  let Φ : {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1} →
      {x : Spec (.of Ω) ⟶ A.X.left // x ≫ φ.left = ξ₀ ≫ φ.left} := fun P =>
    ⟨(ξ * (embo ≫ P.1)).left, by
      have h : (ξ * (embo ≫ P.1)) ≫ φ = ξ ≫ φ := by
        rw [MonObj.mul_comp, Category.assoc, P.2, MonObj.comp_one, _root_.mul_one]
      have h' := congrArg CommaMorphism.left h
      simp only [Over.comp_left] at h'
      exact h'⟩
  have hΦ : Function.Injective Φ := fun P Q h => by
    have h1 : (ξ * (embo ≫ P.1) : ptObj K Ω ⟶ A.X) = ξ * (embo ≫ Q.1) := by
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val h
    have h2 := congrArg CommaMorphism.left (@mul_left_cancel (ptObj K Ω ⟶ A.X) _ _ _ _ _ h1)
    simp only [Over.comp_left] at h2
    change Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ P.1.left =
      Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ Q.1.left at h2
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact hepi.left_cancellation _ _ h2
  obtain ⟨hfinite, hcard⟩ := card_points_le_finrank φ.left (ξ₀ ≫ φ.left) hy
    (fun ψ₀ h p hp => card_ringHom_le_rankAtStalk ψ₀ h p hp)
  calc isogDeg φ = Nat.card {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1} := rfl
    _ ≤ _ := Nat.card_le_card_of_injective Φ hΦ
    _ ≤ _ := hcard

end AbVar

end ZInQ.GRIsogDeg
