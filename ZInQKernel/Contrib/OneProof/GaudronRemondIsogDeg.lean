import ZInQKernel.Contrib.OneProof.AnalyticStableHeight
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # gr-isogdeg: Gaudron–Rémond's degree is the degree of the isogeny as a finite morphism

Task gr-isogdeg (2026-11-17), report `docs/research/gr-isogdeg.md`, scratch `scratch/gr-isogdeg/`.

**The step.** The leaf `ZInQ.R3Residual.GaudronRemondThm14An` (Gaudron–Rémond, Duke Math. J. 163 (2014),
Thm 1.4) bounds `isogDeg φ = # ker φ(K̄)`, while Gaudron and Rémond bound the degree of the isogeny `φ`, the
degree `[K(A) : K(B)]` of `φ` as a finite morphism. The consumer needs `# ker φ(K̄) ≤ deg φ`.

**This file.**
* `finDeg φ` (§3): Mathlib's rank `Scheme.Hom.finrank` of `φ.left` at the generic point of `B`. The stalk of
  `B` there is the function field, so this is `[K(A) : K(B)]`, with no flatness needed.
* `isogDeg_le_finDeg` (§3): `# ker φ(K̄) ≤ finDeg φ` for every isogeny of abelian varieties over **any**
  field. Proof: a geometric generic point `ξ : Spec Ω → A` (`Ω` an algebraic closure of `κ(η_A)`), translated
  by the kernel points (through an embedding `K̄ → Ω` over `K`), gives distinct `Ω`-points of `A` over
  `φ ∘ ξ`, which lies over the generic point of `B` (`card_points_le_finrank`, §2); these inject into the ring
  maps `Γ(φ⁻¹U) → Ω` over `Γ(U) → Ω` for an affine open `U`, at most the rank at the zero prime
  (`card_ringHom_le_rankAtStalk`, §1, from Mathlib's `card_algHom_le_finrank`).
* `GaudronRemondThm14AnDeg` (§4): the leaf with `isogDeg` replaced by `finDeg` (GR's degree);
  `gaudronRemondThm14An_of_deg` derives `GaudronRemondThm14An`, and `gaudronRemondThm14Printed_of_anDeg`
  the bundle field `gaudronRemondThm14Printed` (with T35 through `mumfordTorsionAlgClosed`, as in r3-residual).

No `sorry`, no `axiom`, no code that runs at build time. -/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ZInQ.GRIsogDeg

open TensorProduct

/-! ## §1. Ring maps over an injective map into a field -/

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

/-! ## §2. Geometric points over the generic point -/

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- Scheme-level count: for `f : X ⟶ Y` finite with `Y` integral and `y₀ : Spec Ω ⟶ Y` onto the generic
point, the `Ω`-points of `X` over `y₀` are finitely many, at most Mathlib's rank `f.finrank` at the generic
point. (`hring` is the ring-level count, filled by `card_ringHom_le_rankAtStalk`.) -/
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

/-! ## §3. The degree of an isogeny and the kernel's geometric points -/

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

/-! ## §4. The leaf with Gaudron–Rémond's degree, and the field -/

section Leaf

open ZInQ.DefFaltings (IsIsogeny grKappa)

/-- **Leaf R19-GR over the print's stable height, with the printed degree** (Gaudron–Rémond, Duke Math.
J. 163 (2014), Thm 1.4, p. 2060; `κ` and `α(g) = 1024g³`, p. 2058; read by the locator audit,
docs/research/locators.md). `ZInQ.R3Residual.GaudronRemondThm14An` verbatim with the isogeny degree
`isogDeg φ = # ker φ(K̄)` replaced by `finDeg φ`, the degree of `φ` as a finite morphism (Mathlib's
`Scheme.Hom.finrank` at the generic point of the target, `= [K(A) : K(B)]`). -/
def GaudronRemondThm14AnDeg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → ZInQ.R3Residual.IsAnStableHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (finDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (finDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- r3-residual's leaf `GaudronRemondThm14An` from the leaf with the printed degree, by
`isogDeg_le_finDeg`. -/
theorem gaudronRemondThm14An_of_deg (h : GaudronRemondThm14AnDeg) :
    ZInQ.R3Residual.GaudronRemondThm14An := by
  intro K _ _ A B g x hg hx hiso
  obtain ⟨⟨φ, hφ, hφd⟩, ⟨ψ, hψ, hψd⟩⟩ := h K A B g x hg hx hiso
  exact ⟨⟨φ, hφ, le_trans (by exact_mod_cast isogDeg_le_finDeg φ hφ) hφd⟩,
    ⟨ψ, hψ, le_trans (by exact_mod_cast isogDeg_le_finDeg ψ hψ) hψd⟩⟩

/-- **The field `gaudronRemondThm14Printed`** from the leaf with the printed degree and
`mumfordTorsionAlgClosed` (r3-residual's `gaudronRemondThm14Printed_of_an`; `uniformizationLeafAll`
filled by its proof). -/
theorem gaudronRemondThm14Printed_of_anDeg (h : GaudronRemondThm14AnDeg)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightFix.GaudronRemondThm14Printed :=
  ZInQ.R3Residual.gaudronRemondThm14Printed_of_an (gaudronRemondThm14An_of_deg h) hMT

end Leaf

end ZInQ.GRIsogDeg
