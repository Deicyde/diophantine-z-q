import ZInQKernel.Contrib.OneProof.AnalyticStableHeight
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
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
* `finDeg_eq_finrank_of_flat` (end): for flat `φ` the rank is the same at every point (remark; not used).
* `isogDeg_eq_finDeg` (§3): in characteristic `0` equality holds (`finDeg_le_isogDeg`): the geometric generic
  fibre has exactly `[K(A):K(B)]` points (`finrank_le_card_points`, separability via Mathlib's `AlgHom.card`), each
  a translate of `ξ` by an `Ω`-point of the kernel, and the kernel's `Ω`-points descend to `K̄`
  (`card_points_le_of_isAlgClosed`; ring maps of a finite algebra into `Ω` over `K̄` land in `K̄`).
* `GaudronRemondThm14AnDeg` (§4): the leaf with `isogDeg` replaced by `finDeg` (GR's degree);
  `gaudronRemondThm14An_of_deg` derives `GaudronRemondThm14An`, and `gaudronRemondThm14Printed_of_anDeg`
  the bundle field `gaudronRemondThm14Printed` (with T35 through `mumfordTorsionAlgClosed`, as in r3-residual);
  `gaudronRemondThm14Printed_of_anDeg_final` fills `mumfordTorsionAlgClosed` by its proof;
  `gaudronRemondThm14AnDeg_iff_an`: the new leaf is equivalent to r3-residual's (never stronger).

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

/-- Ring maps `S → L` over `ψ₀` into a field are finitely many when `S` is finite over `R`. -/
theorem finite_ringHom {R S L : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field L] (ψ₀ : R →+* L) : Finite {ψ : S →+* L // ψ.comp (algebraMap R S) = ψ₀} := by
  letI : Algebra R L := ψ₀.toAlgebra
  let toA : {ψ : S →+* L // ψ.comp (algebraMap R S) = ψ₀} → (S →ₐ[R] L) := fun ψ =>
    AlgHom.mk ψ.1 (fun r => congrArg (fun g : R →+* L => g r) ψ.2)
  have hinj : Function.Injective toA := fun a b h => Subtype.ext (congrArg AlgHom.toRingHom h)
  have : Finite (S →ₐ[R] L) := Finite.of_equiv _ (AlgHom.liftEquiv R L S L).symm
  exact Finite.of_injective toA hinj

/-- Equality in the ring-level count (characteristic `0`, `Ω` algebraically closed, `S` a domain
finite over `R`, `R → S` injective): the ring maps over `ψ₀` number exactly the rank at `⊥`. -/
theorem card_ringHom_eq_rankAtStalk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (ψ₀ : R →+* Ω) (hψ₀ : Function.Injective ψ₀) (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    Nat.card {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} = Module.rankAtStalk S p := by
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
  let toA : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} → (S →ₐ[R] Ω) := fun ψ =>
    AlgHom.mk ψ.1 (fun r => congrArg (fun g : R →+* Ω => g r) ψ.2)
  let e₁ : {ψ : S →+* Ω // ψ.comp (algebraMap R S) = ψ₀} ≃ (S →ₐ[R] Ω) :=
    { toFun := toA
      invFun := fun f => ⟨f.toRingHom, RingHom.ext fun r => f.commutes r⟩
      left_inv := fun ψ => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr (e₁.trans (AlgHom.liftEquiv R Rp S Ω)),
    Module.rankAtStalk_eq_finrank_tensorProduct]
  -- `Rp ⊗[R] S` is a localization of the domain `S`, finite over the field `Rp`: a field
  have hdom : IsDomain (Rp ⊗[R] S) := by
    letI : Algebra S (Rp ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid S (⊥ : Ideal R).primeCompl) (Rp ⊗[R] S) :=
      IsLocalization.tensorRight _ _
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := S)
      (M := Algebra.algebraMapSubmonoid S (⊥ : Ideal R).primeCompl) _ ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    apply hr
    have : r = 0 := hinj (by rw [h0, map_zero])
    rw [this]; exact Ideal.zero_mem _
  letI : Field Rp := IsFractionRing.toField R
  have hfield : IsField (Rp ⊗[R] S) := isField_of_isIntegral_of_isField' (R := Rp) (Field.toIsField Rp)
  letI : Field (Rp ⊗[R] S) := hfield.toField
  haveI : CharZero Rp := (RingHom.charZero_iff ψp.injective).mpr inferInstance
  haveI : Algebra.IsSeparable Rp (Rp ⊗[R] S) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← AlgHom.card Rp (Rp ⊗[R] S) Ω, Fintype.card_eq_nat_card]

/-- Descent of ring maps from `Ω` to an algebraically closed subfield `k`: for `S` integral over
`R`, every ring map `S → Ω` over `emb ∘ ψ'` factors through `emb : k → Ω`. -/
theorem card_ringHom_le_of_isAlgClosed {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {k Ω : Type*} [Field k] [IsAlgClosed k] [Field Ω] (emb : k →+* Ω)
    (ψ' : R →+* k) [Finite {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'}] :
    Nat.card {χ : S →+* Ω // χ.comp (algebraMap R S) = emb.comp ψ'} ≤
      Nat.card {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'} := by
  letI : Algebra k Ω := emb.toAlgebra
  letI : Algebra R k := ψ'.toAlgebra
  letI : Algebra R Ω := (emb.comp ψ').toAlgebra
  haveI : IsScalarTower R k Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmem : ∀ χ : {χ : S →+* Ω // χ.comp (algebraMap R S) = emb.comp ψ'}, ∀ s, χ.1 s ∈ emb.range := by
    intro χ s
    let χa : S →ₐ[R] Ω := AlgHom.mk χ.1 (fun r => congrArg (fun g : R →+* Ω => g r) χ.2)
    have h1 : IsIntegral R (χ.1 s) := (Algebra.IsIntegral.isIntegral s).map χa
    have h2 : IsIntegral k (χ.1 s) := h1.tower_top
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
      (K := integralClosure k Ω)).2 ⟨χ.1 s, h2⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  let eR : k ≃+* emb.range := RingEquiv.ofBijective emb.rangeRestrict
    ⟨fun a b h => emb.injective (congrArg Subtype.val h), emb.rangeRestrict_surjective⟩
  have heR : ∀ y : emb.range, emb (eR.symm y) = y := fun y => by
    have := congrArg Subtype.val (eR.apply_symm_apply y)
    exact this
  let down : {χ : S →+* Ω // χ.comp (algebraMap R S) = emb.comp ψ'} →
      {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'} := fun χ =>
    ⟨eR.symm.toRingHom.comp (χ.1.codRestrict emb.range (hmem χ)), by
      ext r
      apply emb.injective
      change emb (eR.symm _) = emb (ψ' r)
      rw [heR]
      exact congrArg (fun g : R →+* Ω => g r) χ.2⟩
  have hdown : Function.Injective down := fun a b h => Subtype.ext (RingHom.ext fun s => by
    have := congrArg (fun χ' : {χ' : S →+* k // χ'.comp (algebraMap R S) = ψ'} => emb (χ'.1 s)) h
    simpa [down, heR] using this)
  exact Nat.card_le_card_of_injective down hdown

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

/-- Points of `X` over a point `Spec L → Spec R → Y` factoring through `u : Spec R ⟶ Y`, for `f` finite,
are the ring maps `Γ(f⁻¹ u) → L` over `Γ(Spec R) → L`. -/
theorem points_equiv_ringHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {R : CommRingCat.{u}}
    (u : Spec R ⟶ Y) {L : Type u} [Field L] (φ : R ⟶ CommRingCat.of L) :
    Nonempty ({x : Spec (.of L) ⟶ X // x ≫ f = Spec.map φ ≫ u} ≃
      {ψ : Γ(pullback f u, ⊤) →+* L //
        ψ.comp (pullback.snd f u).appTop.hom = ((Scheme.ΓSpecIso R).hom ≫ φ).hom}) := by
  let f' := pullback.snd f u
  haveI : IsAffine (pullback f u) := isAffine_of_isAffineHom f'
  let toP : {x : Spec (.of L) ⟶ X // x ≫ f = Spec.map φ ≫ u} →
      {x' : Spec (.of L) ⟶ pullback f u // x' ≫ f' = Spec.map φ} := fun x =>
    ⟨pullback.lift x.1 (Spec.map φ) x.2, pullback.lift_snd _ _ _⟩
  have htoP : Function.Bijective toP := by
    refine ⟨fun a b h => Subtype.ext ?_, fun x' => ⟨⟨x'.1 ≫ pullback.fst f u, ?_⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun x' => x'.1 ≫ pullback.fst f u) h
      simpa [toP] using this
    · rw [Category.assoc, pullback.condition, ← Category.assoc, x'.2]
    · apply pullback.hom_ext
      · simp [toP]
      · simpa [toP] using x'.2.symm
  let toR : {x' : Spec (.of L) ⟶ pullback f u // x' ≫ f' = Spec.map φ} →
      {ψ : Γ(pullback f u, ⊤) →+* L //
        ψ.comp f'.appTop.hom = ((Scheme.ΓSpecIso R).hom ≫ φ).hom} := fun x' =>
    ⟨(x'.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom, by
      have h2 : f'.appTop ≫ x'.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
          (Scheme.ΓSpecIso R).hom ≫ φ := by
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop, x'.2, Scheme.ΓSpecIso_naturality]
      exact congrArg CommRingCat.Hom.hom h2⟩
  have htoR : Function.Bijective toR := by
    refine ⟨fun a b h => Subtype.ext ?_, fun ψ => ?_⟩
    · have h' : a.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
          b.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom :=
        CommRingCat.hom_ext (congrArg Subtype.val h)
      exact ext_of_isAffine ((cancel_mono _).mp h')
    · let x' : Spec (.of L) ⟶ pullback f u :=
        Spec.map (CommRingCat.ofHom ψ.1) ≫ (pullback f u).isoSpec.inv
      have hx' : x'.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom = CommRingCat.ofHom ψ.1 := by
        have e1 : (pullback f u).isoSpec.hom.appTop ≫ x'.appTop =
            (Spec.map (CommRingCat.ofHom ψ.1)).appTop := by
          rw [← Scheme.Hom.comp_appTop]; simp [x']
        have e2 : (pullback f u).isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(pullback f u, ⊤)).hom :=
          Scheme.toSpecΓ_appTop _
        rw [e2] at e1
        rw [← cancel_epi (Scheme.ΓSpecIso Γ(pullback f u, ⊤)).hom, ← Category.assoc, e1,
          Scheme.ΓSpecIso_naturality]
        rfl
      have hcomp : x' ≫ f' = Spec.map φ := by
        apply ext_of_isAffine
        rw [← cancel_mono (Scheme.ΓSpecIso (.of L)).hom, Scheme.Hom.comp_appTop, Category.assoc, hx',
          Scheme.ΓSpecIso_naturality]
        ext r
        exact congrArg (fun g => g r) ψ.2
      exact ⟨⟨x', hcomp⟩, Subtype.ext (congrArg CommRingCat.Hom.hom hx')⟩
  exact ⟨(Equiv.ofBijective _ htoP).trans (Equiv.ofBijective _ htoR)⟩


/-- Equality direction at the generic point (characteristic `0`): Mathlib's rank of `f` at the
generic point is at most the number of `Ω`-points over `y₀`, when `X` is integral and the fibre is nonempty. -/
theorem finrank_le_card_points {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsIntegral X] [IsIntegral Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (y₀ : Spec (.of Ω) ⟶ Y)
    (hy₀ : ∀ z, y₀ z = genericPoint Y) (x₀ : Spec (.of Ω) ⟶ X) (hx₀ : x₀ ≫ f = y₀) :
    f.finrank (genericPoint Y) ≤ Nat.card {x : Spec (.of Ω) ⟶ X // x ≫ f = y₀} := by
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
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ CommRingCat.of Ω, Spec.map φ = y₀' :=
    ⟨Spec.preimage y₀', Spec.map_preimage _⟩
  have hy : Spec.map φ ≫ u = y₀ := by rw [hφ, hfac]
  let f' : pullback f u ⟶ Spec R := pullback.snd f u
  let R' := Γ(Spec R, ⊤)
  let S' := Γ(pullback f u, ⊤)
  let ψ₀ : R' →+* Ω := ((Scheme.ΓSpecIso R).hom ≫ φ).hom
  letI : Algebra R' S' := f'.appTop.hom.toAlgebra
  haveI : Module.Finite R' S' := f'.finite_appTop
  obtain ⟨e⟩ := points_equiv_ringHom f u φ
  -- domains
  haveI : Nonempty (Spec R) := ⟨t⟩
  haveI : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion u
  let z₀ : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  haveI : Nonempty ↥(pullback f u) :=
    ⟨pullback.lift x₀ (Spec.map φ) (by rw [hx₀, hy]) z₀⟩
  haveI : IsIntegral (pullback f u) := isIntegral_of_isOpenImmersion (pullback.fst f u)
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
    have e' : (Spec R).isoSpec.hom ((Spec R).isoSpec.inv q) = q :=
      Scheme.inv_hom_apply (Spec R).isoSpec (q : Spec R')
    rw [e'] at hpq
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes p q).mpr hpq)
  have hψ₀ : Function.Injective ψ₀ :=
    (RingHom.injective_iff_ker_eq_bot ψ₀).mpr (hp_ker ▸ hp_bot)
  have hinj : Function.Injective (algebraMap R' S') := by
    have h0 := (e ⟨x₀, by rw [hx₀, hy]⟩).2
    intro a b hab
    apply hψ₀
    have ha := congrArg (fun g : R' →+* Ω => g a) h0
    have hb := congrArg (fun g : R' →+* Ω => g b) h0
    exact ha.symm.trans ((congrArg (e ⟨x₀, by rw [hx₀, hy]⟩).1 hab).trans hb)
  rw [← hy, Nat.card_congr e]
  exact (card_ringHom_eq_rankAtStalk (R := R') (S := S') hinj ψ₀ hψ₀ p hp_bot).symm.le

/-- Descent of points from `Ω` to an algebraically closed subfield `k` (for `f` finite): the
`Ω`-points over a `k`-point are at most the `k`-points over it; both sets are finite. -/
theorem card_points_le_of_isAlgClosed {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {k Ω : Type u}
    [Field k] [IsAlgClosed k] [Field Ω] (emb : k →+* Ω) (y₀ : Spec (.of k) ⟶ Y) :
    Finite {x : Spec (.of k) ⟶ X // x ≫ f = y₀} ∧
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = Spec.map (CommRingCat.ofHom emb) ≫ y₀} ∧
    Nat.card {x : Spec (.of Ω) ⟶ X // x ≫ f = Spec.map (CommRingCat.ofHom emb) ≫ y₀} ≤
      Nat.card {x : Spec (.of k) ⟶ X // x ≫ f = y₀} := by
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx (y₀ (IsLocalRing.closedPoint k))
  let R := 𝒰.X i
  let u : Spec R ⟶ Y := 𝒰.f i
  have hrange : Set.range y₀ ⊆ Set.range u := by
    rintro _ ⟨z, rfl⟩
    have : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst this
    exact 𝒰.covers _
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ CommRingCat.of k, Spec.map φ = IsOpenImmersion.lift u y₀ hrange :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hy : Spec.map φ ≫ u = y₀ := by rw [hφ]; exact IsOpenImmersion.lift_fac _ _ _
  have hy' : Spec.map (φ ≫ CommRingCat.ofHom emb) ≫ u = Spec.map (CommRingCat.ofHom emb) ≫ y₀ := by
    rw [Spec.map_comp, Category.assoc, hy]
  let f' : pullback f u ⟶ Spec R := pullback.snd f u
  let R' := Γ(Spec R, ⊤)
  let S' := Γ(pullback f u, ⊤)
  letI : Algebra R' S' := f'.appTop.hom.toAlgebra
  haveI : Module.Finite R' S' := f'.finite_appTop
  let ψ' : R' →+* k := ((Scheme.ΓSpecIso R).hom ≫ φ).hom
  obtain ⟨e₀⟩ := points_equiv_ringHom f u φ
  obtain ⟨e₁⟩ := points_equiv_ringHom f u (φ ≫ CommRingCat.ofHom emb)
  haveI : Finite {χ' : S' →+* k // χ'.comp (algebraMap R' S') = ψ'} := finite_ringHom _
  haveI : Finite {χ : S' →+* Ω // χ.comp (algebraMap R' S') = emb.comp ψ'} := finite_ringHom _
  rw [← hy', ← hy]
  refine ⟨Finite.of_equiv _ e₀.symm, Finite.of_equiv _ e₁.symm, ?_⟩
  rw [Nat.card_congr e₀, Nat.card_congr e₁]
  exact card_ringHom_le_of_isAlgClosed (R := R') (S := S') emb ψ'

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

/-- **`deg φ ≤ # ker φ(K̄)` in characteristic `0`**, hence (with `isogDeg_le_finDeg`) equality:
the geometric generic fibre has `[K(A):K(B)]` points (separability), each a translate of the geometric
generic point by an `Ω`-point of the kernel, and the kernel's `Ω`-points come from `K̄`. -/
theorem finDeg_le_isogDeg [CharZero K] {A B : AbVar K} (φ : A.X ⟶ B.X) (hφ : IsIsogeny φ) :
    finDeg φ ≤ isogDeg φ := by
  haveI := isIntegral_left A
  haveI := isIntegral_left B
  obtain ⟨hmon, hfin, hsurj⟩ := hφ
  haveI := hmon
  haveI := hfin
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
  let σ : CommRingCat.of K ⟶ CommRingCat.of Ω := Spec.preimage (ξ₀ ≫ A.X.hom)
  letI : Algebra K Ω := σ.hom.toAlgebra
  haveI : CharZero Ω := (RingHom.charZero_iff σ.hom.injective).mp inferInstance
  let ξ : ptObj K Ω ⟶ A.X := Over.homMk ξ₀ (by
    change ξ₀ ≫ A.X.hom = Spec.map (CommRingCat.ofHom σ.hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
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
  -- step 1: the geometric generic fibre
  have h1 : finDeg φ ≤ Nat.card {x : Spec (.of Ω) ⟶ A.X.left // x ≫ φ.left = ξ₀ ≫ φ.left} :=
    finrank_le_card_points φ.left (ξ₀ ≫ φ.left) hy ξ₀ rfl
  -- step 3: descent of kernel points from `Ω` to `K̄`
  let oneK : ptObj K (AlgebraicClosure K) ⟶ B.X := 1
  let oneΩ : ptObj K Ω ⟶ B.X := 1
  have hone : oneΩ.left = Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ oneK.left := by
    have : embo ≫ oneK = oneΩ := MonObj.comp_one _
    rw [← this]
    rfl
  obtain ⟨hfinK, hfinΩ, h3⟩ := card_points_le_of_isAlgClosed φ.left emb.toRingHom oneK.left
  rw [← hone] at h3 hfinΩ
  -- step 2: the fibre over `ξ ≫ φ` injects into the kernel's `Ω`-points (translation by `ξ⁻¹`)
  have hw : ∀ x : Spec (.of Ω) ⟶ A.X.left, x ≫ φ.left = ξ₀ ≫ φ.left →
      x ≫ A.X.hom = (ptObj K Ω).hom := fun x hx => by
    rw [← Over.w φ, ← Category.assoc, hx, Category.assoc, Over.w φ]
    exact Over.w ξ
  have hinv : ξ⁻¹ ≫ φ = (ξ ≫ φ)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp])
  let F2 : {x : Spec (.of Ω) ⟶ A.X.left // x ≫ φ.left = ξ₀ ≫ φ.left} →
      {x : Spec (.of Ω) ⟶ A.X.left // x ≫ φ.left = oneΩ.left} := fun x =>
    ⟨(ξ⁻¹ * Over.homMk x.1 (hw x.1 x.2)).left, by
      have hx : (Over.homMk x.1 (hw x.1 x.2) : ptObj K Ω ⟶ A.X) ≫ φ = ξ ≫ φ := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left]
        exact x.2
      have : (ξ⁻¹ * Over.homMk x.1 (hw x.1 x.2)) ≫ φ = oneΩ := by
        rw [MonObj.mul_comp, hinv, hx, inv_mul_cancel]
      have h' := congrArg CommaMorphism.left this
      simp only [Over.comp_left] at h'
      exact h'⟩
  have hF2 : Function.Injective F2 := fun a b h => by
    have h1 : (ξ⁻¹ * Over.homMk a.1 (hw a.1 a.2) : ptObj K Ω ⟶ A.X) =
        ξ⁻¹ * Over.homMk b.1 (hw b.1 b.2) := by
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val h
    have h2 := congrArg CommaMorphism.left (@mul_left_cancel (ptObj K Ω ⟶ A.X) _ _ _ _ _ h1)
    exact Subtype.ext h2
  have h2 := Nat.card_le_card_of_injective F2 hF2
  -- step 4: `K̄`-points over the origin are kernel points
  have hw4 : ∀ x : Spec (.of (AlgebraicClosure K)) ⟶ A.X.left, x ≫ φ.left = oneK.left →
      x ≫ A.X.hom = (ptObj K (AlgebraicClosure K)).hom := fun x hx => by
    rw [← Over.w φ, ← Category.assoc, hx]
    exact Over.w oneK
  let F4 : {x : Spec (.of (AlgebraicClosure K)) ⟶ A.X.left // x ≫ φ.left = oneK.left} →
      {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1} := fun x =>
    ⟨Over.homMk x.1 (hw4 x.1 x.2), by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left]
      exact x.2⟩
  have hF4 : Function.Injective F4 := fun a b h =>
    Subtype.ext (congrArg (fun P : {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1} => P.1.left) h)
  let G4 : {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1} →
      {x : Spec (.of (AlgebraicClosure K)) ⟶ A.X.left // x ≫ φ.left = oneK.left} := fun P =>
    ⟨P.1.left, by
      have h' := congrArg CommaMorphism.left P.2
      simp only [Over.comp_left] at h'
      exact h'⟩
  have hG4 : Function.Injective G4 := fun P Q h =>
    Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))
  haveI : Finite {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1} := Finite.of_injective G4 hG4
  have h4 := Nat.card_le_card_of_injective F4 hF4
  calc finDeg φ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ _ := h4
    _ = isogDeg φ := rfl

/-- **`# ker φ(K̄) = deg φ` in characteristic `0`.** -/
theorem isogDeg_eq_finDeg [CharZero K] {A B : AbVar K} (φ : A.X ⟶ B.X) (hφ : IsIsogeny φ) :
    isogDeg φ = finDeg φ :=
  le_antisymm (isogDeg_le_finDeg φ hφ) (finDeg_le_isogDeg φ hφ)

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

/-- **The new leaf is never stronger**: in characteristic `0` (number fields) `isogDeg = finDeg`
(`isogDeg_eq_finDeg`), so r3-residual's leaf implies the leaf with the printed degree. -/
theorem gaudronRemondThm14AnDeg_of_an (h : ZInQ.R3Residual.GaudronRemondThm14An) :
    GaudronRemondThm14AnDeg := by
  intro K _ _ A B g x hg hx hiso
  obtain ⟨⟨φ, hφ, hφd⟩, ⟨ψ, hψ, hψd⟩⟩ := h K A B g x hg hx hiso
  exact ⟨⟨φ, hφ, by rw [← isogDeg_eq_finDeg φ hφ]; exact hφd⟩,
    ⟨ψ, hψ, by rw [← isogDeg_eq_finDeg ψ hψ]; exact hψd⟩⟩

/-- The two forms of the leaf are equivalent. -/
theorem gaudronRemondThm14AnDeg_iff_an :
    GaudronRemondThm14AnDeg ↔ ZInQ.R3Residual.GaudronRemondThm14An :=
  ⟨gaudronRemondThm14An_of_deg, gaudronRemondThm14AnDeg_of_an⟩

/-- **The field `gaudronRemondThm14Printed`** from the leaf with the printed degree and
`mumfordTorsionAlgClosed` (r3-residual's `gaudronRemondThm14Printed_of_an`; `uniformizationLeafAll`
filled by its proof). -/
theorem gaudronRemondThm14Printed_of_anDeg (h : GaudronRemondThm14AnDeg)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : ZInQ.HeightFix.GaudronRemondThm14Printed :=
  ZInQ.R3Residual.gaudronRemondThm14Printed_of_an (gaudronRemondThm14An_of_deg h) hMT

/-- **The field `gaudronRemondThm14Printed`** from the leaf with the printed degree alone
(`mumfordTorsionAlgClosed` filled by its proof, `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`). -/
theorem gaudronRemondThm14Printed_of_anDeg_final (h : GaudronRemondThm14AnDeg) :
    ZInQ.HeightFix.GaudronRemondThm14Printed :=
  gaudronRemondThm14Printed_of_anDeg h ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

end Leaf

section Flat
variable {K : Type} [Field K]
/-- For a flat isogeny (every isogeny is flat, STANDARD; not proved here), `finDeg φ` is Mathlib's rank of
`φ` at every point of `B` (e.g. at the origin, where it is the rank of the kernel group scheme;
finite presentation holds over a field since `B` is noetherian). -/
theorem finDeg_eq_finrank_of_flat {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) [IsFinite φ.left]
    [Flat φ.left] [LocallyOfFinitePresentation φ.left] (y : B.X.left) :
    finDeg φ = φ.left.finrank y := by
  haveI := isIntegral_left B
  exact (Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace _ _
end Flat

end ZInQ.GRIsogDeg
