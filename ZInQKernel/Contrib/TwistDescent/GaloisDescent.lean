/-
Task twist-descent (2026-11-13): Galois descent of morphisms of schemes along a finite Galois
extension of fields, from Mathlib (no project imports).

* `exists_open_gal`: for a finite Galois extension `k'/k` and two morphisms `u v : Z → Spec k'`
  agreeing over `Spec k`, every point of `Z` has an open neighbourhood on which
  `v = u ≫ Spec g` for some `g ∈ Gal(k'/k)` (the scheme form of `k' ⊗_k k' ≅ ∏_{Gal} k'`; proved
  with a primitive element `θ` and the polynomial `∏_g (X - gθ) ∈ k[X]`).
* `descend`: if `X' = X ×_{k} k'` (any pullback square) and `f : X' → Y` is invariant under the
  Galois translates of `X'` over `X`, then `f` factors through `X' → X` (Mathlib: flat surjective
  quasi-compact morphisms are effective epimorphisms, `Sites/Fpqc.lean`).
* `epi_of_isPullback_field`: the base change of `Spec k' → Spec k` along any morphism is an
  epimorphism, for any field extension `k'/k`.
-/
import Mathlib

open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace TwistDescentGD

section Ring

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

/-- Two ring maps out of `k'` agreeing on `k` and on a generator of `k'/k` agree. -/
theorem ringHom_eq_of_gen {R : Type*} [CommRing R] (θ : k') (hθ : Algebra.adjoin k {θ} = ⊤)
    (φ₁ φ₂ : k' →+* R) (hk : φ₁.comp (algebraMap k k') = φ₂.comp (algebraMap k k'))
    (h : φ₁ θ = φ₂ θ) : φ₁ = φ₂ := by
  ext x
  have hx : x ∈ Algebra.adjoin k {θ} := hθ ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact h
  | algebraMap r => exact congrArg (fun f => f r) hk
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

/-- A primitive element generates `k'` as a `k`-algebra. -/
theorem exists_gen [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    ∃ θ : k', Algebra.adjoin k {θ} = ⊤ := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k k'
  refine ⟨θ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic θ), hθ, IntermediateField.top_toSubalgebra]

/-- **The product formula.** For ring maps `us, vs : k' → R` agreeing on `k`, with `k'/k` finite
Galois, `∏_{g ∈ Gal(k'/k)} (vs θ - us (g θ)) = 0`. -/
theorem prod_eq_zero_of_galois [FiniteDimensional k k'] [IsGalois k k'] {R : Type*} [CommRing R]
    (us vs : k' →+* R) (hk : us.comp (algebraMap k k') = vs.comp (algebraMap k k')) (θ : k') :
    ∏ g : (k' ≃ₐ[k] k'), (vs θ - us (g θ)) = 0 := by
  obtain ⟨p, hp1, -, -⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts k k' (k' ≃ₐ[k] k') θ)
    (MulSemiringAction.monic_charpoly (k' ≃ₐ[k] k') θ)
  have h0 : (p.map (algebraMap k k')).eval θ = 0 := by
    rw [hp1, MulSemiringAction.eval_charpoly]
  have key := congrArg (fun q => (q.map us).eval (vs θ)) hp1
  rw [Polynomial.map_map, hk, ← Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, h0, map_zero, MulSemiringAction.charpoly_eq,
    Polynomial.map_prod, Polynomial.eval_prod] at key
  rw [key]
  refine Finset.prod_congr rfl fun g _ => ?_
  simp [AlgEquiv.smul_def]

end Ring

section Schemes

/-- The ring map `R → Γ(Z, ⊤)` of a morphism `u : Z → Spec R`. -/
noncomputable def sharp {Z : Scheme.{0}} {R : CommRingCat.{0}} (u : Z ⟶ Spec R) :
    R →+* Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ u.appTop).hom

theorem sharp_comp_spec {Z : Scheme.{0}} {R S : CommRingCat.{0}} (u : Z ⟶ Spec S) (f : R ⟶ S) :
    sharp (u ≫ Spec.map f) = (sharp u).comp f.hom := by
  unfold sharp
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]
  rfl

theorem sharp_comp {W Z : Scheme.{0}} {R : CommRingCat.{0}} (i : W ⟶ Z) (u : Z ⟶ Spec R) :
    sharp (i ≫ u) = i.appTop.hom.comp (sharp u) := by
  unfold sharp
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem ext_sharp {Z : Scheme.{0}} {R : CommRingCat.{0}} {u v : Z ⟶ Spec R}
    (h : sharp u = sharp v) : u = v := by
  apply ext_of_isAffine
  have h' : (Scheme.ΓSpecIso R).inv ≫ u.appTop = (Scheme.ΓSpecIso R).inv ≫ v.appTop :=
    CommRingCat.hom_ext h
  simpa using congrArg ((Scheme.ΓSpecIso R).hom ≫ ·) h'

/-- The restriction of `F` to (the image of) the open subscheme `D(F)` is a unit. -/
theorem isUnit_appTop_basicOpen {Z : Scheme.{0}} (F : Γ(Z, ⊤)) :
    IsUnit ((Z.basicOpen F).ι.appTop.hom F) := by
  have h1 := RingedSpace.isUnit_res_basicOpen Z.toRingedSpace F
  have hle : ((Z.basicOpen F).ι ''ᵁ ⊤ : TopologicalSpace.Opens Z) ≤
      Z.toRingedSpace.basicOpen F := by
    rw [Scheme.Opens.ι_image_top]; rfl
  have h2 := h1.map (Z.toRingedSpace.presheaf.map
    (@homOfLE (TopologicalSpace.Opens Z) _ _ _ hle).op).hom
  rw [← CommRingCat.comp_apply, ← Functor.map_comp] at h2
  rw [Scheme.Opens.ι_appTop]
  exact h2

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

/-- **Local triviality of `Spec k' ×_k Spec k'`.** For `k'/k` finite Galois and two morphisms
`u v : Z → Spec k'` agreeing over `Spec k`, every point `z` has an open neighbourhood `U` with
`v|_U = u|_U ≫ Spec g` for some `g ∈ Gal(k'/k)`. -/
theorem exists_open_gal [FiniteDimensional k k'] [IsGalois k k'] {Z : Scheme.{0}}
    (u v : Z ⟶ Spec (CommRingCat.of k'))
    (h : u ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      v ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (z : Z) : ∃ (U : Z.Opens) (g : k' ≃ₐ[k] k'), z ∈ U ∧
      U.ι ≫ v = U.ι ≫ u ≫ Spec.map (CommRingCat.ofHom (g : k' →+* k')) := by
  classical
  obtain ⟨θ, hgen⟩ := exists_gen (k := k) (k' := k')
  set us := sharp u
  set vs := sharp v
  have hk : us.comp (algebraMap k k') = vs.comp (algebraMap k k') := by
    have := congrArg sharp h
    rwa [sharp_comp_spec, sharp_comp_spec] at this
  let f : (k' ≃ₐ[k] k') → Γ(Z, ⊤) := fun g => vs θ - us (g θ)
  have hprod : ∏ g, f g = 0 := prod_eq_zero_of_galois us vs hk θ
  let germ := (Z.presheaf.germ ⊤ z trivial).hom
  have hex : ∃ g, ¬ IsUnit (germ (f g)) := by
    by_contra hall
    push Not at hall
    have hu : IsUnit (germ (∏ g, f g)) := by
      rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hall g
    rw [hprod, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨g, hg⟩ := hex
  have hne : ∀ h, h ≠ g → g θ - h θ ≠ 0 := by
    intro h hhg hzero
    apply hhg
    have : (g : k' →+* k') = (h : k' →+* k') :=
      ringHom_eq_of_gen θ hgen _ _ (by ext r; simp) (sub_eq_zero.mp hzero)
    exact (AlgEquiv.ext fun x => (congrArg (fun φ : k' →+* k' => φ x) this).symm)
  have hunit : ∀ h, h ≠ g → IsUnit (germ (f h)) := by
    intro h hhg
    have e : f h = f g + us (g θ - h θ) := by
      simp only [f, map_sub]; ring
    have hb : IsUnit (germ (us (g θ - h θ))) :=
      ((IsUnit.mk0 _ (hne h hhg)).map us).map germ
    have hsum : germ (f h) + -germ (f g) = germ (us (g θ - h θ)) := by
      rw [e, map_add]; ring
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hsum ▸ hb) with h1 | h1
    · exact h1
    · exact absurd (IsUnit.neg_iff _ |>.mp h1) hg
  let F : Γ(Z, ⊤) := ∏ h ∈ Finset.univ.erase g, f h
  have hF : IsUnit (germ F) := by
    simp only [F, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      fun h hh => hunit h (Finset.ne_of_mem_erase hh)
  refine ⟨Z.basicOpen F, g, (Z.mem_basicOpen_top F z).mpr hF, ?_⟩
  set ρ := (Z.basicOpen F).ι.appTop.hom
  have hρF : IsUnit (ρ F) := isUnit_appTop_basicOpen F
  have hfg : ρ (f g) = 0 := by
    have : ρ (f g) * ρ F = 0 := by
      rw [← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ g), hprod, map_zero]
    exact hρF.mul_left_eq_zero.mp this
  apply ext_sharp
  rw [sharp_comp, sharp_comp, sharp_comp_spec]
  apply ringHom_eq_of_gen θ hgen
  · ext r
    have := congrArg (fun φ : k →+* Γ(Z, ⊤) => ρ (φ r)) hk
    change ρ (us (algebraMap k k' r)) = ρ (vs (algebraMap k k' r)) at this
    change ρ (vs (algebraMap k k' r)) = ρ (us (g (algebraMap k k' r)))
    rw [g.commutes]
    exact this.symm
  · change ρ (vs θ) = ρ (us (g θ))
    have := hfg
    simp only [f, map_sub, sub_eq_zero] at this
    exact this

/-- `Spec k' → Spec k` is flat, surjective and quasi-compact, for any field extension. -/
theorem spec_field_props (k k' : Type) [Field k] [Field k'] [Algebra k k'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
  refine ⟨?_, ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- **The base change of `Spec k' → Spec k` is an epimorphism** (flat, surjective, quasi-compact,
hence an effective epimorphism by Mathlib's `Sites/Fpqc.lean`). -/
theorem effectiveEpi_of_isPullback_field {X X' : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)}
    {q : X' ⟶ X} {s : X' ⟶ Spec (CommRingCat.of k')}
    (hpb : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    EffectiveEpi q := by
  obtain ⟨h1, h2, h3⟩ := spec_field_props k k'
  have : Flat q := MorphismProperty.of_isPullback (P := @Flat) hpb.flip h1
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip h2
  have : QuasiCompact q := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip h3
  infer_instance

theorem epi_of_isPullback_field {X X' : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)}
    {q : X' ⟶ X} {s : X' ⟶ Spec (CommRingCat.of k')}
    (hpb : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap k k')))) : Epi q := by
  have := effectiveEpi_of_isPullback_field hpb
  infer_instance

/-- **Galois descent of morphisms** along a finite Galois extension `k'/k`. Let `X' → X` be the
base change of `Spec k' → Spec k` along `p : X → Spec k`. A morphism `f : X' → Y` that is
invariant under (some choice of) the Galois translates `c` of `X'` over `X` factors through
`X' → X`. -/
theorem descend [FiniteDimensional k k'] [IsGalois k k'] {X X' Y : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : X' ⟶ X} {s : X' ⟶ Spec (CommRingCat.of k')}
    (hpb : IsPullback q s p (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (f : X' ⟶ Y)
    (hf : ∀ g : k' ≃ₐ[k] k', ∃ c : X' ⟶ X', c ≫ q = q ∧
      c ≫ s = s ≫ Spec.map (CommRingCat.ofHom (g : k' →+* k')) ∧ c ≫ f = f) :
    ∃ f₀ : X ⟶ Y, q ≫ f₀ = f := by
  have := effectiveEpi_of_isPullback_field hpb
  refine ⟨EffectiveEpi.desc q f fun {Z} a b hab => ?_, EffectiveEpi.fac q f _⟩
  apply Scheme.hom_ext_of_forall
  intro z
  have hw : (a ≫ s) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      (b ≫ s) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
    rw [Category.assoc, Category.assoc, ← hpb.w, reassoc_of% hab]
  obtain ⟨U, g, hz, hU⟩ := exists_open_gal (a ≫ s) (b ≫ s) hw z
  obtain ⟨c, hc1, hc2, hc3⟩ := hf g
  refine ⟨U, hz, ?_⟩
  have hb : U.ι ≫ b = U.ι ≫ a ≫ c := by
    apply hpb.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, hc1, hab]
    · rw [Category.assoc, Category.assoc, Category.assoc, hc2, ← Category.assoc a, ← hU]
  rw [← Category.assoc U.ι b, hb, Category.assoc, Category.assoc, hc3]

end Schemes

end TwistDescentGD
