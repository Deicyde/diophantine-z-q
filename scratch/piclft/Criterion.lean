import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.FiniteType

/-! # piclft (I): a functor-of-points criterion for local finite type over a field -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace PicLFT

/-- Every `K`-family `Spec B → X` factors through `Spec S` for a finitely generated `K`-subalgebra `S ≤ B`. -/
def FGFactor (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra K B] (g : Spec (CommRingCat.of B) ⟶ X.left),
    g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K B)) →
    ∃ (S : Subalgebra K B) (_ : S.FG) (g' : Spec (CommRingCat.of S) ⟶ X.left),
      Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ g' = g

/-- Ring-level core: if `g : Spec B → X` lands in the affine open `V` with `g = fromSpec`, and factors through a
f.g. subalgebra, then `B` is f.g. -/
theorem fg_top_of_factor {K : Type} [Field K] {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V)
    [Algebra K Γ(Y, V)] (S : Subalgebra K Γ(Y, V)) (hS : S.FG)
    (g' : Spec (CommRingCat.of S) ⟶ Y)
    (hg : Spec.map (CommRingCat.ofHom S.val.toRingHom) ≫ g' = hV.fromSpec) :
    (⊤ : Subalgebra K Γ(Y, V)).FG := by
  classical
  -- the closed complement of `g'⁻¹ V`
  let Z : Set (PrimeSpectrum S) :=
    show Set (Spec (CommRingCat.of S)) from ((g' ⁻¹ᵁ V : (Spec (CommRingCat.of S)).Opens) : Set _)ᶜ
  have hZ : IsClosed Z := (g' ⁻¹ᵁ V).isOpen.isClosed_compl
  let J : Ideal S := PrimeSpectrum.vanishingIdeal Z
  have hJ : J.map S.val.toRingHom = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum S := PrimeSpectrum.comap S.val.toRingHom ⟨q, hq.isPrime⟩
    have hpZ : p ∈ Z := by
      rw [← hZ.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      intro x hx
      exact hJq (Ideal.mem_map_of_mem _ hx)
    apply hpZ
    let x0 : Spec Γ(Y, V) := (⟨q, hq.isPrime⟩ : PrimeSpectrum Γ(Y, V))
    have hmem : hV.fromSpec x0 ∈ (V : Set Y) := by
      rw [← hV.range_fromSpec]; exact ⟨_, rfl⟩
    rw [← hg] at hmem
    exact hmem
  have h1 : (1 : Γ(Y, V)) ∈ J.map S.val.toRingHom := by rw [hJ]; trivial
  obtain ⟨T, hTs, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hT
  choose! j hjJ hjt using fun t (ht : t ∈ T) => hTs ht
  let S' : Subalgebra K Γ(Y, V) := S ⊔ Algebra.adjoin K ((T.image c : Finset _) : Set Γ(Y, V))
  have hS' : S'.FG := hS.sup (Subalgebra.fg_adjoin_finset _)
  have hSS' : S ≤ S' := le_sup_left
  have hcS' : ∀ t ∈ T, c t ∈ S' := fun t ht =>
    le_sup_right (a := S) (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem c ht)))
  let incl : S →ₐ[K] S' := Subalgebra.inclusion hSS'
  -- every point of `Spec S'` maps into `g'⁻¹ V`
  let g'' : Spec (CommRingCat.of S') ⟶ Y := Spec.map (CommRingCat.ofHom incl.toRingHom) ≫ g'
  have hrange : Set.range g'' ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    by_contra hx
    have hxZ : PrimeSpectrum.comap incl.toRingHom x ∈ Z := hx
    have hJx : J ≤ (PrimeSpectrum.comap incl.toRingHom x).asIdeal := by
      intro a ha
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha _ hxZ
    apply x.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have hsum : (∑ t ∈ T.attach, (⟨c t, hcS' t t.2⟩ : S') * incl (j t)) = 1 := by
      apply Subtype.ext
      rw [show ((∑ t ∈ T.attach, (⟨c t, hcS' t t.2⟩ : S') * incl (j t) : S') : Γ(Y, V)) =
        ∑ t ∈ T.attach, (((⟨c t, hcS' t t.2⟩ : S') * incl (j t) : S') : Γ(Y, V)) from map_sum S'.val _ _]
      conv_rhs => rw [OneMemClass.coe_one, ← hc, ← Finset.sum_attach]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [smul_eq_mul, MulMemClass.coe_mul]
      congr 1
      exact hjt t t.2
    rw [← hsum]
    exact sum_mem fun t _ => Ideal.mul_mem_left _ _ (hJx (hjJ t t.2))
  let lift : Spec (CommRingCat.of S') ⟶ Spec Γ(Y, V) := IsOpenImmersion.lift hV.fromSpec g'' hrange
  have hlift : Spec.map (CommRingCat.ofHom S'.val.toRingHom) ≫ lift = 𝟙 _ := by
    rw [← cancel_mono hV.fromSpec, Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp, ← hg]
    simp only [g'', ← Category.assoc, ← Spec.map_comp]
    rfl
  let ρ : Γ(Y, V) ⟶ CommRingCat.of S' := Spec.preimage lift
  have hρ : ρ ≫ CommRingCat.ofHom S'.val.toRingHom = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hlift, Spec.map_id]; rfl
  have htop : S' = ⊤ := by
    rw [eq_top_iff]
    intro r _
    have := congrArg (fun f => f.hom r) hρ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply,
      CommRingCat.hom_ofHom] at this
    rw [← this]
    exact (ρ.hom r).2
  rw [← htop]; exact hS'

/-- **Criterion (I).** A `K`-scheme all of whose `K`-families factor through finitely generated subalgebras is
locally of finite type over `K` (the surjectivity half of EGA IV 8.14.2 for local finite type). -/
theorem locallyOfFiniteType_of_fgFactor {K : Type} [Field K] (X : Over (Spec (CommRingCat.of K)))
    (H : FGFactor K X) : LocallyOfFiniteType X.hom := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @LocallyOfFiniteType) (fun V : X.left.affineOpens => V)
    (iSup_affineOpens_eq_top X.left) fun V => ?_
  let ψ := X.hom.appLE ⊤ V.1 le_top
  let φ : K →+* Γ(X.left, V.1) := ψ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K Γ(X.left, V.1) := φ.toAlgebra
  have hψ : ψ.hom = φ.comp (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom := by
    ext r
    simp [φ, ← CommRingCat.comp_apply]
  have hg : V.2.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, V.1))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top _) V.2 le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  obtain ⟨S, hS, g', hg'⟩ := H Γ(X.left, V.1) V.2.fromSpec hg
  have htop := fg_top_of_factor V.2 S hS g' hg'
  have hφ : φ.FiniteType := ⟨htop⟩
  change RingHom.FiniteType ψ.hom
  rw [hψ]
  exact hφ.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)

end PicLFT
