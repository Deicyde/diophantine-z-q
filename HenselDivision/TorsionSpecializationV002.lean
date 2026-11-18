import HenselDivision.SchemeHenselLiftV004
import HenselDivision.TorsionKernelV005

/-!
# Specialization of torsion points over a henselian local ring

`R` henselian local with residue field `k`, `S = Spec R`, `s = Spec k → S` the closed point, and `G`
a group scheme over `S` (a group object of `Over S`). If multiplication by `n` on `G` is étale, then
restricting `S`-points to the closed point is a bijection

  `{g ∈ G(S) | g^n = 1} → {x ∈ G(s) | x^n = 1}`,

and for commutative `G` a group isomorphism `G(S)[n] ≃* G_s(k)[n]`. The proof runs through the
actual torsion scheme `G[n] = G ×_{[n], G, η} S`, which is étale over `S` as the base change of `[n]`,
and Hensel lifting of sections of étale schemes. Finiteness of `G[n]` is never used: for a Néron
model with toric part `G[n]` is only quasi-finite, and the statement holds as it stands.

Edition V002: the restriction homomorphism is a separate definition; statements as in V001.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

universe u

variable {R : Type u} [CommRing R]

/-- The closed point `Spec k → Spec R` as an object over `Spec R`. -/
noncomputable abbrev closedObj (R : Type u) [CommRing R] [IsLocalRing R] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (closedPt R)

lemma toUnit_closedObj_left (R : Type u) [CommRing R] [IsLocalRing R] :
    (toUnit (closedObj R)).left = closedPt R := by
  have h := Over.w (toUnit (closedObj R))
  exact (Category.comp_id _).symm.trans h

lemma over_unit_left_comp {X : Over (Spec (CommRingCat.of R))} (g : 𝟙_ _ ⟶ X) :
    g.left ≫ X.hom = 𝟙 _ := by
  have h := Over.w g
  exact h

variable [HenselianLocalRing R]

/-- Restriction of `S`-morphisms to the closed point is bijective for `X` étale over `S`. -/
theorem over_restrict_bijective (X : Over (Spec (CommRingCat.of R))) [Etale X.hom] :
    Function.Bijective (fun g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ X =>
      toUnit (closedObj R) ≫ g) := by
  have hb := etale_section_restrict_bijective (R := R) X.hom
  constructor
  · intro g₁ g₂ h
    have h' : closedPt R ≫ g₁.left = closedPt R ≫ g₂.left := by
      have := congrArg (fun f => f.left) h
      simpa [toUnit_closedObj_left] using this
    have := hb.1 (a₁ := ⟨g₁.left, over_unit_left_comp g₁⟩)
      (a₂ := ⟨g₂.left, over_unit_left_comp g₂⟩) (Subtype.ext h')
    exact Over.OverMorphism.ext (congrArg Subtype.val this)
  · intro f
    obtain ⟨⟨s, hs⟩, hsf⟩ := hb.2 ⟨f.left, by have h := Over.w f; exact h⟩
    refine ⟨Over.homMk s hs, ?_⟩
    apply Over.OverMorphism.ext
    have := congrArg Subtype.val hsf
    simpa [toUnit_closedObj_left] using this

/-- **Integral and residual `n`-torsion points agree** when `[n]` is étale. -/
theorem torsion_restrict_bijective (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (hn : Etale (powHom G n).left) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (closedObj R) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : closedObj R ⟶ G // f ^ n = 1})) := by
  have hK : Etale (torsionKer G n).hom := etale_torsionKer_hom G n hn
  have hpre := over_restrict_bijective (R := R) (torsionKer G n)
  have hfun : (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (closedObj R) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : closedObj R ⟶ G // f ^ n = 1})) =
      (torsionKerHomEquiv G n (closedObj R)) ∘ (fun g => toUnit (closedObj R) ≫ g) ∘
        (torsionKerHomEquiv G n (𝟙_ _)).symm := by
    funext f
    apply Subtype.ext
    show toUnit (closedObj R) ≫ f.1 =
      (toUnit (closedObj R) ≫ (torsionKerHomEquiv G n _).symm f) ≫ torsionKerι G n
    rw [Category.assoc, ← torsionKerHomEquiv_apply G n (𝟙_ (Over (Spec (CommRingCat.of R))))
      ((torsionKerHomEquiv G n _).symm f), Equiv.apply_symm_apply]
  rw [hfun]
  exact (Equiv.bijective _).comp (hpre.comp (Equiv.bijective _))

omit [HenselianLocalRing R] in
/-- Restriction to the closed point as a homomorphism of `n`-torsion groups. -/
noncomputable def torsionRestrictHom [IsLocalRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    torsionPts G (𝟙_ (Over (Spec (CommRingCat.of R)))) n →* torsionPts G (closedObj R) n where
  toFun f := ⟨toUnit (closedObj R) ≫ f.1, (mem_torsionPts _).2 (by
    rw [← MonObj.comp_pow, (mem_torsionPts _).1 f.2, MonObj.comp_one])⟩
  map_one' := Subtype.ext (MonObj.comp_one _)
  map_mul' f g := Subtype.ext (MonObj.comp_mul _ _ _)

omit [HenselianLocalRing R] in
lemma torsionRestrictHom_apply [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (n : ℕ) (f : torsionPts G (𝟙_ (Over (Spec (CommRingCat.of R)))) n) :
    (torsionRestrictHom G n f).1 = toUnit (closedObj R) ≫ f.1 := rfl

lemma torsionRestrictHom_bijective (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (n : ℕ) (hn : Etale (powHom G n).left) :
    Function.Bijective (torsionRestrictHom G n) := by
  have hb := torsion_restrict_bijective G n hn
  constructor
  · intro a b h
    have := hb.1 (a₁ := ⟨a.1, (mem_torsionPts _).1 a.2⟩) (a₂ := ⟨b.1, (mem_torsionPts _).1 b.2⟩)
      (Subtype.ext (congrArg Subtype.val h))
    exact Subtype.ext (congrArg Subtype.val this)
  · intro c
    obtain ⟨a, ha⟩ := hb.2 ⟨c.1, (mem_torsionPts _).1 c.2⟩
    exact ⟨⟨a.1, (mem_torsionPts _).2 a.2⟩, Subtype.ext (congrArg Subtype.val ha)⟩

/-- **The specialization isomorphism** `G(S)[n] ≃* G(s)[n]` for commutative `G` with `[n]` étale. -/
noncomputable def torsionRestrictEquiv (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (n : ℕ) (hn : Etale (powHom G n).left) :
    torsionPts G (𝟙_ (Over (Spec (CommRingCat.of R)))) n ≃* torsionPts G (closedObj R) n :=
  MulEquiv.ofBijective (torsionRestrictHom G n) (torsionRestrictHom_bijective G n hn)

lemma torsionRestrictEquiv_apply (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (n : ℕ) (hn : Etale (powHom G n).left)
    (f : torsionPts G (𝟙_ (Over (Spec (CommRingCat.of R)))) n) :
    (torsionRestrictEquiv G n hn f).1 = toUnit (closedObj R) ≫ f.1 := by
  rw [torsionRestrictEquiv, MulEquiv.ofBijective_apply, torsionRestrictHom_apply]

end HenselDivision

#check @HenselDivision.over_restrict_bijective
#check @HenselDivision.torsion_restrict_bijective
#check @HenselDivision.torsionRestrictEquiv
#print axioms HenselDivision.over_restrict_bijective
#print axioms HenselDivision.torsion_restrict_bijective
#print axioms HenselDivision.torsionRestrictHom_bijective
#print axioms HenselDivision.torsionRestrictEquiv
#print axioms HenselDivision.torsionRestrictEquiv_apply
