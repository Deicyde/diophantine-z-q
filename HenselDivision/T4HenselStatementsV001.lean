import HenselDivision.SchemeHenselLiftV004

/-!
# Two Hensel statements of the T4 frame, proved from the Hensel lifting above

The bodies of `StacksHenselEtaleSectionStmt` and `HenselEtaleLiftStmt` are copied verbatim from
the T4 leaf `StacksHenselEtaleSection` (Stacks 04GG, (1) ⇒ (8)) and the T4 glue `HenselEtaleLift`
(Hensel's property in scheme form) of the source; both mention only Mathlib notions. Whether they
are definitionally the source propositions is for an independent replay to check; here they are
proved as stated.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace HenselDivision

/-- Verbatim body of the T4 leaf `StacksHenselEtaleSection`. -/
def StacksHenselEtaleSectionStmt : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (S : Type) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime],
    q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
    Function.Surjective ((Ideal.Quotient.mk q).comp (algebraMap R S)) →
    ∃ τ : S →ₐ[R] R, q = (IsLocalRing.maximalIdeal R).comap τ

/-- Verbatim body of the T4 glue `HenselEtaleLift`. -/
def HenselEtaleLiftStmt : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) [Etale f]
    (b : Spec (.of R) ⟶ Y) (a₀ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X),
    a₀ ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ b →
    ∃ a : Spec (.of R) ⟶ X, a ≫ f = b ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ a = a₀

theorem stacksHenselEtaleSection_proof : StacksHenselEtaleSectionStmt := by
  intro R _ _ S _ _ _ q _ hq hsurj
  let φ : R →+* S ⧸ q := (Ideal.Quotient.mk q).comp (algebraMap R S)
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal R := by
    rw [← hq, ← RingHom.comap_ker, Ideal.mk_ker]
  let e1 : S ⧸ q ≃+* R ⧸ RingHom.ker φ := (RingHom.quotientKerEquivOfSurjective hsurj).symm
  let e2 : R ⧸ RingHom.ker φ ≃+* R ⧸ IsLocalRing.maximalIdeal R := Ideal.quotEquivOfEq hker
  let ψ0 : S →+* IsLocalRing.ResidueField R :=
    (e1.trans e2).toRingHom.comp (Ideal.Quotient.mk q)
  have hψ0 : ∀ r : R, ψ0 (algebraMap R S r) = algebraMap R (IsLocalRing.ResidueField R) r := by
    intro r
    have h1 : e1 (φ r) = Ideal.Quotient.mk (RingHom.ker φ) r := by
      rw [RingEquiv.symm_apply_eq]
      exact (RingHom.quotientKerEquivOfSurjective_apply_mk hsurj r).symm
    change e2 (e1 (φ r)) = _
    rw [h1, Ideal.quotEquivOfEq_mk]
    rfl
  let ψ : S →ₐ[R] IsLocalRing.ResidueField R := { ψ0 with commutes' := hψ0 }
  obtain ⟨τ, hτ, -⟩ := etale_existsUnique_lift ψ
  refine ⟨τ, ?_⟩
  ext x
  rw [Ideal.mem_comap, ← IsLocalRing.residue_eq_zero_iff]
  have hres : IsLocalRing.residue R (τ x) = ψ0 x := AlgHom.congr_fun hτ x
  rw [hres]
  constructor
  · intro hx
    change e2 (e1 (Ideal.Quotient.mk q x)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero]
  · intro hx
    have h0 : (e1.trans e2) (Ideal.Quotient.mk q x) = 0 := hx
    rw [map_eq_zero_iff _ (e1.trans e2).injective] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0

theorem henselEtaleLift_proof : HenselEtaleLiftStmt := by
  intro R _ _ X Y f _ b a₀ h
  have hc : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) = closedPt R := by
    rw [closedPt, IsLocalRing.ResidueField.algebraMap_eq]
  rw [hc] at h ⊢
  have : Etale (pullback.snd f b) :=
    MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback f b) ‹Etale f›
  let x : Spec (.of (IsLocalRing.ResidueField R)) ⟶ pullback f b := pullback.lift a₀ (closedPt R) h
  have hx : x ≫ pullback.snd f b = closedPt R := pullback.lift_snd _ _ _
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := etale_section_existsUnique (pullback.snd f b) x hx
  refine ⟨s ≫ pullback.fst f b, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]
  · rw [← Category.assoc, hs2, pullback.lift_fst]

end HenselDivision

#check @HenselDivision.stacksHenselEtaleSection_proof
#check @HenselDivision.henselEtaleLift_proof
#print axioms HenselDivision.stacksHenselEtaleSection_proof
#print axioms HenselDivision.henselEtaleLift_proof
