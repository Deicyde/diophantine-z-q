import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RelativeConstants
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ResidueRoots

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ZInQ.ToricOrthogonality

private theorem specMap_appTop_apply {R S : Type} [CommRing R] [CommRing S]
    (j : R →+* S) (a : Γ(Spec (.of R), ⊤)) :
    (Scheme.ΓSpecIso (.of S)).hom ((Spec.map (CommRingCat.ofHom j)).appTop a) =
      j ((Scheme.ΓSpecIso (.of R)).hom a) := by
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

/-- A global coefficient from a local domain is one if its value at a generic
test point is a prime-to-residue root of unity and its value at a geometric
residue test point is one. -/
theorem global_eq_one_of_residue_at_points
    {R K k : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Field k]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) (hconst : Function.Surjective f.appTop)
    (j : R →+* K) (hj : Function.Injective j)
    (i : IsLocalRing.ResidueField R →+* k)
    (g : Spec (.of K) ⟶ X) (hg : g ≫ f = Spec.map (CommRingCat.ofHom j))
    (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (i.comp (IsLocalRing.residue R))))
    {n : ℕ} (hn : (n : IsLocalRing.ResidueField R) ≠ 0) (u : Γ(X, ⊤))
    (hu : (g.appTop u) ^ n = 1) (hu' : s.appTop u = 1) : u = 1 := by
  obtain ⟨a, rfl⟩ := hconst u
  let b := (Scheme.ΓSpecIso (.of R)).hom a
  have hb : b ^ n = 1 := by
    apply hj
    rw [map_pow, map_one, ← specMap_appTop_apply, ← map_pow]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg] at hu
    rw [hu, map_one]
  have hbr : IsLocalRing.residue R b = 1 := by
    apply i.injective
    rw [← RingHom.comp_apply, ← specMap_appTop_apply, map_one]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs] at hu'
    rw [hu', map_one]
  have h1 := eq_one_of_residue_eq_one hn hb hbr
  have ha : a = 1 := by
    apply (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
    change b = (Scheme.ΓSpecIso (.of R)).hom 1
    rw [map_one]
    exact h1
  rw [ha, map_one]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.global_eq_one_of_residue_at_points
