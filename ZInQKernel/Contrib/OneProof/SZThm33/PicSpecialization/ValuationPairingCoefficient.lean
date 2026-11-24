import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RelativeCoefficient

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ZInQ.ToricOrthogonality

/-- Evaluate a relative Weil function at the identity over the valuation ring.
The resulting integral scalar is one when its generic value is a root of
unity of invertible residue order and its special value is one. -/
theorem eval_eq_one_of_specialization_at_section
    {R K k : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Field k]
    {X : Scheme.{0}} (s : Spec (.of R) ⟶ X)
    (j : R →+* K) (hj : Function.Injective j)
    (i : IsLocalRing.ResidueField R →+* k)
    {n : ℕ} (hn : (n : IsLocalRing.ResidueField R) ≠ 0) (u : Γ(X, ⊤))
    (hu : ((Spec.map (CommRingCat.ofHom j) ≫ s).appTop u) ^ n = 1)
    (hres : (Spec.map (CommRingCat.ofHom (i.comp (IsLocalRing.residue R))) ≫ s).appTop u = 1) :
    s.appTop u = 1 := by
  let f : Spec (.of R) ⟶ Spec (.of R) := 𝟙 _
  have hconst : Function.Surjective f.appTop := by
    simpa [f] using (Function.surjective_id : Function.Surjective (id : Γ(Spec (.of R), ⊤) → Γ(Spec (.of R), ⊤)))
  refine global_eq_one_of_residue_at_points f hconst j hj i
    (Spec.map (CommRingCat.ofHom j)) (Category.comp_id _)
    (Spec.map (CommRingCat.ofHom (i.comp (IsLocalRing.residue R)))) (Category.comp_id _)
    hn (s.appTop u) ?_ ?_
  · exact hu
  · exact hres

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.eval_eq_one_of_specialization_at_section
