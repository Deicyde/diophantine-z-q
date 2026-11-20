import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Main
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.GroupSchemeEquidim
import ZInQKernel.Contrib.CloudR2Poincare.FinalUnconditional

/-! # Splitting homomorphisms of abelian varieties up to isogeny

For a surjective homomorphism with a positive-dimensional kernel, remove a
positive-dimensional abelian subvariety of that kernel by Poincaré
complementarity. Induction on the dimension of the source yields a section
up to multiplication by a nonzero integer.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj PkgI3.AbVar
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.AVSplitMorphisms

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in
private theorem dimension_nat (A : PkgI3.AbVar K) : ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : Nonempty (TopologicalSpace.IrreducibleCloseds A.X.left) := ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
  have hn : 0 ≤ A.dim := Order.krullDim_nonneg
  have hf : A.dim ≠ ⊤ := CloudR2Poincare.L4.scheme_dimension_ne_top A.X.hom
  cases h : A.dim with
  | bot => simp [h] at hn
  | coe d =>
    cases d with
    | top => exact (hf h).elim
    | coe n => exact ⟨n,rfl⟩

private theorem surjective_section_aux (d : ℕ) (A B : PkgI3.AbVar K)
    (hd : A.dim = (d : WithBot ℕ∞)) (f : Hom A B) (hf : Surjective f.hom.left) :
    ∃ (s : Hom B A) (n : ℕ), 0 < n ∧ s.hom ≫ f.hom = ((n : ℤ) : End B).hom := by
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    have := AVGlue.isProper_hom' f.hom
    by_cases hq : LocallyQuasiFinite f.hom.left
    · have hfin := IsFinite.of_isProper_of_locallyQuasiFinite f.hom.left
      obtain ⟨n, hn, s, _, hs⟩ := MilneQuasiInverse.milneIsogenyQuasiInverse_proof K A B f ⟨hfin,hf⟩
      exact ⟨s,n,hn,hs⟩
    have hker := AVGlue.kernelAbSubvariety_of_identityComponent (AVGlue.kernelIdentityComponent_of_leaves
      CloudR2Poincare.L3.cartierSmooth_proof geomConnOfRationalPoint_proof groupSchemeEquidim_proof)
    obtain ⟨C, j, hj, hC, hjf⟩ := hker K A B f hq
    obtain ⟨Z, i, hiso⟩ := CloudR2Poincare.poincareComplement_proof K A C j hj
    let m : C.X ⊗ Z.X ⟶ A.X := (fst C.X Z.X ≫ j.hom) * (snd C.X Z.X ≫ i.hom)
    have : IsFinite m.left := hiso.1
    have : Surjective m.left := hiso.2
    have hdim := (CloudR2Poincare.L4.product_dimension_lower_bound C Z).trans
      (CloudR2Poincare.L4.dimension_eq_of_finite_surjective m.left).le
    obtain ⟨c,hc⟩ := dimension_nat C
    obtain ⟨z,hz⟩ := dimension_nat Z
    change C.dim + Z.dim ≤ A.dim at hdim
    rw [hc, hz, hd, ← Nat.cast_add] at hdim
    rw [hc] at hC
    have hcz : c + z ≤ d := by exact_mod_cast hdim
    have hcpos : 0 < c := by exact_mod_cast hC
    have hsmall : z < d := by omega
    let g : Hom Z B := Hom.mk' (i.hom ≫ f.hom)
    have heq : m ≫ f.hom = snd C.X Z.X ≫ g.hom := by
      simp only [m, MonObj.mul_comp, Category.assoc, hjf, MonObj.comp_one, _root_.one_mul]
      rfl
    have : Surjective (m.left ≫ f.hom.left) := inferInstance
    have hs : Surjective ((snd C.X Z.X).left ≫ g.hom.left) := congrArg (fun t => Surjective t.left) heq ▸ this
    obtain ⟨t, n, hn, ht⟩ := ih z hsmall Z hz g (Surjective.of_comp (snd C.X Z.X).left g.hom.left)
    exact ⟨Hom.mk' (t.hom ≫ i.hom), n, hn, (Category.assoc _ _ _).trans ht⟩

/-- A surjective homomorphism of abelian varieties in characteristic zero
admits a section after multiplication by a positive integer. -/
theorem exists_section_up_to_mul {A B : PkgI3.AbVar K} (f : Hom A B) (hf : Surjective f.hom.left) :
    ∃ (s : Hom B A) (n : ℕ), 0 < n ∧ s.hom ≫ f.hom = ((n : ℤ) : End B).hom := by
  obtain ⟨d, hd⟩ := dimension_nat A
  exact surjective_section_aux d A B hd f hf

/-- A closed abelian subvariety has a retraction up to multiplication by
a positive integer, obtained by projecting the inverse Poincaré isogeny. -/
theorem exists_retraction_up_to_mul {C A : PkgI3.AbVar K} (j : Hom C A) (hj : IsClosedImmersion j.hom.left) :
    ∃ (s : Hom A C) (n : ℕ), 0 < n ∧ j.hom ≫ s.hom = ((n : ℤ) : End C).hom := by
  obtain ⟨Z, i, hiso⟩ := CloudR2Poincare.poincareComplement_proof K A C j hj
  let P := AVGlue.prodAbVar C Z
  let m : P.X ⟶ A.X := (fst C.X Z.X ≫ j.hom) * (snd C.X Z.X ≫ i.hom)
  have : IsMonHom m := by
    change IsMonHom (lift (fst C.X Z.X ≫ j.hom) (snd C.X Z.X ≫ i.hom) ≫ μ[A.X])
    infer_instance
  let q : Hom P A := Hom.mk' m
  obtain ⟨n, hn, r, hm, _⟩ := MilneQuasiInverse.milneIsogenyQuasiInverse_proof K P A q hiso
  let u : C.X ⟶ P.X := lift (𝟙 C.X) (1 : C.X ⟶ Z.X)
  have hu : u ≫ q.hom = j.hom := by
    change lift (𝟙 C.X) (1 : C.X ⟶ Z.X) ≫ ((fst _ _ ≫ j.hom) * (snd _ _ ≫ i.hom)) = _
    simp [MonObj.comp_mul, MonObj.one_comp]
  refine ⟨Hom.mk' (r.hom ≫ fst C.X Z.X), n, hn, ?_⟩
  change j.hom ≫ r.hom ≫ fst C.X Z.X = _
  rw [← hu, Category.assoc, ← Category.assoc q.hom, hm, AVGlue.natCast_hom, AVGlue.natCast_hom,
    MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, show u ≫ fst C.X Z.X = 𝟙 C.X from lift_fst ..]

/-- Every endomorphism of an abelian variety in characteristic zero has an
inner inverse up to multiplication by a positive integer. -/
theorem exists_inner_inverse_up_to_mul (A : PkgI3.AbVar K) (f : End A) :
    ∃ (g : End A) (n : ℕ), 0 < n ∧ f*g*f = n • f := by
  obtain ⟨B, p, i, hp, hi, hpi⟩ := AVGlue.imageFactorization_of_cartier
    CloudR2Poincare.L3.cartierSmooth_proof K A A f
  obtain ⟨s, m, hm, hps⟩ := exists_section_up_to_mul p hp
  obtain ⟨r, n, hn, hir⟩ := exists_retraction_up_to_mul i hi
  let g : End A := Hom.mk' (r.hom ≫ s.hom)
  refine ⟨g, n*m, Nat.mul_pos hn hm, Hom.ext' ?_⟩
  change f.hom ≫ (r.hom ≫ s.hom) ≫ f.hom = f.hom ^ (n*m)
  rw [hpi, Category.assoc, Category.assoc r.hom, ← Category.assoc s.hom, hps,
    ← Category.assoc i.hom, hir, AVGlue.natCast_hom, AVGlue.natCast_hom]
  simp [MonObj.pow_comp, MonObj.comp_pow, ← pow_mul, mul_comm]

end ZInQ.Contrib.AVSplitMorphisms
