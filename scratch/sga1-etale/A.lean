import ZInQKernel.Contrib.OneProof.UniformizationTopology

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace SGA1Etale

open UnifPrinted UnifTopology

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- Restriction to a basic open commutes with the coordinate ring map. -/
theorem eval₂Hom_res {U : X.left.Opens} (s : Γ(X.left, U)) {n : ℕ} (f : Fin n → Γ(X.left, U)) :
    MvPolynomial.eval₂Hom (algC X (X.left.basicOpen s)) (fun i => res (X.left.basicOpen_le s) (f i)) =
      (X.left.presheaf.map (homOfLE (X.left.basicOpen_le s)).op).hom.comp
        (MvPolynomial.eval₂Hom (algC X U) f) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply]
    simp only [algC]
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]
  · intro i
    simp [res]

/-- Étale coordinates restrict to basic opens. -/
theorem etale_res {U : X.left.Opens} (hU : IsAffineOpen U) (s : Γ(X.left, U)) {n : ℕ}
    (f : Fin n → Γ(X.left, U)) (hf : (MvPolynomial.eval₂Hom (algC X U) f).Etale) :
    (MvPolynomial.eval₂Hom (algC X (X.left.basicOpen s))
      (fun i => res (X.left.basicOpen_le s) (f i))).Etale := by
  rw [eval₂Hom_res]
  refine RingHom.Etale.stableUnderComposition _ _ hf ?_
  let _ := (X.left.presheaf.map (homOfLE (X.left.basicOpen_le s)).op).hom.toAlgebra
  have := hU.isLocalization_basicOpen s
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)

/-- **Smooth implies locally étale over affine space** (Mathlib's
`Smooth.exists_isStandardSmooth` and `RingHom.IsStandardSmooth.exists_etale_mvPolynomial`). -/
theorem exists_etale_chart [Smooth X.hom] (x : X.left) :
    ∃ (U : X.left.Opens), IsAffineOpen U ∧ x ∈ U ∧ ∃ (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale := by
  obtain ⟨U', hU', V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth X.hom x
  obtain rfl : U' = ⊤ := eq_top_iff.mpr fun y _ => by
    rw [Subsingleton.elim y (X.hom.base x)]; exact e hxV
  obtain ⟨n, g, hgC, hg⟩ := hst.exists_etale_mvPolynomial
  refine ⟨V, hV, hxV, n, fun i => g (MvPolynomial.X i), ?_⟩
  have heq : MvPolynomial.eval₂Hom (algC X V) (fun i => g (MvPolynomial.X i)) =
      g.comp (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.coe_comp,
        Function.comp_apply, MvPolynomial.map_C]
      rw [← RingHom.comp_apply g MvPolynomial.C, hgC]
      rfl
    · intro i
      simp
  rw [heq]
  refine RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective ?_) hg
  exact (MvPolynomial.mapEquiv (Fin n)
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv).bijective

/-- **A nonempty open of a `ℂ`-scheme locally of finite type has a `ℂ`-point** (Hilbert's
Nullstellensatz, Mathlib's `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`). -/
theorem exists_cPt_of_mem [LocallyOfFiniteType X.hom] {V : X.left.Opens} {x : X.left}
    (hx : x ∈ V) : ∃ P : CPt X, XPtIn X P V := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType X.hom (inferInstance)
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by rw [Scheme.Hom.preimage_top]; exact le_top)
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have hft' : (algC X W).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ hsurj)
  letI := (algC X W).toAlgebra
  obtain ⟨k, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  set f : Fin k → Γ(X.left, W) := fun i => φ (MvPolynomial.X i) with hfdef
  have hgen : Generates W f := by
    intro y
    obtain ⟨p, hp⟩ := hφ y
    refine ⟨p, ?_⟩
    rw [← hp]
    conv_rhs => rw [MvPolynomial.aeval_unique φ]
    rfl
  have hnt : Nontrivial Γ(X.left, W) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h10 : X.left.basicOpen (1 : Γ(X.left, W)) = X.left.basicOpen (0 : Γ(X.left, W)) := by
      rw [Subsingleton.elim (1 : Γ(X.left, W)) 0]
    rw [Scheme.basicOpen_one, Scheme.basicOpen_zero] at h10
    have : x ∈ (⊥ : X.left.Opens) := h10 ▸ hxW
    exact this
  set I := RingHom.ker (MvPolynomial.eval₂Hom (algC X W) f)
  have hI : I ≠ ⊤ := RingHom.ker_ne_top _
  obtain ⟨w, hw⟩ : (MvPolynomial.zeroLocus ℂ I).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h2 := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I
    rw [h, MvPolynomial.vanishingIdeal_empty] at h2
    exact hI (Ideal.radical_eq_top.mp h2.symm)
  have hwz : w ∈ zeroLocus f := fun p hp => by
    have := hw p (RingHom.mem_ker.mpr hp)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  rw [← range_coord hW f hgen] at hwz
  obtain ⟨P, -⟩ := hwz
  exact ⟨P.1, xPtIn_mono hWV P.2⟩

end SGA1Etale
