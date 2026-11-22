import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.AcyclicResolution

/-!
# The native edge comparison for a complex with vanishing lower homology

Source credit: the cycle/boundary comparison uses the actual W07
`Cohomology/AcyclicResolution.lean` short exact sequences and maps (Jacobian-
Challenge c4254cce15b3e284a0a3ae1d73936f2ee195d272, Apache-2.0; W07 LICENSE/NOTICE).
Unlike its all-degree degeneration theorem, this owned proof uses acyclicity of
homology only strictly below the degree being compared. Native providers are
not changed. No spectral-sequence, Leray or coefficient Fact is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits Abelian

namespace ZInQ.Contrib.CloudR2Poincare.L3.NativeEdge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {Y : Scheme.{u}}

/-- A zero native coefficient has zero native cohomology, by identity versus zero. -/
theorem subsingleton_H_of_isZero (F : Y.Modules) (hF : IsZero F) (q : ℕ) :
    Subsingleton (F.H q) := by
  apply subsingleton_of_forall_eq 0
  intro z
  have h := congrArg (fun f : F ⟶ F => Scheme.Modules.H.map f q z)
    (hF.eq_of_src (𝟙 F) 0)
  simpa only [Scheme.Modules.H.map_id_apply, Scheme.Modules.H.map_zero_apply] using h

/-- Only homology in degrees below r is used to show cycles below r acyclic. -/
theorem subsingleton_H_cycles_below (L : CochainComplex Y.Modules ℕ)
    (hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1))) (r : ℕ)
    (hH : ∀ j : ℕ, j < r → ∀ m : ℕ, Subsingleton ((L.homology j).H (m + 1))) :
    ∀ j : ℕ, j < r → ∀ m : ℕ, Subsingleton ((L.cycles j).H (m + 1)) := by
  intro j
  induction j with
  | zero =>
    intro hj m
    haveI := L.isIso_homologyπ 0 0 (by simp) (by simp)
    haveI := hH 0 hj m
    exact (Scheme.Modules.H.mapLinearEquiv (asIso (L.homologyπ 0))
      (m + 1)).injective.subsingleton
  | succ j ih =>
    intro hj m
    have hZ : ∀ m : ℕ, Subsingleton ((L.cycles j).H (m + 1)) :=
      fun m => ih (by omega) m
    haveI : Subsingleton ((Scheme.Modules.boundariesHomologyShortComplex L j).X₁.H
        (m + 1)) := Scheme.Modules.subsingleton_H_image L hL j hZ m
    haveI : Subsingleton ((Scheme.Modules.boundariesHomologyShortComplex L j).X₃.H
        (m + 1)) := hH (j + 1) hj m
    exact Scheme.Modules.subsingleton_H_X₂_of_shortExact
      (Scheme.Modules.shortExact_boundariesHomologyShortComplex L j) (m + 1)

/-- At n+1, the homology projection is surjective on sections using only lower homology. -/
theorem surjective_app_homologyπ_of_lower (L : CochainComplex Y.Modules ℕ)
    (hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1))) (n : ℕ)
    (hH : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L.homology j).H (m + 1))) :
    Function.Surjective ((L.homologyπ (n + 1)).app ⊤).hom := by
  have hZ := subsingleton_H_cycles_below L hL (n + 1) hH n (by omega)
  haveI : Subsingleton ((Scheme.Modules.boundariesHomologyShortComplex L n).X₁.H 1) :=
    Scheme.Modules.subsingleton_H_image L hL n hZ 0
  exact Scheme.Modules.surjective_app_g_of_subsingleton
    (Scheme.Modules.shortExact_boundariesHomologyShortComplex L n)

/-- The kernel is exactly the sections coming from the previous term; no H^{n+1}
acyclicity is assumed for the current homology sheaf. -/
theorem ker_app_homologyπ_of_lower (L : CochainComplex Y.Modules ℕ)
    (hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1))) (n : ℕ)
    (hH : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L.homology j).H (m + 1))) :
    ((L.homologyπ (n + 1)).app ⊤).hom.ker =
      ((L.toCycles n (n + 1)).app ⊤).hom.range := by
  refine (Scheme.Modules.range_app_f_eq_ker_app_g
    (Scheme.Modules.shortExact_boundariesHomologyShortComplex L n)).symm.trans ?_
  haveI : Subsingleton ((Scheme.Modules.cyclesBoundariesShortComplex L n).X₁.H 1) :=
    subsingleton_H_cycles_below L hL (n + 1) hH n (by omega) 0
  have hsurj := Scheme.Modules.surjective_app_g_of_subsingleton
    (Scheme.Modules.shortExact_cyclesBoundariesShortComplex L n)
  change ((Limits.image.ι (L.toCycles n (n + 1))).app ⊤).hom.range = _
  conv_rhs => rw [← Limits.image.fac (L.toCycles n (n + 1))]
  have hsurj' : Function.Surjective ((factorThruImage (L.toCycles n (n + 1))).app ⊤).hom :=
    hsurj
  rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.range_comp,
    AddMonoidHom.range_eq_top.mpr hsurj', ← AddMonoidHom.range_eq_map]

/-- The actual canonical quotient comparison at the edge degree. -/
def homologySectionsEdgeAddEquiv (L : CochainComplex Y.Modules ℕ)
    (hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1))) (n : ℕ)
    (hH : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L.homology j).H (m + 1))) :
    Γ(L.homology (n + 1), ⊤) ≃+
      Γ(L.cycles (n + 1), ⊤) ⧸ ((L.toCycles n (n + 1)).app ⊤).hom.range :=
  ((QuotientAddGroup.quotientAddEquivOfEq (ker_app_homologyπ_of_lower L hL n hH)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_app_homologyπ_of_lower L hL n hH))).symm

/-- The inverse edge comparison is the actual homology projection on sections. -/
theorem homologySectionsEdgeAddEquiv_homologyπ (L : CochainComplex Y.Modules ℕ)
    (hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1))) (n : ℕ)
    (hH : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L.homology j).H (m + 1))) (z : Γ(L.cycles (n + 1), ⊤)) :
    homologySectionsEdgeAddEquiv L hL n hH ((L.homologyπ (n + 1)).app ⊤ z) =
      QuotientAddGroup.mk z := by
  rw [homologySectionsEdgeAddEquiv, AddEquiv.symm_apply_eq, AddEquiv.trans_apply]
  exact (QuotientAddGroup.kerLift_mk _ z).symm

/-- The edge quotient comparison is natural in the actual chain map. -/
theorem homologySectionsEdgeAddEquiv_naturality
    {L L' : CochainComplex Y.Modules ℕ} (χ : L ⟶ L')
    (hL : ∀ j m : ℕ, Subsingleton ((L.X j).H (m + 1)))
    (hL' : ∀ j m : ℕ, Subsingleton ((L'.X j).H (m + 1))) (n : ℕ)
    (hH : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L.homology j).H (m + 1)))
    (hH' : ∀ j : ℕ, j < n + 1 → ∀ m : ℕ,
      Subsingleton ((L'.homology j).H (m + 1))) (y : Γ(L.homology (n + 1), ⊤)) :
    homologySectionsEdgeAddEquiv L' hL' n hH'
        ((HomologicalComplex.homologyMap χ (n + 1)).app ⊤ y) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap χ (n + 1)).app ⊤).hom
        (Scheme.Modules.range_app_toCycles_le_comap χ n)
        (homologySectionsEdgeAddEquiv L hL n hH y) := by
  obtain ⟨z, rfl⟩ := surjective_app_homologyπ_of_lower L hL n hH y
  rw [homologySectionsEdgeAddEquiv_homologyπ, QuotientAddGroup.map_mk]
  have h : ((HomologicalComplex.homologyMap χ (n + 1)).app ⊤)
      (((L.homologyπ (n + 1)).app ⊤) z) =
      ((L'.homologyπ (n + 1)).app ⊤)
        (((HomologicalComplex.cyclesMap χ (n + 1)).app ⊤) z) := by
    change ((L.homologyπ (n + 1) ≫ HomologicalComplex.homologyMap χ (n + 1)).app ⊤) z =
      ((HomologicalComplex.cyclesMap χ (n + 1) ≫ L'.homologyπ (n + 1)).app ⊤) z
    rw [HomologicalComplex.homologyπ_naturality]
  rw [h, homologySectionsEdgeAddEquiv_homologyπ]

end ZInQ.Contrib.CloudR2Poincare.L3.NativeEdge
