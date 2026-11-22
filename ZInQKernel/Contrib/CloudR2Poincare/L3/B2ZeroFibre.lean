import ZInQKernel.Contrib.CloudR2Poincare.L3.B2LocalModel
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2StalkModel
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2LerayUse

/-! All actual higher direct images zero forces zero native cohomology on an
actual rational Cartesian fibre, through the actual local model and its stalk
contraction. No reverse base-change/model hypothesis is assumed. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- A finite-free native model has locally free terms, in the native class
consumed by the actual scheme-stalk freeness supplier. -/
theorem locallyFree_terms_of_finiteFreeComplex {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ) (bound : ℕ)
    (hP : Scheme.Modules.IsFiniteFreeComplex P bound) :
    ∀ n : ℤ, (P.X n).IsLocallyFree := by
  intro n
  obtain ⟨r, ⟨e⟩⟩ := hP.exists_iso_free n
  haveI : (SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r))).IsFiniteLocallyFreeOfRank r :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_free r
  haveI : (P.X n).IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree (P.X n) r

/-- The reverse native model-to-fibre coupling. Only genuine zero higher
DIRECT-IMAGE SHEAVES are the premise; the local model is constructed here. -/
theorem native_fibre_H_zero_of_higherDirectImages_zero
    {k : Type u} [Field k] (B : PkgI3.AbVar k) {X : Scheme.{u}}
    (f : X ⟶ B.X.left) [IsProper f] [Flat f] (F : X.Modules) [F.IsInvertible]
    (slice : (𝟙_ (Over (Spec (.of k))) ⟶ B.X) → (B.X.left ⟶ X))
    (hsquare : ∀ b, IsPullback (slice b) B.X.hom f b.left)
    (hR : ∀ q : ℕ, IsZero ((Scheme.Modules.higherDirectImage f q).obj F))
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) :
    ∀ q : ℕ, Subsingleton (((Scheme.Modules.pullback (slice b)).obj F).H q) := by
  classical
  haveI : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  let y := b.left (IsLocalRing.closedPoint k)
  obtain ⟨U, P, bound, hyU, hP, comparison⟩ := exists_local_native_model f F y
  let Q : CochainComplex U.toScheme.Modules ℤ :=
    ((Scheme.Modules.pullback (𝟙 U.toScheme)).mapHomologicalComplex (.up ℤ)).obj P
  have hQ : Scheme.Modules.IsFiniteFreeComplex Q bound :=
    hP.pullback_complex (𝟙 U.toScheme)
  have comparisonQ : UniversalModelComparison f F U Q :=
    comparison.pullback_open (𝟙 U.toScheme) (by simp)
  have hQzero (q : ℕ) : IsZero (Q.homology q) := by
    have hzero : IsZero (((Scheme.Modules.higherDirectImage f q).obj F).restrict U.ι) :=
      (Scheme.Modules.restrictFunctor U.ι).map_isZero (hR q)
    obtain ⟨e⟩ := nonempty_model_restriction_iso f F comparison (𝟙 U.toScheme) (by simp) q
    exact hzero.of_iso e.symm
  haveI : Q.IsStrictlyGE 0 := hQ.isStrictlyGE
  haveI : Q.IsStrictlyLE (bound : ℤ) := hQ.isStrictlyLE
  have hacyclic : Q.Acyclic := by
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    by_cases hn : n < 0
    · exact ShortComplex.isZero_homology_of_isZero_X₂ _
        (CochainComplex.isZero_of_isStrictlyGE Q 0 n hn)
    · have heq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
      simpa only [heq] using hQzero n.toNat
  haveI : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have hrange : Set.range b.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    change b.left t ∈ U
    rw [Subsingleton.elim t (IsLocalRing.closedPoint k)]
    exact hyU
  let g : Spec (.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι b.left hrange
  have hg : g ≫ U.ι = b.left := IsOpenImmersion.lift_fac _ _ _
  have hfibre (i : ℕ) : IsZero ((Scheme.Modules.higherDirectImage B.X.hom i).obj
      ((Scheme.Modules.pullback (slice b)).obj F)) := by
    have hmodel := isZero_homology_pullback_of_bounded_locallyFree_acyclic Q (bound : ℤ)
      (locallyFree_terms_of_finiteFreeComplex Q bound hQ) hacyclic g (i : ℤ)
    obtain ⟨e⟩ := comparisonQ g (slice b) B.X.hom (by rw [hg]; exact hsquare b) i
    exact hmodel.of_iso e.symm
  intro q
  exact native_global_H_zero_of_higherDirectImages_zero B.X.hom
    ((Scheme.Modules.pullback (slice b)).obj F) hfibre q

end ZInQ.Contrib.CloudR2Poincare.L3
