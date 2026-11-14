import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.Dim.Basic

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace DimJacGlue

variable {X : Scheme.{0}} [IsIntegral X] (g : X ⟶ Spec (CommRingCat.of ℚ))
  {F : Type} [Field F] [Algebra ℚ F] (e : X.functionField ≃+* F)

lemma generic_mem (U : X.Opens) (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- `Γ(X, U) → F`, the germ at the generic point followed by `e`. -/
def ψ (U : X.Opens) (hU : (U : Set X).Nonempty) : Γ(X, U) →+* F :=
  e.toRingHom.comp (X.presheaf.germ U (genericPoint X) (generic_mem U hU)).hom

/-- `Φ_U : Γ(Ω, U) → Ω_{F/ℚ}` for an affine nonempty open `U`. -/
def Φ (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    Γ(g.relativeDifferentials, U) →+ Ω[F⁄ℚ] :=
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  (KaehlerDifferential.map ℚ ℚ Γ(X, U) F).toAddMonoidHom.comp
    (g.kaehlerSectionsEquiv U rfl hU).symm.toLinearMap.toAddMonoidHom


variable {g e}

lemma kse_smul_D (U : X.Opens) (hU : IsAffineOpen U) (a b : Γ(X, U)) :
    letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
    g.kaehlerSectionsEquiv U rfl hU (a • KaehlerDifferential.D ℚ Γ(X, U) b) = a • g.sectionsD U b := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  rw [LinearEquiv.map_smul, Scheme.Hom.kaehlerSectionsEquiv_D]

/-- Induction principle for sections of `Ω¹` over an affine open. -/
lemma induction_affine (U : X.Opens) (hU : IsAffineOpen U) (P : Γ(g.relativeDifferentials, U) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ a b : Γ(X, U), P (a • g.sectionsD U b)) (s : Γ(g.relativeDifferentials, U)) : P s := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  obtain ⟨η, rfl⟩ := (g.kaehlerSectionsEquiv U rfl hU).surjective s
  suffices H : ∀ c : Γ(X, U), P (g.kaehlerSectionsEquiv U rfl hU (c • η)) by simpa using H 1
  have hη : η ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D ℚ Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro c; rw [kse_smul_D]; exact hgen c b
  | zero => intro c; simpa using h0
  | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact hadd _ _ (hx c) (hy c)
  | smul a x _ hx => intro c; rw [smul_smul]; exact hx _

lemma Φ_smul_D (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a b : Γ(X, U)) :
    Φ g e U hU hne (a • g.sectionsD U b) = ψ e U hne a • KaehlerDifferential.D ℚ F (ψ e U hne b) := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  have := kse_smul_D (g := g) U hU a b
  simp only [Φ, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
    LinearEquiv.coe_coe]
  rw [← this, LinearEquiv.symm_apply_apply, LinearMap.map_smul, KaehlerDifferential.map_D]
  rfl

lemma Φ_smul (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a : Γ(X, U))
    (s : Γ(g.relativeDifferentials, U)) :
    Φ g e U hU hne (a • s) = ψ e U hne a • Φ g e U hU hne s := by
  induction s using induction_affine U hU with
  | h0 => simp
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | hgen c b => rw [smul_smul, Φ_smul_D, Φ_smul_D, map_mul, mul_smul]


lemma ψ_res {U V : X.Opens} (h : V ≤ U) (hV : (V : Set X).Nonempty) (a : Γ(X, U)) :
    ψ e V hV (X.presheaf.map (homOfLE h).op a) =
      ψ e U (hV.mono h) a := by
  simp only [ψ, RingHom.coe_comp, Function.comp_apply]
  congr 1
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ a

lemma Φ_res {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hne : (V : Set X).Nonempty) (s : Γ(g.relativeDifferentials, U)) :
    Φ g e V hV hne (g.relativeDifferentials.presheaf.map (homOfLE h).op s) =
      Φ g e U hU (hne.mono h) s := by
  induction s using induction_affine U hU with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | hgen a b =>
    rw [Scheme.Modules.map_smul, ← Scheme.Hom.sectionsD_map, Φ_smul_D, Φ_smul_D, ψ_res, ψ_res]


/-- **GLUE (proved below, `kaehlerToFractionFieldInjective`).** For a domain `A` smooth over `ℚ` with fraction
field `K`, `Ω_{A/ℚ} → Ω_{K/ℚ}` is injective (`Ω_A` is projective, hence torsion-free, and `Ω_K` is its
localization). -/
def KaehlerToFractionFieldInjective : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [Field K] [Algebra ℚ K]
    [Algebra A K] [IsScalarTower ℚ A K] [IsFractionRing A K],
    Function.Injective (KaehlerDifferential.map ℚ ℚ A K)

theorem kaehlerToFractionFieldInjective : KaehlerToFractionFieldInjective := by
  intro A K _ _ _ _ _ _ _ _ _
  have hloc : IsLocalizedModule (nonZeroDivisors A) (KaehlerDifferential.map ℚ ℚ A K) :=
    KaehlerDifferential.isLocalizedModule_map ℚ A K (nonZeroDivisors A)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) _).mp hx
  have hreg : IsRegular r := IsRegular.of_ne_zero (nonZeroDivisors.ne_zero hr)
  exact Module.Flat.isSMulRegular_of_isRegular (M := Ω[A⁄ℚ]) hreg (by simpa using hrx)


omit [IsIntegral X] in
lemma smooth_sections [Smooth g] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
    Algebra.Smooth ℚ Γ(X, U) := by
  have h1 : RingHom.Smooth (g.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE @Smooth g ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have : RingHom.Smooth (g.specStructureMap U).hom := by
    have := RingHom.Smooth.comp h2 h1
    simpa [Scheme.Hom.specStructureMap] using this
  exact this

lemma isFractionRing_ψ (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
    IsFractionRing Γ(X, U) F := by
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : Nonempty U := hne.to_subtype
  have h := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Γ(X, U))
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

lemma Φ_injective [Smooth g] (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    Function.Injective (Φ g e U hU hne) := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  haveI := smooth_sections (g := g) U hU
  haveI := isFractionRing_ψ (e := e) U hU hne
  haveI : IsDomain Γ(X, U) := by
    haveI : Nonempty U := hne.to_subtype
    infer_instance
  exact (kaehlerToFractionFieldInjective Γ(X, U) F).comp (g.kaehlerSectionsEquiv U rfl hU).symm.injective


omit [IsIntegral X] in
lemma res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(g.relativeDifferentials, U)) :
    g.relativeDifferentials.presheaf.map (homOfLE h₂).op
        (g.relativeDifferentials.presheaf.map (homOfLE h₁).op s) =
      g.relativeDifferentials.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma exists_affine_generic (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ V : X.Opens, IsAffineOpen V ∧ genericPoint X ∈ V ∧ V ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (generic_mem W hW) W.2
  exact ⟨V, hV, hηV, hVW⟩

lemma univ_nonempty : (Set.univ : Set X).Nonempty := Set.univ_nonempty

/-- A fixed nonempty affine open. -/
def U₀ (X : Scheme.{0}) [IsIntegral X] : X.Opens :=
  Classical.choose (exists_affine_generic (X := X) ⊤ (by simp))

lemma U₀_spec : IsAffineOpen (U₀ X) ∧ genericPoint X ∈ U₀ X :=
  ⟨(Classical.choose_spec (exists_affine_generic (X := X) ⊤ (by simp))).1,
   (Classical.choose_spec (exists_affine_generic (X := X) ⊤ (by simp))).2.1⟩

variable (g e) in
/-- The global map `Φ : Γ(X, Ω¹) → Ω_{F/ℚ}`. -/
def ΦG : Γ(g.relativeDifferentials, ⊤) →+ Ω[F⁄ℚ] :=
  (Φ g e (U₀ X) U₀_spec.1 ⟨_, U₀_spec.2⟩).comp
    (g.relativeDifferentials.presheaf.map (homOfLE (le_top : U₀ X ≤ ⊤)).op).hom

lemma Φ_eq_of_affine {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUne : (U : Set X).Nonempty) (hVne : (V : Set X).Nonempty) {T : X.Opens} (hUT : U ≤ T) (hVT : V ≤ T)
    (s : Γ(g.relativeDifferentials, T)) :
    Φ g e U hU hUne (g.relativeDifferentials.presheaf.map (homOfLE hUT).op s) =
      Φ g e V hV hVne (g.relativeDifferentials.presheaf.map (homOfLE hVT).op s) := by
  have hUV : ((U ⊓ V : X.Opens) : Set X).Nonempty :=
    ⟨genericPoint X, (show genericPoint X ∈ U ⊓ V from ⟨generic_mem U hUne, generic_mem V hVne⟩)⟩
  obtain ⟨W, hW, hηW, hWUV⟩ := exists_affine_generic (U ⊓ V) hUV
  have hWne : (W : Set X).Nonempty := ⟨_, hηW⟩
  rw [← Φ_res (hWUV.trans inf_le_left) hU hW hWne, ← Φ_res (hWUV.trans inf_le_right) hV hW hWne,
    res_res, res_res]

lemma ΦG_eq (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty)
    (s : Γ(g.relativeDifferentials, ⊤)) :
    ΦG g e s = Φ g e V hV hne (g.relativeDifferentials.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) :=
  Φ_eq_of_affine _ _ _ _ _ _ s


omit [IsIntegral X] in
/-- Locality of sections of `Ω¹` along the affine opens. -/
lemma eq_of_affine_restrict (T : X.Opens) (s t : Γ(g.relativeDifferentials, T))
    (h : ∀ V : X.Opens, IsAffineOpen V → (V : Set X).Nonempty → ∀ hVT : V ≤ T,
      g.relativeDifferentials.presheaf.map (homOfLE hVT).op s =
        g.relativeDifferentials.presheaf.map (homOfLE hVT).op t) : s = t := by
  let ι := {V : X.Opens // IsAffineOpen V ∧ (V : Set X).Nonempty ∧ V ≤ T}
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨g.relativeDifferentials.presheaf, g.relativeDifferentials.isSheaf⟩
    (fun i : ι => i.1) T (fun i => homOfLE i.2.2.2) ?_ s t (fun i => h i.1 i.2.1 i.2.2.1 i.2.2.2)
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx T.2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨x, hxV⟩, hVT⟩, hxV⟩

lemma ΦG_injective [Smooth g] : Function.Injective (ΦG g e) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine eq_of_affine_restrict ⊤ s 0 (fun V hV hne hVT => ?_)
  rw [map_zero]
  apply Φ_injective (e := e) V hV hne
  rw [map_zero, ← hs, ΦG_eq V hV hne]

omit [IsIntegral X] in
/-- Gluing of sections of `Ω¹` given on the affine opens. -/
lemma exists_glue (T : X.Opens)
    (σ : ∀ V : X.Opens, IsAffineOpen V → (V : Set X).Nonempty → V ≤ T → Γ(g.relativeDifferentials, V))
    (compat : ∀ (V V' W : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hW : IsAffineOpen W)
      (hVne : (V : Set X).Nonempty) (hV'ne : (V' : Set X).Nonempty) (hWne : (W : Set X).Nonempty)
      (hVT : V ≤ T) (hV'T : V' ≤ T) (hWV : W ≤ V) (hWV' : W ≤ V'),
      g.relativeDifferentials.presheaf.map (homOfLE hWV).op (σ V hV hVne hVT) =
        g.relativeDifferentials.presheaf.map (homOfLE hWV').op (σ V' hV' hV'ne hV'T)) :
    ∃ s : Γ(g.relativeDifferentials, T), ∀ (V : X.Opens) (hV : IsAffineOpen V)
      (hne : (V : Set X).Nonempty) (hVT : V ≤ T),
      g.relativeDifferentials.presheaf.map (homOfLE hVT).op s = σ V hV hne hVT := by
  let ι := {V : X.Opens // IsAffineOpen V ∧ (V : Set X).Nonempty ∧ V ≤ T}
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨g.relativeDifferentials.presheaf, g.relativeDifferentials.isSheaf⟩
    (fun i : ι => i.1) T (fun i => homOfLE i.2.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx T.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨x, hxV⟩, hVT⟩, hxV⟩)
    (fun i => σ i.1 i.2.1 i.2.2.1 i.2.2.2) (by
      intro i j
      refine eq_of_affine_restrict (g := g) (i.1 ⊓ j.1) _ _ (fun W hW hWne hWij => ?_)
      change g.relativeDifferentials.presheaf.map (homOfLE hWij).op
          (g.relativeDifferentials.presheaf.map (homOfLE inf_le_left).op _) =
        g.relativeDifferentials.presheaf.map (homOfLE hWij).op
          (g.relativeDifferentials.presheaf.map (homOfLE inf_le_right).op _)
      rw [res_res, res_res]
      exact compat _ _ W i.2.1 j.2.1 hW i.2.2.1 j.2.2.1 hWne i.2.2.2 j.2.2.2 _ _)
  exact ⟨s, fun V hV hne hVT => hs ⟨V, hV, hne, hVT⟩⟩


/-- The image of `Φ_U` lies in `regularAt F w` as soon as `ψ_U(Γ(X, U)) ⊆ w`. -/
lemma Φ_mem_regularAt (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (w : ValuationSubring F) (hw : ∀ a, ψ e U hne a ∈ w) (s : Γ(g.relativeDifferentials, U)) :
    Φ g e U hU hne s ∈ ZInQ.Contrib.CurvesG.regularAt F w := by
  induction s using induction_affine U hU with
  | h0 => rw [map_zero]; exact zero_mem _
  | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  | hgen a b =>
    rw [Φ_smul_D]
    exact AddSubgroup.subset_closure ⟨_, _, hw a, hw b, rfl⟩

/-- **GLUE (named): every place of the function field of a proper integral `ℚ`-scheme has a center.**
For `X` integral and proper over `ℚ` and a valuation subring `w` of the function field containing `ℚ`,
some local ring `𝒪_{X,x}` maps into `w` (valuative criterion of properness, Mathlib
`IsProper.eq_valuativeCriterion`; Hartshorne II.4.7, UNVERIFIED number). -/
def ValuationCenter : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (g : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper g]
    (w : ValuationSubring X.functionField), (∀ q : ℚ, (q : X.functionField) ∈ w) →
    ∃ x : X, ∀ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a ∈ w

lemma ΦG_mem_holo (hC : ValuationCenter) [IsProper g] (s : Γ(g.relativeDifferentials, ⊤)) :
    ΦG g e s ∈ ZInQ.Contrib.CurvesG.holoDiff F := by
  refine Submodule.subset_span (fun w hw => ?_)
  obtain ⟨x, hx⟩ := hC X g (w.comap e.toRingHom) (fun q => by
    rw [ValuationSubring.mem_comap]
    simpa [map_ratCast] using hw q)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hne : (V : Set X).Nonempty := ⟨x, hxV⟩
  rw [ΦG_eq V hV hne]
  refine Φ_mem_regularAt V hV hne w (fun a => ?_) _
  haveI : Nonempty V := hne.to_subtype
  have := hx (X.presheaf.germ V x hxV a)
  rw [ValuationSubring.mem_comap, Scheme.algebraMap_germ_eq_germToFunctionField] at this
  exact this

/-- **Stalks at closed points of a smooth curve are valuation rings** (proved: regular local of
dimension one, `ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension` and Mathlib's
DVR TFAE). -/
lemma valuationRing_stalk [SmoothOfRelativeDimension 1 g] (x : X) (hx : IsClosed ({x} : Set X)) :
    ValuationRing (X.presheaf.stalk x) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have h := ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension g 1 x hx
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 6 2).mp h.le

end DimJacGlue
