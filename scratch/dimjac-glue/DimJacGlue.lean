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


omit [Algebra ℚ F] in
/-- The image of a valuation ring `R` in a field `F` that is a fraction field of `R` is a valuation
subring of `F`. -/
def imageVS {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] (f : R →+* F)
    (hf : ∀ z : F, ∃ a b : R, f b ≠ 0 ∧ z * f b = f a) : ValuationSubring F where
  toSubring := f.range
  mem_or_inv_mem' z := by
    obtain ⟨a, b, hb, hz⟩ := hf z
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · by_cases ha : f a = 0
      · left
        have : z * f b = 0 := hz.trans ha
        rw [mul_eq_zero] at this
        rcases this with h | h
        · exact ⟨0, by rw [map_zero, h]⟩
        · exact absurd h hb
      · right
        refine ⟨c, ?_⟩
        have h1 : z * f a * f c = f a := by rw [mul_assoc, ← map_mul, hc, hz]
        have h2 : z * f c = 1 := mul_left_cancel₀ ha (by linear_combination h1)
        exact eq_inv_of_mul_eq_one_right h2
    · left
      refine ⟨c, ?_⟩
      have : f b * f c = f b * z := by rw [← map_mul, hc, ← hz, mul_comm]
      exact mul_left_cancel₀ hb this

omit [IsIntegral X] in
lemma key_identity (a b c d s u : F) (hc : c * s = a) (hd : d * u = b) :
    (s * u * u) • (c • KaehlerDifferential.D ℚ F d) =
      a • (u • KaehlerDifferential.D ℚ F b - b • KaehlerDifferential.D ℚ F u) := by
  subst hc hd
  rw [Derivation.leibniz]
  simp only [smul_add, smul_sub, smul_smul]
  module


lemma Φ_range_smul (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a : Γ(X, U))
    {η : Ω[F⁄ℚ]} (h : η ∈ (Φ g e U hU hne).range) : ψ e U hne a • η ∈ (Φ g e U hU hne).range := by
  obtain ⟨σ, rfl⟩ := h
  exact ⟨a • σ, Φ_smul U hU hne a σ⟩

/-- A maximal ideal of `Γ(X, V)` gives a closed point of `X` (`X` is Jacobson). -/
lemma isClosed_fromSpec [SmoothOfRelativeDimension 1 g] (V : X.Opens) (hV : IsAffineOpen V)
    (y : PrimeSpectrum Γ(X, V)) (hy : y.asIdeal.IsMaximal) : IsClosed ({hV.fromSpec y} : Set X) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have hyc : IsClosed ({y} : Set (PrimeSpectrum Γ(X, V))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hy
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hmem : y ∈ closedPoints (Spec Γ(X, V)) := hyc
  rw [← h] at hmem
  exact hmem

/-- **Local–global step.** A differential regular at every place lies in the image of `Φ_V`. -/
lemma mem_range_Φ_of_regular [SmoothOfRelativeDimension 1 g] (V : X.Opens) (hV : IsAffineOpen V)
    (hne : (V : Set X).Nonempty) (ω : Ω[F⁄ℚ])
    (hω : ∀ w : ValuationSubring F, (∀ c : ℚ, algebraMap ℚ F c ∈ w) →
      ω ∈ ZInQ.Contrib.CurvesG.regularAt F w) :
    ω ∈ (Φ g e V hV hne).range := by
  classical
  by_contra hnot
  let I : Ideal Γ(X, V) :=
    { carrier := {a | ψ e V hne a • ω ∈ (Φ g e V hV hne).range}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, add_smul] at *
        exact add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero, zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_smul] at *
        exact Φ_range_smul V hV hne c ha }
  have hI : I ≠ ⊤ := fun h => hnot (by
    have : (1 : Γ(X, V)) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using this)
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
  let y : PrimeSpectrum Γ(X, V) := ⟨𝔪, h𝔪.isPrime⟩
  have hyV : hV.fromSpec y ∈ V := hV.range_fromSpec.subset ⟨y, rfl⟩
  have hxc := isClosed_fromSpec (g := g) V hV y h𝔪
  haveI := valuationRing_stalk (g := g) (hV.fromSpec y) hxc
  letI : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) := (X.presheaf.germ V _ hyV).hom.toAlgebra
  haveI hloc : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hyV
  haveI : Nonempty V := hne.to_subtype
  let f : X.presheaf.stalk (hV.fromSpec y) →+* F :=
    e.toRingHom.comp (algebraMap (X.presheaf.stalk (hV.fromSpec y)) X.functionField)
  have hf_germ : ∀ a, f (algebraMap Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) a) = ψ e V hne a := by
    intro a
    change e (algebraMap _ X.functionField (X.presheaf.germ V _ hyV a)) = _
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl
  have hfrac : ∀ z : F, ∃ a b, f b ≠ 0 ∧ z * f b = f a := by
    intro z
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (hV.fromSpec y))
      (e.symm z)
    refine ⟨a, b, ?_, ?_⟩
    · exact fun h => (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := X.functionField) hb)
        (e.injective (h.trans (map_zero e).symm))
    · have hb' : algebraMap _ X.functionField b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := X.functionField) hb
      have h1 : algebraMap _ X.functionField a = e.symm z * algebraMap _ X.functionField b := by
        rw [← hab, div_mul_cancel₀ _ hb']
      have h2 := congrArg e h1
      rw [map_mul, RingEquiv.apply_symm_apply] at h2
      exact h2.symm
  let w := imageVS f hfrac
  have hwQ : ∀ c : ℚ, algebraMap ℚ F c ∈ w := by
    intro c
    refine ⟨(X.presheaf.germ V _ hyV).hom ((g.specStructureMap V).hom c), ?_⟩
    exact congrArg (· c) (RingHom.ext_rat
      (f.comp ((X.presheaf.germ V _ hyV).hom.comp (g.specStructureMap V).hom)) (algebraMap ℚ F))
  have key : ∀ η ∈ ZInQ.Contrib.CurvesG.regularAt F w,
      ∃ t : Γ(X, V), t ∉ 𝔪 ∧ ψ e V hne t • η ∈ (Φ g e V hV hne).range := by
    intro η hη
    induction hη using AddSubgroup.closure_induction with
    | mem η hη =>
      obtain ⟨c, d, ⟨c', rfl⟩, ⟨d', rfl⟩, rfl⟩ := hη
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl c'
      obtain ⟨⟨b, u⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl d'
      have hc : f (IsLocalization.mk' _ a s) * ψ e V hne s = ψ e V hne a := by
        rw [← hf_germ, ← hf_germ, ← map_mul, IsLocalization.mk'_spec]
      have hd : f (IsLocalization.mk' _ b u) * ψ e V hne u = ψ e V hne b := by
        rw [← hf_germ, ← hf_germ, ← map_mul, IsLocalization.mk'_spec]
      refine ⟨s * u * u, ?_, ?_⟩
      · have hs : (s : Γ(X, V)) ∉ 𝔪 := s.2
        have hu : (u : Γ(X, V)) ∉ 𝔪 := u.2
        intro h
        rcases h𝔪.isPrime.mem_or_mem h with h | h
        · rcases h𝔪.isPrime.mem_or_mem h with h | h
          · exact hs h
          · exact hu h
        · exact hu h
      · rw [map_mul, map_mul, key_identity _ _ _ _ _ _ hc hd]
        refine ⟨a • ((u : Γ(X, V)) • g.sectionsD V b - b • g.sectionsD V (u : Γ(X, V))), ?_⟩
        rw [Φ_smul, map_sub, Φ_smul_D, Φ_smul_D]
    | zero => exact ⟨1, fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    | add η₁ η₂ _ _ h₁ h₂ =>
      obtain ⟨t₁, ht₁, h₁⟩ := h₁
      obtain ⟨t₂, ht₂, h₂⟩ := h₂
      refine ⟨t₁ * t₂, fun h => (h𝔪.isPrime.mem_or_mem h).elim ht₁ ht₂, ?_⟩
      have e1 := Φ_range_smul V hV hne t₂ h₁
      have e2 := Φ_range_smul V hV hne t₁ h₂
      have : ψ e V hne (t₁ * t₂) • (η₁ + η₂) =
          ψ e V hne t₂ • (ψ e V hne t₁ • η₁) + ψ e V hne t₁ • (ψ e V hne t₂ • η₂) := by
        rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm (ψ e V hne t₂)]
      rw [this]
      exact add_mem e1 e2
    | neg η _ h =>
      obtain ⟨t, ht, h⟩ := h
      exact ⟨t, ht, by rw [smul_neg]; exact neg_mem h⟩
  obtain ⟨t, ht, htω⟩ := key ω (hω w hwQ)
  exact ht (hI𝔪 htω)


/-- **Surjectivity onto the regular differentials**, by gluing the local preimages. -/
lemma mem_range_ΦG_of_regular [SmoothOfRelativeDimension 1 g] (ω : Ω[F⁄ℚ])
    (hω : ∀ w : ValuationSubring F, (∀ c : ℚ, algebraMap ℚ F c ∈ w) →
      ω ∈ ZInQ.Contrib.CurvesG.regularAt F w) :
    ω ∈ (ΦG g e).range := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  choose σ hσ using fun (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty) =>
    mem_range_Φ_of_regular (g := g) (e := e) V hV hne ω hω
  obtain ⟨s, hs⟩ := exists_glue (g := g) ⊤ (fun V hV hne _ => σ V hV hne) (by
    intro V V' W hV hV' hW hVne hV'ne hWne _ _ hWV hWV'
    apply Φ_injective (e := e) W hW hWne
    rw [Φ_res hWV hV hW hWne, Φ_res hWV' hV' hW hWne, hσ, hσ])
  refine ⟨s, ?_⟩
  rw [ΦG_eq (U₀ X) U₀_spec.1 ⟨_, U₀_spec.2⟩, hs (U₀ X) U₀_spec.1 ⟨_, U₀_spec.2⟩]
  exact hσ _ _ _

end DimJacGlue

namespace ModularSplit.DimJac

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves ZInQ.Contrib.CurvesG

/-- **GLUE (named, unproved): `H⁰(X, Ω¹_{X/ℚ})` is the space of differentials of the function field
regular at every place.** For a smooth proper geometrically connected integral curve `X/ℚ` and a field `F`
isomorphic to its function field, `dim_ℚ H⁰(X, Ω¹_{X/ℚ}) = g(F)` (`CurvesG.fieldGenus`, Chevalley's
definition). Needs: `H⁰(X, M) = Γ(X, M)` for the library's sheaf cohomology; `Γ(X, Ω¹) = ⋂_x Ω_{𝒪_{X,x}/ℚ}`
inside `Ω_{F/ℚ}` (`Ω¹` locally free of rank one, `X` integral; on affine opens `Γ(U, Ω¹) = Ω_{Γ(U)/ℚ}` is the
library's `Scheme.Hom.kaehlerSectionsEquiv`, then localization); the image of `Ω_{𝒪_{X,x}/ℚ}` in `Ω_{F/ℚ}` is
`CurvesG.regularAt F 𝒪_{X,x}`; every valuation subring of `F` containing `ℚ` other than `F` is a local ring
`𝒪_{X,x}` at a closed point (`X` proper: valuative criterion; `X` normal of dimension one: `𝒪_{X,x}` is a
DVR), and conversely. Standard (Hartshorne II.8, II.6.7, II.4.7; Stichtenoth 1.5; UNVERIFIED numbers);
project glue, no published-theorem content beyond textbook sheaf theory. -/
def H0DifferentialsEqHolo : Prop :=
  ∀ (X : Over SpecQ) (_ : IsCurve X) (_ : IsIntegral X.left) (F : Type) [Field F] [Algebra ℚ F],
    Nonempty (X.left.functionField ≃+* F) →
    letI : X.left.Over SpecQ := ⟨X.hom⟩
    (X.left ↘ SpecQ).relativeDifferentials.finrankH ℚ 0 = fieldGenus F

open DimJacGlue in
/-- **`H0DifferentialsEqHolo` from the one named glue `ValuationCenter`.** -/
theorem h0DifferentialsEqHolo_of_valuationCenter (hC : ValuationCenter) : H0DifferentialsEqHolo := by
  intro X hX hI F _ _ he
  obtain ⟨e⟩ := he
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  have : IsProper (X.left ↘ SpecQ) := hX.proper
  have : SmoothOfRelativeDimension 1 (X.left ↘ SpecQ) := hX.smooth
  have : Smooth (X.left ↘ SpecQ) := SmoothOfRelativeDimension.smooth 1 _
  let g := X.left ↘ SpecQ
  let E1 := (Scheme.Modules.H.zeroLinearEquiv g.relativeDifferentials).toAddEquiv
  let Ψ : g.relativeDifferentials.H 0 →+ Ω[F⁄ℚ] := (ΦG g e).comp E1.toAddMonoidHom
  let L : g.relativeDifferentials.H 0 →ₗ[ℚ] Ω[F⁄ℚ] :=
    { toFun := Ψ
      map_add' := map_add Ψ
      map_smul' := map_rat_smul Ψ }
  have hL : Function.Injective L := (ΦG_injective (e := e)).comp E1.injective
  have hrange : LinearMap.range L = holoDiff F := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ΦG_mem_holo hC _
    · refine Submodule.span_le.mpr (fun ω hω => ?_)
      obtain ⟨s, hs⟩ := mem_range_ΦG_of_regular (g := g) (e := e) ω hω
      exact ⟨E1.symm s, by simp [L, Ψ, hs]⟩
  unfold Scheme.Modules.finrankH fieldGenus
  rw [← hrange]
  exact (LinearEquiv.ofInjective L hL).finrank_eq

end ModularSplit.DimJac

#print axioms ModularSplit.DimJac.h0DifferentialsEqHolo_of_valuationCenter
#print axioms DimJacGlue.kaehlerToFractionFieldInjective
