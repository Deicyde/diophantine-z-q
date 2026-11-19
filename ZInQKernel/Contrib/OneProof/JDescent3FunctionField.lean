import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq

/-! The function field and the rational identity place of the actual abelian curve. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

variable {L : Type} [Field L]

/-- The underlying scheme of an abelian variety over a field is integral. -/
theorem abVar_isIntegral (A : PkgI3.AbVar L) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

attribute [local instance] abVar_isIntegral

/-- The actual function field of the underlying scheme, its generic stalk. -/
abbrev AbVarFunctionField (A : PkgI3.AbVar L) : Type := A.X.left.functionField

/-- The constants in the generic stalk are induced by the structural morphism. -/
abbrev abVarFunctionFieldAlgebra (A : PkgI3.AbVar L) : Algebra L (AbVarFunctionField A) :=
  (AlgebraicCurve.baseToFunctionField A.X.hom).toAlgebra

attribute [local instance] abVarFunctionFieldAlgebra

/-- A dimension-one abelian variety is smooth of relative dimension one over its field. -/
theorem abVar_smoothRelDimOne (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    SmoothOfRelativeDimension 1 A.X.hom := by
  have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth A.X.hom x
  let _ := (A.X.hom.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of L), U) Γ(A.X.left, V) := h
  obtain ⟨i₀, i₁, _, _, ⟨P⟩⟩ := h'.out
  have hP := P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨z, hzV, hzc⟩ := nonempty_inter_closedPoints (Z := (V : Set A.X.left)) ⟨x, hxV⟩
    V.isOpen.isLocallyClosed
  have h₁ := (ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart A.X.hom hV e P.dimension hP z hzV hzc).1
  have h₂ := (ZInQ.Contrib.Dim.topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth A.X.hom z hzc).1
  have hd : P.dimension = 1 := by
    have : ((P.dimension : ℕ) : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) := by
      rw [← h₁, ← h₂]
      exact hdim
    exact_mod_cast this
  exact ⟨U, hU, V, hV, hxV, e, hd ▸ hP⟩

/-- The generic stalk of a dimension-one abelian variety in characteristic zero is a Tau Ceti
function field over the ground field. -/
theorem abVar_isFunctionField [CharZero L] (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    TauCeti.IsFunctionField L (AbVarFunctionField A) := by
  let _ := abVar_smoothRelDimOne A hdim
  have : Algebra.EssFiniteType L (AbVarFunctionField A) :=
    AlgebraicCurve.essFiniteType_functionField A.X.hom
  have : AlgebraicCurve.IsCurveOver L (AbVarFunctionField A) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      A.X.hom (RingEquiv.refl _) (fun _ => rfl)
  obtain ⟨t, ht, hfin, _⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := L) (F := AbVarFunctionField A)
  exact ⟨t, ht, hfin⟩

/-- The underlying scheme morphism of the group identity. -/
abbrev abVarUnit (A : PkgI3.AbVar L) : Spec (CommRingCat.of L) ⟶ A.X.left :=
  (η[A.X] : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ A.X).left

/-- The identity as a point of the underlying scheme. -/
abbrev abVarIdentity (A : PkgI3.AbVar L) : A.X.left :=
  abVarUnit A (IsLocalRing.closedPoint L)

/-- The image of the unit section is a closed point. -/
theorem abVarIdentity_isClosed (A : PkgI3.AbVar L) :
    IsClosed ({abVarIdentity A} : Set A.X.left) :=
  ZInQ.Contrib.Dim.isClosed_singleton_of_section A.X.hom (abVarUnit A) (Over.w η[A.X]) _

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue field of the place attached to a rational section has degree one. -/
private theorem degree_eq_one_of_section_stalk {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of L)) (s : Spec (.of L) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    let _ := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    ∀ P : TauCeti.Place L X.functionField,
      (algebraMap (X.presheaf.stalk (s (IsLocalRing.closedPoint L))) X.functionField).range =
        P.integers.toSubring → P.degree = 1 := by
  intro alg P hP
  let _ := alg
  let q : X := s (IsLocalRing.closedPoint L)
  let R := X.presheaf.stalk q
  let incl : R →+* X.functionField := algebraMap R X.functionField
  let e : R ≃+* P.integers :=
    RingEquiv.ofBijective (incl.codRestrict P.integers.toSubring (fun a => hP ▸ ⟨a, rfl⟩))
      ⟨fun _ _ hab => IsFractionRing.injective R X.functionField (congrArg Subtype.val hab),
        fun ⟨a, ha⟩ => by
          obtain ⟨b, hb⟩ : a ∈ incl.range := hP.symm ▸ ha
          exact ⟨b, Subtype.ext hb⟩⟩
  let ev : R →+* L := (Scheme.stalkClosedPointTo s).hom
  have : IsLocalHom ev := Scheme.isLocalHom_stalkClosedPointTo' s
  let ρ : P.ResidueField →+* L :=
    (IsLocalRing.ResidueField.lift ev).comp (IsLocalRing.ResidueField.mapEquiv e.symm).toRingHom
  apply (TauCeti.Place.degree_eq_one_iff_algebraMap_surjective P).2
  intro b
  refine ⟨ρ b, ρ.injective ?_⟩
  suffices hc : ∀ a : L, ρ (algebraMap L P.ResidueField a) = a by exact hc _
  intro a
  let v : R := (X.presheaf.germ ⊤ q trivial).hom
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom a))
  have hv : algebraMap L P.integers a = e v := by
    apply Subtype.ext
    change algebraMap L X.functionField a = incl v
    open P2MW.S_AlgebraicCurve_exists_place_range_stalk_eq in
    exact AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk f q a
  have he : ev v = a := by
    let i := Scheme.ΓSpecIso (CommRingCat.of L)
    have hsf : f.appTop ≫ s.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
    change (Scheme.stalkClosedPointTo s).hom
      (X.presheaf.germ ⊤ (s (IsLocalRing.closedPoint L)) trivial (f.appTop (i.inv a))) = a
    rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo s ⊤ trivial]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      TopologicalSpace.Opens.map_top, eqToHom_refl, op_id]
    change i.hom (s.appTop (f.appTop (i.inv a))) = a
    have happ : s.appTop (f.appTop (i.inv a)) = i.inv a := by
      calc
        _ = (f.appTop ≫ s.appTop) (i.inv a) := rfl
        _ = _ := by rw [hsf]; rfl
    exact (congrArg (fun b => i.hom b) happ).trans (Iso.inv_hom_id_apply i a)
  rw [P.algebraMap_residueField, hv]
  simpa [ρ] using he

/-- The local ring at the identity defines a rational place of the actual function field. -/
theorem abVar_exists_identityPlace [CharZero L] (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    ∃ P : TauCeti.Place L (AbVarFunctionField A), P.degree = 1 ∧
      (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
        (AbVarFunctionField A)).range = P.integers.toSubring := by
  let _ := abVar_smoothRelDimOne A hdim
  obtain ⟨v, hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq A.X.hom (abVarIdentity A)
    (abVarIdentity_isClosed A)
  let P := TauCeti.Place.ofValuationSubring (A := v.toValuationSubring)
    (abVar_isFunctionField A hdim) v.algebraMap_mem' v.ne_top'
  have hP : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
      (AbVarFunctionField A)).range = P.integers.toSubring := by
    simpa [P, TauCeti.Place.integers_ofValuationSubring] using hv
  exact ⟨P, degree_eq_one_of_section_stalk A.X.hom (abVarUnit A) (Over.w η[A.X]) P hP, hP⟩

/-- A rational place forces the ground field to be the exact constant field. Specialization
embeds the relative algebraic closure of the ground field into the rational residue field. -/
private theorem isIntegrallyClosedIn_of_rationalPlace {F : Type} [Field F] [Algebra L F]
    (P : TauCeti.Place L F) (hP : P.degree = 1) : IsIntegrallyClosedIn L F := by
  let C := algebraicClosure L F
  let e : C →+* P.integers :=
    (algebraMap C F).codRestrict P.integers.toSubring fun a =>
      (Subring.isIntegrallyClosedIn_iff (S := P.integers.toSubring)).mp
        (inferInstanceAs (IsIntegrallyClosedIn P.integers F))
        ((mem_algebraicClosure_iff'.mp a.2).tower_top (A := P.integers))
  let r : C →+* P.ResidueField := (IsLocalRing.residue P.integers).comp e
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap L F).injective, ?_⟩
  intro x hx
  let x' : C := ⟨x, mem_algebraicClosure_iff'.mpr hx⟩
  obtain ⟨a, ha⟩ := (P.degree_eq_one_iff_algebraMap_surjective.mp hP) (r x')
  have hres : r (algebraMap L C a) = algebraMap L P.ResidueField a := by
    rw [P.algebraMap_residueField]
    change IsLocalRing.residue P.integers (e (algebraMap L C a)) =
      IsLocalRing.residue P.integers (algebraMap L P.integers a)
    congr 1
  have h := congrArg (fun b : C => (b : F)) (r.injective (hres.trans ha))
  exact ⟨a, h⟩

/-- The number field is the exact constant field of the generic stalk. -/
theorem abVar_exactConstants [CharZero L] (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    IsIntegrallyClosedIn L (AbVarFunctionField A) := by
  obtain ⟨P, hP, _⟩ := abVar_exists_identityPlace A hdim
  exact isIntegrallyClosedIn_of_rationalPlace P hP

/-- The remaining genus comparison: the generic stalk of the actual dimension-one abelian
variety has genus one in Tau Ceti's divisor-theoretic definition. -/
def AbVarFunctionFieldGenusOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = 1 →
    TauCeti.genus K (AbVarFunctionField A) = 1

/-- Once the genus comparison is available, the identity has the full positive pole-space
dimension ladder. There are functions with exact poles of orders two and three there and
no poles at any other place. -/
theorem abVar_identityPoleSpaces_of_genusOne [NumberField L] (hgenus : AbVarFunctionFieldGenusOne)
    (A : PkgI3.AbVar L) (hdim : A.dim = 1) :
    ∃ P : TauCeti.Place L (AbVarFunctionField A), P.degree = 1 ∧
      (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
        (AbVarFunctionField A)).range = P.integers.toSubring ∧
      (∀ n : ℕ, 1 ≤ n →
        TauCeti.Divisor.dim (Finsupp.single P (n : ℤ) :
          TauCeti.Divisor L (AbVarFunctionField A)) = n) ∧
      (∀ n : ℕ, 2 ≤ n → ∃ x : AbVarFunctionField A,
        x ≠ 0 ∧ P.ord x = -(n : ℤ) ∧ ∀ Q, Q ≠ P → 0 ≤ Q.ord x) := by
  obtain ⟨P, hP, hstalk⟩ := abVar_exists_identityPlace A hdim
  have hF := abVar_isFunctionField A hdim
  have hex := isIntegrallyClosedIn_of_rationalPlace P hP
  have hg := hgenus L A hdim
  refine ⟨P, hP, hstalk, fun n hn => TauCeti.Divisor.dim_single_of_genus_eq_one hF hex hg hP hn,
    fun n hn => P.exists_ord_eq_neg_and_forall_ne_ord_nonneg hF hex (by simpa [hg] using hn)⟩

#print axioms abVar_isIntegral
#print axioms abVar_smoothRelDimOne
#print axioms abVar_isFunctionField
#print axioms abVarIdentity_isClosed
#print axioms degree_eq_one_of_section_stalk
#print axioms abVar_exists_identityPlace
#print axioms isIntegrallyClosedIn_of_rationalPlace
#print axioms abVar_exactConstants
#print axioms abVar_identityPoleSpaces_of_genusOne

end

end HDec.CMBranch.CMjBridges
