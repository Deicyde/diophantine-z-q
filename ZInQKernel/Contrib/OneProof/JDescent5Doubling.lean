import ZInQKernel.Contrib.OneProof.JDescent5Inversion
import ZInQKernel.Contrib.MulEtale.Direct.PowerAtIdentity

/-! The first-order effect of doubling on a parameter at the rational identity. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TauCeti
open scoped CategoryTheory.MonObj

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def abVarDoubleOver {L : Type} [Field L] (A : PkgI3.AbVar L) : A.X ⟶ A.X :=
  (𝟙 A.X) ^ (2 : ℕ)

theorem abVarDouble_fix_identity {L : Type} [Field L] (A : PkgI3.AbVar L) :
    (abVarDoubleOver A).left (abVarIdentity A) = abVarIdentity A := by
  have h : η[A.X] ≫ abVarDoubleOver A = η[A.X] := by
    rw [abVarDoubleOver, MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  exact congrArg (fun f : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ A.X =>
    f.left (IsLocalRing.closedPoint L)) h

private theorem derivation_of_residue_parameter {R B K : Type} [CommRing R] [IsDomain R]
    [CommRing B] [Field K] (e : R →+* K) (b : B →+* R)
    (hb : Function.Bijective (e.comp b)) (t : R) (ht : t ≠ 0) (ht0 : e t = 0)
    (hker : ∀ a, e a = 0 → ∃ r, a = t * r) :
    letI : Module R K := Module.compHom K e
    ∃ D : Derivation ℤ R K, (∀ s, D (b s) = 0) ∧
      ∀ a, e a = 0 → ∃ r, a = t * r ∧ D a = e r := by
  let : Module R K := Module.compHom K e
  let E := RingEquiv.ofBijective (e.comp b) hb
  let j := b.comp E.symm.toRingHom
  have hj (a : K) : e (j a) = a := E.apply_symm_apply a
  have split (a : R) : ∃ r, a - j (e a) = t * r := hker _ (by rw [map_sub, hj, sub_self])
  let q (a : R) : R := (split a).choose
  have hq (a : R) : a - j (e a) = t * q a := (split a).choose_spec
  have decomp (a : R) : a = j (e a) + t * q a := by linear_combination hq a
  have uniq (a r : R) (hr : a = j (e a) + t * r) : q a = r := by
    apply mul_left_cancel₀ ht
    linear_combination hr - decomp a
  have hq_add (a c : R) : q (a + c) = q a + q c := by
    apply uniq
    rw [map_add, map_add, mul_add]
    linear_combination decomp a + decomp c
  have hq_one : q 1 = 0 := uniq _ _ (by simp)
  have hq_b (s : B) : q (b s) = 0 := by
    apply uniq
    have hs : j (e (b s)) = b s := congrArg b (E.symm_apply_apply s)
    simp [hs]
  have hq_mul (a c : R) : q (a * c) =
      j (e a) * q c + j (e c) * q a + t * q a * q c := by
    apply uniq
    rw [map_mul, map_mul]
    conv_lhs => rw [decomp a, decomp c]
    ring
  let d : R →+ K :=
    { toFun := fun a => e (q a)
      map_zero' := by rw [show q 0 = 0 from uniq _ _ (by simp)]; exact e.map_zero
      map_add' := fun a c => by simp only [hq_add, map_add] }
  let D : Derivation ℤ R K :=
    { toLinearMap := d.toIntLinearMap
      map_one_eq_zero' := by change e (q 1) = 0; rw [hq_one, map_zero]
      leibniz' := by
        intro a c
        change e (q (a * c)) = e a * e (q c) + e c * e (q a)
        rw [hq_mul, map_add, map_add, map_mul, map_mul, hj, hj, map_mul, map_mul, ht0]
        ring }
  refine ⟨D, fun s => ?_, fun a ha => ⟨q a, ?_, rfl⟩⟩
  · change e (q (b s)) = 0
    rw [hq_b, map_zero]
  · simpa only [ha, map_zero, zero_add] using decomp a

private theorem abVar_identity_parameter_dvd {L : Type} [Field L] (A : PkgI3.AbVar L)
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring)
    (t a : A.X.left.presheaf.stalk (abVarIdentity A))
    (ht : P.ord (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
      (AbVarFunctionField A) t) = 1) (ha : A.X.left.residue (abVarIdentity A) a = 0) :
    ∃ r, a = t * r := by
  let X := A.X.left
  let O := abVarIdentity A
  let R := X.presheaf.stalk O
  let F := AbVarFunctionField A
  let φ : R →+* F := algebraMap R F
  have hi := IsFractionRing.injective R F
  have ht' : P.ord (φ t) = 1 := ht
  have ht0 : φ t ≠ 0 := fun h => by rw [h, P.ord_zero] at ht'; omega
  by_cases ha0 : φ a = 0
  · exact ⟨0, by rw [mul_zero]; exact hi (ha0.trans φ.map_zero.symm)⟩
  have hapos : 0 < P.ord (φ a) := by
    have hage : 0 ≤ P.ord (φ a) := P.mem_integers_iff_ord_nonneg.mp
      (show φ a ∈ P.integers.toSubring from hp ▸ ⟨a, rfl⟩)
    by_contra! h
    have he : P.ord (φ a) = 0 := le_antisymm h hage
    have hinv : (φ a)⁻¹ ∈ P.integers.toSubring :=
      P.mem_integers_iff_ord_nonneg.mpr (by rw [P.ord_inv, he, neg_zero])
    obtain ⟨w, hw⟩ : (φ a)⁻¹ ∈ φ.range := hp.symm ▸ hinv
    have hw' : a * w = 1 := hi (by rw [map_mul, hw, mul_inv_cancel₀ ha0, map_one])
    have hunit := (IsUnit.of_mul_eq_one w hw').map (X.residue O).hom
    exact hunit.ne_zero ha
  have hq : φ a / φ t ∈ P.integers.toSubring :=
    P.mem_integers_iff_ord_nonneg.mpr (by rw [P.ord_div ha0 ht0, ht']; omega)
  obtain ⟨r, hr⟩ : φ a / φ t ∈ φ.range := hp.symm ▸ hq
  exact ⟨r, hi (by
    change φ a = φ (t * r)
    rw [map_mul, hr, mul_div_cancel₀ _ ht0])⟩

private theorem fixedStalkMap_residue_zero {X : Scheme} (f : X ⟶ X) (p : X)
    (hp : f p = p) (a : X.presheaf.stalk p) (ha : X.residue p a = 0) :
    X.residue p (fixedStalkMap f p hp a) = 0 := by
  let i := X.presheaf.stalkCongr (Inseparable.of_eq hp.symm)
  have : IsLocalHom i.hom.hom := isLocalHom_of_isIso _
  have : IsLocalHom (fixedStalkMap f p hp).hom :=
    inferInstanceAs (IsLocalHom ((f.stalkMap p).hom.comp i.hom.hom))
  change IsLocalRing.residue _ ((fixedStalkMap f p hp).hom a) = 0
  change IsLocalRing.residue _ a = 0 at ha
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  exact fun hu => ha (IsLocalHom.map_nonunit (f := (fixedStalkMap f p hp).hom) _ hu)

/-- Pullback by doubling takes a parameter (t) to (2t) modulo its square. -/
theorem abVar_double_parameter_mod_square {L : Type} [Field L] (A : PkgI3.AbVar L)
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring)
    (t : A.X.left.presheaf.stalk (abVarIdentity A))
    (ht : P.ord (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A))
      (AbVarFunctionField A) t) = 1)
    (ht0 : A.X.left.residue (abVarIdentity A) t = 0) :
    ∃ u, fixedStalkMap (abVarDoubleOver A).left (abVarIdentity A) (abVarDouble_fix_identity A) t =
      2 * t + t ^ 2 * u := by
  let G := A.X
  let X := G.left
  let O := abVarIdentity A
  let R := X.presheaf.stalk O
  let K := X.residueField O
  let d := (abVarDoubleOver A).left
  let p := G.hom
  let B := (Spec (CommRingCat.of L)).presheaf.stalk (p O)
  let b := (p.stalkMap O).hom
  let e := (X.residue O).hom
  let f := fixedStalkMap d O (abVarDouble_fix_identity A)
  let : Module R K := Module.compHom K e
  have ho : p O = IsLocalRing.closedPoint L := Subsingleton.elim _ _
  let i := (Spec (CommRingCat.of L)).presheaf.stalkCongr (Inseparable.of_eq ho) ≪≫
    AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of L)
  have hι : IsIso (p.residueFieldMap O) :=
    AlgebraicGeometry.isIso_residueFieldMap_of_mem_range_section
      p (abVarUnit A) (Over.w (η[A.X])) (IsLocalRing.closedPoint L)
  have hb : Function.Bijective (e.comp b) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, ?_⟩
    · intro x hx
      by_contra hne
      have hu : IsUnit (i.hom x) := isUnit_iff_ne_zero.mpr (fun hz =>
        hne (i.commRingCatIsoToRingEquiv.injective (hz.trans i.hom.hom.map_zero.symm)))
      have : IsLocalHom i.hom.hom := isLocalHom_of_isIso _
      exact ((IsLocalHom.map_nonunit (f := i.hom.hom) _ hu).map (e.comp b)).ne_zero hx
    ·
      have hb' : e.comp b = (p.residueFieldMap O).hom.comp
          (((Spec (CommRingCat.of L)).residue (p O)).hom) :=
        congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap p O).symm
      rw [hb']
      exact (asIso (p.residueFieldMap O)).commRingCatIsoToRingEquiv.surjective.comp
        ((Spec (CommRingCat.of L)).residue_surjective (p O))
  have ht' : t ≠ 0 := by
    intro h
    rw [h, map_zero, P.ord_zero] at ht
    omega
  obtain ⟨D, hDb, hD⟩ := derivation_of_residue_parameter e b hb t ht' ht0
    (fun a ha => abVar_identity_parameter_dvd A P hp t a ht ha)
  have hDer : ∃ r, t = t * r ∧ D t = e r := hD t ht0
  obtain ⟨r, hr, hrD⟩ := hDer
  have hDt : D t = 1 := by
    have hr' : r = 1 := mul_left_cancel₀ ht' (by simpa only [_root_.mul_one] using hr.symm)
    rw [hrD, hr', map_one]
  let D' : tangentDerivations p O := ⟨D, hDb⟩
  let θ := derivationToDotted p O D'
  have hθ : θ.val ≫ d = (2 • θ).val := comp_pow_id_left_eq_nsmul G
    (IsLocalRing.closedPoint L) θ 1
  have he : Spec.map f ≫ X.fromSpecStalk O = X.fromSpecStalk O ≫ d := by
    change Spec.map (fixedStalkMap d O _) ≫ X.fromSpecStalk O = _
    rw [fixedStalkMap, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hDft : D (f t) = 2 * D t := by
    have hh : f ≫ dottedStalkHom p O θ = dottedStalkHom p O (2 • θ) := by
      apply Spec.map_inj.mp
      apply (cancel_mono (X.fromSpecStalk O)).mp
      rw [Spec.map_comp, Category.assoc, he, ← Category.assoc, dottedStalkHom_spec,
        dottedStalkHom_spec]
      exact hθ
    have hj := congrArg (fun g : R ⟶ CommRingCat.of (DualNumber K) => (g t).snd) hh
    change (dottedToDerivation p O θ).val (f t) = (dottedToDerivation p O (2 • θ)).val t at hj
    rw [two_nsmul, dottedToDerivation_add, dottedToDerivation_derivationToDotted] at hj
    exact hj.trans (two_mul (D t)).symm
  let a := f t - 2 * t
  have ha : e a = 0 := by
    change e (f t - 2 * t) = 0
    have hft := fixedStalkMap_residue_zero d O (abVarDouble_fix_identity A) t ht0
    change e (f t) = 0 at hft
    rw [map_sub, map_mul, hft, ht0, mul_zero, sub_zero]
  have hDa : D a = 0 := by
    change D (f t - 2 * t) = 0
    simp only [map_sub, hDft, two_mul, map_add, sub_self]
  obtain ⟨v, hv, hvD⟩ := hD a ha
  obtain ⟨u, hu⟩ := abVar_identity_parameter_dvd A P hp t v ht (hvD.symm.trans hDa)
  refine ⟨u, ?_⟩
  rw [hu] at hv
  change f t - 2 * t = t * (t * u) at hv
  linear_combination hv

#print axioms abVarDouble_fix_identity
#print axioms derivation_of_residue_parameter
#print axioms abVar_identity_parameter_dvd
#print axioms fixedStalkMap_residue_zero
#print axioms abVar_double_parameter_mod_square

end

end HDec.CMBranch.CMjBridges
