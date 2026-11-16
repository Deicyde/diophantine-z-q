import ZInQKernel.Contrib.OneProof.SGRDirectNV
import ZInQKernel.Contrib.OneProof.ElkiesX6Star

/-!
# sgr-direct, part 2: the square root from Elkies' model of `X₆`

`SGRDirect.heckeSqrtBranchAny_of_elkies : R1R2fp → TorsionStructure → ElkiesX6StarPrinted → HeckeSqrtBranchAny`
(compiled, standard axioms), hence the final form of route NV:

`SGRDirect.heckeVertWitness_of_nvElkies : R1R2fp → TorsionStructure → QMAutCard → SerreRigidity3 →
  ALFixedPoints → NVLocalInertia → ElkiesX6StarPrinted → HDec.HeckeRestNV.HeckeVertWitness`.

The only hypothesis that is not a bundle field is `NVLocalInertia` (local algebra of tame covers; h-b1 Lemma NV
step 3). Steps:
* `elkies_coordinate`: on every triple with R1fp, R2fp, a morphism `m` to Elkies' `X_E` with
  `16 (t_E ∘ m − 1)/27 = π` on `ℚ̄`-points (R1(b) universality into the triple, `CurveBijIso`, the Möbius map from
  `ShimuraGlue.Mob.good_all`, `orbit_iff_twist`, and `MobiusGlue` from T5);
* `exists_ringHom_ker_eq`, `eq_zero_of_forall_ringHom_qbar`: Nullstellensatz for domains of finite type over `ℚ`;
* `heckeSqrtBranchAny_of_elkies`: Elkies' chart section `s` (`s² = −t_E`) pulled back along `Spec B → Y → X_E`
  (defined everywhere: every closed point of `Spec B` maps into `t_E ≠ ∞`, and opens are stable under generization)
  gives `s₀ ∈ B` with `s₀² = −(1 + 27X/16)` (density), so `(4 s₀)² = −(27X + 16)`.
-/

set_option linter.style.haveILetI false

noncomputable section

open Polynomial GlueDescent.B2Q
open HDec HDec.G0ModField HDec.PropTSRed LeafQM.AV

namespace SGRDirect

/-- **Density of `ℚ̄`-points**: in a domain of finite type over `ℚ`, an element killed by every ring map to `ℚ̄`
is zero (Hilbert's Nullstellensatz: the Jacobson radical of `0` is `0`, and every residue field at a maximal ideal
is finite over `ℚ`). -/
theorem eq_zero_of_forall_ringHom_qbar {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.FiniteType ℚ B] (x : B) (h : ∀ ψ : B →+* Qbar, ψ x = 0) : x = 0 := by
  haveI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := ℚ)
  by_contra hx
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out ‹_› (Ideal.isRadical_bot)
  have hxj : x ∉ (⊥ : Ideal B).jacobson := by rw [hj, Ideal.mem_bot]; exact hx
  rw [Ideal.jacobson, Submodule.mem_sInf] at hxj
  push Not at hxj
  obtain ⟨P, ⟨-, hPmax⟩, hxP⟩ := hxj
  haveI := hPmax
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite ℚ (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing ℚ (B ⧸ P)
  haveI : Algebra.IsAlgebraic ℚ (B ⧸ P) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (B ⧸ P) →ₐ[ℚ] Qbar := IsAlgClosed.lift
  apply hxP
  have h1 := h ((φ : B ⧸ P →+* Qbar).comp (Ideal.Quotient.mk P))
  rw [RingHom.comp_apply] at h1
  have h0 : Ideal.Quotient.mk P x = 0 := (map_eq_zero_iff _ (φ : B ⧸ P →+* Qbar).injective).mp h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

/-- Every maximal ideal of a ring of finite type over `ℚ` is the kernel of a ring map to `ℚ̄`. -/
theorem exists_ringHom_ker_eq {B : Type} [CommRing B] [Algebra ℚ B] [Algebra.FiniteType ℚ B]
    (P : Ideal B) [P.IsMaximal] : ∃ ψ : B →+* Qbar, RingHom.ker ψ = P := by
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite ℚ (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing ℚ (B ⧸ P)
  haveI : Algebra.IsAlgebraic ℚ (B ⧸ P) := Algebra.IsAlgebraic.of_finite ℚ _
  let φ : (B ⧸ P) →ₐ[ℚ] Qbar := IsAlgClosed.lift
  refine ⟨(φ : B ⧸ P →+* Qbar).comp (Ideal.Quotient.mk P), ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (φ : B ⧸ P →+* Qbar).injective,
    Ideal.Quotient.eq_zero_iff_mem]

open scoped Classical in
/-- Inverting `t ↦ 16 (t − 1)/27` on `P¹(ℚ̄)`. -/
theorem gl2_inv_val (s : OnePoint Qbar) (z : Qbar)
    (h : Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar)
      (ShimuraGlue.Mob.gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)) • s = OnePoint.some z) :
    s = OnePoint.some (1 + 27 * z / 16) := by
  rw [ShimuraGlue.Mob.map_gl2_smul] at h
  induction s using OnePoint.rec with
  | infty => simp at h
  | coe k =>
    simp at h
    congr 1
    linear_combination (27 / 16 : Qbar) * h

open scoped Classical in
open CategoryTheory AlgebraicGeometry QMSplit.Moduli.ElkiesX6Star in
/-- **The coordinate comparison on every triple** (from `elkiesX6StarPrinted`, `R1R2fp`, T5): for a triple with R1fp
and R2fp there are a morphism `G : Y → Y_E` to Elkies' witness, its forgetful map `fY_E : Y_E → X_E` and Elkies'
coordinate `t_E` on `X_E` (with its charts), such that `16 (t_E − 1)/27 = π` on `ℚ̄`-points of `Y`. -/
theorem elkies_coordinate (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure) (hEl : ElkiesX6StarPrinted)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) :
    ∃ (XE : Over (Spec (CommRingCat.of ℚ))) (tE : ToP1 XE.left) (m : Y.left ⟶ XE.left),
      X6Glue.ElkiesCharts XE tE ∧
      ∀ y : fieldPt Qbar ⟶ Y,
        Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar)
            (ShimuraGlue.Mob.gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)) •
          tE.val (K := Qbar) (y.left ≫ m) = π.val (K := Qbar) y.left := by
  obtain ⟨YE, ΦE, XE, ΨE, fYE, tE, hAb, hX6, hfib, hcm, hch⟩ := hEl
  obtain ⟨hpE, hsE, -, -, hfamAb, -⟩ := hAb
  obtain ⟨𝒜, h𝒜⟩ := R1UnivRigid.r1famProps_of_r1famAbProps hfamAb
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ YE), ∃ P : QML3 K,
      IsFibreOf 𝒜 s.left P :=
    fun K _ _ s => ⟨Quotient.out (ΦE K s), h𝒜 K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g', hg'⟩ := Pin.R1fpProps.univ h1 YE hpE hsE 𝒜 hall
  have hΦg : ∀ (s : fieldPt Qbar ⟶ YE), ΦE Qbar s = Φ Qbar (s ≫ g') := fun s => by
    rw [hg' Qbar s _ (h𝒜 Qbar s _ (Quotient.out_eq _).symm)]
    exact (Quotient.out_eq _).symm
  have hbij : Function.Bijective (fun s : fieldPt Qbar ⟶ YE => s ≫ g') := by
    have e : (fun s : fieldPt Qbar ⟶ YE => s ≫ g') = (Φ Qbar).symm ∘ (ΦE Qbar) := by
      funext s
      simp [hΦg]
    rw [e]
    exact (Φ Qbar).symm.bijective.comp (ΦE Qbar).bijective
  haveI : IsIso g' := CurveSplit.curveBijIso YE Y hpE hsE h1.1 h1.2.1 g' hbij
  set G : Y ⟶ YE := inv g' with hGdef
  have hΦG : ∀ y : fieldPt Qbar ⟶ Y, ΦE Qbar (y ≫ G) = Φ Qbar y := fun y => by
    rw [hΦg, Category.assoc, hGdef, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨jE, hjE⟩ := ShimuraGlue.Mob.good_all
    (ShimuraGlue.Mob.gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)) XE tE
  have hR2 : R2X6Props XE ΨE jE := by
    intro x x' P Q hP hQ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hjE x, hjE x', smul_left_cancel_iff, hfib x x']
      exact orbit_iff_twist hX6 x x' P Q hP hQ
    · intro hc
      rw [hjE x, (hcm x P hP).2.1 hc, ShimuraGlue.Mob.map_gl2_smul]
      norm_num
    · intro hc
      rw [hjE x, (hcm x P hP).2.2 hc, ShimuraGlue.Mob.map_gl2_smul]
      norm_num
    · intro hc
      rw [hjE x, (hcm x P hP).1 hc, ShimuraGlue.Mob.map_gl2_smul]
      norm_num
  have hX6' := hX6.2.2.2.2.2
  set π'' : ToP1 Y.left := (jE.comp fYE.left).comp G.left with hπ''
  have hval'' : ∀ y : fieldPt Qbar ⟶ Y, π''.val (K := Qbar) y.left =
      jE.val (K := Qbar) (y ≫ G ≫ fYE).left := by
    intro y
    have ea : π''.val (K := Qbar) y.left = (ToP1.comp fYE.left jE).val (K := Qbar) (y ≫ G).left :=
      ToP1.val_comp_right (ToP1.comp fYE.left jE) G.left y.left
    have eb : (ToP1.comp fYE.left jE).val (K := Qbar) (y ≫ G).left =
        jE.val (K := Qbar) ((y ≫ G) ≫ fYE).left :=
      ToP1.val_comp_right jE fYE.left (y ≫ G).left
    rw [ea, eb, Category.assoc]
  have h2'' : R2fpProps Y Φ π'' := by
    intro y y' P Q hP hQ
    have hPE : ΨE ((y ≫ G) ≫ fYE) = Quotient.mk _ P.forget := hX6' (y ≫ G) P (by rw [hΦG]; exact hP)
    have hQE : ΨE ((y' ≫ G) ≫ fYE) = Quotient.mk _ Q.forget :=
      hX6' (y' ≫ G) Q (by rw [hΦG]; exact hQ)
    rw [Category.assoc] at hPE hQE
    have h := hR2 (y ≫ G ≫ fYE) (y' ≫ G ≫ fYE) P.forget Q.forget hPE hQE
    rw [hval'' y, hval'' y']
    exact h
  have hM := CurveGlue.mobiusGlue_of_T5 hT
  have hCM := Pin.cm_objects_of_R1R2fp hRR
  have hmob := hM Y Y Φ Φ π π'' (𝟙 Y) h1 h2 h1 h2'' hCM (fun K _ _ y => by rw [Category.comp_id])
  refine ⟨XE, tE, G.left ≫ fYE.left, hch, fun y => ?_⟩
  have e1 := hmob y
  rw [Category.comp_id, hval'', hjE] at e1
  have e2 : (y ≫ G ≫ fYE).left = y.left ≫ G.left ≫ fYE.left := by simp [Over.comp_left]
  rw [e2] at e1
  exact e1

open CategoryTheory AlgebraicGeometry QMSplit.Moduli.ElkiesX6Star Pin Pin.ImagePlane in
/-- **`HeckeSqrtBranchAny` is a theorem** from `elkiesX6StarPrinted`, `R1R2fp` and T5: Elkies' chart section
`s = φ_U(eS)` (`s² = −t_E`) pulled back to the normalization chart `Spec B` (where `t_E = 1 + 27X/16` on `ℚ̄`-points,
`elkies_coordinate`) is an element `s₀ ∈ B` with `s₀² = −(1 + 27X/16)` (density of `ℚ̄`-points), so `(4 s₀)² =
−(27X + 16)`. -/
theorem heckeSqrtBranchAny_of_elkies (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hEl : ElkiesX6StarPrinted) : HeckeSqrtBranchAny := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN
  obtain ⟨XE, tE, m₀, hch, hrel⟩ := elkies_coordinate hRR hT hEl h1 h2
  obtain ⟨h, hO, -, hval⟩ := hN
  set m : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ XE.left := h ≫ m₀ with hmdef
  -- `t_E = 1 + 27X/16` at every `ℚ̄`-point of `Spec (integralClosure ℚ[X] E)`
  have hT' : ∀ ψ : (integralClosure ℚ[X] E) →+* Qbar, tE.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ m) =
      OnePoint.some (1 + 27 * ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) / 16) := by
    intro ψ
    let y : fieldPt Qbar ⟶ Y :=
      Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (PropTSRed.spec_to_specQ_eq _ _)
    have e := hrel y
    have hy : π.val (K := Qbar) y.left = OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)) :=
      hval ψ
    rw [hy] at e
    have e' := gl2_inv_val _ _ e
    rw [← e', hmdef, ← Category.assoc]
    rfl
  -- the chart section `s = φ_U(eS)` with `s² = −t`
  obtain ⟨-, -, φU, -, hφUT, -, -, -⟩ := hch
  set sE : Γ(XE.left, tE.U) := φU X6Glue.eS with hsEdef
  have hsE : sE ^ 2 = -tE.f := by
    have := congrArg φU X6Glue.rel1
    rw [map_add, map_pow, map_zero, hφUT] at this
    linear_combination this
  have hmem : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      ptOf (Spec.map (CommRingCat.ofHom ψ) ≫ m) ∈ tE.U := by
    intro ψ
    by_contra hn
    have := val_of_not_mem tE _ hn
    rw [hT' ψ] at this
    exact OnePoint.coe_ne_infty _ this
  have hev : ∀ (ψ : integralClosure ℚ[X] E →+* Qbar) (hx : ptOf (Spec.map (CommRingCat.ofHom ψ) ≫ m) ∈ tE.U),
      ev _ hx tE.f = 1 + 27 * ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) / 16 := by
    intro ψ hx
    have := val_of_mem tE _ hx
    rw [hT' ψ] at this
    exact (OnePoint.coe_injective this).symm
  -- `B` is of finite type over `ℚ`
  haveI hinjE : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : Module.Finite ℚ[X] (integralClosure ℚ[X] E) :=
    IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  letI : Algebra ℚ (integralClosure ℚ[X] E) :=
    ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp Polynomial.C).toAlgebra
  haveI : IsScalarTower ℚ ℚ[X] (integralClosure ℚ[X] E) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType ℚ (integralClosure ℚ[X] E) :=
    Algebra.FiniteType.trans (S := ℚ[X]) inferInstance inferInstance
  -- `m⁻¹(t ≠ ∞)` is everything
  have hV : m ⁻¹ᵁ tE.U = ⊤ := by
    rw [eq_top_iff]
    intro P _
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    obtain ⟨ψ, hψ⟩ := exists_ringHom_ker_eq M
    have hpt : ptOf (Spec.map (CommRingCat.ofHom ψ)) = (⟨M, hM.isPrime⟩ : PrimeSpectrum _) :=
      PrimeSpectrum.ext (by rw [ptOf_spec_asIdeal]; exact hψ)
    have hMV : (⟨M, hM.isPrime⟩ : PrimeSpectrum (integralClosure ℚ[X] E)) ∈ m ⁻¹ᵁ tE.U := by
      have := hmem ψ
      rw [ptOf_comp, hpt] at this
      exact this
    exact ((PrimeSpectrum.le_iff_specializes P ⟨M, hM.isPrime⟩).mp hPM).mem_open (m ⁻¹ᵁ tE.U).isOpen hMV
  -- the pulled-back section `s₀ ∈ B`
  have hle : (⊤ : (Spec (CommRingCat.of (integralClosure ℚ[X] E))).Opens) ≤ m ⁻¹ᵁ tE.U := le_of_eq hV.symm
  set σ : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) := res hle (m.app tE.U sE) with hσ
  set s₀ : integralClosure ℚ[X] E := (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom σ
    with hs₀
  have hψ : ∀ ψ : integralClosure ℚ[X] E →+* Qbar, ψ s₀ = ev _ (hmem ψ) sE := by
    intro ψ
    have e1 := ev_spec_top (CommRingCat.ofHom ψ) s₀
    have e2 : (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv s₀ = σ := by
      rw [hs₀]
      exact (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom_inv_id_apply σ
    rw [e2, hσ, ev_res, ← ev_comp] at e1
    exact e1.symm
  have hsq : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      ψ s₀ ^ 2 = -(1 + 27 * ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) / 16) := by
    intro ψ
    rw [hψ, ← map_pow, hsE, map_neg, hev]
  -- density: `s₀² = −(1 + 27X/16)` in `B`
  set f : ℚ[X] := 1 + Polynomial.C (27 / 16 : ℚ) * X with hf
  have hψC : ∀ (ψ : integralClosure ℚ[X] E →+* Qbar) (r : ℚ),
      ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (Polynomial.C r)) = (r : Qbar) := by
    intro ψ r
    have hsub : ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp Polynomial.C : ℚ →+* Qbar) =
        Rat.castHom Qbar := Subsingleton.elim _ _
    exact congrArg (fun g : ℚ →+* Qbar => g r) hsub
  have hx0 : s₀ ^ 2 + algebraMap ℚ[X] (integralClosure ℚ[X] E) f = 0 := by
    apply eq_zero_of_forall_ringHom_qbar
    intro ψ
    rw [map_add, map_pow, hsq, hf, map_add, map_add, map_one, map_one, map_mul, map_mul, hψC]
    push_cast
    ring
  -- conclusion in `E`
  refine ⟨-1, 4 * (s₀ : E), by norm_num, ?_⟩
  have h1 := congrArg (fun z : integralClosure ℚ[X] E => (z : E)) hx0
  simp only [Subalgebra.coe_add, Subalgebra.coe_pow, Subalgebra.coe_zero] at h1
  have h2 : ((algebraMap ℚ[X] (integralClosure ℚ[X] E) f : integralClosure ℚ[X] E) : E) =
      algebraMap ℚ[X] E f := rfl
  rw [h2] at h1
  have hpoly : (Polynomial.C (-1 : ℚ) * (Polynomial.C 27 * X + Polynomial.C 16) : ℚ[X]) = -16 * f := by
    rw [hf]
    simp only [map_neg, map_one, mul_add, neg_mul, one_mul]
    rw [show (16 : ℚ[X]) = Polynomial.C 16 from rfl]
    rw [← mul_assoc, ← Polynomial.C_mul]
    norm_num
    ring
  rw [hpoly, map_mul, map_neg, map_ofNat]
  linear_combination 16 * h1

open CategoryTheory AlgebraicGeometry QMSplit.Moduli.ElkiesX6Star in
/-- **`HeckeVertWitness` from the bundle fields and `NVLocalInertia` alone** (compiled): route NV with
`HeckeSqrtBranchAny` from the existing field `elkiesX6StarPrinted`. -/
theorem heckeVertWitness_of_nvElkies (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hL : NVLocalInertia) (hEl : ElkiesX6StarPrinted) : HDec.HeckeRestNV.HeckeVertWitness :=
  heckeVertWitness_of_nvSqrtAny hRR hT hA hS hW hL (heckeSqrtBranchAny_of_elkies hRR hT hEl)

end SGRDirect


#print axioms SGRDirect.heckeSqrtBranchAny_of_elkies
#print axioms SGRDirect.heckeVertWitness_of_nvElkies
