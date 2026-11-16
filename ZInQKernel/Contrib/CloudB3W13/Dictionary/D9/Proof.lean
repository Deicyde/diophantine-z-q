/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD9D10
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D9.Obligation
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D2.Proof
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Obligation
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul

/-!
# D9: the `rightMul` clause over the FLT fine moduli scheme (W13)

Proof of `D9_Obligation` from the FLT level-twist action (`IsFineModuli.exists_isLevelTwistAction`),
the FLT twist-partner lemma (`FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul`),
the accepted dictionary proofs `D2_Obligation_proof` and `d34_obligation` (consumed through their
statements) and fibre uniqueness (`fibreUnique_obligation`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

/-- An element of the FLT lattice as an element of the kernel order (`order_bridge`). -/
def ofΛ (x : ↥Λ) : LeafQM.O := ⟨(x : ℍ[ℚ, 2, -3]), (order_bridge.2.2 _).mp x.2⟩

@[simp] theorem toΛ_ofΛ (x : ↥Λ) : toΛ (ofΛ x) = x := rfl

@[simp] theorem coe_toΛ (a : LeafQM.O) : ((toΛ a : ↥Λ) : ℍ[ℚ, 2, -3]) = (a : ℍ[ℚ, 2, -3]) := rfl

theorem smul_three_eq (y : ℍ[ℚ, 2, -3]) : ((3 : ℕ) : ℚ) • y = 3 * y := by
  rw [Algebra.smul_def]; norm_num

theorem coe_three : ((3 : LeafQM.O) : ℍ[ℚ, 2, -3]) = 3 := by
  have : (3 : LeafQM.O) = ((3 : ℕ) : LeafQM.O) := by norm_num
  rw [this, Subring.coe_natCast]; norm_num

theorem coe_units_mul_inv (u : (LeafQM.O)ˣ) :
    ((u : LeafQM.O) : ℍ[ℚ, 2, -3]) * ((↑u⁻¹ : LeafQM.O) : ℍ[ℚ, 2, -3]) = 1 := by
  rw [← Subring.coe_mul, Units.mul_inv]; rfl

theorem coe_units_inv_mul (u : (LeafQM.O)ˣ) :
    ((↑u⁻¹ : LeafQM.O) : ℍ[ℚ, 2, -3]) * ((u : LeafQM.O) : ℍ[ℚ, 2, -3]) = 1 := by
  rw [← Subring.coe_mul, Units.inv_mul]; rfl

/-- An identity in `O` read in `ℍ` with the FLT `(3 : ℚ) • _` normalization. -/
theorem smul_three_of_eq {x : ℍ[ℚ, 2, -3]} {z : LeafQM.O} (h : x = ((3 * z : LeafQM.O) : ℍ[ℚ, 2, -3])) :
    x = ((3 : ℕ) : ℚ) • ((toΛ z : ↥Λ) : ℍ[ℚ, 2, -3]) := by
  rw [smul_three_eq, h, Subring.coe_mul, coe_three]; rfl

/-- The level point of the twisted datum: `a · (c · P) = (a c) · P`. -/
theorem fltLevelPoint_twist {K : Type} [Field K] (E : FakeEC K)
    (P0 P1 : E.FullLevel 3) (c : ↥Λ)
    (hP : P1.P = FLT.CerednikDrinfeld.QM.pushPt (E.act c) (E.act_over c) P0.P) (a : LeafQM.O) :
    fltLevelPoint (⟨E, P1⟩ : FLTL3 K) a = fltLevelPoint (⟨E, P0⟩ : FLTL3 K) (a * ofΛ c) := by
  simp only [fltLevelPoint, hP, FLT.CerednikDrinfeld.QM.pushPt, FLT.CerednikDrinfeld.QM.mapPt_coe,
    Category.assoc]
  have := E.act_mul (toΛ a) c (by
    have h := (toΛ (a * ofΛ c)).2
    rwa [coe_toΛ, Subring.coe_mul] at h)
  rw [← this]
  rfl

theorem d9_obligation : D9_Obligation := by
  intro 𝒪 _ _ _ M πM ptF hM 𝒜 hF u
  obtain ⟨G, _, _, ρ, χ, hT⟩ :=
    FLT.CerednikDrinfeld.QM.IsFineModuli.exists_isLevelTwistAction Λ oLattice_isOrder 1 3 hM
  obtain ⟨g0, y, hy⟩ := hT.label_surjective (toΛ u) (toΛ ↑u⁻¹)
    ⟨0, by rw [coe_toΛ, coe_toΛ, coe_units_mul_inv]; simp⟩
    ⟨0, by rw [coe_toΛ, coe_toΛ, coe_units_inv_mul]; simp⟩
  -- `χ g0 = u + 3 y` in `O`
  have hH : ((χ g0 : ↥Λ) : ℍ[ℚ, 2, -3]) = ((u : LeafQM.O) : ℍ[ℚ, 2, -3]) + 3 * (y : ℍ[ℚ, 2, -3]) := by
    rw [← smul_three_eq, ← hy, coe_toΛ]; abel
  have hcu : ofΛ (χ g0) = (u : LeafQM.O) + 3 * ofΛ y := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, coe_three]
    exact hH
  have hcdO : ofΛ (χ g0) * ↑u⁻¹ - 1 = 3 * (ofΛ y * ↑u⁻¹) := by
    rw [hcu, add_mul, Units.mul_inv]; noncomm_ring
  have hdcO : (↑u⁻¹ : LeafQM.O) * ofΛ (χ g0) - 1 = 3 * (↑u⁻¹ * ofΛ y) := by
    rw [hcu, mul_add, Units.inv_mul]; noncomm_ring
  have hcd : ∃ z : ↥Λ, ((χ g0 : ↥Λ) : ℍ[ℚ, 2, -3]) * (toΛ (↑u⁻¹ : LeafQM.O) : ↥Λ) - 1 =
      ((3 : ℕ) : ℚ) • (z : ℍ[ℚ, 2, -3]) :=
    ⟨_, smul_three_of_eq (congrArg Subtype.val hcdO)⟩
  have hdc : ∃ z : ↥Λ, ((toΛ (↑u⁻¹ : LeafQM.O) : ↥Λ) : ℍ[ℚ, 2, -3]) * ((χ g0 : ↥Λ) : ℍ[ℚ, 2, -3]) - 1 =
      ((3 : ℕ) : ℚ) • (z : ℍ[ℚ, 2, -3]) :=
    ⟨_, smul_three_of_eq (congrArg Subtype.val hdcO)⟩
  let gI : Over.mk πM ≅ Over.mk πM := Over.isoMk (ρ g0).asIso (hT.over_base g0)
  refine ⟨gI, ?_⟩
  intro yy P P' hP hP'
  obtain ⟨u0, hu0⟩ := hM.ptF_surjective LeafQM.AV.Qbar (yy ≫ πM) ⟨yy, rfl⟩
  obtain ⟨h, hs⟩ := D2_Obligation_proof LeafQM.AV.Qbar u0.1
  obtain ⟨P1, hP1, htw⟩ :=
    FLT.CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_eq_pushPt_act_and_isTwist_of_mul_sub_one_eq_smul
      oLattice_isOrder u0.1 u0.2 (χ g0) (toΛ ↑u⁻¹) hcd hdc
  let u1 : FLTL3 LeafQM.AV.Qbar := ⟨u0.1, P1⟩
  have hy1 : (ptF LeafQM.AV.Qbar (yy ≫ πM) u1).1 = yy ≫ gI.hom.left := by
    rw [hT.twist g0 LeafQM.AV.Qbar (yy ≫ πM) ⟨u0.1, u0.2⟩ u1 htw]
    rw [show (⟨u0.1, u0.2⟩ : FLTL3 LeafQM.AV.Qbar) = u0 from rfl, hu0]
    rfl
  obtain ⟨q0, hq0, e0, he0⟩ := D34.d34_obligation LeafQM.AV.Qbar u0 h
  obtain ⟨q1, hq1, e1, he1⟩ := D34.d34_obligation LeafQM.AV.Qbar u1 h
  have f0 := hF LeafQM.AV.Qbar (yy ≫ πM) u0 h hs q0 e0 ⟨hq0, he0⟩
  have f1 := hF LeafQM.AV.Qbar (yy ≫ πM) u1 h hs q1 e1 ⟨hq1, he1⟩
  rw [hu0] at f0
  rw [hy1] at f1
  rw [fibreUnique_obligation M 𝒜 LeafQM.AV.Qbar yy P _ hP f0,
    fibreUnique_obligation M 𝒜 LeafQM.AV.Qbar _ P' _ hP' f1]
  -- the identity is an isomorphism `(A, q1, e1) ≅ (A, q0, e0 ∘ (· u))`
  have hlev : ∀ a : LeafQM.O, e1.eta a = e0.eta (a * u) := by
    intro a
    have h1 : e1.eta a = e0.eta (a * ofΛ (χ g0)) := by
      apply Additive.toMul.injective
      apply Over.OverMorphism.ext
      rw [he1, he0]
      exact fltLevelPoint_twist u0.1 u0.2 P1 (χ g0) hP1 a
    rw [h1, e0.eq_iff]
    exact ⟨a * ofΛ y, by rw [← mul_sub, hcu]; noncomm_ring⟩
  apply Quotient.sound
  show Nonempty (LeafQM.AV.QML3.Iso ⟨abVarOfFakeEC u0.1 h, hs, q1, e1⟩
    ⟨abVarOfFakeEC u0.1 h, hs, q0, e0.rightMul u⟩)
  refine ⟨⟨1, 1, ?_, ?_, ?_, ?_⟩⟩
  · simp [PkgI3.AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  · simp [PkgI3.AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  · intro a
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    apply Over.OverMorphism.ext
    rw [hq1, hq0]
  · intro a
    change Additive.ofMul (Additive.toMul (e1.eta a) ≫ 𝟙 _) = e0.eta (a * u)
    rw [Category.comp_id, hlev]
    rfl

end ZInQ.Contrib.CloudB2Shimura.Dictionary

#print axioms ZInQ.Contrib.CloudB2Shimura.Dictionary.d9_obligation
