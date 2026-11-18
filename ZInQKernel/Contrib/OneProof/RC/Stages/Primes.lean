import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TateChebotarev
import ZInQKernel.Contrib.OneProof.RC.Stages.Kummer
import ZInQKernel.Contrib.TauCeti.NumberTheory.LegendreSymbol.Frobenius
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! The joint extension and the Chebotarev choice (tex 8358–8377). The prescribed
representative is an actual element of the absolute Galois group. -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve ZInQ.Manuscript.RC.PrintsArith
  ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (IsFrobAt Zbar)

namespace ZInQ.Manuscript.RC.Stages

variable (A E : WeierstrassCurve ℚ)

private abbrev Fiber (Q : GeomPoint A) (M : ℕ) :=
  {R : GeomPoint A // (2 ^ M : ℕ) • R = Q}

private instance [A.IsElliptic] (Q : GeomPoint A) (M : ℕ) : Finite (Fiber A Q M) := by
  let R₀ := (divisionTower (A := A) Q).point M
  have hR₀ : (2 ^ M : ℕ) • R₀ = Q := (divisionTower (A := A) Q).divides M
  letI : Finite (TateModuleLevel 2 (GeomPoint A) M) := by
    have hcard := (A⁄Qbar).natCard_tateModuleLevel two_ne_zero_qbar M
    exact Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine Finite.of_injective
    (fun R : Fiber A Q M => (⟨R.val - R₀, ?_⟩ : TateModuleLevel 2 (GeomPoint A) M)) ?_
  · exact AddSubgroup.torsionBy.nsmul_iff.mpr (by rw [nsmul_sub, R.property, hR₀, sub_self])
  · intro x y h
    apply Subtype.ext
    have hh := congrArg (fun z : TateModuleLevel 2 (GeomPoint A) M => z.val + R₀) h
    change (x.val - R₀) + R₀ = (y.val - R₀) + R₀ at hh
    simpa using hh

/-- Coordinates of all points dividing Q by the prescribed power of two. -/
def divisionCoords (Q : GeomPoint A) (M : ℕ) : Set Qbar :=
  ⋃ R : Fiber A Q M, coordSet R.val

/-- The actual joint extension of the manuscript inside the fixed algebraic closure. -/
def jointField (F₀ : IntermediateField ℚ Qbar) (Q : GeomPoint A) (M : ℕ) :
    IntermediateField ℚ Qbar :=
  ((F₀ ⊔ torsField E M) ⊔ torsField A M) ⊔ IntermediateField.adjoin ℚ (divisionCoords A Q M)

instance jointField_finite [E.IsElliptic] [A.IsElliptic]
    (F₀ : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F₀] (Q : GeomPoint A) (M : ℕ) :
    FiniteDimensional ℚ (jointField A E F₀ Q M) := by
  have hfin : (divisionCoords A Q M).Finite := Set.finite_iUnion fun R => coordSet_finite R.val
  letI : Finite (divisionCoords A Q M) := hfin.to_subtype
  letI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (divisionCoords A Q M)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  unfold jointField
  infer_instance

/-- The same Frobenius representative also agrees on the whole auxiliary field. -/
theorem aux_le_joint (F₀ : IntermediateField ℚ Qbar) (Q : GeomPoint A) (M : ℕ) :
    F₀ ≤ jointField A E F₀ Q M :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

private theorem tors_left_le_joint (F₀ : IntermediateField ℚ Qbar) (Q : GeomPoint A) (M : ℕ) :
    torsField E M ≤ jointField A E F₀ Q M :=
  le_sup_right.trans (le_sup_left.trans le_sup_left)

private theorem tors_right_le_joint (F₀ : IntermediateField ℚ Qbar) (Q : GeomPoint A) (M : ℕ) :
    torsField A M ≤ jointField A E F₀ Q M :=
  le_sup_right.trans le_sup_left

/-- Agreement on both torsion towers and the division field, with the determinant
congruence, at one Frobenius representative outside the given exclusions. -/
theorem exists_jointFrob [A.IsElliptic] [E.IsElliptic] (σ : GalQ)
    (hdet : (tateMatrix E σ).det = -1) (M : ℕ)
    (F₀ : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F₀] (Q : GeomPoint A) (S : Finset ℕ) :
    ∃ (g : GalQ) (p : ℕ), p.Prime ∧ p ∉ S ∧ p ≠ 2 ∧ IsFrobAt g p ∧
      (∀ x ∈ jointField A E F₀ Q M, g x = σ x) ∧
      (PadicInt.toZModPow M).mapMatrix (tateMatrix E g) =
        (PadicInt.toZModPow M).mapMatrix (tateMatrix E σ) ∧
      (PadicInt.toZModPow M).mapMatrix (tateMatrix A g) =
        (PadicInt.toZModPow M).mapMatrix (tateMatrix A σ) ∧
      ((p : ℤ) : ZMod (2 ^ M)) = -1 := by
  obtain ⟨g, p, hp, hn, hf, ha⟩ :=
    ZInQ.Contrib.ChebFD.C10.frobDense ZInQ.Contrib.chebotarevExists (insert 2 S)
      (jointField A E F₀ Q M) inferInstance σ
  have h2 : p ≠ 2 := fun he => hn (by rw [he]; exact Finset.mem_insert_self _ _)
  have hE := tateMatrix_congr_of_eqOn_torsField E
    (fun x hx => ha x (tors_left_le_joint A E F₀ Q M hx))
  have hA := tateMatrix_congr_of_eqOn_torsField A
    (fun x hx => ha x (tors_right_le_joint A E F₀ Q M hx))
  exact ⟨g, p, hp, fun hs => hn (Finset.mem_insert_of_mem hs), h2, hf, ha, hE, hA,
    ell0_congr_neg_one E g (apply_eq_pow_of_isFrobAt h2 hf) _ hdet hE⟩

/-- Agreeing on the joint extension also gives agreement of the square of the two
elements on the division point. No disjointness assumption occurs. -/
theorem DivisionTower.proj_cocycle_sq_eq_of_agree {Q : GeomPoint A}
    (d : DivisionTower A Q) (hQ) (F₀ : IntermediateField ℚ Qbar) {M : ℕ} {g σ : GalQ}
    (ha : ∀ x ∈ jointField A E F₀ Q M, g x = σ x) :
    TateModule.proj M (d.cocycle hQ (g * g)) = TateModule.proj M (d.cocycle hQ (σ * σ)) := by
  have hmap : ∀ R : GeomPoint A, (2 ^ M : ℕ) • R = Q →
      Affine.Point.map (W' := A) g.toAlgHom R = Affine.Point.map σ.toAlgHom R := by
    intro R hR
    have hsub : coordSet R ⊆ jointField A E F₀ Q M := fun x hx =>
      le_sup_right (b := IntermediateField.adjoin ℚ (divisionCoords A Q M))
        (IntermediateField.subset_adjoin ℚ _ (Set.mem_iUnion.mpr ⟨⟨R, hR⟩, hx⟩))
    rcases R with _ | ⟨x, y, hxy⟩
    · rfl
    · have hx := ha x (hsub (by simp [coordSet]))
      have hy := ha y (hsub (by simp [coordSet]))
      show Affine.Point.some _ _ _ = Affine.Point.some _ _ _
      congr 1
  apply Subtype.ext
  rw [d.coe_proj_cocycle, d.coe_proj_cocycle]
  change Affine.Point.map (g.toAlgHom.comp g.toAlgHom) (d.point M) - d.point M =
    Affine.Point.map (σ.toAlgHom.comp σ.toAlgHom) (d.point M) - d.point M
  rw [← Affine.Point.map_map, ← Affine.Point.map_map, hmap _ (d.divides M)]
  rw [hmap _ (by rw [← map_nsmul, d.divides, hQ])]

/-- Congruence to an involution already makes the square of the chosen
Frobenius act trivially on global 2-power torsion. -/
theorem global_frob_sq_on_torsion {M : ℕ} {g σ : GalQ}
    (ha : ∀ x ∈ torsField E M, g x = σ x)
    (hs : ∀ t : TateModuleLevel 2 (GeomPoint E) M,
      Affine.Point.map (W' := E) (σ * σ).toAlgHom t.val = t.val)
    (t : TateModuleLevel 2 (GeomPoint E) M) :
    Affine.Point.map (W' := E) (g * g).toAlgHom t.val = t.val := by
  have h := map_eq_of_eqOn_torsField E ha t
  let t' : TateModuleLevel 2 (GeomPoint E) M :=
    ⟨Affine.Point.map σ.toAlgHom t.val, AddSubgroup.torsionBy.nsmul_iff.mpr (by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp t.property, map_zero])⟩
  have h' := map_eq_of_eqOn_torsField E ha t'
  change Affine.Point.map (g.toAlgHom.comp g.toAlgHom) t.val = t.val
  rw [← Affine.Point.map_map, h]
  change Affine.Point.map g.toAlgHom t'.val = t.val
  rw [h']
  change Affine.Point.map σ.toAlgHom (Affine.Point.map σ.toAlgHom t.val) = t.val
  rw [Affine.Point.map_map]
  exact hs t

/-- The residue sign at the place supplied by absolute Chebotarev. -/
theorem apply_sqrt_of_isFrobAt {g : GalQ} {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2)
    (hf : IsFrobAt g p) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) {x : Qbar}
    (hx : x ^ 2 = (D : Qbar)) :
    g x = legendreSym p D • x := by
  obtain ⟨P, hp, hover, hF⟩ := hf
  have hOver : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hover.symm⟩
  let a : Zbar := ⟨x, show IsIntegral ℤ x from IsIntegral.of_pow (by decide : 0 < 2)
    (by rw [hx]; exact isIntegral_intCast D)⟩
  let φ : Zbar →ₐ[ℤ] Zbar :=
    galRestrictHom ℤ ℚ Qbar Zbar g.toAlgHom
  have hφ : φ.IsArithFrobAt P := by
    intro y
    have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
      rw [hover, ZInQ.Contrib.ChebFD.C10.card_quot p]
    rw [hcard]
    refine hF y (φ y - y ^ p) ?_
    change algebraMap Zbar Qbar (φ y - y ^ p) = _
    simp only [map_sub, map_pow, φ, algebraMap_galRestrictHom_apply] <;> rfl
  have hs : φ a = legendreSym p D • a := by
    exact @AlgHom.IsArithFrobAt.apply_sqrt Zbar _ p _ D _ P a φ hφ hOver h2 hD
      (Subtype.ext hx)
  have hh := congrArg (algebraMap Zbar Qbar) hs
  change algebraMap Zbar Qbar (galRestrictHom ℤ ℚ Qbar Zbar g.toAlgHom a) =
    algebraMap Zbar Qbar (legendreSym p D • a) at hh
  rwa [algebraMap_galRestrictHom_apply, map_zsmul] at hh

/-- At an odd prime that avoids the discriminants, the prescribed action on the
two square roots gives the two stage signs. -/
theorem residueSigns_of_agreement {g σ : GalQ} {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2)
    (hf : IsFrobAt g p) {Dw hstar : ℤ} (hDw : ¬ (p : ℤ) ∣ Dw)
    (hhs : ¬ (p : ℤ) ∣ hstar) {x y : Qbar}
    (hx : x ^ 2 = (Dw : Qbar)) (hy : y ^ 2 = (hstar : Qbar))
    (hgx : g x = σ x) (hgy : g y = σ y) (hsx : σ x = x) (hsy : σ y = -y) :
    legendreSym p Dw = 1 ∧ legendreSym p hstar = -1 := by
  have hx₀ : x ≠ 0 := by
    rintro rfl
    apply hDw
    have : Dw = 0 := by exact_mod_cast (by simpa using hx.symm : (Dw : Qbar) = 0)
    simp [this]
  have hy₀ : y ≠ 0 := by
    rintro rfl
    apply hhs
    have : hstar = 0 := by exact_mod_cast (by simpa using hy.symm : (hstar : Qbar) = 0)
    simp [this]
  have ex := apply_sqrt_of_isFrobAt h2 hf hDw hx
  have ey := apply_sqrt_of_isFrobAt h2 hf hhs hy
  rw [hgx, hsx, zsmul_eq_mul] at ex
  rw [hgy, hsy, zsmul_eq_mul] at ey
  have xeq : (legendreSym p Dw : Qbar) * x = 1 * x := by simpa using ex.symm
  have yeq : (legendreSym p hstar : Qbar) * y = -1 * y := by simpa using ey.symm
  exact ⟨by exact_mod_cast (mul_right_cancel₀ hx₀ xeq),
    by exact_mod_cast (mul_right_cancel₀ hy₀ yeq)⟩

#print axioms aux_le_joint
#print axioms tors_left_le_joint
#print axioms tors_right_le_joint
#print axioms global_frob_sq_on_torsion
#print axioms jointField_finite
#print axioms exists_jointFrob
#print axioms DivisionTower.proj_cocycle_sq_eq_of_agree
#print axioms apply_sqrt_of_isFrobAt
#print axioms residueSigns_of_agreement

end ZInQ.Manuscript.RC.Stages
