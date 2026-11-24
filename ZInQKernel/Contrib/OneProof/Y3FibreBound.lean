import ZInQKernel.Contrib.OneProof.Y3ToP1j
import ZInQKernel.Contrib.OneProof.ElkiesX6Star
import ZInQKernel.Contrib.Mobius.ImagePlane
import ZInQKernel.Contrib.OneProof.Y3HodgePrint

/-! The fibres of the normalized `Y₃` map from the twist-orbit description. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeafQM LeafQM.AV LeafQM.AV.Pin
open HDec.QMSplit.Moduli
open scoped CategoryTheory.MonObj

namespace Y3P1j

private abbrev rep : Fin 4 → (O ≃+* O) := HDec.LeafQM.AV.Pin.Exact.rep

/-- A full `O`-linear level-three marking is determined by the geometric
three-torsion point that is the image of `1`. -/
private theorem level3_card_le {K : Type} [Field K] [CharZero K] {A : PkgI3.AbVar K}
    (hA : A.dim = 2) (q : QMStr A) : Finite (Level3 q) ∧ Nat.card (Level3 q) ≤ 81 := by
  have hd : ObjBridge.dim (ObjBridge.toGrp A) = ((2 : ℕ) : WithBot ℕ∞) := by
    change A.dim = _
    rw [hA]
    rfl
  obtain ⟨equiv, _⟩ := (AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)
      K (ObjBridge.toGrp A) 2 3 hd (by norm_num) (by norm_num)
  let ev (e : Level3 q) : PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure K) 3 :=
    ⟨bcPt A (Additive.toMul (e.eta 1)), e.bcPt_pow_three 1⟩
  have hev : Function.Injective ev := by
    intro e e' hh
    have h1 : e.eta 1 = e'.eta 1 :=
      Additive.toMul.injective (bcPt_injective A (congrArg Subtype.val hh))
    apply Level3.ext'
    apply AddMonoidHom.ext
    intro a
    rw [← mul_one a, e.linear, e'.linear, h1]
  let f := equiv ∘ ev
  have hf : Function.Injective f := equiv.injective.comp hev
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans_eq ?_⟩
  simp [Nat.card_eq_fintype_card]

/-- If equality of `π`-values implies twist-equivalence of the two underlying
QM pairs, every geometric fibre of `π` is finite of cardinality at most 324. -/
theorem fibreBound_of_twist {Y : Over (Spec (CommRingCat.of ℚ))}
    (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (horbit : ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
      Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left →
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) :
    ∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite ∧
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.ncard ≤ 324 := by
  intro t
  let S : Set (fieldPt Qbar ⟶ Y) := {y | π.val (K := Qbar) y.left = t}
  by_cases hn : S.Nonempty
  · obtain ⟨y, hy⟩ := hn
    let P : QML3 Qbar := Quotient.out (Φ Qbar y)
    have hP : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
    let T (i : Fin 4) := Level3 (P.q.twist (rep i))
    have hT (i : Fin 4) : Finite (T i) ∧ Nat.card (T i) ≤ 81 := level3_card_le P.surface _
    have (i : Fin 4) : Finite (T i) := (hT i).1
    let f (x : Σ i, T i) : fieldPt Qbar ⟶ Y :=
      (Φ Qbar).symm (M3.mk ⟨P.A, P.surface, P.q.twist (rep x.1), x.2⟩)
    have hsub : S ⊆ Set.range f := by
      intro y' hy'
      let Q : QML3 Qbar := Quotient.out (Φ Qbar y')
      have hQ : Φ Qbar y' = M3.mk Q := (Quotient.out_eq _).symm
      obtain ⟨α, ⟨e⟩⟩ := horbit y y' P Q hP hQ (hy.trans hy'.symm)
      obtain ⟨i, ⟨e'⟩⟩ := ElkiesX6Star.exists_rep_iso P.q α
      let iso : QMIso Q.q (P.q.twist (rep i)) := (e'.trans e).symm
      refine ⟨⟨i, transportLevel iso Q.e⟩, (Φ Qbar).injective ?_⟩
      rw [hQ]
      change (Φ Qbar) ((Φ Qbar).symm (M3.mk _)) = M3.mk Q
      rw [Equiv.apply_symm_apply]
      exact Quotient.sound ⟨(QML3.isoTransport Q P.surface iso).symm⟩
    have hf : (Set.range f).Finite := Set.finite_range _
    refine ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans ?_⟩
    rw [← Nat.card_coe_set_eq]
    calc
      Nat.card (Set.range f) ≤ Nat.card (Σ i, T i) := Finite.card_range_le f
      _ = ∑ i, Nat.card (T i) := Nat.card_sigma
      _ ≤ ∑ _ : Fin 4, 81 := Finset.sum_le_sum fun i _ => (hT i).2
      _ = 324 := by simp
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change S.Finite ∧ S.ncard ≤ _
    rw [he]
    simp

/-- The geometric orbit and CM values of the normalized coordinate. On the
fine witness these imply surjectivity and the bound in `Y3ToP1jAt`. -/
def OrbitCoordinateAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar), Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
    (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
        ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
    (HasCM4 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some 0) ∧
    (HasCM3 P.q ↔ π.val (K := Qbar) y.left = OnePoint.infty) ∧
    (HasCM24 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))

theorem y3ToP1jAt_iff_orbitCoordinateAt {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (hY : R1fpProps Y Φ) (π : ToP1 Y.left) :
    Y3ToP1jAt Y Φ π ↔ OrbitCoordinateAt Y Φ π := by
  constructor
  · exact fun h => h.1
  · intro h
    have hb := fibreBound_of_twist Φ π (fun y y' P Q hP hQ hπ => (h y y' P Q hP hQ).1.mp hπ)
    exact ⟨h, curveFacts.2 Y hY.1 hY.2.1 hY.2.2.1 π (fun y => (hb _).1), hb⟩

end Y3P1j

#print axioms Y3P1j.fibreBound_of_twist
#print axioms Y3P1j.y3ToP1jAt_iff_orbitCoordinateAt
