import ZInQKernel.Contrib.OneProof.X6AtkinLehnerIdeal

/-! elkies-c: the statements, copied verbatim (as `example`s checking they elaborate to the tree's definitions).

`HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery` (bundle field `elkiesX6StarEvery`,
`ZInQKernel/Contrib/OneProof/ElkiesX6StarEvery.lean`) and x6-coarse's `X6ALIdeal.ElkiesX6StarEveryIdeal`
(`ZInQKernel/Contrib/OneProof/X6AtkinLehnerIdeal.lean`). Step (c) is the CM clause:
`HasCM24 P.q → t x = 0`, `HasCM4 P.q → t x = 1`, `HasCM3 P.q → t x = ∞` at **every** point `x`. -/

open CategoryTheory AlgebraicGeometry Limits
open HDec.LeafQM HDec.LeafQM.AV HDec.QMSplit.Moduli X6ALIdeal

example : ElkiesPrint.ElkiesX6StarEvery =
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        ElkiesCoord.fixedByW Ψ =
          (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
      X6Glue.ElkiesCharts X t := rfl

example : ElkiesX6StarEveryIdeal =
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY → ALIdealClause X Ψ →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        fixedByWIdeal Ψ =
          (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
      (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
      X6Glue.ElkiesCharts X t := rfl
