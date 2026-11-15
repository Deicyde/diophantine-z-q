-- Verbatim copies (gt-x6facts) of the two target Props and the Elkies leaf used, from ZInQKernel/OneProof/H/TailZ22.lean (a454ad64).
-- Reference only: not compiled (the originals are in the build; X6Facts.lean uses them directly).

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.GonzalezRotgerX6`** (González–Rotger 2006 Thm 5.12 on the canonical
`X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def GonzalezRotgerX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ElkiesEquationsX6`** (Elkies, ANTS-III (1998) §3: `X₆` over the
`t`-line as the charts `s² = −t, r² = 3(t − 1)`, with the fibre and CM clauses): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ElkiesEquationsX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

section
open scoped Classical

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.BabaGranathRational`** (Baba–Granath 2008 Thm 2.1 and Lemma 3.1
on the canonical `X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb` (stated, like the original, under
`open scoped Classical`). -/
def BabaGranathRationalAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π : ToP1 X.left)
    (t₄ t₃ t₂₄ : OnePoint ℚ),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ t₄ ≠ t₃ ∧ t₄ ≠ t₂₄ ∧ t₃ ≠ t₂₄ ∧
    ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (π.val (K := Qbar) x.left = π.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM4 P.q ↔ π.val (K := Qbar) x.left = t₄.map (algebraMap ℚ Qbar)) ∧
        (HasCM3 P.q ↔ π.val (K := Qbar) x.left = t₃.map (algebraMap ℚ Qbar)) ∧
        (HasCM24 P.q ↔ π.val (K := Qbar) x.left = t₂₄.map (algebraMap ℚ Qbar))

end

end HDec.QMSplit.Moduli


-- Dependencies: X6Props, R5ptProps, CMExists, cm_of_val (ZInQKernel/HDecomp/QM/Leaves.lean); QMPair, pairSetoid, HasCM4/3/24, ToP1 (HDecomp/QM/Pairs.lean); R1fpPropsAb (TailZ16 L145); X6Glue.ElkiesCharts (TailZ21).
def X6Props (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) : Prop :=
  IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧ Nonempty (fieldPt Qbar ⟶ X) ∧
  (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → ∃ Q : QMPair Qbar,
      Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Quotient.mk _ Q ∧
      IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q) ∧
  (∀ α : O ≃+* O, ∃ g : X ≅ X, ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist α)) ∧
  (∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    Ψ (y ≫ fY) = Quotient.mk _ P.forget)

def R5ptProps (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (residueImage (X := X.left) x.left) =
          (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] residueImage (X := X.left) x.left))

