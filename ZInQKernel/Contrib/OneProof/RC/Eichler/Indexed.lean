import ZInQKernel.Contrib.OneProof.RC.Eichler.Neighbours

/-!
# Counting the ideal correspondences in the stage interface

Tex 9040–9042 and 9067–9071. The only input here is the local-to-global line indexing
(on-the-spot, c), isolated as an equivalence with the actual locally principal subideals.
-/

namespace ZInQ.Manuscript.RC.Eichler

variable {a b : ℚ} {R : Order a b}

/-- The actual locally principal subideals that are neighbours of a chosen representative. -/
abbrev Neighbour (p : ℕ) (hp : p ≠ 0) (i : ClassSet R) :=
  {J : LPIdeal R // RightIdeal.IsNeighbour p hp (representative i).val J.val}

/-- The input needed from the good-prime lattice and matrix correspondence. -/
abbrev LineIndex (R : Order a b) (p : ℕ) (hp : p ≠ 0) :=
  ∀ i : ClassSet R, Option (ZMod p) ≃ Neighbour p hp i

private def cls (I : LPIdeal R) : ClassSet R := Quotient.mk _ I

/-- The class of the actual neighbour at the given line. -/
def nbAt {p : ℕ} {hp : p ≠ 0} (lines : LineIndex R p hp)
    (i : ClassSet R) (L : Option (ZMod p)) : ClassSet R :=
  cls (lines i L).val

private noncomputable def arrowFiber (ha : a < 0) (hb : b < 0) {p : ℕ} {hp : p ≠ 0}
    (lines : LineIndex R p hp) (i j : ClassSet R) :
    RightIdeal.Arrows p hp (representative i).val (representative j).val ≃
      {L : Option (ZMod p) // nbAt lines i L = j} × classG ha hb j := by
  classical
  let K := {J : Neighbour p hp i // cls J.val = j}
  let muls (J : K) := {u : (B a b)ˣ // (representative j).val.translate u = J.val.val.val}
  let A := RightIdeal.Arrows p hp (representative i).val (representative j).val
  have hmul (J : K) : ∃ u : (B a b)ˣ, (representative j).val.translate u = J.val.val.val := by
    exact Quotient.exact ((Quotient.out_eq j).trans J.prop.symm :
      cls (representative j) = cls J.val.val)
  let e₁ : (Σ J : K, muls J) ≃ A := Equiv.ofBijective
    (fun ⟨J, u⟩ => ⟨u.val, by rw [u.prop]; exact J.val.prop⟩) (by
      constructor
      · rintro ⟨J, u⟩ ⟨K, v⟩ h
        have huv : u.val = v.val := congrArg (fun t : A => t.val) h
        have hJK : J = K := by
          apply Subtype.ext
          apply Subtype.ext
          apply Subtype.ext
          exact u.prop.symm.trans (huv ▸ v.prop)
        subst K
        have : u = v := Subtype.ext huv
        subst v
        rfl
      · intro u
        let J : LPIdeal R :=
          ⟨(representative j).val.translate u.val,
            (representative j).val.locallyPrincipal_translate (representative j).prop u.val⟩
        have hj : cls J = j :=
          (Quotient.sound (s := idealRel R)
            (show (idealRel R).r (representative j) J from ⟨u.val, rfl⟩)).symm.trans
            (Quotient.out_eq j)
        exact ⟨⟨⟨⟨J, u.prop⟩, hj⟩, ⟨u.val, rfl⟩⟩, rfl⟩)
  let e₂ : (Σ J : K, muls J) ≃ K × classG ha hb j :=
    Equiv.sigmaEquivProdOfEquiv fun J =>
      RightIdeal.multiplierEquiv ha hb (hmul J).choose (hmul J).choose_spec
  let e₃ : {L : Option (ZMod p) // nbAt lines i L = j} ≃ K :=
    (lines i).subtypeEquiv (fun _ => Iff.rfl)
  exact e₁.symm.trans (e₂.trans (e₃.symm.prodCongr (Equiv.refl _)))

/-- Self-adjointness for the actual ideal correspondence, once its kernels are line indexed. -/
theorem adjointAt (ha : a < 0) (hb : b < 0) {p : ℕ} {hp : p ≠ 0}
    [NeZero p] (lines : LineIndex R p hp) (i j : ClassSet R) :
    AppF.nbrCount (nbAt lines) i j * classWeight ha hb j =
      AppF.nbrCount (nbAt lines) j i * classWeight ha hb i :=
  adjoint_of_arrow_equiv (nbAt lines) (fun z => classG ha hb z)
    (fun i j => RightIdeal.Arrows p hp (representative i).val (representative j).val)
    (arrowFiber ha hb lines)
    (fun i j => RightIdeal.arrowsDual p hp (representative i).val (representative j).val) i j

/-- Total map in the type of `AppF.ThetaStage.nb`. Only the good-prime values are used. -/
noncomputable def nb {Good : ℕ → Prop} (prime : ∀ p, Good p → p.Prime)
    (lines : ∀ p (hp : Good p), LineIndex R p (prime p hp).ne_zero) :
    (p : ℕ) → ClassSet R → Option (ZMod p) → ClassSet R := by
  classical
  exact fun p i L => if hp : Good p then nbAt (lines p hp) i L else i

/-- The exact type of `AppF.ThetaStage.adjoint` for the map `nb`. -/
theorem adjoint {Good : ℕ → Prop} (ha : a < 0) (hb : b < 0)
    (prime : ∀ p, Good p → p.Prime)
    (lines : ∀ p (hp : Good p), LineIndex R p (prime p hp).ne_zero) :
    ∀ p (hp : Good p), haveI : NeZero p := ⟨(prime p hp).ne_zero⟩
      ∀ i j, AppF.nbrCount (nb prime lines p) i j * classWeight ha hb j =
        AppF.nbrCount (nb prime lines p) j i * classWeight ha hb i := by
  classical
  intro p hp i j
  have : NeZero p := ⟨(prime p hp).ne_zero⟩
  have hnb : nb prime lines p = nbAt (lines p hp) := by
    funext i L
    exact dite_eq_left hp
  rw [hnb]
  exact adjointAt ha hb (lines p hp) i j

end ZInQ.Manuscript.RC.Eichler

/-! Axiom audit -/

#print axioms ZInQ.Manuscript.RC.Eichler.nbAt
#print axioms ZInQ.Manuscript.RC.Eichler.arrowFiber
#print axioms ZInQ.Manuscript.RC.Eichler.adjointAt
#print axioms ZInQ.Manuscript.RC.Eichler.nb
#print axioms ZInQ.Manuscript.RC.Eichler.adjoint
