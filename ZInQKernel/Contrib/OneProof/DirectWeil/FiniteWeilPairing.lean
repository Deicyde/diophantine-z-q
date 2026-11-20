import ZInQKernel.Contrib.OneProof.DirectWeil.PicTranslation
import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyOpen

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

variable {K : Type} [Field K] (A : AbVar K)

/-- The polarization by a line bundle defined over the ground field, on geometric points. -/
def polarization (L : A.X.left.Pic) : A.Pt (AlgebraicClosure K) →* (AK A).Pic :=
  (phiHom (AKbar A) (bcPic A L)).comp (ptsHom A)

theorem polarization_apply (L : A.X.left.Pic) (x : A.Pt (AlgebraicClosure K)) :
    polarization A L x = phiPt (bcPic A L) x := phi_pts _ _

variable (L : A.X.left.Pic) {n : ℕ}

abbrev torsionClass (y : tors A n) := polarization A L (Additive.toMul (y : P A))

theorem torsionClass_isDualTors (y : tors A n) : IsDualTors n (torsionClass A L y) := by
  constructor
  · apply (isTI_iff _).mp
    exact phi_is_translationInvariant _ _ _
  · rw [torsionClass, ← map_pow, ← toMul_nsmul, nsmul_tors, toMul_zero, map_one]

theorem torsionClass_add (y y' : tors A n) :
    torsionClass A L (y + y') = torsionClass A L y * torsionClass A L y' :=
  map_mul (polarization A L) _ _

theorem polarization_gal (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    polarization A L (galHom σ ≫ x) = Scheme.Pic.map (gal A σ) (polarization A L x) := by
  have hfst : gal A σ ≫ pullback.fst A.X.hom (ptK K).hom =
      pullback.fst A.X.hom (ptK K).hom := pullback.lift_fst _ _ _
  have hL : Scheme.Pic.map (gal A σ) (bcPic A L) = bcPic A L := by
    rw [bcPic, ← Scheme.Pic.map_comp, hfst]
  simp only [polarization_apply, phiPt, ← Scheme.Pic.mapHom_apply, map_mul, map_inv]
  simp only [Scheme.Pic.mapHom_apply]
  rw [hL, ← Scheme.Pic.map_comp, ← gal_transl, Scheme.Pic.map_comp, hL]

theorem torsionClass_gal (σ : Gal K) (y : tors A n) :
    torsionClass A L (galTors A n σ y) = Scheme.Pic.map (gal A σ) (torsionClass A L y) :=
  polarization_gal A L σ (Additive.toMul (y : P A))

def trivialization (y : tors A n) : Triv A n (torsionClass A L y) :=
  (nonempty_triv (by
    rw [mumfordMulNPicZero_of_ac native_mul_pullback K A _ (torsionClass_isDualTors A L y).1 n,
      (torsionClass_isDualTors A L y).2])).some

private theorem formula_eq {c : (AK A).Pic} (hn : 0 < n) (hchar : (n : K) ≠ 0)
    (x : tors A n) (hc : IsDualTors n c) (t t' : Triv A n c) :
    weilFormula x c t = weilFormula x c t' :=
  (mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof K A n hn hchar
    x x c c hc hc).1 t t'

variable {A L}

private theorem exists_value (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y : tors A n) :
    ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧
      constK A (u : AlgebraicClosure K) = weilFormula x (torsionClass A L y)
        (trivialization A L y) :=
  (mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof K A n hn hchar
    x x _ _ (torsionClass_isDualTors A L y) (torsionClass_isDualTors A L y)).2.1 _

variable (A L)

def value (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y : tors A n) : (AlgebraicClosure K)ˣ :=
  (exists_value (L := L) hn hchar x y).choose

theorem value_pow (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y : tors A n) :
    value A L hn hchar x y ^ n = 1 :=
  (exists_value (L := L) hn hchar x y).choose_spec.1

theorem value_spec (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y : tors A n)
    (ψ : Triv A n (torsionClass A L y)) :
    constK A (value A L hn hchar x y : AlgebraicClosure K) =
      weilFormula x (torsionClass A L y) ψ :=
  (exists_value (L := L) hn hchar x y).choose_spec.2.trans
    (formula_eq A hn hchar x (torsionClass_isDualTors A L y) _ ψ)

private theorem value_add_left (hn : 0 < n) (hchar : (n : K) ≠ 0) (x x' y : tors A n) :
    value A L hn hchar (x + x') y = value A L hn hchar x y * value A L hn hchar x' y := by
  apply Units.ext
  apply constK_injective A
  simp only [Units.val_mul, map_mul, value_spec A L hn hchar _ _ (trivialization A L _)]
  exact (mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof K A n hn hchar
    x x' _ _ (torsionClass_isDualTors A L y) (torsionClass_isDualTors A L y)).2.2.1 _

private theorem value_add_right (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y y' : tors A n) :
    value A L hn hchar x (y + y') = value A L hn hchar x y * value A L hn hchar x y' := by
  apply Units.ext
  apply constK_injective A
  let h := torsionClass_add A L y y'
  let t : Triv A n (torsionClass A L y * torsionClass A L y') := h ▸ trivialization A L (y + y')
  simp only [Units.val_mul, map_mul, value_spec A L hn hchar _ _ (trivialization A L _)]
  rw [← weilFormula_congr x h (trivialization A L (y + y'))]
  exact (mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof K A n hn hchar
    x x _ _ (torsionClass_isDualTors A L y) (torsionClass_isDualTors A L y')).2.2.2 _ _ t

/-- The polarized Weil pairing on prime-to-characteristic torsion. -/
def finitePairing (hn : 0 < n) (hchar : (n : K) ≠ 0) : Pairing A A n :=
  mkPairing (value A L hn hchar) (value_pow A L hn hchar)
    (value_add_left A L hn hchar) (value_add_right A L hn hchar)

@[simp] theorem finitePairing_val (hn : 0 < n) (hchar : (n : K) ≠ 0) (x y : tors A n) :
    (finitePairing A L hn hchar x y).val = value A L hn hchar x y := rfl

theorem finitePairing_self (hn : 0 < n) (hchar : (n : K) ≠ 0) (x : tors A n) :
    finitePairing A L hn hchar x x = 0 := by
  apply Mu.val_injective
  rw [finitePairing_val, Mu.val_zero]
  apply Units.ext
  apply constK_injective A
  change _ = constK A 1
  rw [map_one, value_spec A L hn hchar x x (trivialization A L x)]
  let h := polarization_apply A L (Additive.toMul (x : P A))
  rw [← weilFormula_congr x h (trivialization A L x)]
  exact mumfordWeilAlt_of_ac WeilProof.Theta.mumfordWeilAltAC_proof K A n hn hchar (bcPic A L) x _

theorem finitePairing_gal (hn : 0 < n) (hchar : (n : K) ≠ 0) (σ : Gal K) (x y : tors A n) :
    finitePairing A L hn hchar (galTors A n σ x) (galTors A n σ y) =
      galMu n σ (finitePairing A L hn hchar x y) := by
  apply Mu.val_injective
  apply Units.ext
  rw [finitePairing_val, galMu_val, finitePairing_val]
  apply constK_injective A
  obtain ⟨ψ, hψ⟩ := weilFormulaGaloisEx K A n σ x _ _ (torsionClass_gal A L σ y)
    (trivialization A L y) _ (value_spec A L hn hchar x y (trivialization A L y)).symm
  rw [value_spec A L hn hchar _ _ ψ]
  exact hψ

theorem finitePairing_right_radical (hn : 0 < n) (hchar : (n : K) ≠ 0) (y : tors A n)
    (h : ∀ x : tors A n, finitePairing A L hn hchar x y = 0) : torsionClass A L y = 1 := by
  let ψ := trivialization A L y
  apply PhiSurj.AVDesc.formula_nondeg_right (AKbar A) n (natCast_ne_zero_bar hchar) _ (trivAC ψ)
  intro σ hσ
  obtain ⟨x, rfl⟩ := pts_surjective σ
  have hx : Additive.ofMul x ∈ tors A n := by
    rw [mem_tors]
    apply Additive.toMul.injective
    apply pts_injective
    rw [toMul_nsmul, toMul_ofMul, pts_pow, hσ, toMul_zero]
    exact (map_one (ptsHom A)).symm
  let z : tors A n := ⟨Additive.ofMul x, hx⟩
  have he := congrArg Mu.val (h z)
  rw [finitePairing_val, Mu.val_zero] at he
  have hw := (value_spec A L hn hchar z y ψ).symm
  rw [he, Units.val_one, map_one] at hw
  exact (formula_bridge z _ ψ).trans hw

/-- Transition maps on torsion points induce the power transition on the values. -/
theorem value_transition {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hchar : ((m * n : ℕ) : K) ≠ 0)
    (hnchar : (n : K) ≠ 0) (x y : tors A (m * n)) :
    value A L hn hnchar (torsSmul A m n x) (torsSmul A m n y) =
      value A L (Nat.mul_pos hm hn) hchar x y ^ m := by
  have hpow := congrArg Mu.val (map_nsmul (finitePairing A L (Nat.mul_pos hm hn) hchar x) m y)
  rw [Mu.val_nsmul, finitePairing_val, finitePairing_val] at hpow
  rw [← hpow]
  apply Units.ext
  apply constK_injective A
  let y' := torsSmul A m n y
  have hclass : torsionClass A L (m • y) = torsionClass A L y' := rfl
  let ψ : Triv A (m * n) (torsionClass A L y') := hclass ▸ trivialization A L (m • y)
  rw [value_spec A L hn hnchar _ _ (trivialization A L y'),
    value_spec A L (Nat.mul_pos hm hn) hchar _ _ (trivialization A L (m • y)),
    ← weilFormula_congr x hclass (trivialization A L (m • y))]
  exact (mumfordWeilCompat_of_pairing (mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof)
    K A m n hm hn hchar x _ (torsionClass_isDualTors A L y') ψ (trivialization A L y')).symm

end PicDict.DirectPairing
