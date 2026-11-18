import ZInQKernel.Contrib.OneProof.TatePolarSymNative
import ZInQKernel.Contrib.OneProof.WeilPairingMumfordOpen
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

/-! The Weil formula on the torsion of the native polarization quotient. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open PkgI3 PkgI3.AbVar HDec.WeilPairing PicDict
open T09Pic (constK)
open scoped CategoryTheory.MonObj

namespace HodgeFil1.TatePolar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

variable {K : Type} [Field K] [CharZero K] {A : AbVar K} (D : NativePolarization A)

omit [CharZero K] in
private theorem torPow {B : AbVar K} {n : ℕ} (y : tors B n) :
    Additive.toMul (y : P B) ^ n = 1 := by
  rw [← toMul_nsmul, nsmul_tors, toMul_zero]

private def NativePolarization.clTor {n : ℕ} (y : tors D.Q n) : (AK A).Pic :=
  D.cl (Additive.toMul (y : P D.Q))

private theorem NativePolarization.clTor_isDualTors {n : ℕ} (y : tors D.Q n) : IsDualTors n (D.clTor y) := by
  refine ⟨D.translInv _, ?_⟩
  rw [clTor, ← map_pow, torPow, map_one]

private def NativePolarization.triv {n : ℕ} (y : tors D.Q n) : Triv A n (D.clTor y) :=
  (nonempty_triv (by
    rw [mulN_pic_of_invariant _ (D.clTor_isDualTors y).1, (D.clTor_isDualTors y).2])).some

private theorem NativePolarization.scalar_exists {n : ℕ} (hn : 0 < n) (x : tors A n) (y : tors D.Q n) :
    ∃ u : (AlgebraicClosure K)ˣ, u ^ n = 1 ∧
      constK A (u : AlgebraicClosure K) = weilFormula x (D.clTor y) (D.triv y) :=
  ((mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof) K A n hn
    (Nat.cast_ne_zero.mpr hn.ne') x x _ _ (D.clTor_isDualTors y) (D.clTor_isDualTors y)).2.1 _

private def NativePolarization.scalar {n : ℕ} (hn : 0 < n) (x : tors A n) (y : tors D.Q n) : (AlgebraicClosure K)ˣ :=
  (D.scalar_exists hn x y).choose

private theorem NativePolarization.scalar_formula {n : ℕ} (hn : 0 < n) (x : tors A n) (y : tors D.Q n) :
    constK A (D.scalar hn x y : AlgebraicClosure K) = weilFormula x (D.clTor y) (D.triv y) :=
  (D.scalar_exists hn x y).choose_spec.2

open Classical in
/-- The finite-level native Weil pairing. At level zero the chosen extension is zero. -/
def NativePolarization.weil (n : ℕ) : Pairing A D.Q n :=
  if hn : 0 < n then
    mkPairing (D.scalar hn) (fun x y => (D.scalar_exists hn x y).choose_spec.1)
      (by
        intro x x' y
        apply Units.ext
        apply constK_injective A
        rw [Units.val_mul, map_mul, D.scalar_formula, D.scalar_formula, D.scalar_formula]
        exact ((mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof) K A n hn
          (Nat.cast_ne_zero.mpr hn.ne') x x' _ _ (D.clTor_isDualTors y) (D.clTor_isDualTors y)).2.2.1 _)
      (by
        intro x y y'
        apply Units.ext
        apply constK_injective A
        rw [Units.val_mul, map_mul, D.scalar_formula, D.scalar_formula, D.scalar_formula]
        have hc : D.clTor (y + y') = D.clTor y * D.clTor y' := D.cl.map_mul _ _
        rw [← weilFormula_congr x hc]
        exact ((mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof) K A n hn
          (Nat.cast_ne_zero.mpr hn.ne') x x _ _ (D.clTor_isDualTors y) (D.clTor_isDualTors y')).2.2.2 _ _ _)
  else 0

private theorem NativePolarization.weil_formula {n : ℕ} (hn : 0 < n) (x : tors A n) (y : tors D.Q n)
    (ψ : Triv A n (D.clTor y)) :
    constK A ((D.weil n x y).val : AlgebraicClosure K) = weilFormula x (D.clTor y) ψ := by
  classical
  rw [NativePolarization.weil, dif_pos hn, mkPairing_val, D.scalar_formula]
  exact ((mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof) K A n hn
    (Nat.cast_ne_zero.mpr hn.ne') x x _ _ (D.clTor_isDualTors y) (D.clTor_isDualTors y)).1 _ _

/-- Perfection on the right: a trivial Weil character descends the trivialization. -/
theorem NativePolarization.weil_right {n : ℕ} (hn : 0 < n) (y : tors D.Q n)
    (hy : ∀ x, D.weil n x y = 0) : y = 0 := by
  have hc : D.clTor y = 1 := by
    obtain ⟨ψ⟩ := PhiSurj.AVDesc.nonempty_triv_ac (X := AKbar A) (n := n) (c := D.clTor y)
      (by rw [mul_AKbar, mulN_pic_of_invariant _ (D.clTor_isDualTors y).1, (D.clTor_isDualTors y).2])
    refine PhiSurj.AVDesc.formula_nondeg_right (AKbar A) n (Nat.cast_ne_zero.mpr hn.ne') _ ψ ?_
    intro z hz
    obtain ⟨x, rfl⟩ := pts_surjective z
    obtain ⟨ψ', rfl⟩ := triv_surj ψ
    have hx : Additive.ofMul x ∈ tors A n := by
      rw [mem_tors]
      apply Additive.toMul.injective
      apply pts_injective
      rw [toMul_nsmul, toMul_ofMul, pts_pow, hz, toMul_zero]
      exact (map_one (ptsHom A)).symm
    refine (formula_congr_pt rfl _ _ _ _).trans ((formula_bridge ⟨_, hx⟩ _ ψ').trans ?_)
    rw [← D.weil_formula hn ⟨_, hx⟩ y ψ', hy, Mu.val_zero, Units.val_one, map_one]
  apply Subtype.ext
  apply Additive.toMul.injective
  exact D.injective (hc.trans D.cl.map_one.symm)

/-- Perfection on both sides follows from the equality of quotient and source dimensions. -/
theorem NativePolarization.weil_perfect {n : ℕ} (hn : 0 < n) : IsPerfect (D.weil n) := by
  refine ⟨fun x hx => ?_, D.weil_right hn⟩
  by_contra hx0
  letI : NeZero n := ⟨hn.ne'⟩
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨g, hg⟩ := AbVar.dim_finite A
  have hQ : topologicalKrullDim D.Q.X.left = g := D.dim_eq.trans hg
  have ht := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  obtain ⟨EA⟩ := PhiSurj.exists_torsAddEquiv ht A g n hg hn hnK
  obtain ⟨EQ⟩ := PhiSurj.exists_torsAddEquiv ht D.Q g n hQ hn hnK
  let Φ : tors D.Q n →+ (tors A n →+ Mu K n) := (D.weil n).flip
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    exact D.weil_right hn y fun x => DFunLike.congr_fun hy x
  have : Finite (tors A n) := Finite.of_equiv _ EA.symm.toEquiv
  have : Finite (tors A n →+ Mu K n) := DFunLike.finite _
  have hcard : Nat.card (tors A n →+ Mu K n) ≤ Nat.card (tors D.Q n) := by
    calc Nat.card (tors A n →+ Mu K n) ≤ Nat.card (Mu K n) ^ (2 * g) :=
            PhiSurj.AVDesc.card_hom_le EA
      _ ≤ n ^ (2 * g) := Nat.pow_le_pow_left (PhiSurj.card_mu_le n) _
      _ = Nat.card (tors D.Q n) := by
        rw [Nat.card_congr EQ.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
          Fintype.card_fin]
  obtain ⟨ψ, hψ⟩ := PhiSurj.exists_zmod_mu_injective hnK
  obtain ⟨χ, hχ⟩ := PhiSurj.exists_char_ne_zero EA ψ hψ x hx0
  obtain ⟨y, hy⟩ := (hΦ.bijective_of_nat_card_le hcard).2 χ
  exact hχ (by rw [← hy]; exact hx y)

/-- The finite-level pairings are equivariant over the original field. -/
theorem NativePolarization.weil_galois {n : ℕ} (hn : 0 < n) : IsGalEquivariant (D.weil n) := by
  intro σ x y
  apply Mu.val_injective
  apply Units.ext
  rw [galMu_val]
  apply constK_injective A
  have hgal : D.clTor (galTors D.Q n σ y) = Scheme.Pic.map (gal A σ) (D.clTor y) :=
    D.galois σ _
  obtain ⟨ψ, hψ⟩ := weilFormulaGaloisEx K A n σ x _ _ hgal (D.triv y) _
    (D.weil_formula hn x y _).symm
  exact (D.weil_formula hn _ _ ψ).trans hψ

/-- Compatibility in the exponent on the torsion of the native quotient. -/
theorem NativePolarization.weil_compat {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : tors A (m * n)) (y : tors D.Q n) :
    (D.weil (m * n) x (torsIncl D.Q (dvd_mul_left n m) y)).val =
      (D.weil n (torsSmul A m n x) y).val := by
  apply Units.ext
  apply constK_injective A
  rw [D.weil_formula (Nat.mul_pos hm hn) _ _ (D.triv _), D.weil_formula hn _ _ (D.triv _)]
  exact (mumfordWeilCompat_of_pairing (mumfordWeilPairing_of_ac WeilProof.mumfordWeilPairingAC_proof))
    K A m n hm hn (Nat.cast_ne_zero.mpr (Nat.mul_pos hm hn).ne') x _ (D.clTor_isDualTors y) _ _

/-- After composition with the native quotient isogeny, the form is alternating. -/
theorem NativePolarization.weil_alt {n : ℕ} (hn : 0 < n) (x : tors A n) :
    D.weil n x (torsMap D.q n x) = 0 := by
  apply Mu.val_injective
  apply Units.ext
  apply constK_injective A
  rw [D.weil_formula hn _ _ (D.triv _), Mu.val_zero, Units.val_one, map_one]
  have h : D.clTor (torsMap D.q n x) = phiPt (bcPic A D.L) (Additive.toMul (x : P A)) :=
    D.over_q _
  rw [← weilFormula_congr x h]
  exact (mumfordWeilAlt_of_ac WeilProof.Theta.mumfordWeilAltAC_proof) K A n hn
    (Nat.cast_ne_zero.mpr hn.ne') _ x _

#print axioms torPow
#print axioms NativePolarization.clTor_isDualTors
#print axioms NativePolarization.scalar_exists
#print axioms NativePolarization.scalar_formula
#print axioms NativePolarization.weil_formula
#print axioms NativePolarization.weil_right
#print axioms NativePolarization.weil_perfect
#print axioms NativePolarization.weil_galois
#print axioms NativePolarization.weil_compat
#print axioms NativePolarization.weil_alt

end HodgeFil1.TatePolar
