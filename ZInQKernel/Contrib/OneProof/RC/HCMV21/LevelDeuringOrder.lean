import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelOrderLemma
import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelDeuringMap

/-! **The order lemma for the level-`N` Deuring class map** (tex 8467–8468:
automorphism groups `R_z^×` for `R_z = B ∩ z R̂ z⁻¹`, the left order of the
ideal `fromAdelic z`). For an enhanced curve `(E, C)`, the level endomorphism
ring `End(E, C)` (`levelEnd`) is isomorphic to the left ring of every
representative of its class in `ClassSet (levelOrder q h N hN)`.

The chain: `End(E, C)` is the right order of the placed level ideal
(`levelEndEquivRight`); in a definite algebra the right order of a left ideal
is, as a set, the left order of its mirror (the left order is an order, hence
stable under the standard involution); the reference coordinate keeps left
rings and the class relation conjugates them. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {a b : ℚ}

theorem conj_conj_inv (u : (B a b)ˣ) (y : B a b) :
    (↑u⁻¹ : B a b) * ((u : B a b) * y * ↑u⁻¹) * u = y := by
  simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]

theorem conj_inv_conj (u : (B a b)ˣ) (z : B a b) :
    (u : B a b) * ((↑u⁻¹ : B a b) * z * u) * ↑u⁻¹ = z := by
  simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

theorem conj_mul (u : (B a b)ˣ) (y y' : B a b) :
    (u : B a b) * (y * y') * ↑u⁻¹ = ((u : B a b) * y * ↑u⁻¹) * ((u : B a b) * y' * ↑u⁻¹) := by
  simp only [mul_assoc, Units.inv_mul_cancel_left]

/-- Conjugation by a rational unit, between subrings matched by it. -/
def conjSubringEquiv (A A' : Subring (B a b)) (u : (B a b)ˣ)
    (h : ∀ x, x ∈ A' ↔ (↑u⁻¹ : B a b) * x * u ∈ A) : A ≃+* A' where
  toFun y := ⟨(u : B a b) * (y : B a b) * (↑u⁻¹ : B a b),
    (h ((u : B a b) * (y : B a b) * (↑u⁻¹ : B a b))).mpr (by rw [conj_conj_inv]; exact y.prop)⟩
  invFun z := ⟨(↑u⁻¹ : B a b) * (z : B a b) * (u : B a b), (h (z : B a b)).mp z.prop⟩
  left_inv y := Subtype.ext (conj_conj_inv u (y : B a b))
  right_inv z := Subtype.ext (conj_inv_conj u (z : B a b))
  map_mul' y y' := Subtype.ext (conj_mul u (y : B a b) (y' : B a b))
  map_add' y y' := Subtype.ext (by
    change (u : B a b) * ((y : B a b) + (y' : B a b)) * (↑u⁻¹ : B a b) =
      (u : B a b) * (y : B a b) * (↑u⁻¹ : B a b) + (u : B a b) * (y' : B a b) * (↑u⁻¹ : B a b)
    rw [mul_add, add_mul])

section Classes

variable {q : ℕ} [Fact q.Prime] (h : q % 4 = 3) {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {N : ℕ} (hN : 0 < N) (hcop : N.Coprime q)
  {E₀ : PkgI3.AbVar k} (h₀ : IsSupersingular E₀) {P₀ : E₀.Pt k} (hP₀ : orderOf P₀ = N)
  {S : Order (-1) (-(q : ℚ))} (j : E₀.End ≃+* S.ring)
  (hmax : ∀ T : Order (-1) (-(q : ℚ)), S.ring ≤ T.ring → T.ring ≤ S.ring)
  (hInv : VoightThm4232Invertible)

include h hcop h₀ in
/-- The order lemma for a placed enhanced curve: `End(E, C)` is isomorphic to
the left order of the mirror of its placed level ideal. -/
def levelEndEquivMirror (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) (X : SupersingularEnhanced q k N)
    (Pl : HomPlacement S j X.curve) :
    levelEnd X.curve X.level ≃+* (placedLevelIdeal hN hP₀ X Pl).mirror.leftRing := by
  haveI := charP_of_isAlgClosure q k
  let Pt := Classical.choose X.exists_generator
  have hX : X.level = Subgroup.zpowers Pt := (Classical.choose_spec X.exists_generator).1
  have hPt : orderOf Pt = N := (Classical.choose_spec X.exists_generator).2
  have hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1 := hX ▸ X.pow_level_eq_one
  have hlat : (placedLevelIdeal hN hP₀ X Pl).lattice =
      (levelIdeal Pl (Subgroup.zpowers P₀) hN.ne' (zpowers_pow_eq_one N P₀ hP₀)
        (Subgroup.zpowers Pt) hC).lattice := by
    change levelLattice Pl X.level _ = levelLattice Pl (Subgroup.zpowers Pt) _
    rw [hX]
  have hsub : (levelIdeal Pl (Subgroup.zpowers P₀) hN.ne' (zpowers_pow_eq_one N P₀ hP₀)
      (Subgroup.zpowers Pt) hC).rightRing = (placedLevelIdeal hN hP₀ X Pl).mirror.leftRing := by
    ext x
    rw [← LeftIdeal.mem_rightRing_iff_mem_mirror_leftRing (by norm_num) (neg_q_lt_zero (q := q))]
    change (∀ y ∈ (levelIdeal Pl _ _ _ _ hC).lattice, y * x ∈ (levelIdeal Pl _ _ _ _ hC).lattice) ↔
      (∀ y ∈ (placedLevelIdeal hN hP₀ X Pl).lattice, y * x ∈ (placedLevelIdeal hN hP₀ X Pl).lattice)
    rw [hlat]
  exact ((RingEquiv.subringCongr (congrArg (levelEnd X.curve) hX)).trans
    (levelEndEquivRight hT hV h (by norm_num) (neg_q_lt_zero (q := q)) h₀ X.supersingular Pl
      N hN.ne' hcop Pt hPt P₀ hP₀ (zpowers_pow_eq_one N P₀ hP₀) hC)).trans
    (RingEquiv.subringCongr hsub)

/-- **Order lemma.** For every enhanced curve `X` and every representative
`J` of its class `levelDeuringClass [X]` in `ClassSet (levelOrder q h N hN)`,
the level endomorphism ring `End(E, C)` is isomorphic to the left ring of `J`
(tex 8467–8468: automorphisms are `R_z^×`). -/
theorem levelDeuringClass_order (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) (X : SupersingularEnhanced q k N)
    (J : LPIdeal (levelOrder q h N hN))
    (hJ : levelDeuringClass h hN hcop h₀ hP₀ j hmax hInv (Quotient.mk _ X) = Quotient.mk _ J) :
    Nonempty (levelEnd X.curve X.level ≃+* J.val.leftRing) := by
  let Pl := (hInv q k E₀ h₀ _ _ S j X.curve X.supersingular).some
  let I : LPIdeal (enhancedReferenceOrder q N hN P₀ hP₀ S j) :=
    LPLeftIdeal.mirror ⟨placedLevelIdeal hN hP₀ X Pl,
      placedLevelIdeal_locallyPrincipal hN hcop hP₀ h₀ X Pl⟩
  have hJ' : classSetEquivOfReference (enhancedReferenceCoordinate_spec h hN hcop h₀ hP₀ j hmax)
      (Quotient.mk _ I) = Quotient.mk _ J := hJ
  obtain ⟨u, hu⟩ := leftRing_classSetEquivOfReference _ I J hJ'
  exact ⟨(levelEndEquivMirror h hN hcop h₀ hP₀ j hT hV X Pl).trans
    (conjSubringEquiv _ _ u hu)⟩

include hInv in
/-- The order lemma at the reference: the level endomorphism ring of the
reference pair is isomorphic to the left ring of `fromAdelic z`. -/
theorem levelDeuringClass_reference_order (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) :
    Nonempty (levelEnd E₀ (Subgroup.zpowers P₀) ≃+*
      (fromAdelic (enhancedReferenceCoordinate h hN hcop h₀ hP₀ j hmax)).val.leftRing) :=
  levelDeuringClass_order h hN hcop h₀ hP₀ j hmax hInv hT hV
    (referenceEnhanced E₀ h₀ P₀ hP₀) _ (levelDeuringClass_reference h hN hcop h₀ hP₀ j hmax hInv)

end Classes

end ZInQ.Manuscript.RC.HCMV21
