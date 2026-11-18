import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.AbsoluteInertia

/-!
# (O.12) on the characteristic-zero constituent space

Tex 9754–9892. The printed input is the character-line description obtained using
Casselman's Theorem 1, pp. 302–306, Corollary on p. 306, and Theorem 4, p. 313, and
Carayol §§0.3–0.7, Théorème A, pp. 409–411, in the manuscript's arithmetic
Frobenius normalization. Locators as cited in the manuscript; UNVERIFIED against
the prints. We use the existing constituent representations. On Eisenstein
blocks the corresponding description is data of the character pairs and their
divisor-sum expansions (tex 9862–9864).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.O12

open AddressGenuine PrintsArith Symbols TraceLimits
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open Matrix
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable (X : GaloisConstituentModel T R ap B chiType)

/-- A choice of inertia and arithmetic Frobenius above the same prime of `ℤ̄`
(tex 9866–9867). -/
structure LocalPair (p : ℕ) where
  Q : Ideal Zbar
  maximal : Q.IsMaximal
  above : ((p : ℤ) : Zbar) ∈ Q
  τ : GalQ
  inertia : τ ∈ Q.inertia GalQ
  flip : bitChar p τ = Multiplicative.ofAdd 1
  φ : GalQ
  frob : IsArithFrobAt ℤ φ Q

/-- Existence of the manuscript's local pair, using the squarefree radicand
`p*` for the quadratic character. The comparison with absolute inertia is
already in the tree. -/
theorem localPair_exists {p : ℕ} (hp : T.Good p) : Nonempty (LocalPair p) := by
  have habs : (sstar p).natAbs = p := by simp [sstar, Int.natAbs_mul, Int.natAbs_pow]
  have hsf : Squarefree (sstar p) := Int.squarefree_natAbs.mp (by rw [habs]; exact hp.1.squarefree)
  obtain ⟨Q, hQ, hpQ, τ, hτ, hn⟩ := oddRadicalRamification (sstar p) hsf
    (sqrtQbar (sstar p)) (sqrtQbar_sq _) p hp.1 hp.ne_two (by rw [habs])
  obtain ⟨φ, hφ⟩ := exists_isArithFrobAt hQ hp.1 hpQ
  refine ⟨⟨Q, hQ, hpQ, τ, hτ, ?_, φ, hφ⟩⟩
  have hn' : bitChar p τ ≠ 1 :=
    fun h => hn ((sqrtChar_eq_one_iff _ hsf.ne_zero _).mp h)
  exact (show ∀ x : Multiplicative (ZMod 2), x ≠ 1 → x = Multiplicative.ofAdd 1 by decide)
    _ hn'

/-- All the character conditions required at `p`, from inertia and Frobenius
in the existing quadratic and type characters (tex 9866–9867, 9932–9942). -/
theorem localPair_characters (htyp : IsTypeChar T chiType) {U : Finset ℕ} {p : ℕ}
    (hU : ∀ s ∈ U, T.Good s) (hp : T.Good p) (P : LocalPair p) :
    chiType P.τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s P.τ = 1) ∧
    bitChar p P.τ = Multiplicative.ofAdd 1 ∧
    chiType P.φ = Multiplicative.ofAdd (T.typ p) ∧
    (∀ s ∈ U, s ≠ p → bitChar s P.φ = Multiplicative.ofAdd (legBit p s)) := by
  classical
  have hchar := chars_eq_one_of_mem_inertia T htyp
    (U := U.erase p) (fun s hs => hU s (Finset.mem_of_mem_erase hs)) hp
    (Finset.notMem_erase p U) P.maximal P.above P.inertia
  have hf : IsFrobAt P.φ p := ⟨P.Q, P.maximal, P.above, P.frob⟩
  exact ⟨hchar.1, fun s hs hsp => hchar.2 s (Finset.mem_erase.mpr ⟨hsp, hs⟩),
    P.flip, htyp p _ hp hf, fun s hs hsp => bitChar_of_good T hp (hU s hs) hsp.symm hf⟩

/-- The actual sum for `F_U` at `p`. The coordinates include all multiplicities.
`Up` is the bad-prime weight-two operator on that sum, expressed in the
ambient coordinates. Its action on old blocks can be arbitrary within each
block. Only invariance of the sum of the ramified blocks is needed here. -/
structure LocalBlocks (U : Finset ℕ) {p : ℕ} (P : LocalPair p) where
  active : Set X.I
  ramified : Set X.I
  Up : (X.I → X.K) →ₗ[X.K] (X.I → X.K)
  supported : ∀ i, i ∉ active → (X.F U : X.I → X.K) i = 0
  preserves_ramified : ∀ v : X.I → X.K,
    (∀ i, i ∉ active ∩ ramified → v i = 0) →
    ∀ i, i ∉ active ∩ ramified → Up v i = 0
  old : ∀ i ∈ active, i ∉ ramified → X.ρ i P.τ = 1
  /-- The local input for the ramified blocks, tex 9799–9864, 9866–9873.
  On cuspidal blocks use the Casselman and Carayol prints as cited above;
  on Eisenstein blocks this is the parallel character-pair calculation. -/
  newLine : ∀ i ∈ active ∩ ramified, ∃ (b : GL (Fin 2) X.K) (lam mu : X.K),
    (↑(b * X.ρ i P.τ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] ∧
    (↑(b * X.ρ i P.φ * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![lam, mu] ∧
    ∀ v : X.I → X.K, (∀ j, j ∉ active → v j = 0) → Up v i = lam * v i

/-- The trace difference on the left of (O.12) before applying `U_p^{(2)}`. -/
def upDifference (U : Finset ℕ) (τ φ g : GalQ) : X.I → X.K :=
  tV X.ρ (g * τ * φ) (X.F U) - tV X.ρ (g * φ) (X.F U)

/-- The difference is supported on the ramified blocks (tex 9885–9889). -/
theorem upDifference_supported {U : Finset ℕ} {p : ℕ} {P : LocalPair p}
    (D : LocalBlocks X U P) (g : GalQ) (i : X.I) (hi : i ∉ D.active ∩ D.ramified) :
    upDifference X U P.τ P.φ g i = 0 := by
  by_cases ha : i ∈ D.active
  · have hu := D.old i ha (fun hr => hi ⟨ha, hr⟩)
    have he := (O12_unramified (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K)
      (↑(X.ρ i P.φ))).2
    simp only [upDifference, Pi.sub_apply, tV, scalarOp_apply, map_mul, Units.val_mul, hu,
      Units.val_one, ← sub_mul, he, zero_mul]
  · simp [upDifference, tV, D.supported i ha]

/-- (O.12) on the actual sum in characteristic zero (tex 9866–9892).
On the entire old multiplicity space the input difference is zero, independent
of how the operator acts there. -/
theorem o12_charZero {U : Finset ℕ} {p : ℕ} {P : LocalPair p}
    (D : LocalBlocks X U P) (g : GalQ) :
    D.Up (upDifference X U P.τ P.φ g) =
      dV X.ρ P.φ (tV X.ρ (g * P.τ) (X.F U) - tV X.ρ g (X.F U)) := by
  classical
  funext i
  by_cases hi : i ∈ D.active ∩ D.ramified
  · obtain ⟨b, lam, mu, ht, hf, hUp⟩ := D.newLine i hi
    let σ := (MulAut.conj b).toMonoidHom.comp (X.ρ i)
    have htr (h : GalQ) : (↑(σ h) : Matrix (Fin 2) (Fin 2) X.K).trace =
        (↑(X.ρ i h) : Matrix (Fin 2) (Fin 2) X.K).trace := by
      change (↑(b * X.ρ i h * b⁻¹) : Matrix (Fin 2) (Fin 2) X.K).trace = _
      exact trace_units_conj b (X.ρ i h)
    have hdt : (↑(X.ρ i P.φ) : Matrix (Fin 2) (Fin 2) X.K).det = lam * mu := by
      have e := congrArg Matrix.det hf
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
        Fin.prod_univ_two] at e
      have hb : (↑b : Matrix (Fin 2) (Fin 2) X.K).det *
          (↑(b⁻¹) : Matrix (Fin 2) (Fin 2) X.K).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      simpa only [mul_right_comm _ _ ((↑(b⁻¹) : Matrix (Fin 2) (Fin 2) X.K).det),
        hb, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using e
    have ht' : (↑(σ P.τ) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![1, -1] := ht
    have hf' : (↑(σ P.φ) : Matrix (Fin 2) (Fin 2) X.K) = diagonal ![lam, mu] := hf
    have he : lam * ((↑(σ (g * P.τ * P.φ)) : Matrix (Fin 2) (Fin 2) X.K).trace -
          (↑(σ (g * P.φ)) : Matrix (Fin 2) (Fin 2) X.K).trace) =
        (lam * mu) * ((↑(σ (g * P.τ)) : Matrix (Fin 2) (Fin 2) X.K).trace -
          (↑(σ g) : Matrix (Fin 2) (Fin 2) X.K).trace) := by
      simp only [map_mul, Units.val_mul, ht', hf']
      exact (O12_diag (↑(σ g) : Matrix (Fin 2) (Fin 2) X.K) lam mu).2.2
    simp only [htr] at he
    rw [hUp _ (fun j hj => upDifference_supported X D g j (fun h => hj h.1))]
    simp only [upDifference, Pi.sub_apply, tV, dV, scalarOp_apply, hdt, ← sub_mul, ← mul_assoc, he]
  · rw [D.preserves_ramified _ (upDifference_supported X D g) i hi]
    by_cases ha : i ∈ D.active
    · have hu := D.old i ha (fun hr => hi ⟨ha, hr⟩)
      have he := (O12_unramified (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K)
        (↑(X.ρ i P.φ))).1
      simp only [dV, tV, scalarOp_apply, Pi.sub_apply, map_mul, hu, Units.val_mul,
        Units.val_one, ← sub_mul, he, zero_mul, mul_zero]
    · simp [dV, tV, D.supported i ha]

/-- The finite Whittaker double-coset sum (tex 9844–9848). The
translation invariance is the triviality of the additive character on
the integers; it is written here at the translations used in the sum. -/
theorem whittaker_sum {K : Type*} [Field K] (W : Matrix (Fin 2) (Fin 2) K → K)
    (p : ℕ) (n : K)
    (hW : ∀ b : Fin p, W (!![1, n * (b.val : K); 0, 1] * !![n * (p : K), 0; 0, 1]) =
      W !![n * (p : K), 0; 0, 1]) :
    (∑ b : Fin p, W (!![n, 0; 0, 1] * !![(p : K), (b.val : K); 0, 1])) =
      (p : K) * W !![n * (p : K), 0; 0, 1] := by
  simp only [whittaker_matrix, hW, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

#print axioms localPair_exists
#print axioms localPair_characters
#print axioms upDifference_supported
#print axioms o12_charZero
#print axioms whittaker_sum

end ZInQ.Manuscript.RC.O12
