import ZInQKernel.Contrib.OneProof.RC.KsplitHpacket.Shift
import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.Characters
import ZInQKernel.Contrib.OneProof.RC.KSplit.Coefficients

/-! The determinant characters and the three-block identity (tex 10355–10379). -/

noncomputable section

namespace ZInQ.Manuscript.RC.KsplitHpacket

open Matrix AddressGenuine PrintsArith Symbols O12Local O12Eisenstein KSplit
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}
variable {p : ℕ} {P : O12.LocalPair p}

/-- The sign of the action on the square root of positive p: the actual
quadratic twist (p/·), including its value at a lift at p. -/
def positivePrimeSign (K : Type*) [Field K] (p : ℕ) (g : GalQ) : K :=
  if sqrtChar (p : ℤ) g = 1 then 1 else -1

theorem positivePrimeSign_eq_one_or_neg_one {K : Type*} [Field K] (p : ℕ) (g : GalQ) :
    positivePrimeSign K p g = 1 ∨ positivePrimeSign K p g = -1 := by
  unfold positivePrimeSign
  split <;> simp

theorem positivePrimeSign_at_frob {K : Type*} [Field K] {q : ℕ} [Fact q.Prime]
    (hq₂ : q ≠ 2) (hn : ¬ (q : ℤ) ∣ (p : ℤ)) {g : GalQ} (hg : IsFrobAt g q) :
    positivePrimeSign K p g = (legendreSym q (p : ℤ) : K) := by
  have hq₀ : ((p : ℤ) : ZMod q) ≠ 0 :=
    fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  unfold positivePrimeSign
  rw [sqrtChar_of_isFrobAt (Fact.out : q.Prime) hq₂ hn hg]
  by_cases hs : IsSquare (p : ZMod q)
  · have hs' : IsSquare ((p : ℤ) : ZMod q) := by simpa only [Int.cast_natCast] using hs
    simp [legBit, hs, (legendreSym.eq_one_iff q hq₀).mpr hs']
  · have hs' : ¬ IsSquare ((p : ℤ) : ZMod q) := by simpa only [Int.cast_natCast] using hs
    simp [legBit, hs, (legendreSym.eq_neg_one_iff q).mpr hs']

/-- The normalized Eisenstein pair contributes exactly one weight-two
cyclotomic factor, regardless of which line is unramified. -/
theorem det_of_eisenstein_pair {K : Type*} [Field K] [Fact p.Prime]
    (E : CharacterPair K p) (j : ℤ_[2] →+* K) (g : GalQ) (r b : GL (Fin 2) K)
    (h : (↑(b * r * b⁻¹) : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![(E.unramLine j g : K), (E.ramLine j g : K)]) :
    (↑r : Matrix (Fin 2) (Fin 2) K).det =
      (weightTwist j g : K) * (dirichletGalois E.unram g : K) *
        (dirichletGalois E.ramified g : K) := by
  rw [(trace_det_of_diagonal r b h).2]
  cases he : E.twistUnramified
  <;> simp only [CharacterPair.unramLine, CharacterPair.ramLine, he, Bool.false_eq_true,
    ite_true, ite_false, MonoidHom.mul_apply, Units.val_mul]
  <;> ring

/-- Upgrade a good-Frobenius determinant comparison in the coefficient
field topology to a comparison on the whole Galois group. The realization
supplies continuity in its valued topology, before any embedding into ℂ. -/
theorem det_eq_of_frobenius [TopologicalSpace X.K] [T2Space X.K]
    (i : X.I) (χ : GalQ → X.K) (avoid : Finset ℕ)
    (hdet : Continuous fun g => (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).det)
    (hχ : Continuous χ)
    (hgood : ∀ g q, q.Prime → q ∉ avoid → IsFrobAt g q →
      (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).det = χ g) (g : GalQ) :
    (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).det = χ g := by
  let S : Set GalQ := {g | ∃ q, q.Prime ∧ q ∉ avoid ∧ IsFrobAt g q}
  have hsub : S ⊆ {g | (↑(X.ρ i g) : Matrix (Fin 2) (Fin 2) X.K).det = χ g} := by
    rintro g ⟨q, hq, ha, hf⟩
    exact hgood g q hq ha hf
  have hc := closure_minimal hsub (isClosed_eq hdet hχ)
  have hd : Dense S := (TraceLimits.dense_arithmeticFrobenius avoid).mono (by
    rintro g ⟨q, hq, ha, hf⟩
    exact ⟨q, hq, ha, (isFrobAt_iff_c10 hq).2 hf⟩)
  rw [hd.closure_eq] at hc
  exact hc (Set.mem_univ g)

/-- One genuine weight-two block and the coordinates on which it is supported. -/
structure Block (X : GaloisConstituentModel T R ap B chiType) where
  support : Set X.I
  vec : X.I → X.K
  supported : SupportedOn support vec

/-- Use the given positive Fourier indexing, with an explicit slot at zero
for the all-natural-index identity expected by DphiBlocks. -/
def coeffIndex (A : O12.FourierData X) (zero : X.C) (n : ℕ) : X.C :=
  if h : n = 0 then zero else A.index ⟨n, h⟩

theorem coeffIndex_pos (A : O12.FourierData X) (zero : X.C) {n : ℕ} (hn : n ≠ 0) :
    coeffIndex A zero n = A.index ⟨n, hn⟩ := dite_eq_right hn

/-- Exact realization of the three summands of the transported Fourier
series. The lifts of b₁ and bₚ are in the same coefficient field. -/
structure BlockRealization (A : O12.FourierData X) (zero : X.C) (ι : X.K →+* ℂ)
    (a η : ℕ → ℂ) (m p : ℕ) where
  blockB : Block X
  blockOne : Block X
  blockP : Block X
  b₁ : X.K
  bₚ : X.K
  b₁_eq : ι b₁ = Bp a (η p) p 1
  bₚ_eq : ι bₚ = Bp a (η p) p p
  sum_eq : (X.F {p} : X.I → X.K) =
    (2 : X.K)⁻¹ • (blockB.vec - b₁ • blockOne.vec - bₚ • blockP.vec)
  realize_B : ∀ n, ι (X.coefK blockB.vec (coeffIndex A zero n)) =
    thetaMul (Bp a (η p) p) n
  realize_one : ∀ n, ι (X.coefK blockOne.vec (coeffIndex A zero n)) =
    thetaMul (unaryTheta η m 1) n
  realize_p : ∀ n, ι (X.coefK blockP.vec (coeffIndex A zero n)) =
    thetaMul (unaryTheta η m p) n

/-- The singleton characteristic-zero determinant comparison, at just the
chosen lift. The realization gives the common character on B and Θₚ
and the untwisted character on Θ₁; the weight factor is shared. -/
structure DeterminantAt (P : O12.LocalPair p) (j : ℤ_[2] →+* X.K)
    (χ : GalQ →* X.Kˣ) (vB vOne vP : Block X) : Prop where
  blockB : ∀ i ∈ vB.support, (↑(X.ρ i P.φ) : Matrix (Fin 2) (Fin 2) X.K).det =
    (weightTwist j P.φ : X.K) * (χ P.φ : X.K) * positivePrimeSign X.K p P.φ
  blockOne : ∀ i ∈ vOne.support, (↑(X.ρ i P.φ) : Matrix (Fin 2) (Fin 2) X.K).det =
    (weightTwist j P.φ : X.K) * (χ P.φ : X.K)
  blockP : ∀ i ∈ vP.support, (↑(X.ρ i P.φ) : Matrix (Fin 2) (Fin 2) X.K).det =
    (weightTwist j P.φ : X.K) * (χ P.φ : X.K) * positivePrimeSign X.K p P.φ

/-- The actual determinant acts by a scalar on each of the three vectors,
regardless of the number of constituent coordinates on its support. -/
theorem det_actions_of_characters {j : ℤ_[2] →+* X.K} {χ : GalQ →* X.Kˣ}
    {vB vOne vP : Block X} (h : DeterminantAt P j χ vB vOne vP) :
    let x : X.K := (weightTwist j P.φ : X.K) * (χ P.φ : X.K)
    let y : X.K := x * positivePrimeSign X.K p P.φ
    dV X.ρ P.φ vB.vec = y • vB.vec ∧
      dV X.ρ P.φ vOne.vec = x • vOne.vec ∧ dV X.ρ P.φ vP.vec = y • vP.vec :=
  ⟨scalarOp_eq_smul_of_support _ _ _ vB.supported h.blockB,
    scalarOp_eq_smul_of_support _ _ _ vOne.supported h.blockOne,
    scalarOp_eq_smul_of_support _ _ _ vP.supported h.blockP⟩

variable {A : O12.FourierData X} {zero : X.C} {ι : X.K →+* ℂ} {a η : ℕ → ℂ} {m : ℕ}

theorem fourier_F_of_blocks (Q : BlockRealization A zero ι a η m p) (n : ℕ) :
    ι (X.coefK (X.F {p}) (coeffIndex A zero n)) = thetaMul (Hp a η m p) n := by
  rw [Q.sum_eq]
  simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_inv₀,
    map_ofNat, Q.b₁_eq, Q.bₚ_eq, Q.realize_B, Q.realize_one, Q.realize_p]
  change _ = thetaMul (fun n => (Bp a (η p) p n -
    Bp a (η p) p 1 * unaryTheta η m 1 n - Bp a (η p) p p * unaryTheta η m p n) / 2) n
  rw [thetaMul_linear]
  ring

/-- The three block scalars, their congruence modulo integer two, and the
exact Fourier identity for the determinant translate. -/
theorem dphiBlocks_of_characters (Q : BlockRealization A zero ι a η m p)
    (O : Subring ℂ) (hp : p.Prime) (hp₂ : p ≠ 2)
    {j : ℤ_[2] →+* X.K} {χ : GalQ →* X.Kˣ}
    (hd : DeterminantAt P j χ Q.blockB Q.blockOne Q.blockP)
    (hχO : ι (χ P.φ : X.K) ∈ O) :
    ∃ δB δ1 δp : ℂ, δB = δp ∧ δp ∈ O ∧ InTwoO O (δp - δ1) ∧
      DphiBlocks (fun n => ι (X.coefK (dV X.ρ P.φ (X.F {p})) (coeffIndex A zero n)))
        a η m p δB δ1 δp := by
  let x : X.K := (weightTwist j P.φ : X.K) * (χ P.φ : X.K)
  let y : X.K := x * positivePrimeSign X.K p P.φ
  have hx : ι x ∈ O := by
    simp only [x, map_mul, weightTwist_frob j P hp hp₂, map_natCast]
    exact O.mul_mem (natCast_mem O p) hχO
  have hsign : ι y = ι x ∨ ι y = -ι x := by
    rcases positivePrimeSign_eq_one_or_neg_one (K := X.K) p P.φ with h | h
    · exact Or.inl (by simp [y, h])
    · exact Or.inr (by simp [y, h])
  have hy : ι y ∈ O := by
    rcases hsign with h | h
    · exact h.symm ▸ hx
    · exact h.symm ▸ O.neg_mem hx
  have hdiff : InTwoO O (ι y - ι x) := by
    rcases hsign with h | h
    · rw [h, sub_self]
      exact InTwoO.zero
    · exact ⟨-ι x, O.neg_mem hx, by rw [h]; ring⟩
  have hactions :
      dV X.ρ P.φ Q.blockB.vec = y • Q.blockB.vec ∧
        dV X.ρ P.φ Q.blockOne.vec = x • Q.blockOne.vec ∧
        dV X.ρ P.φ Q.blockP.vec = y • Q.blockP.vec := det_actions_of_characters hd
  obtain ⟨hB, hOne, hP⟩ := hactions
  refine ⟨ι y, ι x, ι y, rfl, hy, hdiff, fun n => ?_⟩
  rw [Q.sum_eq]
  simp only [map_smul, map_sub, hB, hOne, hP, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul,
    map_inv₀, map_ofNat, Q.b₁_eq, Q.bₚ_eq, Q.realize_B, Q.realize_one, Q.realize_p]
  ring

end ZInQ.Manuscript.RC.KsplitHpacket
