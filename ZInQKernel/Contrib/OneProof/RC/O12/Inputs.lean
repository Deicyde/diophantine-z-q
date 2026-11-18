import ZInQKernel.Contrib.OneProof.RC.O12.Theta

/-! Both inputs for the actual theta forms in the constituent model.
Tex 9670–9704 and 9866–9926. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12

open AddressGenuine PrintsArith Symbols
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable {X : GaloisConstituentModel T R ap B chiType}

attribute [local instance] GaloisConstituentModel.modMexp

/-- The manuscript's local structure at an added prime, with the comparison
to the Fourier operator on the same forms. See `LocalBlocks.newLine` for
the exact use of the Casselman and Carayol prints (tex 9799–9864). -/
def LocalInput (A : FourierData X) : Prop :=
  ∀ (U : Finset ℕ) (p : ℕ) (hpU : p ∈ U) (hU : ∀ s ∈ U, T.Good s),
    U.card + 1 ≤ B → ∀ P : LocalPair p,
    ∃ D : LocalBlocks X U P, A.UpAtOne D (hU p hpU).1.ne_zero

variable (X) in
/-- A representative modulo (N_U) gives the same reduced trace on every
subset of (U) (tex 9919–9921). -/
theorem representative_trace {U V : Finset ℕ} {r : ℕ} {x h n : GalQ}
    (hVU : V ⊆ U) (hn : n ∈ X.N U) (hr : X.frob r = h * x * h⁻¹ * n) :
    X.tE (X.frob r) (X.FE V) = X.tE x (X.FE V) := by
  rw [hr, X.level V _ n (X.N_anti U V hVU hn), X.t_class]

variable (X) in
/-- The same representative gives the retained quadratic labels (tex
9919–9925). -/
theorem representative_bit {U : Finset ℕ} {p r : ℕ} {x h n : GalQ}
    (hpU : p ∈ U) (hn : n ∈ X.N U) (hr : X.frob r = h * x * h⁻¹ * n) :
    bitChar p (X.frob r) = bitChar p x := by
  rw [hr, map_mul, (X.N_chi U n hn).2 p hpU, mul_one, map_conj_of_comm]

namespace ThetaData

/-- A bit flip changes the Legendre sign for a prime distinct from (p).
The factor from (-v) and the character ratio are the same for both primes
(tex 9908, 9924–9925). -/
theorem omissionSign_flip {A : FourierData X} (S : ThetaData A)
    {p r₀ r₁ : ℕ} (hp : T.Good p) [Fact p.Prime]
    (hr₀ : T.Good r₀) (hr₁ : T.Good r₁) (hne₀ : r₀ ≠ p) (hne₁ : r₁ ≠ p)
    (hflip : legBit (r₁ : ℤ) p = legBit (r₀ : ℤ) p + 1) (V : Finset ℕ) :
    S.omissionSign p V r₁ = -S.omissionSign p V r₀ := by
  have hd (r : ℕ) (hr : T.Good r) (hne : r ≠ p) : ¬ (p : ℤ) ∣ (r : ℤ) :=
    fun e => hne ((Nat.prime_dvd_prime_iff_eq hp.1 hr.1).mp (Int.natCast_dvd_natCast.mp e)).symm
  have hneZ (r : ℕ) (hr : T.Good r) (hne : r ≠ p) : ((r : ℤ) : ZMod p) ≠ 0 :=
    fun e => hd r hr hne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e)
  have hleg : legendreSym p (r₁ : ℤ) = -legendreSym p (r₀ : ℤ) := by
    rw [legBit_eq_ite_legendreSym (hd r₀ hr₀ hne₀),
      legBit_eq_ite_legendreSym (hd r₁ hr₁ hne₁)] at hflip
    rcases legendreSym.eq_one_or_neg_one p (hneZ r₀ hr₀ hne₀) with h₀ | h₀ <;>
      rcases legendreSym.eq_one_or_neg_one p (hneZ r₁ hr₁ hne₁) with h₁ | h₁ <;>
      norm_num [h₀, h₁] at hflip <;> norm_num [h₀, h₁]
    exact (by decide : (1 : ZMod 2) ≠ 2) hflip
  have sign_eq (r : ℕ) : S.omissionSign p V r =
      S.ratio p * legendreSym p (-((∏ s ∈ V, s : ℕ) : ℤ)) * legendreSym p (r : ℤ) := by
    unfold ThetaData.omissionSign
    rw [Nat.cast_mul, ← neg_mul, legendreSym.mul, mul_assoc]
  rw [sign_eq, sign_eq, hleg, mul_neg]

/-- The second half of `GaloisConstituentModel.Inputs`, with
`κ₀ = (ψ/η)(p)(−vr₀/p)` for a fresh representative of `gφ` and the
opposite sign for a fresh representative of `gτφ`. -/
theorem o12_at_one {A : FourierData X} (S : ThetaData A) [CharZero X.K]
    (localData : LocalInput A) (htyp : IsTypeChar T chiType)
    (U : Finset ℕ) (p : ℕ) (hpU : p ∈ U) (hU : ∀ s ∈ U, T.Good s)
    (hB : U.card + 1 ≤ B) (g : GalQ) :
    ∃ (τ φ : GalQ) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
      chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
      bitChar p τ = Multiplicative.ofAdd 1 ∧
      chiType φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
      (Cp (ap p) (-κ0) : ZMod 2) * X.readE (U.erase p) (X.tE (g * τ * φ) (X.FE (U.erase p))) -
      (Cp (ap p) κ0 : ZMod 2) * X.readE (U.erase p) (X.tE (g * φ) (X.FE (U.erase p))) =
      X.readE U (X.tE (g * τ) (X.FE U)) - X.readE U (X.tE g (X.FE U)) := by
  classical
  let hp := hU p hpU
  let : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨P⟩ := localPair_exists hp
  obtain ⟨hτT, hτB, hτp, hφT, hφB⟩ := localPair_characters htyp hU hp P
  obtain ⟨D, hUp⟩ := localData U p hpU hU hB P
  obtain ⟨r₀, j₀, n₀, hn₀, hr₀, hr₀U, e₀⟩ := X.chebotarev U hU hB (g * P.φ) U
  obtain ⟨r₁, j₁, n₁, hn₁, hr₁, hr₁U, e₁⟩ := X.chebotarev U hU hB (g * P.τ * P.φ) U
  have hne₀ : r₀ ≠ p := fun e => hr₀U (e ▸ hpU)
  have hne₁ : r₁ ≠ p := fun e => hr₁U (e ▸ hpU)
  have b₀ := (X.bit_frob r₀ p hr₀ hp hne₀).symm.trans (representative_bit X hpU hn₀ e₀)
  have b₁ := (X.bit_frob r₁ p hr₁ hp hne₁).symm.trans (representative_bit X hpU hn₁ e₁)
  have hflip : legBit (r₁ : ℤ) p = legBit (r₀ : ℤ) p + 1 := by
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_add, b₁, b₀, map_mul, map_mul, map_mul, hτp]
    ac_rfl
  let V := U.erase p
  let κ₀ := S.omissionSign p V r₀
  have hsign : S.omissionSign p V r₁ = -κ₀ := S.omissionSign_flip hp hr₀ hr₁ hne₀ hne₁ hflip V
  obtain ⟨hκ, hc₀⟩ := S.omission_at_p hpU hU hr₀ hr₀U hB
  obtain ⟨-, hc₁⟩ := S.omission_at_p hpU hU hr₁ hr₁U hB
  change A.decode (A.orbitCoeff U (X.frob r₁) ⟨p, hp.1.ne_zero⟩) =
    (Cp (ap p) (S.omissionSign p V r₁) : ZMod 2) * X.readE V (X.tE (X.frob r₁) (X.FE V)) at hc₁
  rw [hsign] at hc₁
  have eqCoeff {r : ℕ} {x h n : GalQ} (hn : n ∈ X.N U) (e : X.frob r = h * x * h⁻¹ * n) :
      A.orbitCoeff U (X.frob r) ⟨p, hp.1.ne_zero⟩ = A.orbitCoeff U x ⟨p, hp.1.ne_zero⟩ :=
    congrArg (fun v : X.Mexp => v.val (A.index ⟨p, hp.1.ne_zero⟩))
      (representative_trace X (Finset.Subset.refl U) hn e)
  rw [eqCoeff hn₀ e₀, representative_trace X (Finset.erase_subset p U) hn₀ e₀] at hc₀
  rw [eqCoeff hn₁ e₁, representative_trace X (Finset.erase_subset p U) hn₁ e₁] at hc₁
  have ho := congrArg A.decode (A.o12_reduced D hp.1.ne_zero hUp hU hB g)
  rw [map_sub, map_sub, hc₀, hc₁, ← A.read_orbit, ← A.read_orbit] at ho
  exact ⟨P.τ, P.φ, κ₀, hκ, hτT, hτB, hτp, hφT, hφB, ho⟩

end ThetaData

/-- Both inputs for the constituent model on coefficientwise reduced
expansions. The result can be passed directly to
`o12_of_constituents` and `fixedU_of_constituents`. -/
theorem inputs_of_theta {A : FourierData X} (S : ThetaData A) [CharZero X.K]
    (localData : LocalInput A) (htyp : IsTypeChar T chiType) : X.Inputs :=
  ⟨fun _ _ hU hq hqU hB => S.coefficientOne hU hq hqU hB, S.o12_at_one localData htyp⟩

#print axioms representative_trace
#print axioms representative_bit
#print axioms ThetaData.omissionSign_flip
#print axioms ThetaData.o12_at_one
#print axioms inputs_of_theta

end ZInQ.Manuscript.RC.O12
