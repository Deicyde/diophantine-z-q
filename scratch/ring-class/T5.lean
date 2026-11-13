import ZInQKernel.Contrib.TYZGenus.RingClass
import ZInQKernel.Hypotheses.TYZInputs
open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.TYZGenus.RingClass

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei

theorem Hprime_le_H4 (d : ℕ) [NeZero d] : Hprime d ≤ H4 d := IntermediateField.lift_le _

theorem relfinrank_Hprime (d : ℕ) [NeZero d] (hd : d % 8 = 5) : (Hprime d).relfinrank (H4 d) = 2 := by
  rw [Hprime, relfinrank_lift_fixedField, Nat.card_zpowers, MulEquiv.orderOf_eq, orderOf_sigmaClass hd]

theorem sigmaClassOrderTwo : SigmaClassOrderTwo := fun d _ hd _ =>
  ⟨orderOf_sigmaClass hd, relfinrank_Hprime d hd⟩

theorem hilbertLeH4 : HilbertLeH4 := fun _ _ => ringClassField_maximal_le _

theorem gClEqPicSquares : GClEqPicSquares := fun e _ => gCl_eq_card_picSquares e

theorem gCl_eq_relfinrank (e : ℕ) [NeZero e] :
    gCl e = (genusField (maximalNumberFieldOrder (QNeg e))).relfinrank (hilbertField e) := by
  rw [relfinrank_genusField, gCl_eq_card_picSquares]

theorem gClEqRelfinrank : GClEqRelfinrank := fun e _ => gCl_eq_relfinrank e

theorem finrank_hilbertField (d : ℕ) [NeZero d] :
    Module.finrank (QNeg d) (hilbertField d) = classNumber (QNeg d) := by
  rw [hilbertField, ringClassField_maximal_eq_hilbertClassField, finrank_hilbertClassField]

/-- Genus theory in Tau Ceti's terms: `[G_n : K_n] = #Cl[2] = 2^{t−1}`, `t` the number of ramified
primes, for odd squarefree `n > 1`. -/
theorem finrank_genusField_eq (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    Module.finrank (QNeg n) (genusField (maximalNumberFieldOrder (QNeg n))) =
      2 ^ ((ramSet n).card - 1) := by
  rw [finrank_genusField]
  exact card_ker_sq_eq n hn hsq h1

/-- The genus characters `χ_q` (`RouteK.Redei.chi`) cut out the squares: `Pic(𝓞_K)² = ⋂_q ker χ_q`. -/
theorem picSquares_eq_iInf_ker_chi (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n) (h1 : 1 < n) :
    picSquares (maximalNumberFieldOrder (QNeg n)) = ⨅ q, (chi n q).ker :=
  range_sq_eq_ker_chi n hn hsq h1

/-- **The genus field is the field cut out by the genus characters**: the fixed field in the
Hilbert class field of the Artin image of `⋂_q ker χ_q`. -/
theorem genusField_eq_fixedField_chi (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (h1 : 1 < n) :
    genusField (maximalNumberFieldOrder (QNeg n)) =
      IntermediateField.lift (IntermediateField.fixedField
        ((⨅ q, (chi n q).ker).map (ringClassArtinEquiv (maximalNumberFieldOrder (QNeg n))).toMonoidHom)) := by
  rw [genusField, picSquares_eq_iInf_ker_chi n hn hsq h1]

theorem gNat_eq_relfinrank (e : ℕ) [NeZero e] :
    ZInQ.PropN.gNat e = (genusField (maximalNumberFieldOrder (QNeg e))).relfinrank (hilbertField e) := by
  rw [ZInQ.PropN.gNat, dif_neg (NeZero.ne e), gCl_eq_relfinrank]

end ZInQ.Contrib.TYZGenus.RingClass

namespace ZInQ.Contrib.TYZGenus.RingClass
open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Literature

/-- TYZ's `g(e)` read off the ring class fields: `[H_e : G_e]`, the degree of the Hilbert class
field of `K_e = ℚ(√−e)` over its genus field (`0` at `e = 0`, like `PropN.gNat`). -/
def gRingClass (e : ℕ) : ℕ :=
  if h : e = 0 then 0 else
    haveI : NeZero e := ⟨h⟩
    (genusField (maximalNumberFieldOrder (QNeg e))).relfinrank (hilbertField e)

/-- **`PropN.GenusData`'s class numbers are ring-class-field degrees**: `gNat = gRingClass`. -/
theorem gNat_eq_gRingClass : ZInQ.PropN.gNat = gRingClass := by
  funext e
  by_cases h : e = 0
  · simp [ZInQ.PropN.gNat, gRingClass, h]
  · haveI : NeZero e := ⟨h⟩
    rw [gNat_eq_relfinrank, gRingClass, dif_neg h]

theorem gCl_eq_gRingClass (e : ℕ) [NeZero e] : gCl e = gRingClass e := by
  rw [gRingClass, dif_neg (NeZero.ne e), gCl_eq_relfinrank]

/-- `T_5a(d)` with `g` read off the ring class fields. -/
theorem T5aCl_eq_gRingClass (d : ℕ) :
    T5aCl d = ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
      if Admissible5aNat d P then ∏ B ∈ P.parts, ((gRingClass (dProd B) : ℕ) : ZMod 2) else 0 := by
  unfold T5aCl
  simp_rw [gCl_eq_gRingClass]

/-- `T_5b(d)` with `g` read off the ring class fields. -/
theorem T5bCl_eq_gRingClass (d : ℕ) :
    T5bCl d = ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
      if Admissible5bNat d P then ∏ B ∈ P.parts, ((gRingClass (dProd B) : ℕ) : ZMod 2) else 0 := by
  unfold T5bCl
  simp_rw [gCl_eq_gRingClass]

/-- `GenusData.beta_seven` in ring-class-field terms. -/
theorem GenusData.beta_seven_ringClass {L : ℕ → ℤ} {n : ℕ} (G : ZInQ.PropN.GenusData L n) :
    ∀ e ∈ n.divisors, e % 8 = 7 → G.β (G.Z e) + G.Z e = (gRingClass e : ℤ) • G.τ 1 := by
  intro e he h7
  rw [← gNat_eq_gRingClass]
  exact G.beta_seven e he h7

/-- `GenusData.beta_five` in ring-class-field terms. -/
theorem GenusData.beta_five_ringClass {L : ℕ → ℤ} {n : ℕ} (G : ZInQ.PropN.GenusData L n) :
    ∀ e ∈ n.divisors, e % 8 = 5 →
      ∃ k : ℤ, G.β (G.Z e) + G.Z e = (gRingClass e : ℤ) • G.τ ⟨1, -1⟩ + k • G.τ 2 := by
  intro e he h5
  rw [← gNat_eq_gRingClass]
  exact G.beta_five e he h5

end ZInQ.Contrib.TYZGenus.RingClass
