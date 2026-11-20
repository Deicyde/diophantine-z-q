import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedTrace
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Symbol

/-! The residual determinant calculation on the actual even row. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion
open IsDedekindDomain NumberField O12 PrintsArith ThetaCoeff TraceLimits Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

set_option quotPrecheck false
set_option Elab.async false

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)
variable {F : IntermediateField ℚ ℂ} [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hκ : D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC)
variable (hLi : OldNewIndependenceWeightTwo)
variable (hB : IsMovingCharacter P U (A none).χ)
variable (hJ : ∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ)
variable (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)

local notation "τT" => evenTypes W.S hS.1
local notation "κK" => FixedField D.w
local notation "οO" => FixedRing D.w
local notation "ιY" => D.inventory τT hLi
local notation "b₀" => D.evenBasis hU hLi
local notation "z₀" => D.seed hU hLi C₀ hκ

variable (H : D.sourceAttachments (hS := hS) hLi)
variable {m : Ideal (FixedRing D.w)} (hm : m.IsMaximal) (h2 : (2 : FixedRing D.w) ∈ m)

local notation "ρ₀" => D.evenAttachment hU hLi H
local notation "i₀" => (Subtype.val_injective : Function.Injective (algebraMap οO κK))
local notation "h₀" => D.integral_diamonds hU C₀ hκ hLi hB hJ hodd
local notation "c₀" => oneCoeff b₀ z₀ i₀ h₀
local notation "op₀" => oneOps b₀ z₀ ρ₀ (O := οO)
local notation "zΛ" => oneLatSeed b₀ (O := οO) z₀ U

variable (horder : ∃ e : ℕ, P.phaseData.η ^ (2 ^ e) = 1)

include hB hJ hm h2 horder in
private theorem scalar_residue (u : (ZMod (movingLevel P U))ˣ) (ψ : οO)
    (hψ : (D.blockChar none u : κK) = algebraMap οO κK ψ) :
    Ideal.Quotient.mk m ψ = 1 := by
  obtain ⟨s, hs, hu⟩ := even_blockChar_sign hS hB hJ none u
  let n := (u : ZMod (movingLevel P U)).val
  have hN : P.phaseData.N ∣ movingLevel P U :=
    ((dvd_mul_right _ _).trans (dvd_pow_self _ (by decide))).trans (dvd_mul_right _ _)
  letI : NeZero P.phaseData.N := ⟨even_level_ne_zero P⟩
  have hn := (ZMod.val_coe_unit_coprime u).of_dvd_right hN
  have hunit : IsUnit (n : ZMod P.phaseData.N) := (ZMod.isUnit_iff_coprime n _).mpr hn
  obtain ⟨e, he⟩ := horder
  have hη : (P.phaseData.η n) ^ (2 ^ e) = 1 := by
    rw [← MulChar.pow_apply' P.phaseData.η (pow_ne_zero e two_ne_zero), he, MulChar.one_apply hunit]
  have hψC : D.κ (algebraMap οO κK ψ) = P.phaseData.η n * (s : ℂ) := by
    rw [← hψ, D.blockChar_complex]
    exact hu
  apply O12Theta.phase_residue hm h2
  refine ⟨e + 1, i₀ (D.κ.injective ?_)⟩
  let f : οO →+* ℂ := D.κ.comp (algebraMap οO κK)
  change f (ψ ^ (2 ^ (e + 1) : ℕ)) = f 1
  have hf : f ψ = P.phaseData.η n * (s : ℂ) := hψC
  rw [map_pow f, map_one f, hf, mul_pow]
  simp only [pow_succ (2 : ℕ) e, pow_mul, hη, one_pow, one_mul]
  have hs₂ : (s : ℂ) ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [pow_right_comm, hs₂, one_pow]

private theorem odd_residue (h2 : (2 : οO) ∈ m) (r : ℕ) (hr : Odd r) :
    Ideal.Quotient.mk m (r : οO) = 1 := by
  obtain ⟨k, hk⟩ := hr
  have hd : (2 : οO) ∣ (r : οO) - 1 := by
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    ring
  exact O12Theta.residue_congr h2 hd

include hU hB hJ hκ hodd hm h2 horder in
/-- Exact characteristic-zero corrections, reduced only at the maximal ideal
of the receiving place. The two good operators use the same attachment. -/
def PlacedCuspLists.determinantData :
    DeterminantFourierData op₀ m zΛ where
  coeff := c₀
  subscripts := subscripts U
  pos j hj := ((mem_subscripts (fun p hp => (hU p hp).1) j).mp hj).1.ne_zero
  unary j n := D.ringMap (timesTheta (unaryCoeff (τT).Good C₀.η i j) n)
  hecke_eq := oneCoeff_hecke b₀ z₀ ρ₀ i₀ h₀
  unary_eq j _ n hn := by
    simp only [timesTheta_map_ringHom, unaryCoeff_map_ringHom]
    simpa only [one_mul] using
      (unary_timesTheta_mem m h2 (τT).Good (D.ringMap ∘ C₀.η) i 1 (d := j) (n := n) hn)
  correction r hr ha := by
    classical
    let u := (b₀).atPrime ⟨r, hr, ha⟩
    obtain ⟨ψ, c, hψ, hdc⟩ := placed_diamond_eval hU D C₀ hκ hLi hB hJ u hodd
    let c' (j : ℕ) : οO := if hj : j ∈ subscripts U then (r : οO) * c ⟨j, hj⟩ else 0
    refine ⟨c', fun n => ?_⟩
    let a := D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n)
    let b (j : ℕ) := D.ringMap (timesTheta (unaryCoeff (τT).Good C₀.η i j) n)
    change c₀ n ((r : οO) • (op₀).diamond r zΛ - zΛ) - ∑ j ∈ subscripts U, c' j * b j ∈ m
    have ee : c₀ n ((r : οO) • (op₀).diamond r zΛ - zΛ) =
        ((r : οO) * ψ - 1) * a + ∑ j ∈ subscripts U, c' j * b j := by
      have hc := (b₀).coeff_spec (oneSeed (U := U) z₀) i₀ (oneSeed_integral b₀ z₀ h₀) n
        ((r : οO) • (op₀).diamond r zΛ - zΛ)
      refine i₀ (hc.trans ?_)
      simp only [oneOps, dite_eq_left (show Test τT U r from ⟨hr, ha⟩)]
      change (b₀).eval n ((r : οO) • (b₀).diamond u (oneSeed z₀ U) - oneSeed z₀ U) = _
      rw [oneSeed_same, map_sub, eval_smul_O, hdc, D.seed_integral hU hLi C₀ hκ hodd]
      rw [← map_mul, ← map_sub]
      have hh : (r : οO) * (ψ * a + ∑ j : ↥(subscripts U), c j * b j) - a =
          ((r : οO) * ψ - 1) * a + ∑ j ∈ subscripts U, c' j * b j := by
        rw [← Finset.sum_attach (subscripts U) (fun j => c' j * b j),
          Finset.univ_eq_attach, mul_add, Finset.mul_sum]
        have hs : ∀ j : ↥(subscripts U), c' j * b j = (r : οO) * (c j * b j) := by
          intro j
          rw [show c' j = (r : οO) * c j from dite_eq_left j.property, mul_assoc]
        simp_rw [hs]
        ring
      exact congrArg (fun x : οO => algebraMap οO κK x) hh
    rw [ee, add_sub_cancel_right]
    apply m.mul_mem_right
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hr2 : r ≠ 2 := fun hh => ((good_iff hS r).mp hr).2 (hh.symm ▸ hS.2.1)
    rw [map_sub, map_mul, scalar_residue D hB hJ hm h2 horder u ψ hψ,
      odd_residue D h2 r (hr.1.odd_of_ne_two hr2), map_one, mul_one, sub_self]

end ZInQ.Manuscript.RC.EvenJoin
