import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedTwoFresh
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedDiamond
import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedFreshCoefficients

/-! Galois attachment and the two residual orbit inputs, on the same
integral lattice and at the place selected for this row. -/

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

/-- There is one attachment per newform, shared by its dilations. -/
abbrev PlacedCuspLists.sourceAttachments :=
  ∀ s, SourceAttachment ((ιY).sourceLevel s) (chooseFrob frobeniusExists) ((ιY).source s)

abbrev PlacedCuspLists.evenAttachment (H : D.sourceAttachments (hS := hS) hLi) :=
  (ιY).attachment (movingLevel_test_coprime (P := P) (hS := hS) hU) H
    (fun _ hq => chooseFrob_spec frobeniusExists hq.1)

include hB hJ hodd in
theorem PlacedCuspLists.integral_diamonds :
    ∀ u n, (b₀).eval n ((b₀).diamond u z₀) ∈ integralRange (O := οO) := by
  intro u n
  obtain ⟨ψ, c, _, he⟩ := placed_diamond_eval hU D C₀ hκ hLi hB hJ u hodd
  refine ⟨ψ * D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n) +
    ∑ j : ↥(subscripts U), c j * D.ringMap
      (timesTheta (unaryCoeff (τT).Good C₀.η i j.val) n), ?_⟩
  exact (he n).symm

variable (H : D.sourceAttachments (hS := hS) hLi)

/-- A unary block omitting the added prime has trivial inertia on each of
its nonzero coordinates, by its intrinsic level (tex 9757–9760). -/
theorem PlacedCuspLists.unary_inertia
    (j : ↥(subscripts U)) {q : ℕ} (hq : (τT).Good q) (hqj : ¬ q ∣ j.val)
    (x : ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P))))
    (hx : D.vectors hU hLi C₀ hκ (some j) x ≠ 0) :
    UnramifiedAt ((D.evenAttachment hU hLi H).ρ x) q := by
  have hm : q.Coprime (maskedLevel P) :=
    (Nat.Prime.coprime_iff_not_dvd hq.1).mpr fun hd =>
      ((good_iff hS q).mp hq).2 ((evenMasked P hS).2.1 q hq.1 hd)
  have hc := hm.mul_right ((Nat.Prime.coprime_iff_not_dvd hq.1).mpr hqj)
  have hlevel := ((D.vectors_spec hU hLi C₀ hκ).2 (some j) x hx).1
  exact (H ((ιY).origin x)).unramified q
    ⟨hq, hc.of_dvd_right ((dvd_mul_right _ _).trans hlevel)⟩
variable {m : Ideal (FixedRing D.w)} (h2 : (2 : FixedRing D.w) ∈ m)

local notation "ρ₀" => D.evenAttachment hU hLi H
local notation "i₀" => (Subtype.val_injective : Function.Injective (algebraMap οO κK))
local notation "h₀" => D.integral_diamonds hU C₀ hκ hLi hB hJ hodd
local notation "c₀" => oneCoeff b₀ z₀ i₀ h₀
local notation "op₀" => oneOps b₀ z₀ ρ₀ (O := οO)
local notation "zΛ" => oneLatSeed b₀ (O := οO) z₀ U

include hB hJ in
theorem PlacedCuspLists.lattice_seed_coeff (n : ℕ) :
    c₀ n zΛ = D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n) := by
  have hc := (b₀).coeff_spec (oneSeed (U := U) z₀) i₀ (oneSeed_integral b₀ z₀ h₀) n zΛ
  have hseed : (zΛ).val = z₀ := oneSeed_same z₀
  rw [hseed] at hc
  exact i₀ (hc.trans (D.seed_integral hU hLi C₀ hκ hodd n))

include D C₀ hU hκ hLi hB hJ hodd h2 in
theorem PlacedCuspLists.fresh_coeff_mem (q r n : ℕ) (hn : n ≠ 0)
    (hq : (τT).Good q) (hr : (τT).Good r) (hqU : q ∉ U) (hrU : r ∉ U)
    (hqr : q ≠ r) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n) :
    c₀ (r * (q * n)) zΛ ∈ m := by
  obtain ⟨x, hx⟩ := fixedH_two_fresh (hS := hS) (i := i) hU C₀ hn hq hr hqU hrU hqr hqn hrn
  let k := r * (q * n)
  have hmem (x : FixedRing v) : D.ringMap (2 * x) ∈ m := by
    let f : FixedRing v →+* οO := D.ringMap
    change f (2 * x) ∈ m
    rw [map_mul f, map_ofNat f]
    exact m.mul_mem_right _ h2
  have e : c₀ k zΛ = D.ringMap (2 * x) :=
    (D.lattice_seed_coeff hU C₀ hκ hLi hB hJ hodd k).trans
      (congrArg (fun y : FixedRing v => D.ringMap y) hx)
  rw [e]
  exact hmem x

end ZInQ.Manuscript.RC.EvenJoin
