import ZInQKernel.Contrib.OneProof.RC.Wiring.Data
import ZInQKernel.Contrib.OneProof.RC.Central.Nodes
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaT
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Bridges

/-!
# Theorem 5.3, Lane RC0 round 2: the central targets from lane RC15's results

Three fields of `RCSteps` are discharged here from the results of lane RC15 (the class-functional
coordinate, the calibration (4.6), the correction (4.7) and the base-zero lemma), together with
batch 3's paired functional:

* `calibrationTarget_of_inputs : CalibrationInputs D → CalibrationTarget D` ((4.6), tex 3987–4141);
* `baseZeroTarget_of_inputs : Prints → BaseZeroInputs D → BaseZeroTarget D` (tex 4330–4376);
* `commonCoordinateTarget_of_inputs : CommonCoordinateInputs D → CommonCoordinateTarget D`
  ((4.7), tex 4142–4328).

Everything lane RC15 proves is used, so that only the genuinely remaining inputs stay as
hypotheses. In particular the following are **not** hypotheses here, but consequences:

| derived here | by lane RC15's | tex |
|---|---|---|
| `v₂ N_i = v₂ m_i` at the moving prime | `padicValInt_movingNorm` | 4066–4075 |
| `Reg_ℬ = (2/α²) Reg_𝒜` for the real regulators, `2/α² ∈ ℚ`, and `v₂(Reg_ℬ/Reg_𝒜) = ±1` | `regulator_ratio` (over `ℝ`), `regulator_eq_ratCast_mul`, `padicValRat_regulator_ratio` | 4082–4090, 4110 |
| `a ∈ {±1, ±2, ±4}` and `|v₂(Ω_ℬ/Ω_𝒜)| ≤ 4` | `pullback_values`, `padicValRat_period_ratio` | 4093–4104 |
| `s_𝒜 − s_ℬ = 2g_𝒜 − 2g_ℬ + v₂(2/α²) + v₂ρ_Ω + v₂(C_ℬ/C_𝒜)` | `milne_valuation_form_of_adjunction` (through `milne_valuation_form`) | 4105–4112 |
| `v₂(C_ℬ/C_𝒜) = Σ_{p ∣ k} t_p` | `padicValRat_component_ratio` | 4118–4135 |
| (4.6) itself, with `|ε| ≤ 2v₂L + 2G₀ + 5` | `calibration_46` | 4044–4047 |
| the base-zero dichotomy and `ũ₀(0) = 0` | `baseZero_node`, over lane RC20's genuine `A = Λ_(t)` (`baseZero_node_genuine`) | 4330–4376 |
| `ũ_x = (∏ ε_q) u_{prim,x}` from the one-prime (4.7) | `corrected_eq` | 4219–4226 |
| the integral closed row `w` of the paired functional | batch 3's `twoTermClosedRow_proof` | 3704–3875, 4342–4344 |

The constants `v₂L` and `G₀` of the error bound `C_cal = 2v₂L + 2G₀ + 5` are fixed before the
family, as the text requires ("The error depends on the fixed old local types and fixed multiplier,
but not on `h` or `k`", tex 3999–4000).

The auxiliary objects of each input live in `Type`, inside one existential (`Nonempty` of a
bundle whose fields are listed, each with its tex lines, kind and owner).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology
open Matrix

attribute [local instance] Nat.fact_prime_two

/-! ## `Λ`-units are closed under finite products -/

/-- `1 ∈ Λ^×` (PROVED). -/
theorem lamUnit_one : LamUnit 1 := ⟨1, by simp⟩

/-- `Λ^×` is closed under multiplication (PROVED). -/
theorem LamUnit.mul {a b : PowerSeries ℚ_[2]} (ha : LamUnit a) (hb : LamUnit b) :
    LamUnit (a * b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact ⟨u * v, by rw [Units.val_mul, map_mul]⟩

/-- `Λ^×` is closed under finite products (PROVED). -/
theorem lamUnit_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ_[2])
    (h : ∀ i ∈ s, LamUnit (f i)) : LamUnit (∏ i ∈ s, f i) :=
  Finset.prod_induction f LamUnit (fun _ _ => LamUnit.mul) lamUnit_one h

/-! ## (4.6): the calibration -/

/-- The determinant computation of (4.6) (tex 4051–4080): the class and functional free
coefficients contribute `j_rc + v₂(Lm)` each, the ordinary Kummer torsion contributes the disks of
lengths `g_𝒜, s_𝒜, g_𝒜` in degrees one, two, three, the two places above the moving prime
contribute degree-two length `v₂N_i` each, and the two places above each of the `ω(h)` active
primes contribute degree-two length two each. -/
def primValuation (j vL vm gA sA vN ω : ℤ) : ℤ :=
  (j + vL + vm) + (j + vL + vm) +
    (Central.diskContribution 1 gA + Central.diskContribution 2 sA +
      Central.diskContribution 3 gA) +
    (2 * Central.diskContribution 2 vN + ω * (2 * Central.diskContribution 2 2))

/-- **The remaining inputs of (4.6) at one address** (Proposition `ex:arith-central-calibration`,
tex 3987–4141), for the isogenous pair `𝒜 = Res_{K/ℚ}(E^{(h_x)}_K)`, `ℬ = E^{(h_x)} × E^{(h_x k)}`
at a known simple zero `h_x` of the final family. The two fixed constants `v₂L` and `G₀` are
parameters, fixed before the family.

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `shaA`–`tB_ne` | the two-primary orders `|Ш|`, `|tors|` of `𝒜` and `ℬ`, nonzero (finite `Ш` at a known simple zero, by the forward theorem) | 4020–4021, 4050–4057 | existential orders (genuine witnesses finite by Kolyvagin, `lem:forward-rank`, tex 1086–1093) | RC9 |
| `Scomp`, `cA`, `cB`, `tp`, `hTS`, `hcpos`, `hcancel`, `hA1`, `hB` | the component numbers: cancellation at split primes, `c_p(𝒜) = 1` (connected Weil restriction), `c_p(ℬ) = 2^{t_p}` at `p ∣ k` | 4118–4135 | ELLIOT + PRINT (Edixhoven Thm 5.3, Rem 5.4.1) | RC15 / RC9 |
| `htp` | `t_p = dim_{𝔽₂} E[2]^{Fr_p} ≤ 2` | 4000, 4039, 4136 | ELLIOT | RC15 |
| `alpha`, `beta`, `hIJ` | the dual isogeny indices with `IJ = 2` (`φ g_𝒜 ≡ α g_ℬ`, `ψ g_ℬ ≡ β g_𝒜` on free generators) | 4082–4088 | ELLIOT (PROVED by lane RC19 for the genuine generators: `CalibrationModelR.nonempty_model`; with `alpha = I`, `beta = J` the actual cokernel cardinalities: `CalibrationModelR.nonempty_model_index`) | RC15 / RC19 |
| `RegA`, `RegB`, `hadj` | the **real** regulators of `𝒜` and `ℬ` (canonical heights of free generators at rank one) and the height adjunction read on generators, `α Reg_ℬ = β Reg_𝒜`; the rational ratio `Reg_ℬ/Reg_𝒜 = 2/α²` is derived from it (`Central.regulator_eq_ratCast_mul`), it is not a field | 4022–4025, 4082–4090 | GLUE (functoriality of the canonical height; PROVED by lane RC19 for the genuine heights, `regulator_ratio_sumDiff`) | RC15 / RC19 |
| `aPull`, `bPull`, `hab` | the integral pullbacks of the Néron differentials, `ab = 4` | 4093–4096 | ELLIOT | RC15 |
| `gam`, `kap`, `hgam`, `hkap`, `hcv` | the real change of variables, both finite groups of order at most four | 4096–4104 | GLUE | RC15 |
| `OmA`, `hRegA`, `hOmA`, `rhoOm` | the chosen Néron period of `𝒜`, `Reg_𝒜 ≠ 0`, `Ω_𝒜 ≠ 0`, and the rational period ratio | 4089–4092, 4096–4104 | definition | RC15 |
| `hmilne` | Cassels' isogeny invariance of the Birch–Swinnerton-Dyer quotient at the real regulators `Reg_𝒜`, `Reg_ℬ`, with self-dual torsion counts (principal polarizations) | 4027–4030, 4106–4113 | PRINT (Milne ADT I.7.3, (7.3.1)) + GLUE | RC15 |
| `hsB` | `Ш(ℬ) = Ш(E^{(h_x)}) × Ш(E^{(h_x k)})`: `s_ℬ = s(h_x) + s(h_x k)` | 4053–4057 (implicit), and the signs at 4138–4139 | ELLIOT | RC15 |
| `hgB` | the rational torsion of `ℬ` is bounded by the fixed `G₀` | 4115–4116 | ELLIOT | RC15 |
| `rmov`–`hBexp` | the moving prime: `r ≡ 1 (mod 2^B)`, `χ = ±1`, `m = a_r − 2χ ≠ 0`, `v₂m < B` (lane RC17's `moving_character_genuine` produces exactly such a prime over the genuine Tate image) | 4066–4075 | ELLIOT | RC4 / RC17 |
| `hvprim` | determinant multiplicativity in the support triangles: the primitive central value is regular with the computed valuation | 4058–4080 | ELLIOT | RC15 (with the Duality and RankCounts areas) |
-/
structure CalibrationModel {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- `t_p = dim_{𝔽₂} E[2]^{Fr_p}` -/
  tp : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- Edixhoven at a companion prime -/
  hB : ∀ p ∈ D.kfin.natAbs.primeFactors, cB p = 2 ^ tp p
  /-- `t_p ≤ 2` -/
  htp : ∀ p ∈ D.kfin.natAbs.primeFactors, tp p ≤ 2
  /-- the index `I = [ℬ(ℚ)_free : φ 𝒜(ℚ)_free]` of `φ : 𝒜 → ℬ` (RC19's `diffMap`,
  `P ↦ (P + σP, ι⁻¹(P − σP))`; tex 4082–4084) -/
  alpha : ℤ
  /-- the index `J = [𝒜(ℚ)_free : ψ ℬ(ℚ)_free]` of `ψ : ℬ → 𝒜` (RC19's `sumMap`,
  `(Q, R) ↦ Q + ι R`; tex 4085–4086) -/
  beta : ℤ
  /-- `IJ = 2` -/
  hIJ : alpha * beta = 2
  /-- the regulator of `𝒜`, a real number (the canonical height of a free generator) -/
  RegA : ℝ
  /-- the regulator of `ℬ`, a real number (the canonical height of a free generator) -/
  RegB : ℝ
  /-- the height adjunction on generators: `α Reg_ℬ = β Reg_𝒜` -/
  hadj : (alpha : ℝ) * RegB = (beta : ℝ) * RegA
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero regulator -/
  hRegA : RegA ≠ 0
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, at the real regulators `Reg_𝒜`, `Reg_ℬ` -/
  hmilne : Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
    (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) RegA RegB OmA ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℤ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `m_i = a_{r_i} − 2χ ≠ 0` -/
  hmne : amov - 2 * chimov ≠ 0
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ rmov - 1
  /-- `v₂ m_i < B_i` (the manuscript's `v₂ m_i ≤ c_E < B_i`) -/
  hBexp : padicValInt 2 (amov - 2 * chimov) < Bexp
  /-- the primitive central value is regular at the centre with the computed valuation -/
  hvprim : v2 (central (D.uPrim Fam x)) =
    ((primValuation (D.jrc (Fam.h x) D.kfin) vL ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)
      ((padicValNat 2 tA : ℕ) : ℤ) ((padicValNat 2 shaA : ℕ) : ℤ)
      ((padicValInt 2 (rmov + 1 - chimov * amov) : ℕ) : ℤ) ((omega (Fam.h x) : ℕ) : ℤ) :
        ℤ) : WithTop ℤ)

/-- **The remaining inputs of `RCSteps.calibration`** ((4.6), tex 3987–4141): two constants
`v₂L ≥ 0` (the fixed multiplier) and `G₀` (the fixed torsion bound), fixed before the family, and
at every address of a final family with the two analytic hypotheses of the proposition
(`ord_{s=1} L(E^{(h_x)},s) = 1` and `L(E^{(h_x k)},1) ≠ 0`) one `CalibrationModel`, whose fields
are listed there with their tex lines, kind and owner. -/
def CalibrationInputs {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModel D vL G₀ F x)

/-- **`RCSteps.calibration` from those inputs** ((4.6), tex 3987–4141), with the uniform error
bound `C_cal = 2v₂L + 2G₀ + 5` of lane RC15's `calibration_46`. PROVED. -/
theorem calibrationTarget_of_inputs {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputs D) :
    CalibrationTarget D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨2 * vL + 2 * G₀ + 5, ?_⟩
  intro Co Ce F hF x h1 h0
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  -- the component ratio
  have hcB : ∀ p ∈ M.Scomp, 0 < M.cB p := by
    intro p hp
    by_cases hpT : p ∈ D.kfin.natAbs.primeFactors
    · rw [M.hB p hpT]; positivity
    · rw [← M.hcancel p hp hpT]; exact M.hcpos p hp
  have hCA : (∏ p ∈ M.Scomp, M.cA p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (M.hcpos p hp).ne'
  have hCB : (∏ p ∈ M.Scomp, M.cB p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hcB p hp).ne'
  have hprodcast : ((((∏ p ∈ M.Scomp, M.cB p) : ℕ) : ℚ) / (((∏ p ∈ M.Scomp, M.cA p) : ℕ) : ℚ)) =
      (∏ p ∈ M.Scomp, (M.cB p : ℚ)) / ∏ p ∈ M.Scomp, (M.cA p : ℚ) := by
    push_cast
    rfl
  have hvC : padicValRat 2 ((((∏ p ∈ M.Scomp, M.cB p) : ℕ) : ℚ) /
      (((∏ p ∈ M.Scomp, M.cA p) : ℕ) : ℚ)) = ∑ p ∈ D.kfin.natAbs.primeFactors, (M.tp p : ℤ) := by
    rw [hprodcast]
    exact Central.padicValRat_component_ratio M.hTS M.cA M.cB M.tp M.hcpos M.hcancel M.hA1 M.hB
  -- the period ratio
  have hper := Central.padicValRat_period_ratio (ΩB := (M.rhoOm : ℝ) * M.OmA) M.hOmA
    (Central.pullback_values M.hab) M.hgam M.hkap M.hcv
  have hρΩeq : M.rhoOm = (((M.aPull.natAbs * M.gam : ℕ) : ℚ) / M.kap) := by
    have h1 := hper.1
    rw [mul_div_assoc, div_self M.hOmA, mul_one] at h1
    exact_mod_cast h1
  have hΩ : |padicValRat 2 M.rhoOm| ≤ 4 := by rw [hρΩeq]; exact hper.2
  have hρΩ0 : M.rhoOm ≠ 0 := by
    rw [hρΩeq]
    have haP : M.aPull ≠ 0 := by
      intro h0'
      have hab := M.hab
      rw [h0', zero_mul] at hab
      exact absurd hab (by norm_num)
    have hgam := M.hgam
    have hkap := M.hkap
    have h1 : (M.aPull.natAbs * M.gam : ℕ) ≠ 0 :=
      Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr haP) (by omega)
    have h2 : (M.kap : ℚ) ≠ 0 := by
      have : M.kap ≠ 0 := by omega
      exact_mod_cast this
    exact div_ne_zero (by exact_mod_cast h1) h2
  -- the regulator ratio and Milne: from the height adjunction on the real regulators,
  -- `Reg_ℬ = (2/α²) Reg_𝒜` with `2/α² ∈ ℚ` and `v₂(2/α²) = ±1` (derived, not assumed)
  obtain ⟨hMilne, hReg⟩ := Central.milne_valuation_form_of_adjunction M.hIJ M.hadj M.shaA_ne
    M.shaB_ne M.tA_ne M.tB_ne hCA hCB M.hRegA M.hOmA hρΩ0 M.hmilne
  -- the moving prime
  have hvN : ((padicValInt 2 (M.rmov + 1 - M.chimov * M.amov) : ℕ) : ℤ) =
      ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) := by
    exact_mod_cast Central.padicValInt_movingNorm M.hchi M.hmne M.hrmov M.hBexp
  -- (4.6)
  have hprim : primValuation (D.jrc (F.h x) D.kfin) vL
      ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) ((padicValNat 2 M.tA : ℕ) : ℤ)
      ((padicValNat 2 M.shaA : ℕ) : ℤ)
      ((padicValInt 2 (M.rmov + 1 - M.chimov * M.amov) : ℕ) : ℤ) ((omega (F.h x) : ℕ) : ℤ) =
      (D.jrc (F.h x) D.kfin + vL + ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ)) +
        (D.jrc (F.h x) D.kfin + vL + ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ)) +
        (Central.diskContribution 1 ((padicValNat 2 M.tA : ℕ) : ℤ) +
          Central.diskContribution 2 ((padicValNat 2 M.shaA : ℕ) : ℤ) +
          Central.diskContribution 3 ((padicValNat 2 M.tA : ℕ) : ℤ)) +
        (2 * Central.diskContribution 2
            ((padicValInt 2 (M.rmov + 1 - M.chimov * M.amov) : ℕ) : ℤ) +
          ((omega (F.h x) : ℕ) : ℤ) * (2 * Central.diskContribution 2 2)) := rfl
  obtain ⟨hcal, hcalbd⟩ := Central.calibration_46 (G₀ := G₀) hprim hvN hMilne M.hsB hvC hReg hΩ
    ⟨Int.natCast_nonneg _, M.hgB⟩ hvL
  refine ⟨fun p => min (M.tp p) 2, 2 * vL + 2 * ((padicValNat 2 M.tB : ℕ) : ℤ) -
    padicValRat 2 (2 / (M.alpha : ℚ) ^ 2) - padicValRat 2 M.rhoOm, fun p => min_le_right _ _,
    hcalbd, ?_⟩
  have hsum : ∑ p ∈ D.kfin.natAbs.primeFactors, ((min (M.tp p) 2 : ℕ) : ℤ) =
      ∑ p ∈ D.kfin.natAbs.primeFactors, ((M.tp p : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun p hp => by rw [min_eq_left (M.htp p hp)]
  rw [M.hvprim, hcal, hsum]

/-! ## The base-zero lemma -/

/-- The coefficient data of the final family `F`: the coordinates are the coefficients of the
corrected coordinates `ũ_x` (the identification of `FixedFieldPackage.coord`, tex 5486–5506); the
group-ring coefficients play no part in the base-zero lemma. -/
def coordOfFamily {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : CoordData Fam.b where
  F := fun _ _ => 0
  D := fun _ _ => 0
  u := fun y j => PowerSeries.coeff j (D.uTilde Fam y)

@[simp] theorem coordOfFamily_u_zero {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) :
    (coordOfFamily D Fam).u 0 0 = central (D.uTilde Fam 0) := rfl

/-- **The remaining inputs of the base-zero lemma at one final family** (Lemma
`ex:arith-base-zero`, tex 4330–4376), in the form lane RC15's `baseZero_node` takes them.

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `K`, `P` | `K = ℚ(√k)` and the conductor-one ring-class point `P ∈ E(K)` | 4330–4333, 4345 | definition | RC15 / RC10 |
| `hheight` | the conductor-one height formula: `L'(E/K,1) = 0` makes `P` torsion (the application of the print, needing `L(E/K,s) = L(E,s)L(E^{(k)},s)` and `ĥ = 0 ⇔ torsion`) | 4345–4346 | PRINT application (Cai–Shu–Tian Thm 1.1) + GLUE | batch 3 HeegnerCohomology |
| (the DVR) | `A = Λ_(t)` with residue field `ℚ₂` and fraction field `F = Frac Λ` are **genuine** (lane RC20), not inputs | 4341–4342 | PROVED elsewhere | RC20 |
| `m`, `Dm` | the two-term model of the primitive complex at the base (DEPARTURE of form: the complex after cancelling the unit disks outside degrees one and two) | 4353–4360 | ELLIOT + GLUE | RC15 / RC7 |
| `hcentral` | full two-primary Selmer corank one for `E/K` gives central dimensions `(1,1)` | 4350–4352 | ELLIOT | RC15 (with the RankCounts area) |
| `z`, `hz` | the retained integral cycle | 4342–4343, 4347–4348 | ELLIOT | RC15 |
| `CU`, `e1`, `e2`, `hd` | the identification of degrees one and two of the complex with `A^{m+1}`, under which the differential is `Dm` | 3877–3892, 4353–4360 | definition | RC15 |
| `lam`, `hlam` | the paired functional `λ_z`, `A`-linear and closed (its integral row vector is **derived** from batch 3's bridge, not assumed) | 3704–3875, 4342–4344 | ELLIOT/GLUE | batch 3 PairedFunctional (its unit premise: RC7) |
| `uprim`, `hu` | the generic class-functional coordinate of `[z] ⊗ [λ_z]` | 3882–3892 | definition | RC15 |
| `kappa`, `Lm`, `h45` | the central Kummer comparison and the retained boundary (4.5): `z̄ = i(Lm·P)` | 3899–3902, 3911–3915, 4346–4348 | ELLIOT | RC15 / batch 3 Duality |
| `eps0`, `utilde0`, `h47` | (4.7) at the base: `ũ₀ = ε₀ u_{prim,0}` with `ε₀ ∈ A` | 4369–4373 | ELLIOT | RC15 (also `commonCoordinateTarget_of_inputs` below) |
| `wHalf`, `hwHalf` | height-one regularity: `ũ₀ ∈ Λ[1/2]` | 5196–5200, 5703 | ELLIOT | RC16 |
| `hC` | the package's datum is its central value `ũ₀(0)` | 4366–4370, 5719–5721 | definition (RC20's `hcoef_of_lambdaHalf` replaces the earlier GLUE) | RC15 / RC20 |
-/
structure BaseZeroModel {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) : Type 1 where
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [decK : DecidableEq K]
  [algK : Algebra ℚ K]
  /-- the conductor-one ring-class point -/
  P : ((Ecurve ℓ).baseChange K).toAffine.Point
  /-- the conductor-one height formula makes it torsion when `L'(E/K,1) = 0` -/
  hheight : CST.CSTThm11Split → ProductOrderGeTwo (Ecurve ℓ) ((D.kfin : ℚ)) → IsOfFinAddOrder P
  /-- the rank of the two-term model -/
  m : ℕ
  /-- the differential of the two-term model, over `A = Λ_(t)` -/
  Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT
  /-- central dimensions `(1,1)` -/
  hcentral : (Dm.map Rings.rhoT).rank = m
  /-- the retained integral cycle -/
  z : Fin (m + 1) → Rings.LambdaT
  /-- it is a cycle -/
  hz : Dm *ᵥ z = 0
  /-- the complex of the model -/
  CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ
  /-- degree one is `A^{m+1}` -/
  e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  /-- degree two is `A^{m+1}` -/
  e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT)
  /-- in these coordinates the differential is `Dm` -/
  hd : ∀ y, e2 ((CU.d 1 2).hom y) = Dm *ᵥ e1 y
  /-- the paired functional -/
  lam : CU.X 2 →ₗ[Rings.LambdaT] Rings.LambdaT
  /-- it is closed -/
  hlam : ∀ y : CU.X 1, lam ((CU.d 1 2).hom y) = 0
  /-- the generic class-functional coordinate, in `F = Frac Λ` -/
  uprim : FractionRing Uniform.Lambda
  /-- it is the coordinate of `[z] ⊗ [λ_z]` -/
  hu : ∀ w : Fin (m + 1) → Rings.LambdaT, w ᵥ* Dm = 0 →
    (∀ y, lam (e2.symm y) = w ⬝ᵥ y) →
    Central.IsClassFunctionalCoord
      (Dm.map (algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (z i))
      (fun i => algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) (w i)) uprim
  /-- the central Kummer comparison -/
  kappa : ((Ecurve ℓ).baseChange K).toAffine.Point →+ (Fin (m + 1) → ℚ_[2])
  /-- the fixed multiplier `Lm` -/
  Lm : ℤ
  /-- the retained boundary (4.5) at the base -/
  h45 : (fun i => Rings.rhoT (z i)) = (Lm : ℚ_[2]) • kappa P
  /-- the `Λ`-unit of (4.7) at the base -/
  eps0 : Rings.LambdaT
  /-- the corrected coordinate at the base -/
  utilde0 : FractionRing Uniform.Lambda
  /-- (4.7) at the base -/
  h47 : utilde0 = algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) eps0 * uprim
  /-- height-one regularity: the corrected coordinate lies in `Λ[1/2]` -/
  wHalf : Uniform.LambdaHalf
  /-- and is that element of `Λ[1/2]` -/
  hwHalf : Uniform.lambdaHalfToFrac wHalf = utilde0
  /-- the package's datum is its central value -/
  hC : central (D.uTilde Fam 0) = Uniform.centralSpecialization wHalf

attribute [instance] BaseZeroModel.fieldK BaseZeroModel.decK BaseZeroModel.algK

/-- **The remaining inputs of `RCSteps.base_zero`** (Lemma `ex:arith-base-zero`, tex 4330–4376):
under the hypotheses of the lemma on the companion (`L(E^{(k)},1) ≠ 0` and full two-primary Selmer
corank one for `E/K`), every final family has a `BaseZeroModel`, whose fields are listed there with
their tex lines, kind and owner. The model may depend on those two hypotheses (central dimensions
`(1,1)` use `s₂(E/K) = 1`), but not on `L'(E/K,1) = 0`, which enters only through `hheight`. -/
def BaseZeroInputs {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  SelmerCorankOneOverK ℓ D.kfin → AnalyticRank (Etw ℓ D.kfin) 0 →
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → Nonempty (BaseZeroModel D F)

/-- **`RCSteps.base_zero` from those inputs** (tex 4330–4376). The abstract proposition of lane
RC15's `baseZero_node` is instantiated with the blueprint's statement of Cai–Shu–Tian, Theorem 1.1,
taken from `Prints`; the integral closed row vector of the paired functional is produced by batch
3's bridge. PROVED. -/
theorem baseZeroTarget_of_inputs {ℓ : ℕ} {D : RCData ℓ} (P : Prints) (h : BaseZeroInputs D) :
    BaseZeroTarget D := by
  intro hSel hk hL Co Ce F hF
  obtain ⟨M⟩ := h hSel hk Co Ce F hF
  obtain ⟨w, hwD, hrep⟩ :=
    PairedFunctional.twoTermClosedRow_proof Rings.LambdaT M.CU M.m M.Dm M.e1 M.e2 M.hd M.lam
      M.hlam
  have hnode :=
    Rings.baseZero_node_genuine (E := Ecurve ℓ) (k := (D.kfin : ℚ)) (coordOfFamily D F) M.K M.P
      CST.CSTThm11Split P.cst M.hheight M.Dm M.hcentral M.z w M.hz M.uprim
      (M.hu w hwD hrep) M.kappa M.Lm M.h45 M.eps0 M.utilde0 M.h47 M.wHalf M.hwHalf M.hC
  exact hnode hL

/-! ## (4.7): the common coordinate -/

/-- **The remaining inputs of (4.7) at one address** (Lemma `ex:arith-common-coordinate`,
tex 4142–4328), in the form lane RC15's `corrected_eq` takes them.

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `R`, `chi` | the coefficient ring `𝒪[G]` and the character at the address | 4194–4197 | definition | RC15 / RC7 |
| `Q`, `v`, `g`, `l`, `e`, `ei` | the graph primes, the inertia generators, the quotient factors `l_q`, the point factors `e_q` with their inverses, and `v_q = (l_q/e_q² − 1)/2` | 4151–4222 | definition | RC15 |
| `hsign` | `x(g_q) = ±1` at every graph prime | 2728–2729, 2750–2751 | definition (the universal quadratic character) | RC15 / RC4 |
| `hratio` | `x(l_q) x(e_q)^{-2} = 1 + 2x(v_q)` (the evaluated form of `l_q/e_q² = 1 + 2v_q`, PROVED by lane RC15 from the Euler-factor identity and `e_q ∈ 𝒪[G]^×`) | 4208–4219 | ELLIOT (the Frobenius model at `q`) | RC15 / RC4 |
| `hinv` | `e_q` is invertible at the character | 4194–4205 | ELLIOT | RC15 |
| `urel`, `hutilde` | the relaxed coordinate and `ũ = η u_rel` | 4219–4226 | definition | RC15 |
| `U`, `hU` | the unused primes of the address | 4220–4222 | definition | RC15 |
| `h47` | the multi-prime (4.7) at the address, `(∏_U l_q) u_rel = (∏_U e_q² ε_q) u_prim` (lane RC15 derives it from the one-prime identity by `prod_relax`; the one-prime identity itself is the support triangle, naturality of the cup pairing) | 4166–4193 | ELLIOT + GLUE (Nekovář 6.4.1–6.4.3, UNVERIFIED) | RC15 / batch 3 Duality |
| `hunit` | `ε_q ∈ Λ^×` | 4189–4193 | ELLIOT | RC15 |
-/
structure CommonCoordinateModel {ℓ : ℕ} (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) :
    Type 1 where
  /-- the coefficient ring `𝒪[G]` -/
  R : Type
  [commR : CommRing R]
  /-- the character at the address -/
  chi : R →+* PowerSeries ℚ_[2]
  /-- the graph primes -/
  Q : Finset ℕ
  /-- `v_q` -/
  v : ℕ → R
  /-- the inertia generators `g_q` -/
  g : ℕ → R
  /-- the quotient factors `l_q` -/
  l : ℕ → R
  /-- the point factors `e_q` -/
  e : ℕ → R
  /-- their inverses -/
  ei : ℕ → R
  /-- the units `ε_q` -/
  eps : ℕ → PowerSeries ℚ_[2]
  /-- `x(g_q) = ±1` -/
  hsign : ∀ q ∈ Q, chi (g q) = 1 ∨ chi (g q) = -1
  /-- `x(l_q) x(e_q)^{-2} = 1 + 2 x(v_q)` -/
  hratio : ∀ q ∈ Q, chi (l q) * chi (ei q) ^ 2 = 1 + 2 * chi (v q)
  /-- `e_q` is invertible at the character -/
  hinv : ∀ q ∈ Q, chi (e q) * chi (ei q) = 1
  /-- the relaxed coordinate -/
  urel : PowerSeries ℚ_[2]
  /-- the unused primes of the address -/
  U : Finset ℕ
  /-- they are the graph primes at which the character is inactive -/
  hU : ∀ q, q ∈ U ↔ (q ∈ Q ∧ chi (g q) = 1)
  /-- the multi-prime (4.7) at the address -/
  h47 : (∏ q ∈ U, chi (l q)) * urel = (∏ q ∈ U, chi (e q) ^ 2 * eps q) * D.uPrim Fam x
  /-- the `ε_q` are `Λ`-units -/
  hunit : ∀ q ∈ U, LamUnit (eps q)
  /-- the corrected coordinate is `η u_rel` -/
  hutilde : D.uTilde Fam x = chi (Central.eta Q v g) * urel

attribute [instance] CommonCoordinateModel.commR

/-- **The remaining inputs of `RCSteps.common_coordinate`** ((4.7), tex 4142–4328): at every
address of a final family one `CommonCoordinateModel`, whose fields are listed there with their
tex lines, kind and owner. -/
def CommonCoordinateInputs {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
    Nonempty (CommonCoordinateModel D F x)

/-- **`RCSteps.common_coordinate` from those inputs** ((4.7), tex 4142–4328): the corrected
coordinate is the primitive one times the product of the `ε_q` over the unused primes of the
address, and that product is a `Λ`-unit. PROVED (lane RC15's `corrected_eq`). -/
theorem commonCoordinateTarget_of_inputs {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputs D) :
    CommonCoordinateTarget D := by
  intro Co Ce F hF x
  obtain ⟨M⟩ := h Co Ce F hF x
  classical
  have hfilter : (M.Q.filter fun q => M.chi (M.g q) = 1) = M.U := by
    ext q
    rw [Finset.mem_filter, ← M.hU q]
  have h47 : (∏ q ∈ M.Q with M.chi (M.g q) = 1, M.chi (M.l q)) * M.urel =
      (∏ q ∈ M.Q with M.chi (M.g q) = 1, M.chi (M.e q) ^ 2 * M.eps q) * D.uPrim F x := by
    rw [hfilter]; exact M.h47
  have hcorr := Central.corrected_eq M.chi M.Q M.v M.g M.l M.e M.ei M.eps M.urel (D.uPrim F x)
    M.hsign M.hratio M.hinv h47
  refine ⟨∏ q ∈ M.U, M.eps q, lamUnit_prod _ _ M.hunit, ?_⟩
  rw [M.hutilde, hcorr, hfilter]

/-! ## Non-vacuity

The inputs of (4.6) and (4.7) are jointly satisfiable, with a **nonzero** primitive central value
at every address: the deductions above are not vacuous. The witness is the interface data with the
trivial companion `k = 1`, no graph primes and the primitive coordinate prescribed to have the
calibrated valuation; the regulators are the irrational reals `Reg_𝒜 = π`, `Reg_ℬ = 2π` (indices
`α = 1`, `β = 2`, adjunction `1 · 2π = 2 · π`), and the Milne instance is the genuine real identity
`2^{s+1} · π / 1 = 2^s · 2π / 1`.
-/

/-- `v₂((2 : ℚ₂)^n) = n` for every integer exponent (PROVED). -/
theorem v2_two_zpow (n : ℤ) : v2 ((2 : ℚ_[2]) ^ n) = (n : WithTop ℤ) := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hx : (2 : ℚ_[2]) ^ n ≠ 0 := zpow_ne_zero _ h2
  have hv : ((2 : ℚ_[2])).valuation = 1 := by
    exact_mod_cast Padic.valuation_p (p := 2)
  rw [v2, Padic.addValuation.apply hx, Padic.valuation_zpow, hv, mul_one]

/-- The binary family of the non-vacuity witness: dimension zero, no graph primes. -/
def witnessFamily : Family := ⟨0, ∅, fun _ => 0⟩

/-- The prescribed valuation of the primitive central value of the witness at an address
(the right-hand side of (4.6) with `j_rc = 0`, no companion primes and the error `−1`). -/
def witnessPrimVal (ℓ : ℕ) (G : Family) (y : Addr G.b) : ℤ :=
  -((shaLength (Etw ℓ (G.h y)) : ℤ) + (shaLength (Etw ℓ (G.h y * 1)) : ℤ) + 1) -
    4 * (omega (G.h y) : ℤ)

/-- The interface data of the non-vacuity witness: the trivial companion `k = 1` and the
coordinates `u_{prim,x} = ũ_x = 2^{witnessPrimVal}` (constant power series). -/
def witnessData (ℓ : ℕ) : RCData ℓ where
  S := ∅
  prepared := fun _ => True
  Lstar := fun _ => 0
  jgen := fun _ => 0
  jrc := fun _ _ => 0
  hstar := 0
  stages := pure 0
  Mθ := fun _ => 0
  aθ := fun _ _ => 0
  admissible := fun _ _ => True
  δo := 0
  kfin := 1
  uPrim := fun G y => PowerSeries.C ((2 : ℚ_[2]) ^ witnessPrimVal ℓ G y)
  uTilde := fun G y => PowerSeries.C ((2 : ℚ_[2]) ^ witnessPrimVal ℓ G y)

@[simp] theorem witnessData_central_uPrim (ℓ : ℕ) (G : Family) (y : Addr G.b) :
    central ((witnessData ℓ).uPrim G y) = (2 : ℚ_[2]) ^ witnessPrimVal ℓ G y := by
  simp [witnessData, central]

/-- The primitive central value of the witness is nonzero at every address (PROVED): the
conclusion of (4.6) is not the statement about a coordinate that vanishes. -/
theorem witnessData_central_ne_zero (ℓ : ℕ) (G : Family) (y : Addr G.b) :
    central ((witnessData ℓ).uPrim G y) ≠ 0 := by
  rw [witnessData_central_uPrim]
  exact zpow_ne_zero _ (by norm_num)

/-- **The inputs of (4.6) are satisfiable** (PROVED; the non-vacuity witness of
`CalibrationModel`): every address of every family carries a `CalibrationModel` over the witness
data, with `v₂L = 0`, `G₀ = 0` (hence `C_cal = 5`), a nonzero primitive central value, and the
irrational real regulators `Reg_𝒜 = π`, `Reg_ℬ = 2π` related by the height adjunction with
`α = 1`, `β = 2` (so the real carrier of the regulators is genuinely used; their ratio `2 = 2/1²`
is rational, as it must be). -/
theorem calibrationInputs_witness (ℓ : ℕ) : CalibrationInputs (witnessData ℓ) := by
  refine ⟨0, 0, le_refl 0, ?_⟩
  intro Co Ce G hG y _ _
  refine ⟨{
    shaA := 2 ^ (shaLength (Etw ℓ (G.h y)) + shaLength (Etw ℓ (G.h y * 1)) + 1)
    shaB := 2 ^ (shaLength (Etw ℓ (G.h y)) + shaLength (Etw ℓ (G.h y * 1)))
    tA := 1
    tB := 1
    shaA_ne := by positivity
    shaB_ne := by positivity
    tA_ne := one_ne_zero
    tB_ne := one_ne_zero
    Scomp := ∅
    cA := fun _ => 1
    cB := fun _ => 1
    tp := fun _ => 0
    hTS := by simp [witnessData]
    hcpos := by simp
    hcancel := by simp
    hA1 := by simp [witnessData]
    hB := by simp [witnessData]
    htp := by simp [witnessData]
    alpha := 1
    beta := 2
    hIJ := by norm_num
    RegA := Real.pi
    RegB := 2 * Real.pi
    hadj := by push_cast; ring
    aPull := 1
    bPull := 4
    hab := by norm_num
    gam := 1
    kap := 1
    hgam := by norm_num
    hkap := by norm_num
    OmA := 1
    hRegA := Real.pi_ne_zero
    hOmA := one_ne_zero
    rhoOm := 1
    hcv := by norm_num
    hmilne := by
      simp only [Central.MilneIsogenyInvariance, Finset.prod_empty]
      push_cast
      rw [pow_succ]
      ring
    hsB := by
      simp [witnessData]
    hgB := by simp
    rmov := 3
    amov := 3
    chimov := 1
    Bexp := 1
    hchi := Or.inl rfl
    hmne := by norm_num
    hrmov := by norm_num
    hBexp := by norm_num [padicValInt]
    hvprim := by
      rw [witnessData_central_uPrim, v2_two_zpow]
      congr 1
      simp only [primValuation, Central.diskContribution, witnessPrimVal, witnessData,
        padicValNat.prime_pow, padicValNat_one_right, padicValInt]
      norm_num
      ring }⟩

/-- **The inputs of (4.7) are satisfiable** (PROVED): over the witness data the corrected and
primitive coordinates agree, which is (4.7) with the empty set of graph primes. -/
theorem commonCoordinateInputs_witness (ℓ : ℕ) : CommonCoordinateInputs (witnessData ℓ) := by
  intro Co Ce G hG y
  refine ⟨{
    R := PowerSeries ℚ_[2]
    chi := RingHom.id _
    Q := ∅
    v := fun _ => 0
    g := fun _ => 0
    l := fun _ => 0
    e := fun _ => 0
    ei := fun _ => 0
    eps := fun _ => 1
    hsign := by simp
    hratio := by simp
    hinv := by simp
    urel := (witnessData ℓ).uPrim G y
    U := ∅
    hU := by simp
    h47 := by simp
    hunit := by simp
    hutilde := by simp [Central.eta, witnessData] }⟩

/-- The two targets at the witness data (PROVED): (4.6) and (4.7) hold there, with the error
bound `C_cal = 5` and a nonzero primitive central value at every address. -/
theorem calibrationTarget_witness (ℓ : ℕ) : CalibrationTarget (witnessData ℓ) :=
  calibrationTarget_of_inputs (calibrationInputs_witness ℓ)

/-- (4.7) at the witness data (PROVED). -/
theorem commonCoordinateTarget_witness (ℓ : ℕ) : CommonCoordinateTarget (witnessData ℓ) :=
  commonCoordinateTarget_of_inputs (commonCoordinateInputs_witness ℓ)

/-- **The inputs of the base-zero lemma are satisfiable** (PROVED): whenever the base coordinate
does vanish — the conclusion of the lemma, so the best possible converse — the model exists over
the genuine `A = Λ_(t)`, with the two-term model `[A --0--> A]`, the cycle `z = t` (vanishing at
the centre), the closed functional `w = 1` and the generic coordinate `u_{prim,0} = t ≠ 0`. So the
hypotheses of `BaseZeroModel` are consistent and do not force the generic coordinate to be zero. -/
theorem baseZeroModel_nonvacuous {ℓ : ℕ} (D : RCData ℓ) (Fam : Family)
    (h0 : central (D.uTilde Fam 0) = 0) : Nonempty (BaseZeroModel D Fam) := by
  classical
  refine ⟨{
    K := ℚ
    P := 0
    hheight := fun _ _ => IsOfFinAddOrder.zero
    m := 0
    Dm := 0
    hcentral := by rw [Matrix.map_zero _ (map_zero _), Matrix.rank_zero]
    z := fun _ => algebraMap Uniform.Lambda Rings.LambdaT PowerSeries.X
    hz := by simp
    CU := PairedFunctional.threeTermComplex (M := Fin 1 → Rings.LambdaT)
      (N := Fin 1 → Rings.LambdaT) (M' := Fin 1 → Rings.LambdaT) 0 0 (by simp)
    e1 := LinearEquiv.refl _ _
    e2 := LinearEquiv.refl _ _
    hd := by
      intro y
      simp only [PairedFunctional.threeTermComplex_d_one_two, Matrix.zero_mulVec]
      rfl
    lam := LinearMap.proj 0
    hlam := by
      intro y
      simp only [PairedFunctional.threeTermComplex_d_one_two]
      rfl
    uprim := algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)
      (algebraMap Uniform.Lambda Rings.LambdaT PowerSeries.X)
    hu := ?_
    kappa := 0
    Lm := 0
    h45 := by
      funext i
      simp [Uniform.lambdaEvalZero]
    eps0 := 1
    utilde0 := algebraMap Rings.LambdaT (FractionRing Uniform.Lambda) 1 *
      algebraMap Rings.LambdaT (FractionRing Uniform.Lambda)
        (algebraMap Uniform.Lambda Rings.LambdaT PowerSeries.X)
    h47 := rfl
    wHalf := algebraMap Uniform.Lambda Uniform.LambdaHalf PowerSeries.X
    hwHalf := by
      rw [map_one, one_mul, ← Rings.algebraMap_halfToT, Rings.halfToT_algebraMap]
    hC := by
      rw [h0, Uniform.centralSpecialization_algebraMap]
      simp }⟩
  · intro w _ hrep
    have hw0 : w 0 = 1 := by
      have h := hrep (Pi.single 0 1)
      rw [dotProduct_single, mul_one] at h
      exact h.symm.trans (by rfl)
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.vecMulVec_apply, Matrix.adjugate_fin_one, hw0]

/-! ## The closed paired functional from batch 3's proposition -/

section PairedFunctionalBridge

open CategoryTheory Limits

/-- **The `lam` field of a `BaseZeroModel` is what batch 3's paired-functional proposition
produces** (Proposition `ex:arith-paired-functional`, tex 3704–3880): from its cone hypothesis and
the retained duality components, there is a closed `A`-linear functional on degree two. The unit
premise of the local models (`A_v, D_v` units, or inertia minus one a unit) is an explicit
hypothesis here; it is the augmentation/unit criterion of lane RC7. PROVED. -/
theorem exists_closed_functional_of_cone (S : Type) [CommRing S]
    (CU C' C Z : CochainComplex (ModuleCat.{0} S) ℤ) (j : C' ⟶ C) (c : Z ⟶ C) (z : Z.X 1)
    (pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S) (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S)
    (pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S) (ε ε' : S)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module S (M v)]
    (A Cin Dloc : ∀ v, Module.End S (M v)) (hDC : ∀ v, Dloc v * Cin v = Cin v * A v) (n : ι → ℤ)
    (hunit : ∀ v, (IsUnit (A v) ∧ IsUnit (Dloc v)) ∨ IsUnit (Cin v))
    (hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (PairedFunctional.tameComplex (A v) (Cin v) (Dloc v) (hDC v))⟦n v⟧)))
    (hz : (Z.d 1 2).hom z = 0)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (hL2 : ∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) :
    ∃ lam : CU.X 2 →ₗ[S] S, ∀ w : CU.X 1, lam ((CU.d 1 2).hom w) = 0 := by
  obtain ⟨e, -, hcl⟩ := PairedFunctional.exists_closed_pairedFunctional S CU C' C Z j c z pd1 pd2
    pd3 ε ε' ι M A Cin Dloc hDC n hunit hcone hz hL1 hL2
  exact ⟨PairedFunctional.pairedFunctional pd2 e.inv ((c.f 1).hom z), hcl⟩

end PairedFunctionalBridge

end ZInQ.Manuscript.RC.Wiring
