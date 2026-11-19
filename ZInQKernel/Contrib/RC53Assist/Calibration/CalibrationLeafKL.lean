import ZInQKernel.Contrib.RC53Assist.Calibration.KummerCoordinate
import ZInQKernel.Contrib.RC53Assist.Calibration.GenuineLocalBlocks

/-!
# The calibration leaf with the Kummer coordinate and the local lengths derived

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141).
`CalibrationModelHKL` has every field of `CalibrationModelH` except the Kummer valuation `hK` and
the local-block fields `Fr`, `hFtr`, `hFdet`, `PW`, `QW`, `eW`, `zmov`, `zmov'`, `Bact`, `hDW`,
`hPW`, `hQW`, `hzmov`, `hzmov'`, `hact`, with the same names and types, and in their place

* `kummer : KummerCoordinateBlock …`: the ordinary Kummer complex as genuine Galois Selmer data
  over `K` with its Knudsen–Mumford model, from which `hK` is derived
  (`KummerCoordinateBlock.hK`);
* `blocks : GenuineLengthBlockModel …`: the central quotient block as the block sum of integral
  local blocks presenting the central full/Kummer quotients of the actual Kummer conditions, with
  the genuine lengths `v₂ N` and two, from which the quotient length `2 v₂N + 4ω` is derived
  (`GenuineLengthBlockModel.hδ`).

Results (PROVED, standard axioms): `CalibrationModelHKL.nonempty_modelP`,
`calibrationInputsP_of_HKL`, `calibrationTarget_of_HKL`.

**Status.** The Kummer block `KummerCoordinateBlock` is conditional bookkeeping (its disk orders
are freely assignable and `link` is a coordinate equation), so this leaf does not discharge `hK`
arithmetically; the leaf `CalibrationModelHKL2` replaces it by `KummerCoordinateBlockG` (disk
lengths read from the genuine finite-level Kummer Selmer complexes) and adds `MovingPrimeData`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine Matrix
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **The inputs of (4.6) at one address, with the Kummer coordinate derived and the local
quotient lengths read from the genuine Kummer quotients** (tex 3987–4141). -/
structure CalibrationModelHKL {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
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
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
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
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- **the Kummer block**: the ordinary Kummer complex as genuine Galois Selmer data with its
  Knudsen–Mumford model; it replaces the field `hK` of `CalibrationModelH`, which is derived -/
  kummer : KummerCoordinateBlock K DK zK wK (D.jrc (Fam.h x) D.kfin) vL (amov - 2 * chimov) tA
    shaA
  /-- **the local blocks with the lengths read from the genuine local quotients**; they replace
  the fields `Fr` … `hact` of `CalibrationModelH` -/
  blocks : GenuineLengthBlockModel K (Ecurve ℓ) (Fam.h x) DW rmov
    (padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov)) (omega (Fam.h x))

attribute [instance] CalibrationModelHKL.fieldK CalibrationModelHKL.nfK CalibrationModelHKL.decK
  CalibrationModelHKL.quadK CalibrationModelHKL.fκ CalibrationModelHKL.dκ

namespace CalibrationModelHKL

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- `m = a_r − 2χ_h(r) ≠ 0`, from the non-divisibility `2^{c_E+1} ∤ m`. PROVED. -/
theorem m_ne_zero (M : CalibrationModelHKL D vL G₀ Fam x) : M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- **`CalibrationModelP` from `CalibrationModelHKL`**: `hvprim` from the triangular Kummer model,
the derived Kummer valuation (`KummerCoordinateBlock.hK`) and the derived quotient length
(`GenuineLengthBlockModel.hδ`). PROVED. -/
theorem nonempty_modelP (M : CalibrationModelHKL D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) := by
  obtain ⟨tp, hB, htp⟩ := componentFields_of_edixhovenIso M.hEdix M.hodd M.hram M.goodModel
  obtain ⟨hchi, hmne, hrmov, hBexp⟩ := movingFields_of_nondiv (M.rmov : ℤ) M.amov
    M.chimov M.cE M.Bexp M.hchi M.hnd M.hrmov M.hcB
  have hvprim := hvprim_of_triangular_model M.DK M.X M.DW M.zK M.wK M.zP M.wP M.uK
    (D.uPrim Fam x) M.hz M.hw M.hP M.hKc M.hadj (D.jrc (Fam.h x) D.kfin) vL
    ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) ((padicValNat 2 M.tA : ℕ) : ℤ)
    ((padicValNat 2 M.shaA : ℕ) : ℤ)
    ((padicValInt 2 ((M.rmov : ℤ) + 1 - M.chimov * M.amov) : ℕ) : ℤ)
    ((omega (Fam.h x) : ℕ) : ℤ) (M.kummer.hK M.m_ne_zero M.hKc M.hadj) M.blocks.hδ
  exact ⟨{ M with
    tp := tp
    hB := hB
    htp := htp
    rmov := (M.rmov : ℤ)
    hchi := hchi
    hmne := hmne
    hrmov := hrmov
    hBexp := hBexp
    hvprim := hvprim }⟩

end CalibrationModelHKL

/-- **The remaining inputs of `RCSteps.calibration`, with the Kummer coordinate derived and the
local quotient lengths read from the genuine Kummer quotients** ((4.6), tex 3987–4141). -/
def CalibrationInputsHKL {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHKL D vL G₀ F x)

/-- `CalibrationInputsP` from `CalibrationInputsHKL` (PROVED). -/
theorem calibrationInputsP_of_HKL {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsHKL D) :
    CalibrationInputsP D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelP

/-- **`RCSteps.calibration` from `CalibrationInputsHKL`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5`. PROVED. -/
theorem calibrationTarget_of_HKL {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHKL D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_HKL h))

end ZInQ.Contrib.RC53Assist.Calibration
