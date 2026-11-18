import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationPrints
import ZInQKernel.Contrib.CloudB3RC53.Calibration.Lengths
import ZInQKernel.Contrib.CloudB3RC53.Calibration.MovingFields

/-!
**Theorem 5.3, Lane RC0 round 3: the calibration leaf with the local lengths and the moving fields**

Batch 3's `Calibration/Lengths.lean` and `Calibration/MovingFields.lean` discharge more of
Proposition `ex:arith-central-calibration` (tex 3987–4141) than `CalibrationLeaf.lean` uses:

* `hvprim_of_model_and_lengths`: the field `hvprim` from a triangular model of the support
  triangle (Kummer complex → primitive complex), the Kummer coordinate's valuation (tex 4055–4064)
  and the identification of the central quotient block with the moving block `χ Fr_r − r` at the
  two places above `r` and `2 · 1₂` at each of the `2ω` active places; the total length
  `2 v₂N + 4ω` is PROVED (`v2_det_quotient`, tex 4066–4080), so the input `hdetW` of
  `CalibrationLeaf.lean` disappears, and the support triangle `det(D_W) · u_prim = u_K` is PROVED
  from the model (`triangular_coord`);
* `movingFields_of_nondiv`: `hmne` and `hBexp` (`m ≠ 0`, `v₂ m < B`) from the non-divisibility
  `2^{c_E+1} ∤ a_r − 2χ` and `B ≥ c_E + 1`, which is the output of lane RC17's
  `moving_character_genuine` (tex 4066–4074).

`N ≠ 0` and `r` odd are PROVED from these (`r ≡ 1 (mod 2^B)`, `B ≥ 1`). With lane RC19's
regulator data, the free generators from the prints (`CalibrationPrints.lean`) and batch 3's
component fields (`componentFields_of_reductions`), the resulting leaf is `CalibrationModelC`:

* `CalibrationModelC.nonempty_modelP : CalibrationModelC D vL G₀ F x →
  Nonempty (CalibrationModelP D vL G₀ F x)` (PROVED);
* `calibrationTarget_of_C : Prints → 0 < ℓ → CalibrationInputsC D → CalibrationTarget D`
  (PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open WeierstrassCurve WeierstrassCurve.Affine Matrix
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **The remaining inputs of (4.6) at one address, with the local lengths and the moving fields
discharged** (Proposition `ex:arith-central-calibration`, tex 3987–4141). Fields not listed are
those of `CalibrationModelP` / `CalibrationModelB` (same names, tex lines, kinds and owners).

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `kres`, `Wred`, `h2` | at `p ∣ k`: the residue field `𝔽_p`, the good reduction `Ẽ₀` of `E^{(h_x)}`, `p` odd (designated objects) | 4116–4118 | definition | RC15 / RC9 |
| `hEdix` | `c_p(ℬ) = |Ẽ₀(𝔽_p)[2]|` | 4034–4040, 4119–4127 | PRINT (Edixhoven Thm 5.3, Rem 5.4.1) as GLUE | RC9 / batch 3 Calibration |
| `rmov`, `amov`, `chimov`, `Bexp`, `cE`, `hchi`, `hrmov`, `hnd`, `hcB` | the moving prime `r ∈ ℕ` with `r ≡ 1 (mod 2^B)`, `χ = χ_h(r) = ±1`, `2^{c_E+1} ∤ a_r − 2χ`, `B ≥ c_E + 1` (lane RC17's `moving_character_genuine` output) | 4066–4074 | ELLIOT | RC4 / RC17 |
| `nK`, `κ`, `DK`, `X`, `DW` | the triangular model of the support triangle: the primitive complex is the relaxation `[[D_K, X], [0, D_W]]` of the Kummer complex `D_K` at the moving and active places, over `ℚ₂[[t]]` | 4058–4080; 3492–3494 | ELLIOT + GLUE (identification of the model with the Galois cochains) | RC15 / batch 3 Duality |
| `zK`, `wK`, `zP`, `wP`, `hz`, `hw` | the retained class and functional of the primitive complex restrict to those of the Kummer complex | 4061–4064 | ELLIOT | RC15 |
| `uK`, `hKc`, `hP` | `u_K` and `u_prim` are the class-functional coordinates of the Kummer and primitive models | 3882–3892 | definition | RC15 |
| `hadj` | the Kummer model has generic dimensions `(1,1)` (`adj D_K ≠ 0`) | 4010–4019 | ELLIOT | RC15 |
| `hK` | the Kummer coordinate has central valuation `2(j_rc + v₂L + v₂m) + (2g_𝒜 − s_𝒜)` (class and functional free coefficients, torsion disks in degrees one, two, three) | 4055–4064 | ELLIOT | RC15 |
| `Fmov`, `hFtr`, `hFdet` | the Frobenius at `r` on the Tate module: trace `a_r`, determinant `r` | 4066–4071 | definition | RC15 / RC17 |
| `hcentralW` | at the centre the quotient block is `diag(χ Fr_r − r, χ Fr_r − r, 2 · 1_{4ω})` (the two places above `r`, and `E[2]` at the two places above each active prime) | 4066–4080 | ELLIOT | RC15 (with the MinimalComplexes area) |

No longer fields compared with `CalibrationModelB`: `detW`, `htri`, `hdetW` (PROVED from the model
and `v2_det_quotient`), `hmne`, `hBexp` (PROVED by `movingFields_of_nondiv`). -/
structure CalibrationModelC {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- the residue field `𝔽_p` at a companion prime -/
  kres : ℕ → Type
  [fieldR : ∀ p, Field (kres p)]
  [decR : ∀ p, DecidableEq (kres p)]
  /-- the good reduction `Ẽ₀` of `E₀ = E^{(h_x)}` at a companion prime -/
  Wred : ∀ p, WeierstrassCurve (kres p)
  [ellR : ∀ p, (Wred p).IsElliptic]
  /-- `p` is odd -/
  h2 : ∀ p ∈ D.kfin.natAbs.primeFactors, IsUnit (2 : kres p)
  /-- Edixhoven: `c_p(ℬ) = |Ẽ₀(𝔽_p)[2]|` at a companion prime -/
  hEdix : ∀ p ∈ D.kfin.natAbs.primeFactors,
    cB p = Nat.card (AddSubgroup.torsionBy (Wred p).toAffine.Point (2 : ℕ))
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
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (lane RC17's non-divisibility) -/
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
  /-- the Kummer model has generic dimensions `(1,1)` -/
  hadj : DK.adjugate ≠ 0
  /-- the central valuation of the Kummer coordinate -/
  hK : v2 (central uK) =
    ((((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      ((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
        Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
        Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ)
  /-- the Frobenius at the moving prime -/
  Fmov : Matrix (Fin 2) (Fin 2) ℚ_[2]
  /-- its trace is `a_{r_i}` -/
  hFtr : Fmov.trace = (amov : ℚ_[2])
  /-- its determinant is `r_i` -/
  hFdet : Fmov.det = (rmov : ℚ_[2])
  /-- at the centre the quotient block is the moving block at the two places above `r_i` and
  `2 · 1₂` at the two places above each active prime -/
  hcentralW : central DW.det =
    (fromBlocks (CommonCoordinate.twoPlaceBlock Fmov (rmov : ℚ_[2]) (chimov : ℚ_[2])
      (chimov : ℚ_[2])) 0 0
      ((2 : ℚ_[2]) • (1 : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x)))
        ℚ_[2]))).det

attribute [instance] CalibrationModelC.fieldR CalibrationModelC.decR CalibrationModelC.ellR
  CalibrationModelC.fieldK CalibrationModelC.nfK CalibrationModelC.decK CalibrationModelC.quadK
  CalibrationModelC.fκ CalibrationModelC.dκ

/-- **`r` is odd and `N = r + 1 − χ a_r ≠ 0`** at the moving prime (PROVED): from
`r ≡ 1 (mod 2^B)` with `B ≥ c_E + 1 ≥ 1`, and from `N = 0 ⇒ χ (a_r − 2χ) = r − 1`, which would make
`2^{c_E+1} ∣ a_r − 2χ`. -/
theorem moving_odd_and_norm_ne_zero {r : ℕ} {a χ : ℤ} {c B : ℕ} (hχ : χ = 1 ∨ χ = -1)
    (hr : (2 : ℤ) ^ B ∣ (r : ℤ) - 1) (hnd : ¬ (2 : ℤ) ^ (c + 1) ∣ a - 2 * χ) (hB : c + 1 ≤ B) :
    Odd r ∧ (r : ℤ) + 1 - χ * a ≠ 0 := by
  refine ⟨?_, fun h0 => hnd ?_⟩
  · have h2 : (2 : ℤ) ∣ (r : ℤ) - 1 := (dvd_pow_self 2 (by omega : B ≠ 0)).trans hr
    obtain ⟨c', hc'⟩ := h2
    exact Nat.odd_iff.mpr (by omega)
  · have hm : a - 2 * χ = χ * ((r : ℤ) - 1) := by
      rcases hχ with h | h <;> subst h <;> linarith
    rw [hm]
    exact (pow_dvd_pow 2 hB).trans (Dvd.dvd.mul_left hr _)

/-- **`CalibrationModelP` from `CalibrationModelC`** (tex 4051–4080, 4066–4074, 4116–4138):
`t_p` by batch 3's `componentFields_of_reductions`; `hchi`, `hmne`, `hrmov`, `hBexp` by batch 3's
`movingFields_of_nondiv`; `hvprim` by batch 3's `hvprim_of_model_and_lengths` (the support triangle
from the model and the quotient length `2 v₂N + 4ω` from `v2_det_quotient`). PROVED. -/
theorem CalibrationModelC.nonempty_modelP {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
    {x : Addr Fam.b} (M : CalibrationModelC D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) := by
  obtain ⟨tp, hB, htp⟩ := Calibration.componentFields_of_reductions D.kfin.natAbs.primeFactors
    M.kres M.Wred M.h2 M.cB M.hEdix
  obtain ⟨hchi, hmne, hrmov, hBexp⟩ := Calibration.movingFields_of_nondiv (M.rmov : ℤ) M.amov
    M.chimov M.cE M.Bexp M.hchi M.hnd M.hrmov M.hcB
  obtain ⟨hodd, hN⟩ := moving_odd_and_norm_ne_zero M.hchi M.hrmov M.hnd M.hcB
  have hvprim := Calibration.hvprim_of_model_and_lengths M.DK M.X M.DW M.zK M.wK M.zP M.wP M.uK
    (D.uPrim Fam x) M.hz M.hw M.hP M.hKc M.hadj (D.jrc (Fam.h x) D.kfin) vL
    ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) ((padicValNat 2 M.tA : ℕ) : ℤ)
    ((padicValNat 2 M.shaA : ℕ) : ℤ) M.hK M.Fmov M.rmov hodd M.amov M.chimov M.hchi M.hFtr
    M.hFdet hN (omega (Fam.h x)) M.hcentralW
  exact ⟨{
    shaA := M.shaA
    shaB := M.shaB
    tA := M.tA
    tB := M.tB
    shaA_ne := M.shaA_ne
    shaB_ne := M.shaB_ne
    tA_ne := M.tA_ne
    tB_ne := M.tB_ne
    Scomp := M.Scomp
    cA := M.cA
    cB := M.cB
    tp := tp
    hTS := M.hTS
    hcpos := M.hcpos
    hcancel := M.hcancel
    hA1 := M.hA1
    hB := hB
    htp := htp
    K := M.K
    quad := M.quad
    aPull := M.aPull
    bPull := M.bPull
    hab := M.hab
    gam := M.gam
    kap := M.kap
    hgam := M.hgam
    hkap := M.hkap
    OmA := M.OmA
    hOmA := M.hOmA
    rhoOm := M.rhoOm
    hcv := M.hcv
    hmilne := M.hmilne
    hsB := M.hsB
    hgB := M.hgB
    rmov := (M.rmov : ℤ)
    amov := M.amov
    chimov := M.chimov
    Bexp := M.Bexp
    hchi := hchi
    hmne := hmne
    hrmov := hrmov
    hBexp := hBexp
    hvprim := hvprim }⟩

/-- **The remaining inputs of `RCSteps.calibration`, with the local lengths and the moving fields
discharged** ((4.6), tex 3987–4141): as `CalibrationInputs`, with `CalibrationModelC` at every
address. -/
def CalibrationInputsC {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelC D vL G₀ F x)

/-- `CalibrationInputsP` from `CalibrationInputsC` (PROVED). -/
theorem calibrationInputsP_of_C {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsC D) :
    CalibrationInputsP D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelP

/-- `CalibrationInputs` from `CalibrationInputsC` and the prints (PROVED). -/
theorem calibrationInputs_of_C {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsC D) : CalibrationInputs D :=
  calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_C h)

/-- **`RCSteps.calibration` from `CalibrationInputsC`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5` of lane RC15's `calibration_46`. PROVED. -/
theorem calibrationTarget_of_C {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsC D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_C Pr hℓ h)

end ZInQ.Manuscript.RC.Wiring
