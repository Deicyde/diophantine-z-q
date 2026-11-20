import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.LocalOrders
import ZInQKernel.Contrib.RC53Assist.Calibration.KummerIntegral

/-!
The HKL2 calibration with the three length fields derived by local duality
(tex 4032–4036, 4066–4080). This consumer leaves the existing leaf wiring untouched.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open NumberField IsDedekindDomain CategoryTheory Matrix
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- The genuine length block model with local Galois action at the two moving places and the
active places in place of the three eventual cardinality fields. -/
structure GenuineLengthBlockModelP (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {κ : Type} [Fintype κ] [DecidableEq κ] (DW : Matrix κ κ (PowerSeries ℚ_[2]))
    (rmov : ℕ) (amov chimov : ℤ) (ω : ℕ) : Type 1 where
  [ellE : E₀.IsElliptic]
  /-- the finite set of places of the Selmer complexes -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- the curve `E` over `K` -/
  W : WeierstrassCurve K
  [ellW : W.IsElliptic]
  /-- it is the base change of the fixed curve -/
  hW : W = E₀.baseChange K
  /-- a square root of `h` in `K_S` (it defines `χ_h`) -/
  s : KS K S
  /-- `s² = h` -/
  hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)
  /-- `s ≠ 0` -/
  hs0 : s ≠ 0
  /-- `E[2^i] ⊂ E(K_S)` at every precision -/
  hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)
  /-- the first place above the moving prime -/
  wmov : Places K S
  /-- the second place above the moving prime -/
  wmov' : Places K S
  /-- the places above the active primes -/
  act : Fin (2 * ω) → Places K S
  /-- the first place lies above the moving prime -/
  hwmov : (rmov : 𝓞 K) ∈ wmov.1.asIdeal
  /-- the second place lies above the moving prime -/
  hwmov' : (rmov : 𝓞 K) ∈ wmov'.1.asIdeal
  /-- the two places above the split moving prime are distinct -/
  hwne : wmov ≠ wmov'
  /-- the active places are distinct -/
  hact_inj : Function.Injective act
  /-- every active place lies above a prime dividing `h` -/
  hact_above : ∀ a, ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ hZ ∧ (p : 𝓞 K) ∈ (act a).1.asIdeal
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the local places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ (Fin 2 × Fin (2 * ω))
  /-- the integral central local block at the first place above the moving prime -/
  Bmov : Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- the integral central local block at the second place above the moving prime -/
  Bmov' : Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- the integral central local blocks at the active places -/
  Bact : Fin (2 * ω) → Matrix (Fin 2) (Fin 2) ℤ_[2]
  /-- at the centre the quotient block is the block sum of the local blocks, up to the changes of
  basis -/
  hcentral : DW.map central = PW.map central *
    ((fromBlocks (fromBlocks Bmov 0 0 Bmov') 0 0 (Matrix.blockDiagonal Bact)).map
      PadicInt.Coe.ringHom).submatrix eW eW * QW.map central
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the first moving block presents the quotient at the first place above `r` -/
  presMov : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) wmov s hs hs0 (hFull i)
    (isLocallyQuadAt_centralChar i s hs hs0 wmov.1) Bmov
  /-- the second moving block presents the quotient at the second place above `r` -/
  presMov' : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) wmov' s hs hs0 (hFull i)
    (isLocallyQuadAt_centralChar i s hs hs0 wmov'.1) Bmov'
  /-- each active block presents the quotient at its active place -/
  presAct : ∀ (i : ℕ) (a : Fin (2 * ω)), PresentsLocalQuotient W i (centralChar i s hs hs0) (act a)
    s hs hs0 (hFull i) (isLocallyQuadAt_centralChar i s hs hs0 (act a).1) (Bact a)
  /-- The local action at the first moving place. -/
  movAction : MovingLocalAction E₀ s hs hs0 wmov rmov amov chimov
  /-- The local action at the other moving place. -/
  movAction' : MovingLocalAction E₀ s hs hs0 wmov' rmov amov chimov
  /-- The local action at each active place. -/
  actAction : ∀ a, ActiveLocalAction (E₀.baseChange K) s hs hs0 (act a)

attribute [instance] GenuineLengthBlockModelP.ellW

/-- Derive the three original length fields from the local actions using finite local duality. -/
def GenuineLengthBlockModelP.toLengthModel {K : Type} [Field K] [NumberField K]
    {E : WeierstrassCurve ℚ} {hZ : ℤ} {κ : Type} [Fintype κ] [DecidableEq κ]
    {DW : Matrix κ κ (PowerSeries ℚ_[2])} {r : ℕ} {a χ : ℤ} {ω : ℕ}
    (G : GenuineLengthBlockModelP K E hZ DW r a χ ω) (hM : MilneLocalDualityOrder)
    (hχ : χ = 1 ∨ χ = -1) (hN : (r : ℤ) + 1 - χ * a ≠ 0)
    (hRat : ∀ (g : GKS K G.S) (P : TorsS K G.S (E.baseChange K) (2 : ℤ)), g • P = P) :
    GenuineLengthBlockModel K E hZ DW r (padicValInt 2 ((r : ℤ) + 1 - χ * a)) ω := by
  letI : E.IsElliptic := G.ellE
  letI : G.W.IsElliptic := G.ellW
  have hFull (i : ℕ) : FullTorsion K G.S (E.baseChange K) (2 ^ i) := by
    simpa only [G.hW] using G.hFull i
  have moving (v : Places K G.S) (H : MovingLocalAction E G.s G.hs G.hs0 v r a χ) :
      ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (locH G.W i (centralChar i G.s G.hs G.hs0) v 2) =
        2 ^ (padicValInt 2 ((r : ℤ) + 1 - χ * a) * i) := by
    apply length_H2_of_H0 hM G.hFull v
    refine ⟨max 1 (padicValInt 2 ((r : ℤ) + 1 - χ * a)), fun i hi => ?_⟩
    simpa only [G.hW] using card_locH0_moving H hχ hN i (by omega)
      ((le_max_right _ _).trans hi) (hFull i)
  refine { G with
    lenMov := moving G.wmov G.movAction
    lenMov' := moving G.wmov' G.movAction'
    lenAct := ?_ }
  intro b
  apply length_H2_of_H0 hM G.hFull (G.act b)
  refine ⟨1, fun i hi => ?_⟩
  simpa only [G.hW] using card_locH0_active (G.act b) (G.actAction b) hRat i (by omega) (hFull i)

/-- HKL2 with the arithmetic local actions in place of the local quotient orders. -/
structure CalibrationModelHKL2P {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- **the Kummer block with the disk lengths read from the genuine Selmer complexes**; it
  replaces the field `hK`, which is derived -/
  kummer : KummerCoordinateBlockG K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
    (amov - 2 * chimov) tA shaA
  /-- The genuine local blocks, with local actions supplying the three length fields. -/
  blocks : GenuineLengthBlockModelP K (Ecurve ℓ) (Fam.h x) DW rmov amov chimov (omega (Fam.h x))
  /-- **the moving prime tied to the curve**: prime, good, with the actual Frobenius trace and
  quadratic Frobenius sign -/
  moving : MovingPrimeData ℓ (Fam.h x) rmov amov chimov

attribute [instance] CalibrationModelHKL2P.fieldK CalibrationModelHKL2P.nfK
  CalibrationModelHKL2P.decK CalibrationModelHKL2P.quadK CalibrationModelHKL2P.fκ
  CalibrationModelHKL2P.dκ

/-- The original calibration model after deriving the three local lengths. -/
def CalibrationModelHKL2P.toHKL2 {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ}
    {Fam : Family} {x : Addr Fam.b} (M : CalibrationModelHKL2P D vL G₀ Fam x)
    (hM : MilneLocalDualityOrder) : CalibrationModelHKL2 D vL G₀ Fam x := by
  have hN := (moving_odd_and_norm_ne_zero M.hchi M.hrmov M.hnd M.hcB).2
  exact { M with blocks := M.blocks.toLengthModel hM M.hchi hN ecurve_torsTwo_fixed }

/-- The HKL2P input family, at the same addresses and ranks as HKL2. -/
def CalibrationInputsHKL2P {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHKL2P D vL G₀ F x)

/-- HKL2P supplies HKL2 uniformly, by the printed local duality statement. -/
theorem calibrationInputsHKL2_of_HKL2P {ℓ : ℕ} {D : RCData ℓ} (hM : MilneLocalDualityOrder)
    (h : CalibrationInputsHKL2P D) : CalibrationInputsHKL2 D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  exact ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => (H Co Ce F hF x h1 h0).map (·.toHKL2 hM)⟩

/-- The original calibration target from the local-action version and Milne's local duality. -/
theorem calibrationTarget_of_HKL2P {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (hM : MilneLocalDualityOrder) (h : CalibrationInputsHKL2P D) : CalibrationTarget D :=
  calibrationTarget_of_inputs
    (calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_HKL2 (calibrationInputsHKL2_of_HKL2P hM h)))

end ZInQ.Contrib.RC53Assist.Calibration
