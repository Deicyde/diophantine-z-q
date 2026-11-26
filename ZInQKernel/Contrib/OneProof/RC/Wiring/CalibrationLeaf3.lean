import ZInQKernel.Contrib.CloudB3RC53.Calibration.EdixhovenModel
import ZInQKernel.Contrib.CloudB3RC53.Calibration.CentralBlocks

/-!
**Theorem 5.3, Lane RC0 round 4: the calibration leaf over good models up to isomorphism and the
local quotient blocks**

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3987–4141). Round 3's leaf
`CalibrationInputsC` (`Wiring/CalibrationLeaf2.lean`) carried, at every address, designated residue
fields and curves with the Edixhoven count as a bare equation, and the central quotient block as a
literal determinant identity `hcentralW`. Batch 3 replaced the first by genuine objects
(`CalibrationModelG`, `Calibration/Edixhoven.lean`); its good model `GoodModelAt` must map to the
given Weierstrass equation of `E₀ = E^{(h_x)}` literally, so that field cannot be supplied at a
companion prime where `E₀` has good reduction but its given coefficients are not `p`-good.
This file states the leaf with

* **good models up to isomorphism** (`GoodModelIso`: an integral Weierstrass model of `E₀` up to a
  rational change of variables, discriminant prime to `p`; "it has good reduction", tex 4117) and
  the print in its model-free form `EdixhovenComponentNumberIso` (Edixhoven Thm 5.3, Rem. 5.4.1,
  tex 4119–4127). `componentFields_of_edixhovenIso` gives `c_p(ℬ) = 2^{t_p}`, `t_p ≤ 2` (PROVED;
  batch 3 proves the count model-independent, `card_twoTorsion_red_eq_of_iso`);
* **the central quotient block from its local blocks** (batch 3's
  `hvprim_of_model_and_local_blocks`, `Calibration/CentralBlocks.lean`), replacing `hcentralW`:
  the full/Kummer quotient block is, up to integral changes of basis whose determinants have central
  valuation `0`, the direct sum of the two-place singular block of (4.4) at the moving prime (central
  Frobenius `Fr_r` with trace `a_r` and determinant `r`, moving scalars with central value
  `χ_h(r) = ±1`) and the minimal model `2 · 1` of `E[2]` at the `2ω(h_x)` active places
  (tex 4066–4080). The valuation `2 v₂ N_r + 4ω` of the posited block is PROVED from it.

Results (PROVED, standard axioms):

* `CalibrationModelH.nonempty_modelP : CalibrationModelH D vL G₀ F x →
  Nonempty (CalibrationModelP D vL G₀ F x)`;
* `calibrationTarget_of_H : Prints → 0 < ℓ → CalibrationInputsH D → CalibrationTarget D`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.Calibration
open WeierstrassCurve WeierstrassCurve.Affine Matrix
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **RC0's component fields `hB`, `htp` from the Edixhoven print over good models up to
isomorphism** (tex 4116–4138): `c_p(ℬ) = 2^{t_p}` with `t_p ≤ 2` at every companion prime. As
batch 3's `componentFields_of_edixhoven`, with `GoodModelIso` and `EdixhovenComponentNumberIso`.
PROVED. -/
theorem componentFields_of_edixhovenIso {ℓ : ℕ} {h : ℚ} {k : ℤ} {cB : ℕ → ℕ}
    (hE : EdixhovenComponentNumberIso ℓ h k cB) (hodd : ∀ p ∈ k.natAbs.primeFactors, p ≠ 2)
    (hram : ∀ p ∈ k.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ k))
    (models : ∀ p ∈ k.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) h) p) :
    ∃ tp : ℕ → ℕ, (∀ p ∈ k.natAbs.primeFactors, cB p = 2 ^ tp p) ∧
      (∀ p ∈ k.natAbs.primeFactors, tp p ≤ 2) := by
  classical
  have key : ∀ p, ∃ t : ℕ, p ∈ k.natAbs.primeFactors → (t ≤ 2 ∧ cB p = 2 ^ t) := by
    intro p
    by_cases hp : p ∈ k.natAbs.primeFactors
    · have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : (p : ℤ) ∣ k := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
      have := Fact.mk hpr
      have := (models p hp).isElliptic_red
      have h2 : IsUnit (2 : ZMod p) := by
        refine isUnit_iff_ne_zero.mpr fun h0 => hodd p hp ?_
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp this)
      obtain ⟨t, ht, heq⟩ := card_twoTorsion_eq_two_pow (models p hp).red h2
      exact ⟨t, fun _ => ⟨ht, (hE p hpr (hodd p hp) hdvd (hram p hp) (models p hp)).trans heq⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose tp htp using key
  exact ⟨tp, fun p hp => (htp p hp).2, fun p hp => (htp p hp).1⟩

/-- **The remaining inputs of (4.6) at one address** (Proposition `ex:arith-central-calibration`,
tex 3987–4141). The fields not listed are those of batch 3's `CalibrationModelG` (the same as
`CalibrationModelC`, with the same names, tex lines, kinds and owners: the two-primary Ш and
torsion orders with `s_ℬ = s(h_x) + s(h_x k)` and the torsion bound, ELLIOT + GLUE Kolyvagin; the
component numbers with cancellation away from `k` and `c_p(𝒜) = 1` at `p ∣ k`; `K = ℚ(√k)`; the
pullbacks `ab = 4`, the real kernel and cokernel orders, the periods; Cassels–Milne at the canonical
regulators of any free generators, PRINT Milne ADT I.7.3 + GLUE; the moving prime in the output
form of RC17's moving character, ELLIOT; the triangular Kummer model with its class, functional,
coordinates and the Kummer valuation, ELLIOT). Changed fields:

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `hodd`, `hram` | the companion primes are odd and exactly divide `k` (`K_p/ℚ_p` tame ramified quadratic) | 4117–4118 | definition | RC15 / RC2 |
| `goodModel` | `E₀ = E^{(h_x)}` has good reduction at each companion prime: an integral Weierstrass model up to a rational change of variables with discriminant prime to `p` | 4116–4117 | ELLIOT ("it has good reduction") | RC15 / RC9 |
| `hEdix` | `EdixhovenComponentNumberIso`: at an odd `p ∥ k` and any good model up to isomorphism, `c_p(ℬ) = |Ẽ₀(𝔽_p)[2]|`; it fixes the free `cB p` at `p ∣ k` (`cBcanonical`); only `c_p(ℬ) ∈ {1,2,4}` is consumed | 4119–4127 | PRINT (Edixhoven Thm 5.3, Rem. 5.4.1) as GLUE | RC9 / batch 3 Calibration |
| `Fr`, `hFtr`, `hFdet` | the Frobenius at the moving prime over `ℚ₂[[t]]`; its central value has trace `a_r` and determinant `r` | 4066–4071 | definition | RC15 / RC17 |
| `PW`, `QW`, `hPW`, `hQW`, `eW`, `zmov`, `zmov'`, `Bact`, `hDW`, `hzmov`, `hzmov'`, `hact` | the quotient block `D_W` is `P_W · diag(twoPlaceBlock Fr r z z', B_act) · Q_W` up to relabelling, `v₂ det P_W(0) = v₂ det Q_W(0) = 0`, the moving scalars have central value `χ_h(r)` (the moving character is trivial at the centre), and the active block is the minimal model `2 · 1` of `E[2]` at the `2ω(h_x)` active places; all matrices are existential, not identified with Galois cochains; with `rmov … hK` the block is equivalent to `v₂ u_prim(0) = 2(j_rc + v₂L) + 2g_𝒜 − s_𝒜 − 4ω`; `r = 1`, `a_r = 3`, `χ = 1` is admissible | 4066–4080 | ELLIOT (the quotient complex is the direct sum of the local quotients; local conditions of `ex:arith-data`) | RC15 / batch 3 Calibration |

No longer fields compared with `CalibrationModelG`: `Fmov` (it is `Fr(0)`) and `hcentralW` (a
literal, basis-dependent determinant identity; its valuation is PROVED from the local blocks).

The orders, component numbers, moving prime and trace, and Kummer model
cochains are existential witnesses. The field hK retains the ordinary
Kummer determinant valuation of tex 4058–4064. The field cE is per-model,
a weaker requirement than a single Tate-image constant before the family. -/
structure CalibrationModelH {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- the central valuation of the Kummer coordinate -/
  hK : v2 (central uK) =
    ((((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      ((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (amov - 2 * chimov) : ℕ) : ℤ)) +
      (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
        Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
        Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ)
  /-- the Frobenius at the moving prime, over `ℚ₂[[t]]` -/
  Fr : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- its central value has trace `a_{r_i}` -/
  hFtr : (Fr.map central).trace = (amov : ℚ_[2])
  /-- its central value has determinant `r_i` -/
  hFdet : (Fr.map central).det = (rmov : ℚ_[2])
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the two moving places and the active places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * omega (Fam.h x))
  /-- the moving scalar at the first place above `r_i` -/
  zmov : PowerSeries ℚ_[2]
  /-- the moving scalar at the second place above `r_i` -/
  zmov' : PowerSeries ℚ_[2]
  /-- the block at the active places -/
  Bact : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) (PowerSeries ℚ_[2])
  /-- the quotient block is the direct sum of the local blocks, up to the changes of basis -/
  hDW : DW = PW * (fromBlocks (CommonCoordinate.twoPlaceBlock Fr (rmov : PowerSeries ℚ_[2]) zmov
    zmov') 0 0 Bact).submatrix eW eW * QW
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the moving character is trivial at the centre: the first scalar is `χ_h(r_i)` -/
  hzmov : central zmov = chimov
  /-- the second scalar is `χ_h(r_i)` at the centre -/
  hzmov' : central zmov' = chimov
  /-- the active block is the minimal model `2 · 1` of `E[2]` at the centre -/
  hact : Bact.map central =
    (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) ℚ_[2])

attribute [instance] CalibrationModelH.fieldK CalibrationModelH.nfK CalibrationModelH.decK
  CalibrationModelH.quadK CalibrationModelH.fκ CalibrationModelH.dκ

/-- **`CalibrationModelP` from `CalibrationModelH`** (tex 4051–4080, 4116–4138): `t_p` from
`componentFields_of_edixhovenIso`; the moving fields from batch 3's `movingFields_of_nondiv`;
`hvprim` from batch 3's `hvprim_of_model_and_local_blocks` (the support triangle from the model, the
quotient length `2 v₂N + 4ω` from the local blocks). PROVED. -/
theorem CalibrationModelH.nonempty_modelP {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
    {x : Addr Fam.b} (M : CalibrationModelH D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) := by
  obtain ⟨tp, hB, htp⟩ := componentFields_of_edixhovenIso M.hEdix M.hodd M.hram M.goodModel
  obtain ⟨hchi, hmne, hrmov, hBexp⟩ := movingFields_of_nondiv (M.rmov : ℤ) M.amov
    M.chimov M.cE M.Bexp M.hchi M.hnd M.hrmov M.hcB
  obtain ⟨hodd, hN⟩ := moving_odd_and_norm_ne_zero M.hchi M.hrmov M.hnd M.hcB
  have hvprim := hvprim_of_model_and_local_blocks M.DK M.X M.DW M.zK M.wK M.zP M.wP M.uK
    (D.uPrim Fam x) M.hz M.hw M.hP M.hKc M.hadj (D.jrc (Fam.h x) D.kfin) vL
    ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) ((padicValNat 2 M.tA : ℕ) : ℤ)
    ((padicValNat 2 M.shaA : ℕ) : ℤ) M.hK (omega (Fam.h x)) M.PW M.QW M.eW M.Fr M.rmov M.zmov
    M.zmov' M.Bact M.hDW M.hPW M.hQW (M.Fr.map central) hodd M.amov M.chimov M.hchi M.hFtr
    M.hFdet hN rfl M.hzmov M.hzmov' M.hact
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

/-- **The remaining inputs of `RCSteps.calibration`** ((4.6), tex 3987–4141): as
`CalibrationInputsC`, with `CalibrationModelH` at every address. -/
def CalibrationInputsH {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelH D vL G₀ F x)

/-- `CalibrationInputsP` from `CalibrationInputsH` (PROVED). -/
theorem calibrationInputsP_of_H {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsH D) :
    CalibrationInputsP D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelP

/-- `CalibrationInputs` from `CalibrationInputsH` and the prints (PROVED). -/
theorem calibrationInputs_of_H {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsH D) : CalibrationInputs D :=
  calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_H h)

/-- **`RCSteps.calibration` from `CalibrationInputsH`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5` of lane RC15's `calibration_46`. PROVED. -/
theorem calibrationTarget_of_H {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsH D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_H Pr hℓ h)

end ZInQ.Manuscript.RC.Wiring
