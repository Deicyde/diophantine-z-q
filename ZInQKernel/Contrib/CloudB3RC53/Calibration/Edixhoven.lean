import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf2

/-!
# Calibration: the Edixhoven component field over the actual objects (repair of
CommonCoordinate-v2 review item 7)

Manuscript `diophantine_zq.tex`, tex 4116–4138: "At `p ∣ k`, put `E₀ = E^{(h)}`; it has good
reduction, and `K_p/ℚ_p` is a tame ramified quadratic extension. By [Edixhoven, Theorem 5.3 and
Remark 5.4.1, pp. 299–300], the component group of the ramified twist is the fixed subgroup of the
good special fiber under its descent action `[−1]`: `Φ(E₀^{(k)}) ≃ Ẽ₀[2]` … its rational component
number is `#E[2]^{Fr_p}`."

`componentFields_of_reductions` (`Calibration/Bookkeeping.lean`) assumed `c_p(ℬ) = #W(k)[2]` for
arbitrary fields `k`, curves `W` and numbers. Here:

* `GoodModelAt E p`: a genuine good integral model of `E/ℚ` at `p` (a Weierstrass curve over `ℤ`
  mapping to `E`, with `p ∤ Δ`); `GoodModelAt.red`: its reduction over `𝔽_p = ZMod p`, elliptic
  (`isElliptic_red`). Non-vacuity of the model itself (LESSON 2): `goodModelE0`, the model
  `y² = x³ + 2hℓ x² − 3h²ℓ² x` of `E₀ = E^{(h)}` (`Δ = 2⁸3²h⁶ℓ⁶`) at every `p ∤ 6hℓ`.
* `EdixhovenComponentNumber ℓ h k cB` — **PRINT (Edixhoven Thm 5.3, Rem 5.4.1) as GLUE**, stated
  over the actual objects with the print's hypotheses in the type: for an odd prime `p` with
  `p ∥ k` (so `ℚ_p(√k)/ℚ_p` is tame ramified quadratic) and a good integral model of
  `E₀ = E^{(h)}` at `p`, the component number `cB p` of `ℬ` (RC0's field: `c_p(E^{(h)}) ·
  c_p(E^{(hk)})`, the first factor being `1` at good reduction) is `#Ẽ₀(𝔽_p)[2]`. Néron models
  and component groups are not in the library, so `cB` stays RC0's number field.
* `componentFields_of_edixhoven`: RC0's fields `hB`, `htp` (`c_p(ℬ) = 2^{t_p}`, `t_p ≤ 2`) from the
  print over those objects. PROVED.
* `CalibrationModelG`, `CalibrationInputsG`, `calibrationTarget_of_G`: RC0's calibration leaf
  (`CalibrationModelC`, `calibrationTarget_of_C`) with the free `kres`/`Wred`/`h2`/`hEdix`
  replaced by the actual objects and the print. PROVED from the remaining fields.

Kinds: `EdixhovenComponentNumber` PRINT/GLUE (hypothesis); the rest PROVED. Because `GoodModelAt`
requires the integral model to map to `E₀` literally, the print is silent where the given
coefficients of `E₀` are not `p`-good (for instance `p = 3`, `3² ∣ Δ(E0Z)`); the model-free form
`EdixhovenComponentNumberIso` and the model independence of the count
(`card_twoTorsion_red_eq_of_iso`) are in `EdixhovenModel.lean`, a concrete instance in
`EdixhovenWitness.lean`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Calibration

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine Matrix
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **A good integral model of `E/ℚ` at `p`**: a Weierstrass curve over `ℤ` whose base change to
`ℚ` is `E` and whose discriminant is prime to `p`. -/
structure GoodModelAt (E : WeierstrassCurve ℚ) (p : ℕ) where
  /-- the integral model -/
  W : WeierstrassCurve ℤ
  /-- it is a model of `E` -/
  hmap : W.map (Int.castRingHom ℚ) = E
  /-- good reduction at `p` -/
  hgood : ¬ (p : ℤ) ∣ W.Δ

/-- The reduction `Ẽ` of a good integral model over `𝔽_p = ZMod p`. -/
def GoodModelAt.red {E : WeierstrassCurve ℚ} {p : ℕ} (M : GoodModelAt E p) :
    WeierstrassCurve (ZMod p) :=
  M.W.map (Int.castRingHom (ZMod p))

/-- The reduction of a good model is an elliptic curve over `𝔽_p`. -/
theorem isElliptic_red {E : WeierstrassCurve ℚ} {p : ℕ} [Fact p.Prime] (M : GoodModelAt E p) :
    M.red.IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [GoodModelAt.red, map_Δ, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact M.hgood

/-- The integral model `y² = x³ + 2hℓ x² − 3h²ℓ² x` of `E₀ = E^{(h)}`. -/
def E0Z (ℓ : ℕ) (h : ℤ) : WeierstrassCurve ℤ := ⟨0, 2 * h * ℓ, 0, -3 * h ^ 2 * ℓ ^ 2, 0⟩

theorem E0Z_map (ℓ : ℕ) (h : ℤ) : (E0Z ℓ h).map (Int.castRingHom ℚ) = qtwist (Ecurve ℓ) (h : ℚ) := by
  ext <;> simp [E0Z, qtwist, Ecurve, ZInQ.Manuscript.curve, b₂, b₄, b₆] <;> ring

theorem E0Z_Δ (ℓ : ℕ) (h : ℤ) : (E0Z ℓ h).Δ = 2 ^ 8 * 3 ^ 2 * h ^ 6 * (ℓ : ℤ) ^ 6 := by
  simp [E0Z, Δ, b₂, b₄, b₆, b₈]; ring

/-- **Non-vacuity of `GoodModelAt` (LESSON 2)**: `E₀ = E^{(h)}` has a good integral model at
every prime `p ∤ 6hℓ`. -/
def goodModelE0 (ℓ : ℕ) (h : ℤ) {p : ℕ} (hp : p.Prime) (hp6 : ¬ (p : ℤ) ∣ 6 * h * ℓ) :
    GoodModelAt (qtwist (Ecurve ℓ) (h : ℚ)) p where
  W := E0Z ℓ h
  hmap := E0Z_map ℓ h
  hgood := by
    intro hd
    rw [E0Z_Δ] at hd
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    apply hp6
    have h6 : (2 : ℤ) ^ 8 * 3 ^ 2 * h ^ 6 * (ℓ : ℤ) ^ 6 = 2 ^ 7 * 3 * (6 * h * ℓ) * (h ^ 5 * ℓ ^ 5) := by
      ring
    rw [h6] at hd
    rcases hpp.dvd_or_dvd hd with hd | hd
    · rcases hpp.dvd_or_dvd hd with hd | hd
      · rcases hpp.dvd_or_dvd hd with hd | hd
        · exact (hpp.dvd_of_dvd_pow hd).trans ⟨3 * h * ℓ, by ring⟩
        · exact hd.trans ⟨2 * h * ℓ, by ring⟩
      · exact hd
    · rcases hpp.dvd_or_dvd hd with hd | hd
      · exact (hpp.dvd_of_dvd_pow hd).trans ⟨6 * ℓ, by ring⟩
      · exact (hpp.dvd_of_dvd_pow hd).trans ⟨6 * h, by ring⟩

/-- **PRINT — Edixhoven, *Néron models and tame ramification*, Theorem 5.3 and Remark 5.4.1,
pp. 299–300, as cited at tex 4119–4127; GLUE (component groups of Néron models are not in the
library).** For the fixed curve `E₀ = E^{(h)}` and the companion `k`: at an odd prime `p` with
`p ∥ k` (so `ℚ_p(√k)/ℚ_p` is a tame ramified quadratic extension) where `E₀` has a good integral
model, the component group of the ramified twist `E₀^{(k)} = E^{(hk)}` is `Ẽ₀[2]`, so the component
number `cB p` of `ℬ = E^{(h)} × E^{(hk)}` (the first factor contributing `1` at good reduction) is
`#Ẽ₀(𝔽_p)[2]`, the rational two-torsion of the reduction of that model. The model-free form is
`EdixhovenComponentNumberIso` (`EdixhovenModel.lean`). -/
def EdixhovenComponentNumber (ℓ : ℕ) (h : ℚ) (k : ℤ) (cB : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime, p ≠ 2 → (p : ℤ) ∣ k → ¬ ((p : ℤ) ^ 2 ∣ k) →
    ∀ M : GoodModelAt (qtwist (Ecurve ℓ) h) p,
      letI := Fact.mk hp
      letI := isElliptic_red M
      cB p = Nat.card (AddSubgroup.torsionBy M.red.toAffine.Point (2 : ℕ))

/-- **RC0's component fields `hB`, `htp` from the Edixhoven print over the actual objects**
(tex 4116–4138): `c_p(ℬ) = 2^{t_p}` with `t_p ≤ 2` at every companion prime. PROVED. -/
theorem componentFields_of_edixhoven {ℓ : ℕ} {h : ℚ} {k : ℤ} {cB : ℕ → ℕ}
    (hE : EdixhovenComponentNumber ℓ h k cB) (hodd : ∀ p ∈ k.natAbs.primeFactors, p ≠ 2)
    (hram : ∀ p ∈ k.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ k))
    (models : ∀ p ∈ k.natAbs.primeFactors, GoodModelAt (qtwist (Ecurve ℓ) h) p) :
    ∃ tp : ℕ → ℕ, (∀ p ∈ k.natAbs.primeFactors, cB p = 2 ^ tp p) ∧
      (∀ p ∈ k.natAbs.primeFactors, tp p ≤ 2) := by
  classical
  have key : ∀ p, ∃ t : ℕ, p ∈ k.natAbs.primeFactors → (t ≤ 2 ∧ cB p = 2 ^ t) := by
    intro p
    by_cases hp : p ∈ k.natAbs.primeFactors
    · have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hdvd : (p : ℤ) ∣ k := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)
      have := Fact.mk hpr
      have := isElliptic_red (models p hp)
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

/-- **The inputs of (4.6) at one address, with the component fields over the actual objects**
(Proposition `ex:arith-central-calibration`, tex 3987–4141). As `CalibrationModelC`
(`RC/Wiring/CalibrationLeaf2.lean`), except that its designated residue fields `kres`, curves
`Wred`, oddness `h2` and the Edixhoven field `hEdix` (over arbitrary fields and curves) are replaced
by: the companion primes are odd (`hodd`) and exactly divide `k` (`hram`), `E₀ = E^{(h_x)}` has a
good integral model at each of them (`goodModel`), and the print `EdixhovenComponentNumber` over
those objects (`hEdix`). -/
structure CalibrationModelG {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- the companion primes are ramified in `K = ℚ(√k)`: `p ∥ k` (so `K_p/ℚ_p` is a tame ramified
  quadratic extension, `p` being odd) -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime: a designated integral model
  with discriminant prime to `p` (tex 4116–4117) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelAt (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, over the actual objects: the
  component number of `ℬ` at a companion prime is `#Ẽ₀(𝔽_p)[2]` -/
  hEdix : EdixhovenComponentNumber ℓ (Fam.h x : ℚ) D.kfin cB
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

attribute [instance] CalibrationModelG.fieldK CalibrationModelG.nfK CalibrationModelG.decK CalibrationModelG.quadK
  CalibrationModelG.fκ CalibrationModelG.dκ


/-- **`CalibrationModelP` from `CalibrationModelG`** (tex 4051–4080, 4066–4074, 4116–4138): as
`CalibrationModelC.nonempty_modelP`, with `t_p` from `componentFields_of_edixhoven`. PROVED. -/
theorem CalibrationModelG.nonempty_modelP {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
    {x : Addr Fam.b} (M : CalibrationModelG D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) := by
  obtain ⟨tp, hB, htp⟩ := componentFields_of_edixhoven M.hEdix M.hodd M.hram M.goodModel
  obtain ⟨hchi, hmne, hrmov, hBexp⟩ := movingFields_of_nondiv (M.rmov : ℤ) M.amov
    M.chimov M.cE M.Bexp M.hchi M.hnd M.hrmov M.hcB
  obtain ⟨hodd, hN⟩ := moving_odd_and_norm_ne_zero M.hchi M.hrmov M.hnd M.hcB
  have hvprim := hvprim_of_model_and_lengths M.DK M.X M.DW M.zK M.wK M.zP M.wP M.uK
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
discharged** ((4.6), tex 3987–4141): as `CalibrationInputs`, with `CalibrationModelG` at every

address. -/
def CalibrationInputsG {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelG D vL G₀ F x)

/-- `CalibrationInputsP` from `CalibrationInputsG` (PROVED). -/
theorem calibrationInputsP_of_G {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsG D) :
    CalibrationInputsP D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelP

/-- `CalibrationInputs` from `CalibrationInputsG` and the prints (PROVED). -/
theorem calibrationInputs_of_G {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsG D) : CalibrationInputs D :=
  calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_G h)

/-- **`RCSteps.calibration` from `CalibrationInputsG`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5` of lane RC15's `calibration_46`. PROVED. -/
theorem calibrationTarget_of_G {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsG D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_G Pr hℓ h)


end ZInQ.Contrib.CloudB3RC53.Calibration
