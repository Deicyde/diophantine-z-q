import ZInQKernel.Contrib.OneProof.RC.Wiring.Central
import ZInQKernel.Contrib.OneProof.RC.Height.Discharge
import ZInQKernel.Contrib.OneProof.RC.Height.FreeQuotientIndex

/-!
**Theorem 5.3, Lane RC0 round 3: the regulator inputs of (4.6) from lane RC19**

`CalibrationModel` (`Wiring/Central.lean`, Proposition `ex:arith-central-calibration`, tex
3987–4141) takes the isogeny and regulator data of the proof as abstract numbers:

* `alpha`, `beta`, `hIJ : alpha * beta = 2` (the dual isogeny indices, tex 4082–4090, ELLIOT);
* `RegA`, `RegB : ℝ` (the real regulators of `𝒜` and `ℬ`) and
  `hadj : alpha * RegB = beta * RegA` (the height adjunction read on generators, tex 4022–4025,
  4082–4090, GLUE);
* `hRegA : RegA ≠ 0`, and `hmilne` stated with the regulators `RegA` and `RegB`.

Lane RC19 (`RC/Height/SumDifference.lean`, `RC/Height/Discharge.lean`) constructs the
sum/difference isogenies `φ = diffMap : 𝒜(ℚ) → ℬ(ℚ)`, `ψ = sumMap : ℬ(ℚ) → 𝒜(ℚ)` between
`𝒜(ℚ) = E^{(h)}(K)` and `ℬ(ℚ) = E^{(h)}(ℚ) × E^{(hk)}(ℚ)` (`K = ℚ(√k)`), proves `ψφ = [2]`,
`φψ = [2]` and their adjunction for the canonical height pairings, and derives
(`regulator_inputs_sumDiff`), from free generators `g_𝒜`, `g_ℬ` of the two rank-one Mordell–Weil
lattices, integers `α, β` with `φ g_𝒜 ≡ α g_ℬ`, `ψ g_ℬ ≡ β g_𝒜` modulo torsion, `αβ = 2`, the
adjunction `α ĥ_ℬ(g_ℬ) = β ĥ_𝒜(g_𝒜)`, `ĥ_ℬ(g_ℬ) = (2/α²) ĥ_𝒜(g_𝒜)`, `v₂(2/α²) = ±1` and
`ĥ_𝒜(g_𝒜) > 0`.

This file replaces the seven fields `alpha`, `beta`, `hIJ`, `RegA`, `RegB`, `hadj`, `hRegA` of
`CalibrationModel` by the quadratic field `K = ℚ(√k)` with its datum, the two free generators and
their freeness (`CalibrationModelR`; the two twists are elliptic for `ℓ > 0`, `h_x ≠ 0`, `k ≠ 0`
by `ellA_of`, `ellB_of`, so no field is needed for that), and states the Milne field with the
**genuine** canonical regulators `Reg_𝒜 = ĥ_𝒜(g_𝒜)`, `Reg_ℬ = ĥ_ℬ(g_ℬ)`. All other fields are
those of `CalibrationModel`, verbatim. The free generators themselves are derived from the
forward theorems in `CalibrationPrints.lean` (`CalibrationModelP`).

* `CalibrationModelR.nonempty_model_index` (PROVED): a `CalibrationModel` with `alpha = I` and
  `beta = J`, the cardinalities of the actual cokernels of `φ` and `ψ` on the quotients of the
  point groups by their full torsion (`Height/FreeQuotientIndex.lean`: `sumDifferenceI`,
  `sumDifferenceJ`, `freeCokernel_card`), as `alpha = |α|`, `beta = |β|`;
* `CalibrationModelR.nonempty_model : 0 < ℓ → h_x ≠ 0 → CalibrationModelR D vL G₀ F x →
  Nonempty (CalibrationModel …)` (PROVED: `α`, `β`, `IJ = 2`, the adjunction
  `α ĥ_ℬ(g_ℬ) = β ĥ_𝒜(g_𝒜)` and `Reg_𝒜 ≠ 0` by lane RC19; the genuine real regulators
  `Reg_𝒜 = ĥ_𝒜(g_𝒜)`, `Reg_ℬ = ĥ_ℬ(g_ℬ)` are the fields `RegA`, `RegB` of `CalibrationModel`
  directly, and the rational ratio `2/α²` is derived downstream by lane RC15's
  `regulator_eq_ratCast_mul`);
* `calibrationInputs_of_R : 0 < ℓ → CalibrationInputsR D → CalibrationInputs D` (PROVED);
* `calibrationTarget_of_R : 0 < ℓ → CalibrationInputsR D → CalibrationTarget D` (PROVED, with lane
  RC15's `calibration_46` through `calibrationTarget_of_inputs`).

Lane RC19's other results: `BaseChange`, `Isomorphism`, `Transfer`, `Torsion` enter through
`regulator_inputs_sumDiff`; `IndexTwo.lean` is the index-two step of (3.4) (tex 2433–2435), and
its descent lemma `conj_sub_isOfFinAddOrder_of_twist_torsion` is used in
`CalibrationPrints.lean` to produce `g_𝒜`; `TwoIsogeny.lean`, `Rational.lean` (functoriality for
the 2-isogenies of `E_ℓ` and for maps given by a rational function) are not used in
tex 3987–4141.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open WeierstrassCurve WeierstrassCurve.Affine

attribute [local instance] Nat.fact_prime_two

/-- **The remaining inputs of (4.6) at one address, with lane RC19's regulator data**
(Proposition `ex:arith-central-calibration`, tex 3987–4141), for `𝒜 = Res_{K/ℚ}(E^{(h_x)}_K)`,
`ℬ = E^{(h_x)} × E^{(h_x k)}`, `K = ℚ(√k)`, at a known simple zero `h_x` of the final family.
The fields of `CalibrationModel` not listed below are unchanged (same names, statements, tex lines,
kinds and owners as there).

| field | content | tex | kind | owner |
|---|---|---|---|---|
| `K`, `quad` | `K = ℚ(√k)`: a quadratic number field with a square root of `k` and the automorphism `√k ↦ −√k` (lane RC19's `QuadData`) | 3988, 4053 | definition | RC15 / RC19 |
| `gA`, `freeA` | a free generator of `𝒜(ℚ) = E^{(h_x)}(K)` modulo torsion (rank one) | 4020–4021, 4050–4052; `lem:forward-rank` 1086–1090 | PRINT (BCDT Thm A) + GLUE (Kolyvagin Thm 1) + Mordell–Weil | RC9 / RC19 |
| `gB`, `freeB` | a free generator of `ℬ(ℚ) = E^{(h_x)}(ℚ) × E^{(h_x k)}(ℚ)` modulo torsion (rank one) | 4020–4021, 4050–4052; 1086–1090 | PRINT (BCDT Thm A) + GLUE (Kolyvagin Thm 1) + Mordell–Weil | RC9 / RC19 |
| `hmilne` | Cassels' isogeny invariance in Milne's form, with the canonical regulators `Reg_𝒜 = ĥ_𝒜(g_𝒜)` (the height of `E^{(h_x)}` relative to `K`) and `Reg_ℬ = ĥ_ℬ(g_ℬ)` (the sum of the two heights over `ℚ`), and self-dual torsion counts; as a leaf field it constrains only free parameters (`shaA`, `tA`, `tB`, `C_𝒜`, `C_ℬ`, `Ω_𝒜`, `ρ_Ω`): with RC19's height relation it holds for every choice of the other data, and its effect is to define `v₂ shaA − 2v₂ tA` | 4027–4030, 4106–4113 | PRINT (Milne ADT I.7.3, (7.3.1)) + GLUE (RC19's pairings are the canonical height pairings of `𝒜`, `ℬ` for their principal polarizations, `SumDifference.lean`) | RC15 / RC19 |

No longer fields (PROVED by lane RC19's `regulator_inputs_sumDiff`, see
`CalibrationModelR.nonempty_model`): the indices `α, β` with `αβ = 2` (tex 4082–4090), the
regulators `Reg_𝒜 = ĥ_𝒜(g_𝒜)`, `Reg_ℬ = ĥ_ℬ(g_ℬ)` with the adjunction `α Reg_ℬ = β Reg_𝒜`
(tex 4022–4025, 4082–4090), and `Reg_𝒜 ≠ 0`. -/
structure CalibrationModelR {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : ZInQ.Manuscript.RC.Height.QuadData K (D.kfin : ℚ)
  /-- a generator of `𝒜(ℚ) = E^{(h_x)}(K)` modulo torsion -/
  gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point
  /-- a generator of `ℬ(ℚ) = E^{(h_x)}(ℚ) × E^{(h_x k)}(ℚ)` modulo torsion -/
  gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
    ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point
  /-- `𝒜(ℚ)` has rank one, generated by `g_𝒜` modulo torsion -/
  freeA : ZInQ.Manuscript.RC.Height.IsFreeGenerator gA
  /-- `ℬ(ℚ)` has rank one, generated by `g_ℬ` modulo torsion -/
  freeB : ZInQ.Manuscript.RC.Height.IsFreeGenerator gB
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
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators
  `Reg_𝒜 = ĥ_𝒜(g_𝒜)` and `Reg_ℬ = ĥ_ℬ(g_ℬ)` -/
  hmilne : Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
    (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
    (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
    ((rhoOm : ℝ) * OmA)
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

attribute [instance] CalibrationModelR.fieldK CalibrationModelR.nfK CalibrationModelR.decK
  CalibrationModelR.quadK

/-! Ellipticity of the two twists -/

/-- `E^{(h)}` is elliptic for `ℓ > 0` and `h ≠ 0` (PROVED). -/
theorem ellA_of {ℓ : ℕ} (hℓ : 0 < ℓ) {h : ℤ} (hh : h ≠ 0) :
    (qtwist (Ecurve ℓ) (h : ℚ)).IsElliptic :=
  Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_isElliptic' (by exact_mod_cast hℓ.ne'))
    (by exact_mod_cast hh)

/-- `E^{(hk)}` is elliptic for `ℓ > 0`, `h ≠ 0` and `k ≠ 0` (PROVED). -/
theorem ellB_of {ℓ : ℕ} (hℓ : 0 < ℓ) {h : ℤ} (hh : h ≠ 0) {k : ℚ} (hk : k ≠ 0) :
    (qtwist (Ecurve ℓ) ((h : ℚ) * k)).IsElliptic :=
  Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_isElliptic' (by exact_mod_cast hℓ.ne'))
    (mul_ne_zero (by exact_mod_cast hh) hk)

/-- A quadratic datum `QuadData K k` forces `k ≠ 0` (`s ≠ 0` and `s² = k`) (PROVED). -/
theorem QuadData.k_ne_zero {K : Type*} [Field K] [Algebra ℚ K] {k : ℚ}
    (Q : ZInQ.Manuscript.RC.Height.QuadData K k) : k ≠ 0 := by
  intro hk
  subst hk
  have h := Q.hsk
  rw [map_zero] at h
  exact Q.hs (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)

/-- **The regulator data of `CalibrationModel` from lane RC19, with the indices identified** (tex
4022–4025, 4082–4090, 4106–4112): a `CalibrationModelR` gives a `CalibrationModel` whose real
regulators are the genuine canonical heights `Reg_𝒜 = ĥ_𝒜(g_𝒜) > 0` and `Reg_ℬ = ĥ_ℬ(g_ℬ)`, with
`alpha = |α|`, `beta = |β|` for the integers `α, β` of `regulator_inputs_sumDiff` (`αβ = 2`, so
`α` and `β` have the same sign, and the height adjunction `α Reg_ℬ = β Reg_𝒜` passes to the
absolute values). Then `alpha = I` and `beta = J` are the cardinalities of the actual cokernels of
`φ = diffMap` and `ψ = sumMap` on the quotients of the point groups by their full torsion
(`FreeQuotientIndex.sumDifferenceI`, `sumDifferenceJ`, by `freeCokernel_card`): the labels of the
fields `alpha`, `beta` hold for the genuine twists. PROVED. -/
theorem CalibrationModelR.nonempty_model_index {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
    {x : Addr Fam.b} (M : CalibrationModelR D vL G₀ Fam x)
    [(qtwist (Ecurve ℓ) (Fam.h x : ℚ)).IsElliptic]
    [(qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).IsElliptic] :
    ∃ C : CalibrationModel D vL G₀ Fam x,
      C.alpha = (ZInQ.Manuscript.RC.Height.FreeQuotientIndex.sumDifferenceI (K := M.K)
        (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) M.quad : ℤ) ∧
      C.beta = (ZInQ.Manuscript.RC.Height.FreeQuotientIndex.sumDifferenceJ (K := M.K)
        (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) M.quad : ℤ) := by
  obtain ⟨α, β, hα, hβ, hαβ, hadj, -, -, -, hpos⟩ :=
    ZInQ.Manuscript.RC.Height.regulator_inputs_sumDiff (K := M.K) (Ecurve ℓ) (Fam.h x : ℚ)
      (D.kfin : ℚ) M.quad M.gA M.gB M.freeA M.freeB
  have hsign : (0 < α ∧ 0 < β) ∨ (α < 0 ∧ β < 0) := by
    rcases lt_trichotomy α 0 with ha | ha | ha
    · right
      refine ⟨ha, ?_⟩
      rcases lt_or_ge β 0 with hb | hb
      · exact hb
      · nlinarith
    · subst ha
      simp at hαβ
    · left
      refine ⟨ha, ?_⟩
      rcases lt_or_ge 0 β with hb | hb
      · exact hb
      · nlinarith
  refine ⟨{
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
    tp := M.tp
    hTS := M.hTS
    hcpos := M.hcpos
    hcancel := M.hcancel
    hA1 := M.hA1
    hB := M.hB
    htp := M.htp
    alpha := (α.natAbs : ℤ)
    beta := (β.natAbs : ℤ)
    hIJ := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, ← abs_mul, hαβ]
      rfl
    RegA := M.gA.canonicalHeight
    RegB := ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) M.gB
    hadj := by
      rcases hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [Int.natAbs_of_nonneg ha.le, Int.natAbs_of_nonneg hb.le]
        exact hadj
      · rw [Int.ofNat_natAbs_of_nonpos ha.le, Int.ofNat_natAbs_of_nonpos hb.le]
        simp only [Int.cast_neg, neg_mul, hadj]
    aPull := M.aPull
    bPull := M.bPull
    hab := M.hab
    gam := M.gam
    kap := M.kap
    hgam := M.hgam
    hkap := M.hkap
    OmA := M.OmA
    hRegA := hpos.ne'
    hOmA := M.hOmA
    rhoOm := M.rhoOm
    hcv := M.hcv
    hmilne := M.hmilne
    hsB := M.hsB
    hgB := M.hgB
    rmov := M.rmov
    amov := M.amov
    chimov := M.chimov
    Bexp := M.Bexp
    hchi := M.hchi
    hmne := M.hmne
    hrmov := M.hrmov
    hBexp := M.hBexp
    hvprim := M.hvprim }, ?_, ?_⟩
  · change (α.natAbs : ℤ) = _
    rw [ZInQ.Manuscript.RC.Height.FreeQuotientIndex.sumDifferenceI,
      ZInQ.Manuscript.RC.Height.FreeQuotientIndex.freeCokernel_card _ M.gA M.gB M.freeA M.freeB hα]
  · change (β.natAbs : ℤ) = _
    rw [ZInQ.Manuscript.RC.Height.FreeQuotientIndex.sumDifferenceJ,
      ZInQ.Manuscript.RC.Height.FreeQuotientIndex.freeCokernel_card _ M.gB M.gA M.freeB M.freeA hβ]

/-- **The regulator data of `CalibrationModel` from lane RC19** (tex 4022–4025, 4082–4090,
4106–4112): `CalibrationModelR.nonempty_model_index` with the two twists elliptic (`ℓ > 0`,
`h_x ≠ 0`, `k ≠ 0`). PROVED. -/
theorem CalibrationModelR.nonempty_model {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family}
    {x : Addr Fam.b} (hℓ : 0 < ℓ) (hx0 : Fam.h x ≠ 0) (M : CalibrationModelR D vL G₀ Fam x) :
    Nonempty (CalibrationModel D vL G₀ Fam x) := by
  have := ellA_of hℓ hx0
  have := ellB_of hℓ hx0 (QuadData.k_ne_zero M.quad)
  obtain ⟨C, -⟩ := M.nonempty_model_index
  exact ⟨C⟩

/-- **The remaining inputs of `RCSteps.calibration` with lane RC19's regulator data**
((4.6), tex 3987–4141): as `CalibrationInputs`, with `CalibrationModelR` (free generators of the
two Mordell–Weil lattices in place of the isogeny indices, the regulator ratio, the adjunction and
the regulator) at every address. -/
def CalibrationInputsR {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelR D vL G₀ F x)

/-- `CalibrationInputs` from `CalibrationInputsR` (PROVED). -/
theorem calibrationInputs_of_R {ℓ : ℕ} {D : RCData ℓ} (hℓ : 0 < ℓ) (h : CalibrationInputsR D) :
    CalibrationInputs D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_model hℓ (Family.h_ne_zero hF.1 x)

/-- **`RCSteps.calibration` from the RC19 form of the inputs** ((4.6), tex 3987–4141), with the
uniform error bound `C_cal = 2v₂L + 2G₀ + 5` of lane RC15's `calibration_46`. PROVED. -/
theorem calibrationTarget_of_R {ℓ : ℕ} {D : RCData ℓ} (hℓ : 0 < ℓ) (h : CalibrationInputsR D) :
    CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_R hℓ h)

end ZInQ.Manuscript.RC.Wiring
