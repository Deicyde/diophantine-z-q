import ZInQKernel.Contrib.OneProof.CarayolDDTOdd

/-!
# carirr-refold: Carayol's leaf with the unramified clause in the manuscript's normalization

Task carirr-refold (2026-11-17), report `docs/research/carirr-refold.md`, scratch `scratch/carirr-refold/`.

The open field `carayolThmAIrr : CarayolPrinted.CarayolThmAIrr` has an **odd** clause
(`∃ c, c² = 1 ∧ det ρ(c) = -1`) that no print states in that form. carirr-odd replaced it by the global
determinant `det ρ = ψ·χ_ℓ` of Darmon–Diamond–Taylor 1997 Thm 3.1 (`CarayolDDT.CarayolDDT31`). The manuscript
cites Carayol 1986, Théorème (A), once (diophantine_zq.tex L9778-9796) and reads off from Carayol's
normalization the polynomial of **arithmetic Frobenius**: `X² − a_q X + q χ(q)` at good primes `q`. This file
states the leaf with exactly that per-Frobenius clause (trace `a_p`, determinant `p ψ(p)`) and proves:

* `odd_of_frobDet` (new): if `det ρ(Frob_p) = p` at every arithmetic Frobenius with `p ≡ -1 (mod N)`,
  `p ∤ Nℓ`, then complex conjugation `c` has `det ρ(c) = -1`. One Frobenius element near `c` (the kernel's
  Chebotarev density T18, `CarayolLevel.frobeniusDense_C9`) in the open subgroup cut out by `p ≡ -1 (mod N)`,
  `p ≡ -1 (mod ℓ^k)` and `‖det ρ − 1‖ < ‖2‖` forces `det ρ(c) ≠ 1`; with `det ρ(c)² = 1` this gives `-1`.
  No `ℓ`-adic cyclotomic character in `K_{f,λ}` and no embedding `ℤ_ℓ → K_{f,λ}` is needed.
* `CarayolThmAFrob` (the leaf), `carayolThmAIrr_of_frob : CarayolThmAFrob → CarayolPrinted.CarayolThmAIrr`.
* `frob_of_DDT31 : CarayolDDT.CarayolDDT31 → CarayolThmAFrob`: the new leaf is implied by carirr-odd's DDT
  form (so it is not stronger than DDT 3.1), via `χ_ℓ(Frob_p) = p`, `Frob_p mod N = p` (hodge-split's
  `cyc_arithFrob`, `arithFrob_pow_of_rootOfUnity`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace CarayolRefold

open PkgI4 LadicCond

/-! ## §1. The mod-`M` cyclotomic character: open kernel, value at Frobenius -/

/-- `ker (σ ↦ σ mod M)` is open in `G_ℚ`: it contains `Gal(ℚ̄/ℚ(ζ_M))`. -/
theorem isOpen_ker_cycN (M : ℕ) [NeZero M] : IsOpen ((CarayolDDT.cycN M).ker : Set GQ) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar M
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {ζ}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hK : K.fixingSubgroup ≤ (CarayolDDT.cycN M).ker := by
    intro σ hσ
    have hfix : σ ζ = ζ := hσ ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    refine (modularCyclotomicCharacter.unique Qbar (CarayolDDT.natCard_rootsOfUnity_Qbar M)
      (MulSemiringAction.toRingAut GQ Qbar σ) fun t ht => ?_).symm
    have htn : (t : Qbar) ^ M = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htn
    show σ (t : Qbar) = ((t ^ ((1 : (ZMod M)ˣ) : ZMod M).val : Qbarˣ) : Qbar)
    rw [← hi, map_pow, hfix, Units.val_pow_eq_pow_val, ← hi]
    by_cases hM1 : M = 1
    · subst hM1
      have : (t : Qbar) = 1 := by simpa using htn
      rw [hi, this, one_pow]
    · have : Fact (1 < M) := ⟨by have := NeZero.ne M; omega⟩
      rw [Units.val_one, ZMod.val_one, pow_one]
  exact Subgroup.isOpen_mono hK (IntermediateField.fixingSubgroup_isOpen K)

/-- An arithmetic Frobenius at `v ∣ p`, `p ∤ M`, has `σ mod M = p`. -/
theorem cycN_arithFrob {M : ℕ} [NeZero M] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpM : ¬ p ∣ M) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((CarayolDDT.cycN M σ : (ZMod M)ˣ) : ZMod M) = (p : ZMod M) := by
  refine (modularCyclotomicCharacter.unique Qbar (CarayolDDT.natCard_rootsOfUnity_Qbar M)
    (MulSemiringAction.toRingAut GQ Qbar σ) fun t ht => ?_).symm
  have htn : (t : Qbar) ^ M = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  show σ (t : Qbar) = ((t ^ ((p : ZMod M)).val : Qbarˣ) : Qbar)
  rw [ZInQ.Contrib.HodgeSplit.arithFrob_pow_of_rootOfUnity hp hv hσ (NeZero.ne M) htn hpM,
    Units.val_pow_eq_pow_val, ZMod.val_natCast,
    ← ZInQ.Contrib.HodgeSplit.pow_eq_pow_mod_of htn]

/-- An arithmetic Frobenius at `v ∣ p`, `p ≠ ℓ`, has `χ_ℓ(σ) = p`. -/
theorem cycL_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((CarayolDDT.cycL ℓ σ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
  have h := ZInQ.Contrib.HodgeSplit.cyc_arithFrob (ℓ := ℓ) hp hpl hv hσ
  have he : MulSemiringAction.toRingAut GQ Qbar σ = σ.toRingEquiv := RingEquiv.ext fun _ => rfl
  simp only [CarayolDDT.cycL, MonoidHom.coe_comp, Function.comp_apply, he]
  exact h

/-! ## §2. Oddness from the determinant at Frobenius elements -/

section Odd

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem norm_eq_one_of_near {x : E} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have := CarayolHerbrand.norm_eq_of_norm_sub_lt (a := x) (b := 1) (by rwa [norm_one])
  rwa [norm_one] at this

/-- `{σ : ‖d(σ) − 1‖ < r}` for a character `d : G_ℚ → Eˣ` and `0 < r ≤ 1`: a subgroup. -/
def nearOne (d : GQ →* Eˣ) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) : Subgroup GQ where
  carrier := {σ | ‖((d σ : Eˣ) : E) - 1‖ < r}
  one_mem' := by simp [hr0]
  mul_mem' := by
    intro a b ha hb
    change ‖_‖ < r at ha hb ⊢
    simp only [map_mul, Units.val_mul]
    have hna : ‖((d a : Eˣ) : E)‖ = 1 := norm_eq_one_of_near (lt_of_lt_of_le ha hr1)
    have e : ((d a : Eˣ) : E) * (d b : Eˣ) - 1 =
        ((d a : Eˣ) : E) * (((d b : Eˣ) : E) - 1) + (((d a : Eˣ) : E) - 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ha)
    rw [norm_mul, hna, one_mul]
    exact hb
  inv_mem' := by
    intro a ha
    change ‖_‖ < r at ha ⊢
    simp only [map_inv, Units.val_inv_eq_inv_val]
    have hna : ‖((d a : Eˣ) : E)‖ = 1 := norm_eq_one_of_near (lt_of_lt_of_le ha hr1)
    have h0 : ((d a : Eˣ) : E) ≠ 0 := (d a).ne_zero
    have e : ((d a : Eˣ) : E)⁻¹ - 1 = -((((d a : Eˣ) : E) - 1) * ((d a : Eˣ) : E)⁻¹) := by
      field_simp; ring
    rw [e, norm_neg, norm_mul, norm_inv, hna, inv_one, mul_one]
    exact ha

/-- **Odd from the determinant at Frobenius elements (GLUE, proved).** Let `E` be an ultrametric normed
field with `‖ℓ‖ < 1` and `2 ≠ 0`, and `ρ : G_ℚ → GL₂(E)` continuous with `det ρ(σ) = p` at every arithmetic
Frobenius `σ` above a prime `p ∤ Nℓ` with `σ mod N = -1`. Then some `c` with `c² = 1` (complex conjugation)
has `det ρ(c) = -1`. -/
theorem odd_of_frobDet {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ‖(ℓ : E)‖ < 1) (h2 : (2 : E) ≠ 0)
    {N : ℕ} [NeZero N] (ρ : GQ →* GL (Fin 2) E) (hρ : Continuous ρ)
    (hfrob : ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ (v : ValuationSubring Qbar) (σ : GQ),
      LiesOver v p → IsArithFrob σ v p → CarayolDDT.cycN N σ = -1 →
        (ρ σ : Matrix (Fin 2) (Fin 2) E).det = (p : E)) :
    ∃ c : GQ, c * c = 1 ∧ (ρ c : Matrix (Fin 2) (Fin 2) E).det = -1 := by
  obtain ⟨c, hcc, hc⟩ := CarayolDDT.exists_complexConj
  refine ⟨c, hcc, ?_⟩
  let d : GQ →* Eˣ := Matrix.GeneralLinearGroup.det.comp ρ
  have hdv : ∀ σ, ((d σ : Eˣ) : E) = (ρ σ : Matrix (Fin 2) (Fin 2) E).det := fun σ =>
    Matrix.GeneralLinearGroup.val_det_apply _
  have hdc : Continuous fun σ => ((d σ : Eˣ) : E) := by
    simp only [hdv]
    exact (Units.continuous_val.comp hρ).matrix_det
  set r : ℝ := ‖(2 : E)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 h2
  have hr1 : r ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one E 2
    simpa using this
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr0 hℓ
  have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let U : Subgroup GQ := (CarayolDDT.cycN N).ker ⊓ (CarayolDDT.cycN (ℓ ^ k)).ker ⊓
    nearOne d r hr0 hr1
  have hU : IsOpen (U : Set GQ) := by
    refine ((isOpen_ker_cycN N).inter (isOpen_ker_cycN (ℓ ^ k))).inter ?_
    have : ((fun σ => ((d σ : Eˣ) : E)) ⁻¹' Metric.ball 1 r) = (nearOne d r hr0 hr1 : Set GQ) := by
      ext σ; simp [nearOne, dist_eq_norm]
    exact this ▸ Metric.isOpen_ball.preimage hdc
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := CarayolLevel.frobeniusDense_C9 U hU c (N * ℓ).primeFactors
  have hNl : N * ℓ ≠ 0 := mul_ne_zero (NeZero.ne N) (Fact.out : ℓ.Prime).ne_zero
  have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, hNl⟩)
  have hpN : ¬ p ∣ N := fun h => hpNl (dvd_mul_of_dvd_left h _)
  have hpl : p ≠ ℓ := fun h => hpNl (h ▸ dvd_mul_left p N)
  have hlp : ¬ ℓ ∣ p := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hp).1 h).symm
  have hplk : ¬ p ∣ ℓ ^ k := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨⟨hU1, hU2⟩, hU3⟩ := hU'
  have hcN : ∀ M [NeZero M], τ⁻¹ * c ∈ (CarayolDDT.cycN M).ker → CarayolDDT.cycN M τ = -1 := by
    intro M _ h
    rw [MonoidHom.mem_ker, map_mul, map_inv, CarayolDDT.cycN_eq_neg_one M hc, inv_mul_eq_one] at h
    exact h
  have hτN := hcN N hU1
  have hτl := hcN (ℓ ^ k) hU2
  -- `det ρ(τ) = p`
  have hdτ : ((d τ : Eˣ) : E) = (p : E) := by rw [hdv]; exact hfrob p hp hpNl v τ hv hτ hτN
  -- `p ≡ -1 (mod ℓ^k)`
  have hpk : ((p : ℕ) : ZMod (ℓ ^ k)) = -1 := by
    rw [← cycN_arithFrob hp hplk hv hτ, hτl, Units.val_neg, Units.val_one]
  have hdvd : ℓ ^ k ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpk, Nat.cast_one, neg_add_cancel]
  obtain ⟨m, hm⟩ := hdvd
  have hp1 : ‖((p : E) + 1)‖ < r := by
    have : ((p : E) + 1) = (ℓ : E) ^ k * (m : E) := by
      have h' := congrArg (Nat.cast : ℕ → E) hm
      push_cast at h'
      exact h'
    rw [this, norm_mul, norm_pow]
    calc ‖(ℓ : E)‖ ^ k * ‖(m : E)‖ ≤ ‖(ℓ : E)‖ ^ k * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one E m)
            (pow_nonneg (norm_nonneg _) _)
      _ < r := by rw [mul_one]; exact hk
  have hpn : ‖(p : E)‖ = 1 := CarayolHerbrand.norm_natCast_eq_one_of hℓ hlp
  have hp0 : (p : E) ≠ 0 := by intro h; rw [h, norm_zero] at hpn; exact zero_ne_one hpn
  -- `det ρ(c)² = 1`
  have hsq : ((d c : Eˣ) : E) * (d c : Eˣ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hcc, map_one, Units.val_one]
  rw [← hdv]
  rcases mul_self_eq_one_iff.1 hsq with h1 | h1
  · exfalso
    have hnear : ‖((d (τ⁻¹ * c) : Eˣ) : E) - 1‖ < r := hU3
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hdτ, h1, mul_one] at hnear
    have hpm1 : ‖(p : E) - 1‖ < r := by
      have e : (p : E) - 1 = -((p : E) * ((p : E)⁻¹ - 1)) := by field_simp; ring
      rw [e, norm_neg, norm_mul, hpn, one_mul]
      exact hnear
    have e2 : (2 : E) = ((p : E) + 1) - ((p : E) - 1) := by ring
    have : ‖(2 : E)‖ < r := by
      rw [e2, sub_eq_add_neg]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hp1 ?_)
      rw [norm_neg]; exact hpm1
    exact lt_irrefl _ (hr ▸ this)
  · exact h1

end Odd

/-! ## §3. The leaf in the manuscript's normalization of Carayol's Théorème (A) -/

section Leaf

open HeckeRing.GL2 NumberField IsDedekindDomain

/-- **LEAF (published; consequence of Darmon–Diamond–Taylor 1997 Thm 3.1, proved below from carirr-odd's
transcription `CarayolDDT.CarayolDDT31`): the `λ`-adic representation of a weight-2 newform, with its
Frobenius polynomial in the normalization the manuscript reads off Carayol 1986, Théorème (A).**

For a newform `f ∈ S₂(Γ₁(N), ψ)` (Tau Ceti's `Newform N 2`, `ψ = f.χ`) whose coefficient field
`K_f = ℚ(a_n) ⊆ ℂ` is a number field, a prime `ℓ` and a place `λ ∣ ℓ` of `K_f`, there is a continuous
`ρ = ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` (Mathlib's `adicCompletion`) such that

* **irreducible**: no `ρ(G_ℚ)`-stable `K_{f,λ}`-subspace of `K_{f,λ}²` other than `0` and `K_{f,λ}²`
  (Ribet, LNM 601 (1977) Thm 2.3; DDT 1997 Thm 3.1(c) prints the stronger "absolutely irreducible";
  locators UNVERIFIED);
* **unramified at every `p ∤ Nℓ`, and arithmetic Frobenius has polynomial `X² − a_p X + p ψ(p)`**: trace
  `a_p(f)` and determinant `p ψ(p)` (the value `p ψ(p) ∈ ℂ` read in `K_f ⊆ ℂ`, quantified as every `b ∈ K_f`
  equal to it, and `ψ(p) = ψ(u)` for the unit `u = p mod N`). This is the manuscript's reading of Carayol's
  normalization (diophantine_zq.tex L9784-9796: reciprocity sends geometric Frobenius to a uniformizer,
  `ρ_f = σ(Π_f^∨)^∨`, "its good polynomial is `X² − a_q X + q χ(q)`" on arithmetic Frobenius); also
  Shimura 1971 Thm 7.14 / Deligne 1971 (Diamond–Shurman Thm 9.6.5) and DDT 3.1 (trace `a_p`, `det = ψ χ_ℓ`);
* **conductor** (DDT's form, as in `CarayolDDT.CarayolDDT31`): for every prime `p ≠ ℓ`,
  `codim V^{I_p} + ∫₀^∞ codim V^{G_p^u} du = v_p(N)`. Source: Carayol 1986, Théorème (A) (local–global
  compatibility at every `p ≠ ℓ`) with the conductor compatibility of the local Langlands correspondence and
  Casselman, Math. Ann. 201 (1973), Thm 1 (`a(π_{f,p}) = v_p(N)` for a newform); packaged as "the conductor
  of `ρ_{f,λ}` is the prime-to-`ℓ` part of `N`" in DDT 1997 Thm 3.1. Carayol's own statement (`σ_λ(π)|_{G_{ℚ_p}}`
  corresponds to `π_p` under local Langlands) has no Lean form: no local components `π_{f,p}`, no
  Weil–Deligne representations and no local Langlands correspondence exist in Lean (report §2).

Oddness is not a clause: it is proved from the Frobenius determinant (`odd_of_frobDet`). The leaf asserts one
representation and only listed properties of it, each implied by DDT 3.1 (`frob_of_DDT31`). -/
def CarayolThmAFrob : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
          (Fin 2 → lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
        (∀ σ : GQ, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2)
            (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).trace =
            algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))
              ⟨coeff (f.toCuspForm : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩ ∧
          ∀ (u : (ZMod N)ˣ) (b : DSCoeffExt.coeffField (f.toCuspForm : CF N 2)),
            (u : ZMod N) = (p : ZMod N) → (b : ℂ) = (p : ℂ) * ((f.χ u : ℂˣ) : ℂ) →
            (ρ σ : Matrix (Fin 2) (Fin 2)
              (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))).det =
              algebraMap (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
                (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) b) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        (codimInv (ρ.comp (decomp p)) inertiaSet : ℝ) +
          ∫ u in Set.Ioi (0 : ℝ), (codimInv (ρ.comp (decomp p)) (upperAbs p u) : ℝ) =
          (N.factorization p : ℝ)

theorem two_ne_zero_adic {F : Type*} [Field F] [NumberField F] (lam : HeightOneSpectrum (𝓞 F)) :
    (2 : lam.adicCompletion F) ≠ 0 := by
  have : (2 : lam.adicCompletion F) = algebraMap F (lam.adicCompletion F) 2 := by rw [map_ofNat]
  rw [this]
  exact (map_ne_zero_iff _ (algebraMap F (lam.adicCompletion F)).injective).mpr two_ne_zero

/-- **GLUE (proved): the leaf gives carayol-herbrand's `CarayolThmAIrrDDT`** (odd from the Frobenius
determinant, `odd_of_frobDet`, with `ψ(-1) = 1` in weight 2). -/
theorem carayolThmAIrrDDT_of_frob (h : CarayolThmAFrob) : CarayolHerbrand.CarayolThmAIrrDDT := by
  intro N _ f _ ℓ _ lam hlam
  obtain ⟨ρ, hc, hirr, hatt, hcond⟩ := h N f ℓ lam hlam
  refine ⟨ρ, hc, hirr, ?_, fun p hp hpN => ⟨(hatt p hp hpN).1, fun v σ hv hσ =>
    ((hatt p hp hpN).2 v σ hv hσ).1⟩, hcond⟩
  refine odd_of_frobDet (N := N) (CarayolHerbrand.norm_natCast_lt_one lam hlam) (two_ne_zero_adic lam)
    ρ hc ?_
  intro p hp hpNl v σ hv hσ hσN
  have hpN : ¬ p ∣ N := fun h => hpNl (dvd_mul_of_dvd_left h _)
  have hu : ((-1 : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := by
    rw [← cycN_arithFrob hp hpN hv hσ, hσN]
  have hb : (((p : DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) : ℂ) =
      (p : ℂ) * ((f.χ (-1) : ℂˣ) : ℂ) := by
    rw [CarayolDDT.chi_neg_one_eq_one f, mul_one]; rfl
  rw [((hatt p hp hpNl).2 v σ hv hσ).2 (-1) _ hu hb, map_natCast]

/-- **The open field `carayolThmAIrr` from the leaf** (Herbrand's theorem for the conductor's form,
carayol-herbrand). -/
theorem carayolThmAIrr_of_frob (h : CarayolThmAFrob) : CarayolPrinted.CarayolThmAIrr :=
  CarayolHerbrand.carayolThmAIrr_of_DDT (carayolThmAIrrDDT_of_frob h)

/-- **The leaf is implied by carirr-odd's transcription of DDT 1997 Thm 3.1** (absolutely irreducible ⇒
irreducible; `det ρ = ψ χ_ℓ` at an arithmetic Frobenius is `ψ(p)·p`, since `Frob_p mod N = p`,
`χ_ℓ(Frob_p) = p`). So `CarayolThmAFrob` is not stronger than `CarayolDDT31`. -/
theorem frob_of_DDT31 (h : CarayolDDT.CarayolDDT31) : CarayolThmAFrob := by
  intro N _ f _ ℓ _ lam hlam
  obtain ⟨ρ, hc, habs, ⟨ι, -, hdet⟩, hatt, hcond⟩ := h N f ℓ lam hlam
  refine ⟨ρ, hc, CarayolDDT.irreducible_of_absIrreducible _ habs,
    fun p hp hpNl => ⟨(hatt p hp hpNl).1, fun v σ hv hσ => ⟨(hatt p hp hpNl).2 v σ hv hσ, ?_⟩⟩, hcond⟩
  intro u b hu hb
  have hpN : ¬ p ∣ N := fun h => hpNl (dvd_mul_of_dvd_left h _)
  have hpl : p ≠ ℓ := fun h => hpNl (h ▸ dvd_mul_left p N)
  have hσu : CarayolDDT.cycN N σ = u := Units.ext ((cycN_arithFrob hp hpN hv hσ).trans hu.symm)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hχ : ((f.χ (CarayolDDT.cycN N σ) : ℂˣ) : ℂ) = (b : ℂ) / (p : ℂ) := by
    rw [hσu, hb]; field_simp
  have hmem : ((f.χ (CarayolDDT.cycN N σ) : ℂˣ) : ℂ) ∈
      DSCoeffExt.coeffField (f.toCuspForm : CF N 2) := by
    rw [hχ]
    exact div_mem b.2 (natCast_mem _ p)
  rw [hdet σ hmem, cycL_arithFrob hp hpl hv hσ, map_natCast, ← map_natCast (algebraMap
    (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))
    (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))) p, ← map_mul]
  congr 1
  apply Subtype.ext
  have hpc : (((p : DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) : ℂ) = (p : ℂ) := by simp
  simp only [MulMemClass.coe_mul, hpc]
  rw [hχ]; field_simp

/-- **The open field from carirr-odd's DDT 3.1 form** (through the new leaf). -/
theorem carayolThmAIrr_of_DDT31 (h : CarayolDDT.CarayolDDT31) : CarayolPrinted.CarayolThmAIrr :=
  carayolThmAIrr_of_frob (frob_of_DDT31 h)

/-- `r17` (`LadicCond.CarayolR17'`) from the leaf and the bundle leaf `EigenformCoeffFieldFinite`. -/
theorem carayolR17'_of_frob (h : CarayolThmAFrob) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    LadicCond.CarayolR17' :=
  CarayolPrinted.carayolR17'_of_printedIrr (carayolThmAIrr_of_frob h) hK

end Leaf

end CarayolRefold
