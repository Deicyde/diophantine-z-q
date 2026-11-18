import ZInQKernel.Contrib.OneProof.DeRhamScholzeHT
import ZInQKernel.Contrib.OneProof.PanBergerPst
import ZInQKernel.Contrib.OneProof.PanBergerSanity
import ZInQKernel.Contrib.OneProof.DeRhamPrintTDict
import ZInQKernel.Contrib.OneProof.BdRInvariants

/-!
# derham-scholze, part 3 (`ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean`, scratch copy
`scratch/derham-scholze/FontaineT.lean`): Fontaine's `t = log [ε]` is a uniformizer of `B_dR^+` with `σ(t) = χ(σ) t`

Proves `FontaineTwistT` (stated in `DeRhamScholzeHT.lean`): for a generator `ε₀ = (1, ζ_p, ζ_{p²}, …)` of
`ℤ_p(1)` in `𝓞_ℂ_p♭`, `t = log [ε₀]` (bst-construct's `logTeich`) satisfies `𝔪 = (t)` and `σ(t) = χ(σ) t`.

* `σ(log [ε]) = log [σ ε]` (bst-construct's `bdrAct_logTeich`);
* `σ ε₀ = ε₀^{χ(σ)}` coordinatewise: `σ(ζ_{pᵏ}) = ζ_{pᵏ}^{χ(σ) mod pᵏ}` (Mathlib's `cyclotomicCharacter.spec`);
* `log [σ ε₀] = χ(σ) log [ε₀]`: pb-pst's `log_decomp` and the `p`-adic separatedness of `A_max` (`amax_sep`), as
  in pb-pst's `logTeich_eq_mul` with the exponents `χ(σ) mod pᵏ`;
* `log [ε₀] ≡ [ε₀] − 1 mod 𝔪²` and `[ε₀] − 1 ∈ 𝔪 ∖ 𝔪²` (TDict's `xe_mem`, `xe_not_mem_sq`), so `t` is a
  uniformizer.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace DeRhamScholze.TT

open HDec.PkgI4 HDec.PkgI4.BergerBst HDec.PkgI4.BmaxOne
open HDec.PkgI4.PanBergerSplit (Ainf AinfP flatAct locAct)

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Copy of `DeRhamScholze.HT.FontaineTwistT` (`DeRhamScholzeHT.lean`); checked `Iff.rfl` there. -/
def FontaineTwistT' : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ t : BDeRhamPlus 𝓞_ℂ_[p] p,
    IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {t} ∧
    ∀ σ : ZInQ.Contrib.G9.PkgI4.GQp p,
      ZInQ.Contrib.G9.PkgI4.DR.bdrPlusMap p (ZInQ.Contrib.G9.PkgI4.oAct p σ) t =
        ZInQ.Contrib.G9.qpToPlus p (ZInQ.Contrib.G9.PkgI4.cycPow p σ 1) * t

/-! ## §1. The Galois action on `log [ε]` in `B_dR^+` -/

theorem plus_logTeich (σ : GQp p) {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    DR.bdrPlusMap p (oAct p σ) (logTeich p h) =
      logTeich p (show PreTilt.untilt (flatAct p σ ε) = 1 by rw [DR.untilt_preTiltMap, h, map_one]) := by
  apply toBdR_injective p
  rw [← bdrAct_toBdR, bdrAct_logTeich]

/-! ## §2. `σ` on the coordinates of `ε₀`: the cyclotomic character -/

/-- A `pᵏ`-th root of unity of `ℂ_p` comes from `ℚ̄_p`. -/
theorem exists_coe_of_pow_eq_one (k : ℕ) {r : ℂ_[p]} (hr : r ^ p ^ k = 1) :
    ∃ s : PadicAlgCl p, ((s : PadicAlgCl p) : ℂ_[p]) = r ∧ s ^ p ^ k = 1 := by
  haveI : NeZero ((p ^ k : ℕ) : PadicAlgCl p) := ⟨by
    rw [Nat.cast_pow]; exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
  have hζ' : IsPrimitiveRoot (algebraMap (PadicAlgCl p) ℂ_[p] ζ) (p ^ k) :=
    hζ.map_of_injective (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  obtain ⟨j, -, hj⟩ := hζ'.eq_pow_of_pow_eq_one hr
  refine ⟨ζ ^ j, ?_, ?_⟩
  · rw [← hj, PadicComplex.coe_eq, map_pow]
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- The exponent `χ(σ) mod pᵏ`. -/
abbrev cexp (σ : GQp p) (k : ℕ) : ℕ :=
  ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]).toZModPow k).val

open ZInQ.Contrib.G9.BdrKer.Cp (root root_pow) in
/-- `σ(ε^{(k)}) = (ε^{(k)})^{χ(σ) mod pᵏ}` for `ε^♯ = 1`. -/
theorem root_flatAct (σ : GQp p) {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) (k : ℕ) :
    root (flatAct p σ ε) k = root ε k ^ cexp p σ k := by
  rw [PanBergerSplit.root_preTiltMap]
  apply Subtype.ext
  have hr : ((root ε k : 𝓞_ℂ_[p]) : ℂ_[p]) ^ p ^ k = 1 := by
    have h1 := root_pow ε k
    rw [h] at h1
    have h2 := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) h1
    simpa using h2
  obtain ⟨s, hs, hs1⟩ := exists_coe_of_pow_eq_one p k hr
  change cpAct p σ ((root ε k : 𝓞_ℂ_[p]) : ℂ_[p]) = ((root ε k ^ cexp p σ k : 𝓞_ℂ_[p]) : ℂ_[p])
  rw [← hs, cpAct_coe]
  have := cyclotomicCharacter.spec p σ.toRingEquiv s hs1
  change σ s = _ at this
  rw [this, SubmonoidClass.coe_pow, ← hs]
  exact map_pow (algebraMap (PadicAlgCl p) ℂ_[p]) s _

/-! ## §3. `log [σ ε₀] = χ(σ) log [ε₀]` -/

open ZInQ.Contrib.G9.BdrKer.Cp (root root_pow) in
theorem logTeich_flatAct {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (σ : GQp p) :
    logTeich p (show PreTilt.untilt (flatAct p σ ε₀) = 1 by rw [DR.untilt_preTiltMap, h.1, map_one]) =
      zpB p (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]) * logTeich p h.1 := by
  set a : ℤ_[p] := (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]) with ha
  have hε : PreTilt.untilt (flatAct p σ ε₀) = 1 := by rw [DR.untilt_preTiltMap, h.1, map_one]
  refine sub_eq_zero.mp (amax_sep p _ fun k => ?_)
  have hb : root ε₀ k ^ cexp p σ k = root (flatAct p σ ε₀) k := (root_flatAct p σ h.1 k).symm
  have hblt : cexp p σ k ≤ p ^ k := (ZMod.val_lt _).le
  obtain ⟨z, hz, hlog⟩ := log_decomp p h hε k (cexp p σ k) hblt hb
  have hab : a - (cexp p σ k : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hab
  have hac : a = (cexp p σ k : ℤ_[p]) + c * (p : ℤ_[p]) ^ k := by linear_combination -hc
  refine ⟨z - zpB p c * logTeich p h.1,
    Subring.sub_mem _ hz (Subring.mul_mem _ (zpB_mem p c) (logTeich_mem_amax p h.1)), ?_⟩
  rw [hlog, hac, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

/-! ## §4. `t = log [ε₀]` is a uniformizer, for `ε₀` TDict's generator -/

open PowerSeries in
/-- `log(1 + X) = X + X² g`. -/
theorem logSeries_eq : ∃ g : (AinfP p)⟦X⟧, logSeries p = X + X ^ 2 * g := by
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 2) (logSeries p), ?_⟩
  ext n
  rw [map_add, coeff_X_pow_mul', coeff_X]
  rcases n with _ | _ | n
  · simp [logSeries]
  · simp [logSeries]
  · simp

theorem psEval_X {x : AinfP p} (hx : x ∈ Ith p) :
    psEval (Ith p) hx PowerSeries.X = AdicCompletion.of (Ith p) (AinfP p) x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psEval, AdicCompletion.evalₐ_of]
  apply Ideal.Quotient.eq.mpr
  rcases n with _ | _ | n
  · rw [pow_zero, Ideal.one_eq_top]; trivial
  · have h0 : PowerSeries.trunc 1 (PowerSeries.X : PowerSeries (AinfP p)) = 0 := by
      ext i
      simp [PowerSeries.coeff_trunc, PowerSeries.coeff_X]
    rw [h0, Polynomial.eval_zero, zero_sub, zero_add, pow_one]
    exact neg_mem hx
  · rw [PowerSeries.trunc_X, Polynomial.eval_X, sub_self]
    exact zero_mem _

/-- TDict's generator `ε₀ = (1, ζ_p, ζ_{p²}, …)`. -/
abbrev eps0 : PreTilt 𝓞_ℂ_[p] p := DeRhamPrint.TDict.eps (DeRhamPrint.TDict.rootSystem p)

theorem isGenEps_eps0 : IsGenEps p (eps0 p) := by
  refine ⟨DeRhamPrint.TDict.untilt_eps _, ?_⟩
  have h1 : (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm (eps0 p) =
      DeRhamPrint.TDict.eps1 (DeRhamPrint.TDict.rootSystem p) := by
    apply (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).injective
    rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, DeRhamPrint.TDict.eps1_pow]
  change PreTilt.untilt ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[1] (eps0 p)) ≠ 1
  rw [Function.iterate_one, h1, DeRhamPrint.TDict.untilt_eps1]
  exact (DeRhamPrint.TDict.rootSystem p).one_ne

theorem logTeich_sub_xe_mem :
    logTeich p (isGenEps_eps0 p).1 - DeRhamPrint.TDict.xe (DeRhamPrint.TDict.rootSystem p) ∈
      Ideal.span {DeRhamPrint.TDict.varpi p ^ 2} := by
  obtain ⟨g, hg⟩ := logSeries_eq p
  have hxe : DeRhamPrint.TDict.xe (DeRhamPrint.TDict.rootSystem p) =
      psEval (Ith p) (teich_sub_one_mem p (isGenEps_eps0 p).1) PowerSeries.X := by
    rw [psEval_X, DeRhamPrint.TDict.xe]
    simp only [map_sub, map_one]
    rfl
  have hmem : DeRhamPrint.TDict.xe (DeRhamPrint.TDict.rootSystem p) ∈ Ideal.span {DeRhamPrint.TDict.varpi p} := by
    have := DeRhamPrint.TDict.xe_mem (DeRhamPrint.TDict.rootSystem p)
    rwa [ZInQ.Contrib.G9.BdrKer.Cp.maximalIdeal_BDeRhamPlus] at this
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  change psEval (Ith p) (teich_sub_one_mem p (isGenEps_eps0 p).1) (logSeries p) - _ ∈ _
  rw [hg, map_add, ← hxe]
  have key : (psEval (Ith p) (teich_sub_one_mem p (isGenEps_eps0 p).1) (PowerSeries.X ^ 2 * g) :
      BDeRhamPlus 𝓞_ℂ_[p] p) ∈ Ideal.span {DeRhamPrint.TDict.varpi p ^ 2} := by
    rw [map_mul, map_pow, ← hxe, ← hd]
    have h1 : (d * DeRhamPrint.TDict.varpi p) ^ 2 ∈
        (Ideal.span {DeRhamPrint.TDict.varpi p ^ 2} : Ideal (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
      rw [mul_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    rw [mul_comm]
    exact Ideal.mul_mem_left _ _ h1
  convert key using 1
  exact add_sub_cancel_left _ _

theorem maximalIdeal_eq_logTeich :
    IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) = Ideal.span {logTeich p (isGenEps_eps0 p).1} := by
  set t := logTeich p (isGenEps_eps0 p).1
  set Z := DeRhamPrint.TDict.rootSystem p
  have hsub := logTeich_sub_xe_mem p
  have hsq_le : (Ideal.span {DeRhamPrint.TDict.varpi p ^ 2} : Ideal (BDeRhamPlus 𝓞_ℂ_[p] p)) ≤
      IsLocalRing.maximalIdeal _ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_of_mem _ (DeRhamPrint.TDict.varpi_mem_max (p := p)) 2 (by norm_num)
  have htm : t ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := by
    have : t = DeRhamPrint.TDict.xe Z + (t - DeRhamPrint.TDict.xe Z) := by ring
    rw [this]
    exact Ideal.add_mem _ (DeRhamPrint.TDict.xe_mem Z) (hsq_le hsub)
  have htsq : t ∉ (Ideal.span {DeRhamPrint.TDict.varpi p ^ 2} : Ideal (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
    intro h
    apply DeRhamPrint.TDict.xe_not_mem_sq Z
    have : DeRhamPrint.TDict.xe Z = t - (t - DeRhamPrint.TDict.xe Z) := by ring
    rw [this]
    exact Ideal.sub_mem _ h hsub
  have ht0 : t ≠ 0 := fun h => htsq (h ▸ Ideal.zero_mem _)
  obtain ⟨n, u, hu, h⟩ := ZInQ.Contrib.G9.BdrKer.Cp.eq_xi_pow_mul_unit p t ht0
  rcases n with _ | _ | n
  · exfalso
    rw [pow_zero, one_mul] at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) (h ▸ htm)
  · rw [ZInQ.Contrib.G9.BdrKer.Cp.maximalIdeal_BDeRhamPlus, h, zero_add, pow_one,
      Ideal.span_singleton_mul_right_unit hu]
  · exfalso
    apply htsq
    rw [h, Ideal.mem_span_singleton']
    exact ⟨DeRhamPrint.TDict.varpi p ^ n * u, by ring⟩

/-! ## §5. `FontaineTwistT` -/

theorem zpB_eq_qpToPlus (a : ℤ_[p]) : zpB p a = ZInQ.Contrib.G9.qpToPlus p (a : ℚ_[p]) := by
  apply BdRInv.alg_injective p
  exact toBdR_zpB p a

theorem cycPow_one_eq (σ : ZInQ.Contrib.G9.PkgI4.GQp p) :
    ZInQ.Contrib.G9.PkgI4.cycPow p σ 1 = ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]) : ℚ_[p]) := by
  simp only [ZInQ.Contrib.G9.PkgI4.cycPow, ZInQ.Contrib.G9.PkgI4.cyc, zpow_one]

/-- **Fontaine's `t`** (proved): `t = log [ε₀]` is a uniformizer of `B_dR^+` and `σ(t) = χ(σ) t`. -/
theorem fontaineTwistT_proof : FontaineTwistT' := by
  intro p _
  refine ⟨logTeich p (isGenEps_eps0 p).1, maximalIdeal_eq_logTeich p, fun σ => ?_⟩
  have h1 := plus_logTeich p σ (isGenEps_eps0 p).1
  rw [logTeich_flatAct p (isGenEps_eps0 p) σ, zpB_eq_qpToPlus] at h1
  rw [cycPow_one_eq]
  exact h1

/-- The copy is `DeRhamScholzeHT.lean`'s statement. -/
theorem fontaineTwistT'_iff : FontaineTwistT' ↔ DeRhamScholze.HT.FontaineTwistT := Iff.rfl

/-- **`FontaineTwistT`, proved.** -/
theorem fontaineTwistT : DeRhamScholze.HT.FontaineTwistT := fontaineTwistT_proof

/-- **`DeRhamHodgeTate01`, proved** (the manuscript's "consequently", L10995): from Fontaine's `t` and Tate's
theorems. -/
theorem deRhamHodgeTate01_proof : DeRhamScholze.DeRhamHodgeTate01 :=
  DeRhamScholze.HT.deRhamHodgeTate01_of_fontaineT fontaineTwistT

/-- **The research field `hodgeTateDecompOr` from Scholze's comparison and Milne's identification alone.** -/
theorem hodgeTateDecompOr_of_scholzeMilne (hS : DeRhamScholze.ScholzeDeRhamAlg)
    (hT : T10Etale.T10_TateDuality) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  DeRhamScholze.hodgeTateDecompOr_of_leaves hS hT deRhamHodgeTate01_proof

end

end DeRhamScholze.TT
