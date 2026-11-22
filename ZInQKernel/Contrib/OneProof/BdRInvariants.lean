import ZInQKernel.Contrib.OneProof.DeRhamPrint
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.TateTwistInvariants

/-!
# bdr-inv: `B_dR^{G_F} = F` (Fontaine), proved: `DeRhamPrint.BdRInvariantsPrinted`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task bdr-inv, 2026-11-17).
Report `docs/research/bdr-inv.md`, scratch `scratch/bdr-inv/` (same content as `BdRInv.lean`).
The statement `DeRhamPrint.BdRInvariantsPrinted`
(`ZInQKernel/Contrib/OneProof/DeRhamPrint.lean`) is used verbatim (imported, not restated).

Proof (Brinon–Conrad, *CMI notes* (2009), Prop. 4.3.1 / Thm. 4.3.2-type argument; Fontaine, Astérisque 223,
Exp. II; locators UNVERIFIED):
1. `σ([ε] - 1) = ([ε] - 1) · c_σ` in `B_dR^+` with `θ(c_σ) = χ(σ)` (`bdrPlus_T`): `σ(ε) = ε^a ρ^{p^m}` in the
   tilt with `ρ^♯ = 1`, `a ≡ χ(σ) mod p^m`, and `[ρ] - 1 ∈ ξ W(O♭)` gives `θ(c_σ) ≡ a mod p^m` (bounded error).
2. `[ε] - 1` is a uniformizer of the DVR `B_dR^+`; a `G_K`-invariant `x = T^{j-k} u` gives
   `χ^{j-k} σ(θ u) = θ u`, so `j = k` by Tate's theorem (`tateTwistInvariants_proof`): `x ∈ (B_dR^+)^×`.
3. `θ(x) ∈ ℂ_p^{G_K} = K` (Ax–Sen–Tate, `axSenTate_proof`); the Hensel lift `F → B_dR^+` (G9's
   `exists_hensel_lift`) is `G_F`-invariant; the difference is invariant with `θ = 0`, hence `0` by 2.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace BdRInv

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.PkgI4.Cp ZInQ.Contrib.G9.BdrKer
  ZInQ.Contrib.G9.BdrKer.Cp ZInQ.Contrib.HodgeSplit DeRhamPrint.TDict Module

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. A compatible system of `p`-power roots of unity coming from `ℚ̄_p` -/

theorem exists_prim : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ p := by
  have : NeZero (p : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (PadicAlgCl p))
    (Polynomial.degree_cyclotomic_pos p (PadicAlgCl p) hp.out.pos).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/-- `1, ζ_p, ζ_{p²}, …` in `ℚ̄_p`. -/
def zq : ℕ → PadicAlgCl p
  | 0 => 1
  | 1 => Classical.choose (exists_prim p)
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (zq (n + 1)) hp.out.pos)

theorem zq_succ_pow (n : ℕ) : zq p (n + 1) ^ p = zq p n := by
  rcases n with _ | n
  · exact (Classical.choose_spec (exists_prim p)).pow_eq_one
  · exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (zq p (n + 1)) hp.out.pos)

theorem zq_pow (n : ℕ) : zq p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [zq]
  | succ n ih => rw [pow_succ', pow_mul, zq_succ_pow, ih]

theorem zq_pow_add (n m : ℕ) : zq p (n + m) ^ p ^ m = zq p n := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, pow_succ', pow_mul, zq_succ_pow, ih]

theorem norm_zq (n : ℕ) : ‖((zq p n : PadicAlgCl p) : ℂ_[p])‖ = 1 := by
  have h1 : ‖((zq p n : PadicAlgCl p) : ℂ_[p])‖ ^ p ^ n = 1 := by
    rw [← norm_pow, PadicComplex.coe_eq, ← map_pow, zq_pow, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).mp h1

theorem zq_ne_zero (n : ℕ) : ((zq p n : PadicAlgCl p) : ℂ_[p]) ≠ 0 := by
  intro h; have := norm_zq p n; rw [h, norm_zero] at this; exact zero_ne_one this

/-- The root system of TDict built from `zq`. -/
def Zq : RootSystem p where
  z n := ⟨((zq p n : PadicAlgCl p) : ℂ_[p]), (mem_O_iff p _).mpr (norm_zq p n).le⟩
  pow_succ n := Subtype.ext (by
    push_cast
    rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow, zq_succ_pow])
  zero := Subtype.ext (by simp [zq])
  one_ne h := by
    have h1 := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at h1
    rw [PadicComplex.coe_eq, ← map_one (algebraMap (PadicAlgCl p) ℂ_[p])] at h1
    exact (Classical.choose_spec (exists_prim p)).ne_one hp.out.one_lt
      ((algebraMap (PadicAlgCl p) ℂ_[p]).injective h1)

theorem Zq_z (n : ℕ) : ((Zq p).z n : ℂ_[p]) = ((zq p n : PadicAlgCl p) : ℂ_[p]) := rfl

/-! ## 2. The Galois action on `ε` -/

/-- The cyclotomic exponent mod `p^m`: `σ(ζ) = ζ^{a}` for `ζ^{p^m} = 1`. -/
def aexp (σ : GQp p) (m : ℕ) : ℕ := (PadicInt.toZModPow m ((cyc p σ : ℤ_[p]))).val

theorem cpAct_zq (σ : GQp p) (m : ℕ) :
    cpAct p σ ((zq p m : PadicAlgCl p) : ℂ_[p]) = ((zq p m : PadicAlgCl p) : ℂ_[p]) ^ aexp p σ m := by
  rw [cpAct_coe]
  have h := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := m) σ.toRingEquiv (zq p m) (zq_pow p m)
  rw [show σ (zq p m) = σ.toRingEquiv (zq p m) from rfl, h, PadicComplex.coe_eq, PadicComplex.coe_eq, map_pow]
  rfl


/-- The components of `ρ = (σ(ε) ε^{-a})^{1/p^m}`, in `ℂ_p`. -/
def rhoC (σ : GQp p) (m n : ℕ) : ℂ_[p] :=
  cpAct p σ ((zq p (n + m) : PadicAlgCl p) : ℂ_[p]) *
    (((zq p (n + m) : PadicAlgCl p) : ℂ_[p])⁻¹) ^ aexp p σ m

theorem norm_rhoC (σ : GQp p) (m n : ℕ) : ‖rhoC p σ m n‖ = 1 := by
  rw [rhoC, norm_mul, norm_pow, norm_inv, norm_cpAct, norm_zq]; simp

/-- `ρ`'s components in `𝓞_ℂ_p`. -/
def rhoO (σ : GQp p) (m n : ℕ) : (𝓞_ℂ_[p] : Type) :=
  ⟨rhoC p σ m n, (mem_O_iff p _).mpr (norm_rhoC p σ m n).le⟩

theorem coe_pow_zq (k N : ℕ) : (((zq p k : PadicAlgCl p) : ℂ_[p])) ^ N = (((zq p k ^ N : PadicAlgCl p)) : ℂ_[p]) := by
  rw [PadicComplex.coe_eq, PadicComplex.coe_eq, map_pow]

theorem inv_pow_pow (c : ℂ_[p]) (a N : ℕ) : ((c⁻¹) ^ a) ^ N = ((c ^ N)⁻¹) ^ a := by
  rw [← pow_mul, mul_comm, pow_mul, inv_pow]

theorem rhoC_pow (σ : GQp p) (m n N : ℕ) (k : ℕ) (hk : zq p (n + m) ^ N = zq p k) :
    rhoC p σ m n ^ N = cpAct p σ ((zq p k : PadicAlgCl p) : ℂ_[p]) *
      (((zq p k : PadicAlgCl p) : ℂ_[p])⁻¹) ^ aexp p σ m := by
  rw [rhoC, mul_pow, inv_pow_pow, ← map_pow, coe_pow_zq, hk]

theorem rhoO_succ (σ : GQp p) (m n : ℕ) : rhoO p σ m (n + 1) ^ p = rhoO p σ m n := by
  apply Subtype.ext
  simp only [rhoO, SubmonoidClass.coe_pow]
  rw [rhoC_pow p σ m (n + 1) p (n + m) (by rw [Nat.add_right_comm]; exact zq_succ_pow p (n + m))]
  rfl

/-- `ρ ∈ O♭`. -/
def rho (σ : GQp p) (m : ℕ) : PreTilt (𝓞_ℂ_[p] : Type) p := mkSeq p (rhoO p σ m) (rhoO_succ p σ m)

theorem untilt_rho (σ : GQp p) (m : ℕ) : (rho p σ m).untilt = 1 := by
  rw [rho, untilt_mkSeq]
  apply Subtype.ext
  simp only [rhoO, rhoC, OneMemClass.coe_one, zero_add]
  rw [cpAct_zq, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (zq_ne_zero p m))]

theorem oAct_coe (σ : GQp p) (x : (𝓞_ℂ_[p] : Type)) : ((oAct p σ x : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) = cpAct p σ (x : ℂ_[p]) := rfl

/-- **`σ(ε) = ε^a · ρ^{p^m}`** in the tilt. -/
theorem preTiltMap_eps (σ : GQp p) (m : ℕ) :
    DR.preTiltMap p (oAct p σ) (eps (Zq p)) = eps (Zq p) ^ aexp p σ m * rho p σ m ^ p ^ m := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (DR.preTiltMap p (oAct p σ) (eps (Zq p))) =
    PreTilt.coeff n (eps (Zq p) ^ aexp p σ m * rho p σ m ^ p ^ m)
  rw [map_mul, map_pow, map_pow, eps, rho, coeff_mkSeq, coeff_mkSeq, ← map_pow, ← map_pow, ← map_mul]
  change Ideal.Quotient.mk _ (oAct p σ ((Zq p).z n)) = _
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, oAct_coe, Zq_z, rhoO]
  rw [rhoC_pow p σ m n (p ^ m) n (zq_pow_add p n m), inv_pow]
  have h0 := pow_ne_zero (aexp p σ m) (zq_ne_zero p n)
  field_simp

/-! ## 3. `B_dR^+`: `θ⁺` and `σ` on Teichmüller lifts -/

theorem thetaPlusCp_plus (w : WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) :
    thetaPlusCp p (plus p w) = ((fontaineTheta (𝓞_ℂ_[p] : Type) p w : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) := by
  change awayEquivCp p (thetaPlus p (plus p w)) = _
  rw [thetaPlus_plus, AlgEquiv.commutes]
  rfl

theorem thetaPlusCp_teich (x : PreTilt (𝓞_ℂ_[p] : Type) p) :
    thetaPlusCp p (plus p (teichmuller p x)) = ((x.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) := by
  rw [thetaPlusCp_plus, fontaineTheta_teichmuller]

theorem bdrPlusMap_plus (σ : GQp p) (w : WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) :
    DR.bdrPlusMap p (oAct p σ) (plus p w) = plus p (WittVector.map (DR.preTiltMap p (oAct p σ)) w) := by
  change DR.bdrPlusMap p (oAct p σ) (ofLoc p (algebraMap _ _ w)) = ofLoc p (algebraMap _ _ _)
  rw [bdrPlusMap_ofLoc, locMap_algebraMap]

theorem bdrPlusMap_teich (σ : GQp p) (x : PreTilt (𝓞_ℂ_[p] : Type) p) :
    DR.bdrPlusMap p (oAct p σ) (plus p (teichmuller p x)) = plus p (teichmuller p (DR.preTiltMap p (oAct p σ) x)) := by
  rw [bdrPlusMap_plus, map_teichmuller]

/-! ## 4. `T = [ε] - 1` is a uniformizer and `σ(T) = T · c_σ` with `θ(c_σ) = χ(σ)` -/

/-- `T = [ε] - 1 ∈ B_dR^+`. -/
abbrev T : BDeRhamPlus (𝓞_ℂ_[p] : Type) p := xe (Zq p)

theorem exists_T_eq : ∃ v : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ, T p = varpi p * v := by
  have hm : T p ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := xe_mem (Zq p)
  rw [maximalIdeal_BDeRhamPlus] at hm
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hm
  by_cases hu : IsUnit v
  · obtain ⟨u, rfl⟩ := hu
    exact ⟨u, by rw [← hv, mul_comm]⟩
  · exfalso
    have hv' : v ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := hu
    rw [maximalIdeal_BDeRhamPlus] at hv'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hv'
    apply xe_not_mem_sq (Zq p)
    rw [Ideal.mem_span_singleton']
    exact ⟨b, by show b * varpi p ^ 2 = T p; rw [← hv, ← hb]; ring⟩

/-- The unit `v` with `T = ξ · v`. -/
def vT : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ := (exists_T_eq p).choose

theorem T_eq : T p = varpi p * (vT p : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := (exists_T_eq p).choose_spec

theorem irreducible_T : Irreducible (T p) := by
  haveI := isDiscreteValuationRing_BDeRhamPlus p
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, T_eq,
    Ideal.span_singleton_mul_right_unit (vT p).isUnit, maximalIdeal_BDeRhamPlus]

theorem T_ne_zero : T p ≠ 0 := (irreducible_T p).ne_zero

/-- The bound constant `‖θ(v)‖⁻¹`. -/
def CT : ℝ := ‖thetaPlusCp p (vT p : BDeRhamPlus (𝓞_ℂ_[p] : Type) p)‖⁻¹

theorem CT_nonneg : 0 ≤ CT p := inv_nonneg.mpr (norm_nonneg _)

/-- **`[ρ] - 1 ∈ T · B_dR^+` with a uniformly bounded `θ` of the cofactor** for `ρ♯ = 1`. -/
theorem teich_sub_one (ρ : PreTilt (𝓞_ℂ_[p] : Type) p) (hρ : ρ.untilt = 1) :
    ∃ r, plus p (teichmuller p ρ) - 1 = T p * r ∧ ‖thetaPlusCp p r‖ ≤ CT p := by
  have hk : teichmuller p ρ - 1 ∈ RingHom.ker (fontaineTheta (𝓞_ℂ_[p] : Type) p) := by
    rw [RingHom.mem_ker, map_sub, fontaineTheta_teichmuller, hρ, map_one, sub_self]
  rw [ker_fontaineTheta_Cp] at hk
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.mp hk
  refine ⟨plus p r' * ((vT p)⁻¹ : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ), ?_, ?_⟩
  · have h1 : plus p (teichmuller p ρ) - 1 = plus p r' * varpi p := by
      show _ = plus p r' * plus p (xi p)
      rw [← map_mul, hr', map_sub, map_one]
    rw [h1, T_eq]
    calc plus p r' * varpi p = varpi p * ((vT p : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) *
        ((vT p)⁻¹ : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ)) * plus p r' := by
          rw [Units.mul_inv, mul_one, mul_comm]
      _ = _ := by ring
  · rw [map_mul, norm_mul, map_units_inv, norm_inv, thetaPlusCp_plus, CT]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (norm_le_one p _)

theorem thetaPlusCp_geom (x : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (hx : thetaPlusCp p x = 1) (n : ℕ) :
    thetaPlusCp p (∑ i ∈ Finset.range n, x ^ i) = n := by
  rw [map_sum]
  simp only [map_pow, hx, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- Step A: for each `m`, `σ(T) = T · w` with `θ(w) ≡ a_m` up to `C ‖p‖^m`. -/
theorem bdrPlus_T_approx (σ : GQp p) (m : ℕ) : ∃ w, DR.bdrPlusMap p (oAct p σ) (T p) = T p * w ∧
    ‖thetaPlusCp p w - (aexp p σ m : ℂ_[p])‖ ≤ CT p * ‖(p : ℂ_[p])‖ ^ m := by
  obtain ⟨r, hr, hrb⟩ := teich_sub_one p (rho p σ m) (untilt_rho p σ m)
  set a := aexp p σ m
  set N := p ^ m
  set E := plus p (teichmuller p (eps (Zq p)))
  set R := plus p (teichmuller p (rho p σ m))
  have hE : E - 1 = T p := rfl
  have hθE : thetaPlusCp p E = 1 := by
    rw [thetaPlusCp_teich, untilt_eps]; rfl
  have hθR : thetaPlusCp p R = 1 := by
    rw [thetaPlusCp_teich, untilt_rho]; rfl
  have hσT : DR.bdrPlusMap p (oAct p σ) (T p) = E ^ a * R ^ N - 1 := by
    change DR.bdrPlusMap p (oAct p σ) (E - 1) = _
    rw [map_sub, map_one, bdrPlusMap_teich, preTiltMap_eps p σ m, map_mul, map_pow, map_pow,
      map_mul, map_pow, map_pow]
  refine ⟨(∑ i ∈ Finset.range a, E ^ i) * R ^ N + r * ∑ i ∈ Finset.range N, R ^ i, ?_, ?_⟩
  · rw [hσT]
    have h1 : E ^ a - 1 = (∑ i ∈ Finset.range a, E ^ i) * T p := by rw [← hE, geom_sum_mul]
    have h2 : R ^ N - 1 = (∑ i ∈ Finset.range N, R ^ i) * (T p * r) := by rw [← hr, geom_sum_mul]
    linear_combination R ^ N * h1 + h2
  · rw [map_add, map_mul, map_mul, map_pow, hθR, one_pow, mul_one, thetaPlusCp_geom p E hθE,
      thetaPlusCp_geom p R hθR, add_sub_cancel_left, norm_mul]
    have : ((N : ℕ) : ℂ_[p]) = (p : ℂ_[p]) ^ m := by simp [N]
    rw [this, norm_pow]
    exact mul_le_mul_of_nonneg_right hrb (pow_nonneg (norm_nonneg _) m)

/-- `ℤ_p → ℂ_p`. -/
def iZ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom

theorem norm_algebraMap_qp' (c : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem norm_iZ_le (y : ℤ_[p]) : ‖iZ p y‖ ≤ 1 := by
  change ‖algebraMap ℚ_[p] ℂ_[p] (y : ℚ_[p])‖ ≤ 1
  rw [norm_algebraMap_qp']
  exact PadicInt.norm_le_one y

theorem aexp_approx (σ : GQp p) (m : ℕ) :
    ‖(aexp p σ m : ℂ_[p]) - iZ p (cyc p σ : ℤ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
  have hk : ((aexp p σ m : ℕ) : ℤ_[p]) - (cyc p σ : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, aexp, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow] at hk
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hk
  have : (aexp p σ m : ℂ_[p]) - iZ p (cyc p σ : ℤ_[p]) = iZ p y * (p : ℂ_[p]) ^ m := by
    rw [← map_natCast (iZ p), ← map_sub, ← hy, map_mul, map_pow, map_natCast]
  rw [this, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (norm_iZ_le p y)

theorem eq_zero_of_norm_le_pow {D : ℂ_[p]} {K : ℝ} (h : ∀ m : ℕ, ‖D‖ ≤ K * ‖(p : ℂ_[p])‖ ^ m) : D = 0 := by
  by_contra hD
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hK : 0 < K := by
    have := h 0
    rw [pow_zero, mul_one] at this
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hpos hK) (norm_p_lt_one p)
  rw [lt_div_iff₀ hK] at hm
  linarith [h m, mul_comm K (‖(p : ℂ_[p])‖ ^ m)]

/-- **`σ(T) = T · w` with `θ(w) = χ(σ)`.** -/
theorem bdrPlus_T (σ : GQp p) : ∃ w, DR.bdrPlusMap p (oAct p σ) (T p) = T p * w ∧
    thetaPlusCp p w = iZ p (cyc p σ : ℤ_[p]) := by
  obtain ⟨w, hw, -⟩ := bdrPlus_T_approx p σ 0
  refine ⟨w, hw, ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_norm_le_pow p (K := CT p + 1)
  intro m
  obtain ⟨w', hw', hb⟩ := bdrPlus_T_approx p σ m
  have hww : w' = w := mul_left_cancel₀ (T_ne_zero p) (hw'.symm.trans hw)
  rw [hww] at hb
  calc ‖thetaPlusCp p w - iZ p (cyc p σ : ℤ_[p])‖
      = ‖(thetaPlusCp p w - (aexp p σ m : ℂ_[p])) + ((aexp p σ m : ℂ_[p]) - iZ p (cyc p σ : ℤ_[p]))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖thetaPlusCp p w - (aexp p σ m : ℂ_[p])‖ + ‖(aexp p σ m : ℂ_[p]) - iZ p (cyc p σ : ℤ_[p])‖ :=
        norm_add_le _ _
    _ ≤ CT p * ‖(p : ℂ_[p])‖ ^ m + ‖(p : ℂ_[p])‖ ^ m := add_le_add hb (aexp_approx p σ m)
    _ = (CT p + 1) * ‖(p : ℂ_[p])‖ ^ m := by ring

/-! ## 5. Invariants of `B_dR` lie in `(B_dR^+)^×` (Tate's theorem) -/

theorem bdrAct_algebraMap (σ : GQp p) (z : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) :
    bdrAct p σ (algebraMap _ (BdR p) z) = algebraMap _ (BdR p) (DR.bdrPlusMap p (oAct p σ) z) := by
  rw [bdrAct, DR.bdrMap, IsLocalization.map_eq]

theorem isFR : IsFractionRing (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BdR p) := isFractionRing_BDeRham p

theorem alg_injective : Function.Injective (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BdR p)) := by
  haveI := isFR p
  exact IsFractionRing.injective _ _

theorem iZ_cyc_ne_zero (σ : GQp p) (k : ℕ) : iZ p (cyc p σ : ℤ_[p]) ^ k ≠ 0 :=
  pow_ne_zero _ (((cyc p σ).isUnit.map (iZ p)).ne_zero)

theorem tate_step (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (u : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ) (j k : ℕ)
    (h : ∀ σ ∈ K.fixingSubgroup, thetaPlusCp p u * iZ p (cyc p σ : ℤ_[p]) ^ k =
      cpAct p σ (thetaPlusCp p u) * iZ p (cyc p σ : ℤ_[p]) ^ j) : j = k := by
  by_contra hjk
  have hθ : thetaPlusCp p (u : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) ≠ 0 := (u.isUnit.map (thetaPlusCp p)).ne_zero
  apply hθ
  refine ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof p K ((j : ℤ) - k)
    (sub_ne_zero.mpr (by exact_mod_cast hjk)) _ fun σ hσ => ?_
  have hc : iZ p (((cyc p σ ^ ((j : ℤ) - k) : ℤ_[p]ˣ) : ℤ_[p])) * iZ p (cyc p σ : ℤ_[p]) ^ k =
      iZ p (cyc p σ : ℤ_[p]) ^ j := by
    rw [← map_pow, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      zpow_sub, zpow_natCast, zpow_natCast, inv_mul_cancel_right]
  rw [Algebra.smul_def]
  change iZ p (((cyc p σ ^ ((j : ℤ) - k) : ℤ_[p]ˣ) : ℤ_[p])) * _ = _
  apply mul_right_cancel₀ (iZ_cyc_ne_zero p σ k)
  rw [mul_right_comm, hc, mul_comm, h σ hσ]

/-- **Every nonzero `G_K`-invariant of `B_dR` is a unit of `B_dR^+`** (Tate's theorem). -/
theorem key (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (x : BdR p) (hx0 : x ≠ 0)
    (hx : ∀ σ ∈ K.fixingSubgroup, bdrAct p σ x = x) :
    ∃ u : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ, x = algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BdR p) u := by
  haveI := isFR p
  haveI := isDiscreteValuationRing_BDeRhamPlus p
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) x
  dsimp only at hab
  have hb0 : (b : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx0
    rw [← hab, IsLocalization.mk'_zero]
  obtain ⟨j, ua, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 (irreducible_T p)
  obtain ⟨k, ub, hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 (irreducible_T p)
  set u := ua * ub⁻¹ with hu
  have hspec := IsLocalization.mk'_spec (BdR p) a b
  rw [hab, hb, ha] at hspec
  have hx1 : x * algebraMap _ (BdR p) (T p ^ k) = algebraMap _ (BdR p) ((u : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) * T p ^ j) := by
    have e1 : x * algebraMap _ (BdR p) (T p ^ k) = x * algebraMap _ (BdR p) ((ub : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) * T p ^ k) *
        algebraMap _ (BdR p) ((ub⁻¹ : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)ˣ) : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := by
      rw [mul_assoc, ← map_mul, mul_right_comm, Units.mul_inv, one_mul]
    rw [e1, hspec, ← map_mul, hu, Units.val_mul]
    congr 1
    ring
  have hjk : j = k := by
    apply tate_step p K u j k
    intro σ hσ
    obtain ⟨w, hw, hθw⟩ := bdrPlus_T p σ
    have h2 := congrArg (bdrAct p σ) hx1
    have e1 : DR.bdrPlusMap p (oAct p σ) (T p ^ k) = (T p * w) ^ k := by rw [map_pow, hw]
    have e2 : DR.bdrPlusMap p (oAct p σ) ((u : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) * T p ^ j) =
        DR.bdrPlusMap p (oAct p σ) u * (T p * w) ^ j := by rw [map_mul, map_pow, hw]
    rw [map_mul, hx σ hσ, bdrAct_algebraMap, bdrAct_algebraMap, e1, e2] at h2
    have h3 : algebraMap _ (BdR p) ((u : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) * T p ^ j * w ^ k) =
        algebraMap _ (BdR p) (DR.bdrPlusMap p (oAct p σ) u * (T p * w) ^ j) := by
      rw [← h2, mul_pow, map_mul (algebraMap _ (BdR p)) (T p ^ k), ← mul_assoc, hx1, ← map_mul]
    have h4 := alg_injective p h3
    have h5 : (u : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) * w ^ k = DR.bdrPlusMap p (oAct p σ) u * w ^ j := by
      apply mul_left_cancel₀ (pow_ne_zero j (T_ne_zero p))
      linear_combination h4
    have h6 := congrArg (thetaPlusCp p) h5
    rw [map_mul, map_mul, map_pow, map_pow, thetaPlusCp_bdrPlusMap, hθw] at h6
    exact h6
  subst hjk
  refine ⟨u, ?_⟩
  have hunit : IsUnit (algebraMap _ (BdR p) (T p ^ j)) :=
    IsLocalization.map_units (BdR p)
      (⟨T p ^ j, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (T_ne_zero p))⟩ :
        nonZeroDivisors (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))
  apply hunit.mul_right_cancel
  rw [hx1, map_mul]

/-! ## 6. `B_dR^{G_F} ≅ F` -/

/-- **`DeRhamPrint.BdRInvariantsPrinted`, proved**: `dim_{ℚ_p} B_dR^{G_F} = [F : ℚ_p]`. -/
theorem bdRInvariantsPrinted_proof : DeRhamPrint.BdRInvariantsPrinted := by
  intro p _ F _ _ _
  letI := algPlus p
  have hrange := range_gfToGqp_eq p F
  have hS : ∀ σ : Field.absoluteGaloisGroup F, gfToGqp p F σ ∈ (fieldF p F).fixingSubgroup := fun σ => by
    have h : gfToGqp p F σ ∈ Set.range (gfToGqp p F) := ⟨σ, rfl⟩
    rw [hrange] at h
    exact h
  have hS' : ∀ τ ∈ (fieldF p F).fixingSubgroup, ∃ σ, gfToGqp p F σ = τ := fun τ hτ => by
    have h : τ ∈ ((fieldF p F).fixingSubgroup : Set (GQp p)) := hτ
    rw [← hrange] at h
    exact h
  have hfix : ∀ x ∈ DeRhamPrint.bdrFix p F, ∀ τ ∈ (fieldF p F).fixingSubgroup, bdrAct p τ x = x := by
    intro x hx τ hτ
    obtain ⟨σ, rfl⟩ := hS' τ hτ
    exact hx σ
  let ιΩ : F →ₐ[ℚ_[p]] ℂ_[p] := (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (phiF p F)
  have hιΩ : ∀ y, ιΩ y = ((phiF p F y : PadicAlgCl p) : ℂ_[p]) := fun y => rfl
  obtain ⟨ι₀, hι₀⟩ := exists_hensel_lift (thetaAlg p) (thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) ιΩ
  have hfixΩ : ∀ τ ∈ (fieldF p F).fixingSubgroup, ∀ y, cpAct p τ (ιΩ y) = ιΩ y := by
    intro τ hτ y
    have h := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ (phiF p F y) (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
    rw [hιΩ, cpAct_coe, h]
  have hinv : ∀ τ ∈ (fieldF p F).fixingSubgroup, ∀ y, DR.bdrPlusMap p (oAct p τ) (ι₀ y) = ι₀ y := by
    intro τ hτ y
    exact hensel_lift_natural (thetaAlg p) ιΩ ι₀ hι₀ (sPlus p τ) (AlgHom.id _ _) (fun x => by
      change thetaPlusCp p (DR.bdrPlusMap p (oAct p τ) (ι₀ x)) = ιΩ x
      rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, hι₀, hfixΩ τ hτ]) y
  let Φ : F →ₗ[ℚ_[p]] DeRhamPrint.bdrFix p F :=
    { toFun := fun y => ⟨algebraMap _ (BdR p) (ι₀ y), fun σ => by rw [bdrAct_algebraMap, hinv _ (hS σ)]⟩
      map_add' := fun y z => Subtype.ext (by
        change algebraMap _ (BdR p) (ι₀ (y + z)) = algebraMap _ (BdR p) (ι₀ y) + algebraMap _ (BdR p) (ι₀ z)
        rw [map_add, map_add])
      map_smul' := fun c y => by
        apply Subtype.ext
        rw [RingHom.id_apply, Submodule.coe_smul]
        dsimp only
        rw [map_smul, Algebra.smul_def c (ι₀ y), map_mul, Algebra.smul_def]
        rfl }
  have hΦ : ∀ y, ((Φ y : DeRhamPrint.bdrFix p F) : BdR p) = algebraMap _ (BdR p) (ι₀ y) := fun y => rfl
  have hinj : Function.Injective Φ := by
    intro y z h
    have h1 := congrArg Subtype.val h
    rw [hΦ, hΦ] at h1
    exact ι₀.toRingHom.injective (alg_injective p h1)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨x, hx⟩
    by_cases hx0 : x = 0
    · subst hx0
      exact ⟨0, by rw [map_zero]; rfl⟩
    obtain ⟨u, rfl⟩ := key p (fieldF p F) x hx0 (hfix x hx)
    have hθ : ∀ τ ∈ (fieldF p F).fixingSubgroup, cpAct p τ (thetaPlusCp p u) = thetaPlusCp p u := by
      intro τ hτ
      have h1 := hfix _ hx τ hτ
      rw [bdrAct_algebraMap] at h1
      rw [← thetaPlusCp_bdrPlusMap, alg_injective p h1]
    obtain ⟨y', hy'⟩ := ZInQ.Contrib.CloudB3W11.axSenTate_proof p (fieldF p F) _ hθ
    obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange (f := phiF p F)).mp y'.2
    refine ⟨y, Subtype.ext ?_⟩
    rw [hΦ]
    by_contra hne
    set z := algebraMap _ (BdR p) (u : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) - algebraMap _ (BdR p) (ι₀ y) with hz
    have hz0 : z ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0).symm
    have hzfix : ∀ τ ∈ (fieldF p F).fixingSubgroup, bdrAct p τ z = z := by
      intro τ hτ
      rw [hz, map_sub, bdrAct_algebraMap, bdrAct_algebraMap, hinv τ hτ]
      congr 1
      have h1 := hfix _ hx τ hτ
      rwa [bdrAct_algebraMap] at h1
    obtain ⟨u₂, hu₂⟩ := key p (fieldF p F) z hz0 hzfix
    rw [hz, ← map_sub] at hu₂
    have h2 := alg_injective p hu₂
    have h3 : thetaPlusCp p (u₂ : BDeRhamPlus (𝓞_ℂ_[p] : Type) p) = 0 := by
      rw [← h2, map_sub, hy', ← thetaAlg_apply, hι₀, hιΩ, hy, sub_self]
    exact (u₂.isUnit.map (thetaPlusCp p)).ne_zero h3
  exact (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq.symm

end

end BdRInv

