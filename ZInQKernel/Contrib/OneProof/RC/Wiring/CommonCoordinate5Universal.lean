import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5Objects

/-!
# Theorem 5.3, Lane RC32: the universal correction `η ∈ 𝒪[G]` and its character values

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex 4148–4149, 4196–4229, 4297–4327):
"For a finite binary family the universal correction `η` lies in `𝒪[G]`" and its value at a
character `x` is the `η_x` that multiplies the relaxed coordinate. Over the genuine
`𝒪 = (Λ_{(2)})^` (lane RC7's `OO`, a DVR by lane RC20) and `G = 𝔽₂^b`:

Each object: tex lines; here; kind.

* `g_q ∈ G ⊂ 𝒪[G]`: tex 4283–4285; `gU`; definition.
* `z_q = [ε(F̃r_q)](1 + t)`, `z_q⁻¹` (lift choice `c`): tex 4286–4291, 4297–4299; `zU`, `ziU`,
  `zU_mul_ziU`; definition, PROVED.
* `e_q = a_q − z_q − z_q⁻¹ ∈ 𝒪[G]^×`: tex 4196–4206; `eU`, `isUnit_eU`; definition, PROVED.
* `l_q`: tex 4209–4213; `lU`; definition.
* `v_q`, `l_q/e_q² = 1 + 2v_q`: tex 4214–4220, 4310–4318; `vU`, `lU_mul_eiU_sq`; definition (the
  text's formula), PROVED.
* `η = ∏_{q ∈ Q} (1 + v_q(1 + g_q)) ∈ 𝒪[G]`: tex 4221–4224; `etaU`; definition.
* `x(η)` is `η_x`: tex 4221–4231; `eval_etaU`; PROVED.
* `η` is independent of the Frobenius lifts: tex 4297–4306; `etaU_lift_independent`; PROVED.

`eval_etaU` is the honest form of "evaluate `η` at `x`": the value `x(η) ∈ 𝒪` and the element
`η_x ∈ F = Frac Λ` of `CommonCoordinate5Objects.lean` have the same image in `Frac 𝒪`, under
lane RC20's embedding `ι : Frac Λ → Frac 𝒪` (`iotaO`). There is no map `𝒪 → ℚ₂[[t]]` fixing `t`
(`t` is a unit of `𝒪`), nor is there a ring map `𝒪 → F` fixing `t` (`1 + 8t⁻¹` is a square in `𝒪`,
not in `F`): `η_x` is the `ι`-preimage of `x(η)`, which is why `η_x` is read in `F`, where it may
have a pole at `t = 0`.

DEPARTURE (proof only): the unit property of `e_q` is checked, as in the text, modulo the maximal
ideal `(2, I_G)` (augmentation, then reduction modulo `2`); the nonvanishing of `ē_q` is read on
its `t²` coefficient, which needs no parity of `a_q`. The text computes `ē_q = t²/(1 + t)` using
that `a_q` is even (tex 4200–4204; PROVED for good `q` as `apE_even`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform
  ZInQ.Manuscript.RC.Rings ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Determinant (OO lamToO SignGroup sgnChar signEval aug signGroup_mul_self)

/-- **`𝒪[G]`** for `G = 𝔽₂^b` (tex 2747–2751, 4148–4149). -/
abbrev OG (b : ℕ) : Type := MonoidAlgebra OO (SignGroup b)

/-- `Λ → 𝒪 → 𝒪[G]`. -/
abbrev lamToOG (b : ℕ) : Lambda →+* OG b := (algebraMap OO (OG b)).comp lamToO

/-- **`g_q ∈ 𝒪[G]`** (tex 4283–4285). -/
def gU (Fam : Family) (q : ℕ) : OG Fam.b := MonoidAlgebra.of OO _ (inertiaGen Fam q)

/-- **`z_q = [ε(F̃r_q)] (1 + t) ∈ 𝒪[G]`**, defined with a Frobenius lift of choice `c` (tex
4286–4291; "Fix a lift of arithmetic Frobenius at the chosen orientation and define `z_q` using
that lift"). -/
def zU (Fam : Family) (q : ℕ) (c : ZMod 2) : OG Fam.b :=
  MonoidAlgebra.single (frobLift Fam q c) (lamToO (onePlusT : Lambda))

/-- `z_q⁻¹ = [ε(F̃r_q)] (1 + t)⁻¹` (`ε(F̃r_q)² = 1`). -/
def ziU (Fam : Family) (q : ℕ) (c : ZMod 2) : OG Fam.b :=
  MonoidAlgebra.single (frobLift Fam q c) (lamToO ((onePlusT⁻¹ : Lambdaˣ) : Lambda))

theorem zU_mul_ziU (Fam : Family) (q : ℕ) (c : ZMod 2) : zU Fam q c * ziU Fam q c = 1 := by
  rw [zU, ziU, MonoidAlgebra.single_mul_single, signGroup_mul_self, ← map_mul, Units.mul_inv,
    map_one, MonoidAlgebra.one_def]

/-- **`e_q = a_q − z_q − z_q⁻¹ ∈ 𝒪[G]`** (tex 4145, 4196–4206). -/
def eU (ℓ : ℕ) (Fam : Family) (q : ℕ) (c : ZMod 2) : OG Fam.b :=
  pointFactor (apE ℓ q : OG Fam.b) (zU Fam q c) (ziU Fam q c)

/-- `q⁻¹ ∈ 𝒪[G]` (from `ℤ₂`; tex 4318–4320). -/
def qiU (b : ℕ) (q : ℕ) : OG b := lamToOG b (PowerSeries.C (qInv q))

/-- **`l_q ∈ 𝒪[G]`** through `tr Fr_q = a_q`, `det Fr_q = q` (tex 4209–4213). -/
def lU (ℓ : ℕ) (Fam : Family) (q : ℕ) (c : ZMod 2) : OG Fam.b :=
  quotPoly (apE ℓ q : OG Fam.b) (q : OG Fam.b) (qiU Fam.b q) (zU Fam q c) (ziU Fam q c)

/-- `e_q⁻¹ ∈ 𝒪[G]` (`isUnit_eU`). -/
def eiU (ℓ : ℕ) (Fam : Family) (q : ℕ) (c : ZMod 2) : OG Fam.b := Ring.inverse (eU ℓ Fam q c)

/-- **`v_q ∈ 𝒪[G]`**, the text's formula
`v_q = ((q−1)/2) (−(q+1)e_q² + (q−1) − s_q e_q) q⁻² e_q⁻²`, `s_q = z_q + z_q⁻¹` (tex 4310–4316). -/
def vU (ℓ : ℕ) (Fam : Family) (q : ℕ) (c : ZMod 2) : OG Fam.b :=
  (((q - 1) / 2 : ℕ) : OG Fam.b) *
    (-((q : OG Fam.b) + 1) * eU ℓ Fam q c ^ 2 + ((q : OG Fam.b) - 1) -
      (zU Fam q c + ziU Fam q c) * eU ℓ Fam q c) * qiU Fam.b q ^ 2 * eiU ℓ Fam q c ^ 2

/-- **The universal correction `η = ∏_{q ∈ Q} (1 + v_q(1 + g_q)) ∈ 𝒪[G]`** (tex 4221–4224), with
lift choices `c`. -/
def etaU (ℓ : ℕ) (Fam : Family) (c : ℕ → ZMod 2) : OG Fam.b :=
  Central.eta Fam.Q (fun q => vU ℓ Fam q (c q)) (gU Fam)

/-! ## `e_q` is a unit of `𝒪[G]` -/

/-- `2` is not a unit of `ℤ₂` (PROVED). -/
theorem not_isUnit_two_zTwo : ¬ IsUnit (2 : ℤ_[2]) := by
  intro h
  have h1 := PadicInt.isUnit_iff.mp h
  have h2 : ‖((2 : ℕ) : ℤ_[2])‖ = ((2 : ℕ) : ℝ)⁻¹ := PadicInt.norm_p
  push_cast at h2
  rw [h2] at h1
  norm_num at h1

/-- **`e_q(x) ∉ (2)`** in `Λ` (PROVED): the `t²` coefficient of `(1 + t) e_q(x)` is `−σ = ∓1`,
not divisible by `2`. -/
theorem ptFac_not_mem_span_two (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    ptFac ℓ Fam x q ∉ Ideal.span {(2 : Lambda)} := by
  intro hmem
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  have h := one_add_X_mul_ptFac ℓ Fam x q
  rw [← hg] at h
  set σ : ℤ := (frobSign Fam x q : ℤ) with hσdef
  have key : (apE ℓ q : Lambda) * (1 + PowerSeries.X) - (σ : Lambda) * (1 + PowerSeries.X) ^ 2 -
      (σ : Lambda) = PowerSeries.C ((apE ℓ q : ℤ_[2]) - 2 * (σ : ℤ_[2])) * (1 + PowerSeries.X) -
        PowerSeries.C (σ : ℤ_[2]) * PowerSeries.X ^ 2 := by
    simp only [map_sub, map_mul, map_intCast, map_ofNat]
    ring
  rw [key] at h
  have hc : ∀ c : ℤ_[2], PowerSeries.coeff 2 (PowerSeries.C c * (1 + PowerSeries.X)) = 0 := by
    intro c
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_one, PowerSeries.coeff_X]
  have hs2 : PowerSeries.coeff 2 (PowerSeries.C (σ : ℤ_[2]) * PowerSeries.X ^ 2) = (σ : ℤ_[2]) := by
    rw [PowerSeries.coeff_C_mul_X_pow, ite_eq_left rfl]
  have h2 := congrArg (PowerSeries.coeff 2) h
  rw [map_sub, hc, hs2, zero_sub] at h2
  have h2' : PowerSeries.coeff 2 ((1 + PowerSeries.X) * (g * 2)) =
      2 * PowerSeries.coeff 2 ((1 + PowerSeries.X) * g) := by
    rw [show (1 + PowerSeries.X) * (g * 2) = PowerSeries.C (2 : ℤ_[2]) * ((1 + PowerSeries.X) * g)
      by rw [map_ofNat]; ring, PowerSeries.coeff_C_mul]
  rw [h2'] at h2
  apply not_isUnit_two_zTwo
  rcases Int.units_eq_one_or (frobSign Fam x q) with hs | hs
  · refine IsUnit.of_mul_eq_one (-PowerSeries.coeff 2 ((1 + PowerSeries.X) * g)) ?_
    rw [hσdef, hs] at h2
    push_cast at h2
    linear_combination -h2
  · refine IsUnit.of_mul_eq_one (PowerSeries.coeff 2 ((1 + PowerSeries.X) * g)) ?_
    rw [hσdef, hs] at h2
    push_cast at h2
    linear_combination h2

/-- The augmentation of `z_q` and `z_q⁻¹` (PROVED). -/
theorem aug_zU (Fam : Family) (q : ℕ) (c : ZMod 2) :
    aug (zU Fam q c) = lamToO (onePlusT : Lambda) := by
  rw [zU, Determinant.aug_single]

theorem aug_ziU (Fam : Family) (q : ℕ) (c : ZMod 2) :
    aug (ziU Fam q c) = lamToO ((onePlusT⁻¹ : Lambdaˣ) : Lambda) := by
  rw [ziU, Determinant.aug_single]

/-- At the augmentation every sign is `1` (PROVED). -/
theorem frobSign_zero (Fam : Family) (q : ℕ) : frobSign Fam 0 q = 1 := by
  rw [frobSign, Determinant.sgnChar_zero]; rfl

/-- **`e_q ∈ 𝒪[G]^×`** (tex 4196–4206): modulo `(2, I_G)` the element `e_q` reduces to the
reduction of `e_q(0) = a_q − (1 + t) − (1 + t)⁻¹`, which is not in `(2)`. PROVED. -/
theorem isUnit_eU (ℓ : ℕ) (Fam : Family) (q : ℕ) (c : ZMod 2) : IsUnit (eU ℓ Fam q c) := by
  rw [Determinant.isUnit_iff_isUnit_aug Determinant.isUnit_one_add_two_mul_OO signGroup_mul_self]
  have haug : aug (eU ℓ Fam q c) = lamToO (ptFac ℓ Fam 0 q) := by
    rw [eU, ptFac, pointFactor, pointFactor, map_sub, map_sub, aug_zU, aug_ziU, map_intCast,
      map_sub, map_sub, map_intCast]
    congr 2
    · simp [zAt, frobSign_zero]
    · simp [zAt, frobSign_zero]
  rw [haug]
  exact Determinant.isUnit_algebraMap_of_not_mem_span_two _ (ptFac_not_mem_span_two ℓ Fam 0 q)

/-! ## `l_q/e_q² = 1 + 2 v_q` in `𝒪[G]` -/

/-- The companion matrix `[[0, −q], [1, a]]` (trace `a`, determinant `q`); `l_q` only depends on
the trace and the determinant of `Fr_q` (tex 4213). -/
def companion {K : Type*} [CommRing K] (a q : K) : Matrix (Fin 2) (Fin 2) K := !![0, -q; 1, a]

theorem companion_trace {K : Type*} [CommRing K] (a q : K) : (companion a q).trace = a := by
  simp [companion, Matrix.trace_fin_two]

theorem companion_det {K : Type*} [CommRing K] (a q : K) : (companion a q).det = q := by
  simp [companion, Matrix.det_fin_two]

/-- `q q⁻¹ = 1` in `𝒪[G]` for odd `q` (PROVED). -/
theorem natCast_mul_qiU {b q : ℕ} (hq : Odd q) : (q : OG b) * qiU b q = 1 := by
  have hu : IsUnit (q : ℤ_[2]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr (Nat.coprime_two_left.mpr hq))
  rw [qiU, ← map_natCast (lamToOG b), ← map_mul,
    show ((q : Lambda) * PowerSeries.C (qInv q)) = PowerSeries.C ((q : ℤ_[2]) * qInv q) by
      rw [map_mul, map_natCast], qInv, Ring.mul_inverse_cancel _ hu, map_one, map_one]

/-- **`l_q / e_q² = 1 + 2 v_q`, so `l_q/e_q² − 1 ∈ 2𝒪[G]`** (tex 4214–4220, 4310–4318; lane
RC15's `quotientFactor_mul_inv_sq`). PROVED for odd `q`. -/
theorem lU_mul_eiU_sq (ℓ : ℕ) (Fam : Family) {q : ℕ} (hq : Odd q) (c : ZMod 2) :
    lU ℓ Fam q c * eiU ℓ Fam q c ^ 2 = 1 + 2 * vU ℓ Fam q c := by
  have hqi := natCast_mul_qiU (b := Fam.b) hq
  have hz := zU_mul_ziU Fam q c
  have he : eU ℓ Fam q c * eiU ℓ Fam q c = 1 := Ring.mul_inverse_cancel _ (isUnit_eU ℓ Fam q c)
  have hodd : (q : OG Fam.b) = 1 + 2 * (((q - 1) / 2 : ℕ) : OG Fam.b) := by
    obtain ⟨k, rfl⟩ := hq
    have : (2 * k + 1 - 1) / 2 = k := by omega
    rw [this]; push_cast; ring
  have h := quotientFactor_mul_inv_sq (F := companion (apE ℓ q : OG Fam.b) (q : OG Fam.b))
    hqi hz (companion_trace _ _) (companion_det _ _) hodd he
  rw [quotientFactor_eq_quotPoly _ _ _ (companion_trace _ _) (companion_det _ _)] at h
  exact h

/-! ## The character values of the universal objects -/

/-- `signEval` of `single g (lamToO u)` (PROVED). -/
theorem signEval_single_lamToO {b : ℕ} (x : Addr b) (g : SignGroup b) (u : Lambda) :
    signEval (sgnChar x) (MonoidAlgebra.single g (lamToO u) : OG b) =
      lamToO (((sgnChar x g : ℤˣ) : ℤ) * u) := by
  rw [Determinant.signEval_single, map_mul, map_intCast, mul_comm]

theorem signEval_zU (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    signEval (sgnChar x) (zU Fam q 0) = lamToO (zAt Fam x q : Lambda) := by
  rw [zU, signEval_single_lamToO]
  congr 1

theorem signEval_ziU (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    signEval (sgnChar x) (ziU Fam q 0) = lamToO ((zAt Fam x q)⁻¹ : Lambdaˣ) := by
  rw [ziU, signEval_single_lamToO]
  congr 1
  rw [zAt, mul_inv, Units.val_mul, ← map_inv]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, eq_intCast,
    Int.units_inv_eq_self, frobSign]

theorem signEval_eU (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    signEval (sgnChar x) (eU ℓ Fam q 0) = lamToO (ptFac ℓ Fam x q) := by
  rw [eU, ptFac, pointFactor, pointFactor, map_sub, map_sub, map_intCast, signEval_zU,
    signEval_ziU, map_sub, map_sub, map_intCast]

theorem signEval_lU (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    signEval (sgnChar x) (lU ℓ Fam q 0) = lamToO (quotFac ℓ Fam x q) := by
  have hq : signEval (sgnChar x) (qiU Fam.b q) = lamToO (PowerSeries.C (qInv q)) := by
    rw [qiU, RingHom.comp_apply, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  rw [lU, quotFac, ← AlgHom.coe_toRingHom, map_quotPoly, map_quotPoly, map_intCast, map_natCast]
  simp only [AlgHom.coe_toRingHom, signEval_zU, signEval_ziU, hq, map_intCast, map_natCast]

theorem signEval_gU (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    signEval (sgnChar x) (gU Fam q) = (((sgnChar x (inertiaGen Fam q) : ℤˣ) : ℤ) : OO) := by
  rw [gU, Determinant.signEval_of]

/-- `Central.eta` commutes with ring homomorphisms (PROVED). -/
theorem map_eta_hom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*}
    (Q : Finset ι) (v g : ι → R) :
    f (Central.eta Q v g) = Central.eta Q (fun q => f (v q)) (fun q => f (g q)) := by
  simp only [Central.eta, Central.correctionFactor, map_prod, map_add, map_mul, map_one]

/-- `2 ≠ 0` in `Frac 𝒪` (PROVED). -/
theorem two_ne_zero_fracO : (2 : FractionRing OO) ≠ 0 := by
  have := (map_ne_zero_iff (algebraMap OO (FractionRing OO))
    (IsFractionRing.injective OO (FractionRing OO))).mpr two_ne_zero_OO
  rwa [map_ofNat] at this

/-- **The character value of the universal correction is `η_x`** (tex 4221–4231): for a family
with odd graph primes and the lift choice `0`, `x(η) ∈ 𝒪` and `η_x ∈ F` have the same image in
`Frac 𝒪`. PROVED. -/
theorem eval_etaU (ℓ : ℕ) (Fam : Family) (hodd : ∀ q ∈ Fam.Q, Odd q) (x : Addr Fam.b) :
    algebraMap OO (FractionRing OO) (signEval (sgnChar x) (etaU ℓ Fam fun _ => 0)) =
      iotaO (etaF ℓ Fam x) := by
  set ψ : OG Fam.b →+* FractionRing OO :=
    (algebraMap OO (FractionRing OO)).comp (Determinant.signEval (sgnChar x)).toRingHom with hψ
  have hψa : ∀ s, ψ s = algebraMap OO (FractionRing OO) (Determinant.signEval (sgnChar x) s) :=
    fun _ => rfl
  rw [← hψa, etaU, etaF, map_eta_hom, map_eta_hom]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hg : ψ (gU Fam q) = iotaO (gF Fam x q) := by
    rw [hψa, signEval_gU, gF, map_intCast, map_intCast]
  have he : ψ (eU ℓ Fam q 0) = iotaO (eF ℓ Fam x q) := by
    rw [hψa, signEval_eU, eF, iotaO_algebraMap]
  have hl : ψ (lU ℓ Fam q 0) = iotaO (lF ℓ Fam x q) := by
    rw [hψa, signEval_lU, lF, iotaO_algebraMap]
  have hei : ψ (eiU ℓ Fam q 0) = (iotaO (eF ℓ Fam x q))⁻¹ := by
    have h1 : ψ (eU ℓ Fam q 0) * ψ (eiU ℓ Fam q 0) = 1 := by
      rw [← map_mul, eiU, Ring.mul_inverse_cancel _ (isUnit_eU ℓ Fam q 0), map_one]
    rw [he] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hv : ψ (vU ℓ Fam q 0) = iotaO (vF ℓ Fam x q) := by
    have h := congrArg ψ (lU_mul_eiU_sq ℓ Fam (hodd q hq) 0)
    rw [map_mul, map_pow, map_add, map_one, map_mul, map_ofNat, hl, hei] at h
    have h' : iotaO (lF ℓ Fam x q) / iotaO (eF ℓ Fam x q) ^ 2 = 1 + 2 * ψ (vU ℓ Fam q 0) := by
      rw [div_eq_mul_inv, ← inv_pow]; exact h
    rw [vF, map_div₀, map_sub, map_div₀, map_pow, map_one, map_ofNat, h']
    field_simp [two_ne_zero_fracO]
    ring
  simp only [Central.correctionFactor, hg, hv]

/-! ## The correction does not depend on the Frobenius lift (tex 4297–4306) -/

/-- `𝒪[G]` has no two-torsion ("Since `R` is two-torsion-free", tex 4301–4302; PROVED). -/
theorem og_two_torsion_free {b : ℕ} (y : OG b) (h : 2 * y = 0) : y = 0 := by
  rw [two_mul] at h
  apply MonoidAlgebra.ext
  refine Finsupp.ext fun g => ?_
  have h1 := congrArg (fun f : OG b => f.coeff g) h
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at h1
  have h2 : (2 : OO) * y.coeff g = 0 := by rw [two_mul]; exact h1
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' two_ne_zero_OO
  · simpa using h'

/-- Changing the lift multiplies its image in `G` by `g_q` (tex 4290–4291; PROVED). -/
theorem frobLift_one (Fam : Family) (q : ℕ) :
    frobLift Fam q 1 = frobLift Fam q 0 * inertiaGen Fam q := by
  rw [frobLift, frobLift, inertiaGen, ← ofAdd_add]
  congr 1
  simp [frobLiftVec]

theorem zU_one (Fam : Family) (q : ℕ) : zU Fam q 1 = zU Fam q 0 * gU Fam q := by
  rw [zU, zU, gU, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, frobLift_one]

theorem ziU_one (Fam : Family) (q : ℕ) : ziU Fam q 1 = ziU Fam q 0 * gU Fam q := by
  rw [ziU, ziU, gU, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one,
    frobLift_one]

theorem gU_sq (Fam : Family) (q : ℕ) : gU Fam q ^ 2 = 1 := by
  rw [gU, ← map_pow, pow_two, signGroup_mul_self, map_one]

/-- **The correction factor `1 + v_q(1 + g_q)` does not depend on the Frobenius lift** (tex
4297–4306: both choices give units `e_q`, the ratios agree in `R/(g_q − 1)`, so
`(1 + g_q)(v'_q − v_q) = 0`; lane RC15's `ratio_agree_mod` and `correction_lift_independent`).
PROVED for odd `q`. -/
theorem correctionFactor_lift_independent (ℓ : ℕ) (Fam : Family) {q : ℕ} (hq : Odd q)
    (c : ZMod 2) :
    Central.correctionFactor (vU ℓ Fam q c) (gU Fam q) =
      Central.correctionFactor (vU ℓ Fam q 0) (gU Fam q) := by
  fin_cases c
  · rfl
  · change Central.correctionFactor (vU ℓ Fam q 1) (gU Fam q) = _
    have hz : zU Fam q 1 - zU Fam q 0 ∈ Ideal.span {gU Fam q - 1} :=
      Ideal.mem_span_singleton'.mpr ⟨zU Fam q 0, by rw [zU_one]; ring⟩
    have hzi : ziU Fam q 1 - ziU Fam q 0 ∈ Ideal.span {gU Fam q - 1} :=
      Ideal.mem_span_singleton'.mpr ⟨ziU Fam q 0, by rw [ziU_one]; ring⟩
    have he : eU ℓ Fam q 0 * eiU ℓ Fam q 0 = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_eU ℓ Fam q 0)
    have he' : eU ℓ Fam q 1 * eiU ℓ Fam q 1 = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_eU ℓ Fam q 1)
    have hagree := Central.ratio_agree_mod
      (F := companion (apE ℓ q : OG Fam.b) (q : OG Fam.b)) (qi := qiU Fam.b q) hz hzi he he'
    rw [quotientFactor_eq_quotPoly _ _ _ (companion_trace _ _) (companion_det _ _),
      quotientFactor_eq_quotPoly _ _ _ (companion_trace _ _) (companion_det _ _)] at hagree
    exact (Central.correction_lift_independent og_two_torsion_free (gU_sq Fam q)
      (lU_mul_eiU_sq ℓ Fam hq 0) (lU_mul_eiU_sq ℓ Fam hq 1) hagree).2

/-- **The universal correction `η` does not depend on the Frobenius lifts** (tex 4306: "The
correction `1 + (1 + g_q)v_q` is consequently independent of the lift"). PROVED. -/
theorem etaU_lift_independent (ℓ : ℕ) (Fam : Family) (hodd : ∀ q ∈ Fam.Q, Odd q)
    (c : ℕ → ZMod 2) : etaU ℓ Fam c = etaU ℓ Fam fun _ => 0 :=
  Finset.prod_congr rfl fun q hq => correctionFactor_lift_independent ℓ Fam (hodd q hq) (c q)

end ZInQ.Manuscript.RC.Wiring
