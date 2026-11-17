import ZInQKernel.Contrib.OneProof.PanBergerFontaine

/-!
# Transcendence of `log [p̃]`: `B_cris ⊆ B_max` and the Galois reduction (task logp-transc)

Report: `docs/research/logp-transc.md`. This file proves:

* **`B_cris ⊆ B_max`** inside `B_dR`, for every element `w` of `ker θ` used to write `A_cris`
  (`acrisOf_le_amax_any`, `bcrisPlusOf_le_bmaxPlus`, `bcrisOf_le_bmax`, `bstFOf_le_bst`). The existing
  `acrisOf_le_amax` needed `w` to generate `ker θ`; here any `w ∈ ker θ = (ξ)` is reduced to `ξ`.
* **The Galois reduction** (`transcendental_of_logCore`): for a `G_{ℚ_p}`-stable `ℚ_p`-subalgebra
  `B ⊆ B_dR` and `u ∈ B_dR` with `σ(u) − u ∈ B` for every `σ`, `u` is transcendental over `B` as soon as
  `u ∉ Frac(B) + B_dR^{G_{ℚ_p}}` (`LogCore`: no `a ≠ 0`, `b` in `B` and invariant `y` with `a(u − y) = b`).
  This is the minimal-polynomial argument (Brinon-Conrad p. 143 sketch / Fontaine; filled on the spot).
* Applied to `u = log [p̃]` (`σ(log [p̃]) = log [p̃] + log [u_σ]`, `log [u_σ] ∈ A_cris ⊆ A_max`):
  `logPTildeTranscendental_of_core` (over `B_max`, i.e. `BergerBst.LogPTildeTranscendental`) and
  `transcendental_bcris_of_core` (over `B_cris`).
* **Transfer to `B_cris` and `BstFOf`** (`transcendental_bcrisOf`, `bcrisPolyEquiv`, `bstFOf_eq_adjoin`):
  the transcendence over `B_max` gives the injectivity of `B_cris[X] → B_dR`, `X ↦ log [p̃]`, i.e.
  Brinon-Conrad Thm 9.2.10 at `K = ℚ_p`, and `BstFOf ≅ B_cris[X]`.
* **Converse** (`logCore_of_transcendental`): the transcendence over `B` gives `LogCore B` whenever
  `B_dR^{G_{ℚ_p}} ⊆ B`; so `LogCore` is exactly the remaining content.

* **Units** (§6, `unit_log_mem_amax`): for every unit `v ∈ ℤ_p^×`, `log([ν]/v) ∈ A_max` (`ν♯ = v`) with
  `σ(log([ν]/v)) = log([ν]/v) + log [u_σ]`, the Galois shape of `log [p̃]`; so the core cannot follow from that shape.
  By-products: `logOne_mem_amax` (`log z ∈ A_max` whenever `θ(z) = 1`), `untilt_flatOf` (`♯` is onto `𝓞_ℂ_p`).

The core `LogCore (B_max) (log [p̃])` itself is not proved: every proof known here uses the Frobenius of
`B_max` (see the report, §4).
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace HDec
namespace PkgI4
namespace LogPTransc

open Polynomial BergerBst FontaineSt BmaxOne
open PanBergerSplit (Ainf AinfP)

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## §1. `A_cris ⊆ A_max` for every `w ∈ ker θ`, hence `B_cris ⊆ B_max` and `B_st^F ⊆ B_st` -/

/-- **`A_cris ⊆ A_max`** for every `w ∈ ker θ` (not only generators): `w = ξ c`. -/
theorem acrisOf_le_amax_any {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    AcrisOf p w hw ⊆ (Amax p : Set (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
  have hk : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  exact (acrisOf_le p (theta_xi' p) hw c (by rw [← hc, mul_comm])).trans
    (acrisOf_le_amax p (theta_xi' p) (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p))

/-- **`B_cris^+ ⊆ B_max^+`.** -/
theorem bcrisPlusOf_le_bmaxPlus {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    BcrisPlusOf p w hw ≤ BmaxPlus p :=
  Algebra.adjoin_mono (Set.image_mono (acrisOf_le_amax_any p hw))

/-- **`B_cris ⊆ B_max`** inside `B_dR`. -/
theorem bcrisOf_le_bmax {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : BcrisOf p h w hw ≤ Bmax p := by
  rw [← bmaxOf_eq p h]
  apply Algebra.adjoin_mono
  rintro x (⟨y, hy, rfl⟩ | hx)
  · exact Or.inl ⟨y, acrisOf_le_amax_any p hw hy, rfl⟩
  · exact Or.inr hx

/-- **Fontaine's `B_st = B_cris[log [p̃]]` lies in `B_max[log [p̃]]`**, for every `w ∈ ker θ`. -/
theorem bstFOf_le_bst {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : BstFOf p h w hw ≤ Bst p := by
  rw [← bstOf_eq p h]
  apply Algebra.adjoin_mono
  rintro x ((⟨y, hy, rfl⟩ | hx) | hx)
  · exact Or.inl (Or.inl ⟨y, acrisOf_le_amax_any p hw hy, rfl⟩)
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

/-! ## §2. Two polynomial lemmas -/

/-- The coefficient of `X^{d−1}` of `f(X + r)`, `d = deg f ≥ 1`: `f_{d−1} + d r f_d`. -/
theorem coeff_taylor_pred {R : Type*} [CommRing R] (f : R[X]) (r : R) {d : ℕ}
    (hd : f.natDegree = d) (hd0 : d ≠ 0) :
    (taylor r f).coeff (d - 1) = f.coeff (d - 1) + d * r * f.coeff d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  rw [taylor_coeff]
  have hdeg : (hasseDeriv (n + 1 - 1) f).natDegree < 2 := by
    have := natDegree_hasseDeriv_le f (n + 1 - 1)
    omega
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_one, hasseDeriv_coeff,
    hasseDeriv_coeff]
  simp only [Nat.succ_sub_one, zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one,
    pow_one]
  rw [show 1 + n = n + 1 by omega, Nat.choose_succ_self_right]
  push_cast
  ring

/-! ## §3. The Galois reduction: `u ∉ Frac(B) + B_dR^G` implies `u` transcendental over `B` -/

/-- `B ⊆ B_dR` is stable under `G_{ℚ_p}`. -/
def GStable (B : Subalgebra ℚ_[p] (BdR p)) : Prop :=
  ∀ (σ : GQp p), ∀ x ∈ B, bdrAct p σ x ∈ B

/-- `σ` restricted to a stable `B`. -/
def sigB (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (σ : GQp p) : B →+* B :=
  RingHom.codRestrict ((bdrAct p σ).comp (algebraMap B (BdR p))) B (fun x => hB σ x x.2)

theorem sigB_coe (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (σ : GQp p) (x : B) :
    ((sigB p B hB σ x : B) : BdR p) = bdrAct p σ x := rfl

theorem bdrAct_injective (σ : GQp p) : Function.Injective (bdrAct p σ) := by
  have hF := ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p
  intro x y hxy
  by_contra hne
  obtain ⟨z, hz⟩ := hF.mul_inv_cancel (sub_ne_zero.mpr hne)
  have hz' : (x - y) * (show BdR p from z) = 1 := hz
  have h01 := congrArg (bdrAct p σ) hz'
  rw [map_mul, map_sub, hxy, sub_self, zero_mul, map_one] at h01
  have h0 : ∀ c : BdR p, c = 0 := fun c => by rw [← mul_one c, ← h01, mul_zero]
  obtain ⟨a, b, hab⟩ := hF.exists_pair_ne
  exact hab ((h0 a).trans (h0 b).symm)

theorem sigB_injective (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (σ : GQp p) :
    Function.Injective (sigB p B hB σ) := by
  intro x y hxy
  have h := congrArg (fun z : B => (z : BdR p)) hxy
  simp only [sigB_coe] at h
  exact Subtype.ext (bdrAct_injective p σ h)

theorem aeval_map_sigB (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (σ : GQp p) (P : B[X])
    (x : BdR p) :
    aeval (bdrAct p σ x) (P.map (sigB p B hB σ)) = bdrAct p σ (aeval x P) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  rfl

/-- **The core: `u ∉ Frac(B) + B_dR^{G_{ℚ_p}}`.** No `a ≠ 0`, `b` in `B` and `G_{ℚ_p}`-invariant
`y ∈ B_dR` with `a (u − y) = b`. -/
def LogCore (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p) : Prop :=
  ∀ a b : B, a ≠ 0 → ∀ y : BdR p, (∀ σ : GQp p, bdrAct p σ y = y) → (a : BdR p) * (u - y) ≠ b

/-- The relation on the two top coefficients of a minimal-degree relation `P(u) = 0`. -/
theorem top_coeff_relation (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (u : BdR p)
    (P : B[X]) {d : ℕ} (hPd : P.natDegree = d) (hd0 : d ≠ 0) (hPu : aeval u P = 0)
    (hmin : ∀ Q : B[X], Q ≠ 0 → aeval u Q = 0 → d ≤ Q.natDegree) (σ : GQp p) (δ : B)
    (hδ : bdrAct p σ u = u + δ) :
    sigB p B hB σ (P.coeff d) * P.coeff (d - 1) =
      P.coeff d * (sigB p B hB σ (P.coeff (d - 1)) + d * δ * sigB p B hB σ (P.coeff d)) := by
  set s := sigB p B hB σ
  set Pσ := taylor δ (P.map s) with hPσ
  have hPσu : aeval u Pσ = 0 := by
    rw [hPσ, taylor_apply, aeval_comp]
    simp only [map_add, aeval_X, aeval_C]
    rw [show u + algebraMap B (BdR p) δ = bdrAct p σ u from hδ.symm, aeval_map_sigB, hPu,
      map_zero]
  have hmapd : (P.map s).natDegree = d := by
    rw [natDegree_map_eq_of_injective (sigB_injective p B hB σ)]
    exact hPd
  set Q := C (s (P.coeff d)) * P + C (-P.coeff d) * Pσ with hQ
  have hQu : aeval u Q = 0 := by
    rw [hQ, map_add, map_mul, map_mul, hPu, hPσu, mul_zero, mul_zero, add_zero]
  have hQd : ∀ N, d - 1 < N → Q.coeff N = 0 := by
    intro N hN
    rw [hQ, coeff_add, coeff_C_mul, coeff_C_mul]
    rcases (show N = d ∨ d < N by omega) with rfl | hN'
    · have h1 := coeff_taylor_natDegree (r := δ) (f := P.map s)
      rw [hmapd] at h1
      rw [hPσ, h1, leadingCoeff, hmapd, coeff_map]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by rw [hPσ, natDegree_taylor, hmapd]; omega :
          Pσ.natDegree < N)]
      ring
  have hQ0 : Q = 0 := by
    by_contra hQne
    have h1 := hmin Q hQne hQu
    have h2 : Q.natDegree ≤ d - 1 := natDegree_le_iff_coeff_eq_zero.mpr hQd
    omega
  have hc := congrArg (fun R => R.coeff (d - 1)) hQ0
  simp only [hQ, coeff_add, coeff_C_mul, coeff_zero] at hc
  rw [hPσ, coeff_taylor_pred (P.map s) δ hmapd hd0, coeff_map, coeff_map] at hc
  linear_combination hc

/-- **The Galois reduction.** If `B ⊆ B_dR` is `G_{ℚ_p}`-stable, `σ(u) − u ∈ B` for every `σ`, and
`u ∉ Frac(B) + B_dR^{G_{ℚ_p}}` (`LogCore`), then `u` is transcendental over `B`.

Proof (minimal polynomial; Brinon-Conrad p. 143 sketch, steps filled on the spot): take `P ∈ B[X]`
nonzero of least degree `d` with `P(u) = 0`; `d ≥ 1`. For `σ` with `σ(u) = u + δ`,
`P_σ(X) = P^σ(X + δ)` has `P_σ(u) = σ(P(u)) = 0` and the same degree, so
`σ(a_d) P − a_d P_σ = 0` by minimality. Its `X^{d−1}` coefficient gives
`σ(b) = b − δ` for `b = a_{d−1}/(d a_d)`, so `y = u + b` is `G_{ℚ_p}`-invariant and
`a_d (u − y) = −a_{d−1}/d ∈ B`. -/
theorem transcendental_of_logCore (B : Subalgebra ℚ_[p] (BdR p)) (hB : GStable p B) (u : BdR p)
    (hu : ∀ σ : GQp p, ∃ δ : B, bdrAct p σ u = u + δ) (hcore : LogCore p B u) :
    Transcendental B u := by
  classical
  haveI : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
  rintro ⟨P0, hP00, hP0u⟩
  have hex : ∃ d : ℕ, ∃ P : B[X], P ≠ 0 ∧ P.natDegree = d ∧ aeval u P = 0 :=
    ⟨_, P0, hP00, rfl, hP0u⟩
  obtain ⟨P, hP0, hPd, hPu⟩ := Nat.find_spec hex
  have hmin : ∀ Q : B[X], Q ≠ 0 → aeval u Q = 0 → Nat.find hex ≤ Q.natDegree :=
    fun Q hQ hQu => Nat.find_min' hex ⟨Q, hQ, rfl, hQu⟩
  set d := Nat.find hex with hd_def
  have ha0 : P.coeff d ≠ 0 := by
    rw [← hPd]
    exact leadingCoeff_ne_zero.mpr hP0
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hPd
    rw [eq_C_of_natDegree_eq_zero hPd, aeval_C] at hPu
    apply ha0
    rw [h0]
    exact Subtype.ext hPu
  have haB : ((P.coeff d : B) : BdR p) ≠ 0 := fun h => ha0 (Subtype.ext h)
  have hdB : ((d : ℕ) : BdR p) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[p] (BdR p))]
    exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd0)
  set a : BdR p := ((P.coeff d : B) : BdR p) with ha_def
  set b : BdR p := ((P.coeff (d - 1) : B) : BdR p) with hb_def
  have hda : (d : BdR p) * a ≠ 0 := mul_ne_zero hdB haB
  have hinv : ∃ e : BdR p, (d : BdR p) * a * e = 1 :=
    (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hda
  obtain ⟨e, he'⟩ := hinv
  set y : BdR p := u + b * e with hy_def
  have hy : ∀ σ : GQp p, bdrAct p σ y = y := by
    intro σ
    obtain ⟨δ, hδ⟩ := hu σ
    have hr := congrArg (fun z : B => (z : BdR p))
      (top_coeff_relation p B hB u P hPd hd0 hPu hmin σ δ hδ)
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, sigB_coe, SubringClass.coe_natCast] at hr
    have hX := congrArg (bdrAct p σ) he'
    rw [map_mul, map_mul, map_natCast, map_one] at hX
    rw [hy_def, map_add, map_mul, hδ]
    linear_combination (b * e - (δ : BdR p) * ((d : BdR p) * a) * e) * hX +
      (-(δ : BdR p) - bdrAct p σ b * bdrAct p σ e) * he' +
      (-(d : BdR p) * bdrAct p σ e * e) * hr
  have hq : algebraMap ℚ_[p] (BdR p) ((d : ℚ_[p])⁻¹) * (d : BdR p) = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (BdR p)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd0), map_one]
  refine hcore (P.coeff d) (-(algebraMap ℚ_[p] B ((d : ℚ_[p])⁻¹) * P.coeff (d - 1))) ha0 y hy ?_
  show a * (u - (u + b * e)) = -(algebraMap ℚ_[p] (BdR p) ((d : ℚ_[p])⁻¹) * b)
  linear_combination (-(algebraMap ℚ_[p] (BdR p) ((d : ℚ_[p])⁻¹)) * b) * he' + (a * b * e) * hq

/-- **Converse.** If `B_dR^{G_{ℚ_p}} ⊆ B` and `u` is transcendental over `B`, then `LogCore B u`. -/
theorem logCore_of_transcendental (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p)
    (hinv : ∀ y : BdR p, (∀ σ : GQp p, bdrAct p σ y = y) → y ∈ B) (ht : Transcendental B u) :
    LogCore p B u := by
  intro a b ha y hy he
  apply ht
  refine ⟨C a * X + C (-(b + a * ⟨y, hinv y hy⟩)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun R => R.coeff 1) h0
    simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero, ite_false,
      add_zero, coeff_zero] at h1
    exact ha h1
  · rw [map_add, map_mul, aeval_C, aeval_X, aeval_C]
    change (a : BdR p) * u + -((b : BdR p) + a * y) = 0
    rw [← he]
    ring

/-- **The core in its sharp form: `u ∉ Frac(B)`.** -/
def NotInFrac (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p) : Prop :=
  ∀ a b : B, a ≠ 0 → (a : BdR p) * u ≠ b

/-- With `B_dR^{G_{ℚ_p}} = ℚ_p` (element form; Fontaine, proved in dimension form in the tree as
`BdRInv.bdRInvariantsPrinted_proof`), `u ∉ Frac(B)` is the core. -/
theorem logCore_of_notInFrac (B : Subalgebra ℚ_[p] (BdR p)) (u : BdR p)
    (hinv : ∀ y : BdR p, (∀ σ : GQp p, bdrAct p σ y = y) → ∃ c : ℚ_[p], y = algebraMap ℚ_[p] (BdR p) c)
    (h : NotInFrac p B u) : LogCore p B u := by
  intro a b ha y hy he
  obtain ⟨c, rfl⟩ := hinv y hy
  apply h a (b + algebraMap ℚ_[p] B c * a) ha
  rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← he]
  ring

/-! ## §4. `log [p̃]`: the reduction over `B_max` and over `B_cris` -/

theorem bmax_gStable : GStable p (Bmax p) := by
  intro σ x hx
  have := bmax_stable p σ hx
  rwa [Subalgebra.mem_comap, bdrAlg_apply] at this

/-- `σ(log [p̃]) − log [p̃] = log [u_σ]` lies in every `B` containing all `log [ε]`, `ε^♯ = 1`. -/
theorem logPTilde_shift (B : Subalgebra ℚ_[p] (BdR p))
    (hB : ∀ (ε : PreTilt 𝓞_ℂ_[p] p) (h : PreTilt.untilt ε = 1), toBdR p (logTeich p h) ∈ B)
    (σ : GQp p) : ∃ δ : B, bdrAct p σ (toBdR p (logPTilde p)) = toBdR p (logPTilde p) + δ := by
  obtain ⟨u, hu, hu1⟩ := exists_uSigma p σ
  exact ⟨⟨_, hB u hu1⟩, by rw [bdrAct_logPTilde p σ hu hu1, add_comm]⟩

theorem logTeich_mem_bmax {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    toBdR p (logTeich p h) ∈ Bmax p :=
  Algebra.subset_adjoin (Or.inl ⟨_, logTeich_mem_amax p h, rfl⟩)

/-- **`BergerBst.LogPTildeTranscendental` follows from the core over `B_max`.** -/
theorem logPTildeTranscendental_of_core
    (hcore : ∀ (p : ℕ) [Fact p.Prime], LogCore p (Bmax p) (toBdR p (logPTilde p))) :
    LogPTildeTranscendental := fun p _ =>
  transcendental_of_logCore p (Bmax p) (bmax_gStable p) _
    (logPTilde_shift p (Bmax p) fun _ h => logTeich_mem_bmax p h) (hcore p)

/-- The core is monotone: over a smaller ring it is a weaker statement. -/
theorem logCore_mono {B B' : Subalgebra ℚ_[p] (BdR p)} (hBB' : B ≤ B') {u : BdR p}
    (h : LogCore p B' u) : LogCore p B u := by
  intro a b ha y hy he
  exact h ⟨a, hBB' a.2⟩ ⟨b, hBB' b.2⟩ (by intro h0; apply ha; rw [Subtype.ext_iff] at h0 ⊢; exact h0) y hy he

/-- `B_cris` (at the generator `ξ`) is `G_{ℚ_p}`-stable. -/
theorem bcris_gStable {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) :
    GStable p (BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)) := by
  intro σ x hx
  have hle : BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) ≤
      (BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)).comap (bdrAlg p σ) := by
    rw [BcrisOf, Algebra.adjoin_le_iff]
    intro z hz
    rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
    rcases hz with ⟨y, hy, rfl⟩ | hz
    · obtain ⟨y', hy', he⟩ := bdrAct_acris p σ hy
      rw [he]
      exact Algebra.subset_adjoin (Or.inl ⟨y', hy', rfl⟩)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      refine tInv_mem_of p h _ (Algebra.subset_adjoin (Or.inr rfl)) ?_
      exact tInvSet_stable p σ ⟨ε₀, h.1, ne_one_of_isGenEps p h, rfl⟩
  have := hle hx
  rwa [Subalgebra.mem_comap, bdrAlg_apply] at this

/-- **Transcendence over `B_cris` from the (weaker) core over `B_cris`.** -/
theorem transcendental_bcris_of_core {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (hcore : LogCore p (BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p))
      (toBdR p (logPTilde p))) :
    Transcendental (BcrisOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p))
      (toBdR p (logPTilde p)) :=
  transcendental_of_logCore p _ (bcris_gStable p h) _
    (logPTilde_shift p _ fun _ hε => Algebra.subset_adjoin (Or.inl ⟨_, logTeich_mem_acris p hε, rfl⟩))
    hcore

/-! ## §5. Transfer: transcendence over `B_max` gives Brinon-Conrad Thm 9.2.10 for `B_cris` -/

/-- Transcendence passes to a smaller subalgebra. -/
theorem transcendental_of_le {B B' : Subalgebra ℚ_[p] (BdR p)} (hBB' : B ≤ B') {u : BdR p}
    (h : Transcendental B' u) : Transcendental B u := by
  rintro ⟨P, hP0, hPu⟩
  apply h
  refine ⟨P.map (Subalgebra.inclusion hBB'), ?_, ?_⟩
  · intro h0
    apply hP0
    exact (Polynomial.map_eq_zero_iff (Subalgebra.inclusion_injective hBB')).mp h0
  · rw [aeval_def, eval₂_map]
    exact hPu

/-- **Brinon-Conrad Thm 9.2.10 at `K = ℚ_p` (injectivity), from the transcendence over `B_max`:**
`B_cris[X] → B_dR`, `X ↦ log [p̃]`, is injective, for every `w ∈ ker θ`. -/
theorem transcendental_bcrisOf (ht : LogPTildeTranscendental) {ε₀ : PreTilt 𝓞_ℂ_[p] p}
    (h : IsGenEps p ε₀) {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    Function.Injective (aeval (R := BcrisOf p h w hw) (toBdR p (logPTilde p))) :=
  transcendental_iff_injective.mp (transcendental_of_le p (bcrisOf_le_bmax p h hw) (ht p))

/-- `BstFOf` is the `B_cris`-algebra generated by `log [p̃]`. -/
theorem bstFOf_eq_adjoin {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    BstFOf p h w hw =
      (Algebra.adjoin (BcrisOf p h w hw) {toBdR p (logPTilde p)}).restrictScalars ℚ_[p] := by
  rw [BstFOf, Algebra.adjoin_union_eq_adjoin_adjoin]
  rfl

/-- **`BstFOf ≅ B_cris[X]`** (`X ↦ log [p̃]`), given the transcendence over `B_max`: Brinon-Conrad's abstract
`B_st = B_cris[X]` (Def. 9.2.3) is identified with its image `BstFOf` in `B_dR` (p. 142, Thm 9.2.10). -/
def bcrisPolyEquiv (ht : LogPTildeTranscendental) {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    Polynomial (BcrisOf p h w hw) ≃ₐ[BcrisOf p h w hw]
      Algebra.adjoin (BcrisOf p h w hw) {toBdR p (logPTilde p)} :=
  (AlgEquiv.ofInjective _ (transcendental_bcrisOf p ht h hw)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval _ _).symm)

theorem bcrisPolyEquiv_X (ht : LogPTildeTranscendental) {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    ((bcrisPolyEquiv p ht h hw Polynomial.X : Algebra.adjoin (BcrisOf p h w hw)
      {toBdR p (logPTilde p)}) : BdR p) = toBdR p (logPTilde p) := by
  simp [bcrisPolyEquiv]


/-! ## §6. Units: `log([ν]/v) ∈ A_max`, with the same Galois shape as `log [p̃]`

For a unit `v ∈ ℤ_p^×` and `ν ∈ 𝓞_ℂ_p♭` with `ν^♯ = v`, the element `log([ν]/v)` lies in `A_max ⊆ B_max`, and
`σ(log([ν]/v)) = log([ν]/v) + log [u_σ]` with `u_σ^♯ = 1`: the same shape as `σ(log [p̃]) = log [p̃] + log [u_σ]`
(`bdrAct_logPTilde`). So no argument that uses only this Galois shape can prove `log [p̃] ∉ Frac(B_max)`; a proof must
use that `p` is not a unit (report §4.2). -/

section Units

open PanBergerSplit (locAct flatAct theta)

theorem sub_one_mem_ith {z : Ainf p} (hz : theta p z = 1) :
    algebraMap (Ainf p) (AinfP p) (z - 1) ∈ Ith p := by
  have hk : z - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, map_sub, map_one]
    exact sub_eq_zero.mpr hz
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  rw [← hc, map_mul, mul_comm]
  exact Ideal.mul_mem_right _ _ (xi'_mem p)

/-- **`log z ∈ B_dR^+`** for `z ∈ A_inf` with `θ(z) = 1`: `log(1 + (z − 1))`. -/
def logOne {z : Ainf p} (hz : theta p z = 1) : BDeRhamPlus 𝓞_ℂ_[p] p :=
  logPlus p (sub_one_mem_ith p hz)

theorem logOne_congr {z z' : Ainf p} (hz : theta p z = 1) (hz' : theta p z' = 1) (h : z = z') :
    logOne p hz = logOne p hz' := by
  subst h
  rfl

theorem logOne_teich {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1)
    (hz : theta p (WittVector.teichmuller p ε) = 1) : logOne p hz = logTeich p h := rfl

/-- **`log z ∈ A_max`** for every `z ∈ A_inf` with `θ(z) = 1` (`logTeich_mem_amax`'s proof, for any such `z`). -/
theorem logOne_mem_amax {z : Ainf p} (hz : theta p z = 1) : logOne p hz ∈ Amax p := by
  have hk : z - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, map_sub, map_one]
    exact sub_eq_zero.mpr hz
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  let f : PowerSeries (Ainf p) := PowerSeries.mk fun n =>
    if n = 0 then 0 else (-1) ^ (n + 1) * zpToW p (logCoeff p n) * c ^ n
  have hf : f ∈ restricted p := fun k => ⟨2 * k + 1, fun n hn => by
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n f
    rw [PowerSeries.coeff_mk, ite_eq_right (by omega)]
    obtain ⟨d, hd⟩ := (logCoeff_spec p (show n ≠ 0 by omega)).2 k (by omega)
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨zpToW p d, ?_⟩ _) _
    rw [hd, map_mul, map_pow, map_natCast]⟩
  refine ⟨f, hf, ?_⟩
  rw [RingHom.comp_apply, logOne, logPlus]
  apply psEval_eq_of_terms
  intro n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, logSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, ite_eq_right hn, ← hc]
    have key : ((n : ℚ_[p]))⁻¹ = (logCoeff p n : ℚ_[p]) * ((p : ℚ_[p])⁻¹) ^ n := by
      have h1 := (logCoeff_spec p hn).1
      have hn' : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hp' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      have he : (logCoeff p n : ℚ_[p]) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact pow_ne_zero _ hp' h1.symm
      rw [inv_pow, ← h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
    have hq : qpToLoc p (logCoeff p n : ℚ_[p]) = algebraMap _ _ (zpToW p (logCoeff p n)) :=
      qpToLoc_algebraMap p _
    rw [key]
    simp only [map_mul, map_pow, map_neg, map_one]
    rw [← hq, omegaP, ZInQ.Contrib.G9.BdrKer.Cp.xi']
    ring

/-- `log` is multiplicative-to-additive on `θ = 1`. -/
theorem logOne_mul {z z' : Ainf p} (hz : theta p z = 1) (hz' : theta p z' = 1)
    (hzz : theta p (z * z') = 1) : logOne p hzz = logOne p hz + logOne p hz' := by
  rw [logOne, logOne, logOne, ← logPlus_add]
  exact evalB_congr' p _ _ (by simp only [map_sub, map_mul, map_one]; ring) _

/-- `σ(log z) = log σ(z)`. -/
theorem bdrAct_logOne (σ : GQp p) {z : Ainf p} (hz : theta p z = 1)
    (hz' : theta p (WittVector.map (flatAct p σ) z) = 1) :
    bdrAct p σ (toBdR p (logOne p hz)) = toBdR p (logOne p hz') := by
  rw [logOne, logPlus, bdrAct_evalB, map_locAct_logSeries]
  exact congrArg (toBdR p) (evalB_congr' p _ _ (by rw [PanBergerSplit.locAct_algebraMap, map_sub, map_one]) _)

/-- `θ([ν] · v⁻¹) = 1` when `ν^♯ = v` (`v` seen in `𝓞_ℂ_p` as `θ(v)`, `v ∈ ℤ_p ⊆ A_inf`). -/
theorem theta_unit {v : ℤ_[p]ˣ} {ν : PreTilt 𝓞_ℂ_[p] p}
    (hν : PreTilt.untilt ν = theta p (zpToW p v)) :
    theta p (WittVector.teichmuller p ν * zpToW p ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) = 1 := by
  rw [map_mul, theta, WittVector.fontaineTheta_teichmuller, hν, ← map_mul, ← map_mul, Units.mul_inv,
    map_one, map_one]

/-- **`σ(log([ν]/v)) = log([ν]/v) + log [u]`** when `σ(ν) = ν u`, `u^♯ = 1`. -/
theorem bdrAct_logUnit (σ : GQp p) {v : ℤ_[p]ˣ} {ν u : PreTilt 𝓞_ℂ_[p] p}
    (hν : PreTilt.untilt ν = theta p (zpToW p v)) (hσ : flatAct p σ ν = ν * u)
    (hu : PreTilt.untilt u = 1) :
    bdrAct p σ (toBdR p (logOne p (theta_unit p hν))) =
      toBdR p (logOne p (theta_unit p hν)) + toBdR p (logTeich p hu) := by
  set z := WittVector.teichmuller p ν * zpToW p ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hzdef
  have hmap : WittVector.map (flatAct p σ) z = WittVector.teichmuller p u * z := by
    rw [hzdef, map_mul, WittVector.map_teichmuller, wittMap_zpToW, hσ, map_mul]
    ring
  have htu : theta p (WittVector.teichmuller p u) = 1 := by
    rw [theta, WittVector.fontaineTheta_teichmuller, hu]
  have hz1 : theta p z = 1 := theta_unit p hν
  have hz' : theta p (WittVector.map (flatAct p σ) z) = 1 := by
    rw [hmap, map_mul, htu, hz1, one_mul]
  have hzz : theta p (WittVector.teichmuller p u * z) = 1 := by rw [← hmap]; exact hz'
  rw [bdrAct_logOne p σ hz1 hz', logOne_congr p hz' hzz hmap, logOne_mul p htu hz1 hzz,
    logOne_teich p hu htu, map_add, add_comm]

/-- A compatible system of `p`-power roots of `x` in `ℂ_p`. -/
noncomputable def rootsOf (x : ℂ_[p]) : ℕ → ℂ_[p]
  | 0 => x
  | n + 1 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (rootsOf x n) hp.out.pos)

theorem rootsOf_succ_pow (x : ℂ_[p]) (n : ℕ) : rootsOf p x (n + 1) ^ p = rootsOf p x n :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (rootsOf p x n) hp.out.pos)

theorem rootsOf_pow (x : ℂ_[p]) (n : ℕ) : rootsOf p x n ^ p ^ n = x := by
  induction n with
  | zero => simp [rootsOf]
  | succ n ih => rw [pow_succ', pow_mul, rootsOf_succ_pow, ih]

theorem norm_rootsOf_le {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖rootsOf p x n‖ ≤ 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [← rootsOf_succ_pow, norm_pow] at ih
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp ih

/-- `x♭ = (x, x^{1/p}, …) ∈ 𝓞_ℂ_p♭` (bdr-kertheta's `pFlat` for any `x ∈ 𝓞_ℂ_p`). -/
noncomputable def flatOf (x : 𝓞_ℂ_[p]) : PreTilt 𝓞_ℂ_[p] p :=
  ⟨fun n => Ideal.Quotient.mk _ ⟨rootsOf p x n, (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr
      (norm_rootsOf_le p ((ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mp x.2) n)⟩,
    fun n => by
      rw [← map_pow]
      congr 1
      exact Subtype.ext (by simpa using rootsOf_succ_pow p (x : ℂ_[p]) n)⟩

/-- **`♯ : 𝓞_ℂ_p♭ → 𝓞_ℂ_p` is onto** (`(x♭)♯ = x`). -/
theorem untilt_flatOf (x : 𝓞_ℂ_[p]) : (flatOf p x).untilt = x := by
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {((p : 𝓞_ℂ_[p]))})]
  intro n
  rw [SModEq.sub_mem, ZInQ.Contrib.G9.BdrKer.mem_span_pow_iff']
  have h1 : ZInQ.Contrib.G9.BdrKer.Cp.root (flatOf p x) n -
      ⟨rootsOf p x n, (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr
        (norm_rootsOf_le p ((ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mp x.2) n)⟩ ∈
      Ideal.span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, ZInQ.Contrib.G9.BdrKer.Cp.mk_root]; rfl
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [ZInQ.Contrib.G9.BdrKer.Cp.root_pow] at h2
  have h3 : (⟨rootsOf p x n, (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr
      (norm_rootsOf_le p ((ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mp x.2) n)⟩ : 𝓞_ℂ_[p]) ^ p ^ n = x :=
    Subtype.ext (by simpa using rootsOf_pow p (x : ℂ_[p]) n)
  rw [h3] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨p * c, by rw [hc]; ring⟩

theorem coeff_pow_pow (x : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]

/-- An element of `𝓞_ℂ_p♭` whose `♯` is a unit is a unit. -/
theorem isUnit_of_isUnit_untilt {x : PreTilt 𝓞_ℂ_[p] p} (h : IsUnit (PreTilt.untilt x)) : IsUnit x := by
  have h0 : IsUnit (PreTilt.coeff 0 x) := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero]
    exact h.map _
  have hn : ∀ n, IsUnit (PreTilt.coeff n x) := fun n =>
    (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).mp (by rw [coeff_pow_pow]; exact h0)
  have hcomp : ∀ n, (hn (n + 1)).unit ^ p = (hn n).unit := fun n =>
    Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, IsUnit.unit_spec, PreTilt.coeff_pow_p])
  let y : PreTilt 𝓞_ℂ_[p] p := ⟨fun n => (((hn n).unit⁻¹ : (ModP 𝓞_ℂ_[p] p)ˣ) : ModP 𝓞_ℂ_[p] p),
    fun n => by
      beta_reduce
      rw [← Units.val_pow_eq_pow_val, inv_pow, hcomp]⟩
  refine isUnit_iff_exists_inv.mpr ⟨y, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n (x * y) = PreTilt.coeff n 1
  rw [map_mul, map_one]
  exact (hn n).mul_val_inv

/-- For `ν♯ = v` a unit of `ℤ_p`: `σ(ν) = ν u` with `u♯ = 1`. -/
theorem exists_uSigma_unit (σ : GQp p) {v : ℤ_[p]ˣ} {ν : PreTilt 𝓞_ℂ_[p] p}
    (hν : PreTilt.untilt ν = theta p (zpToW p v)) :
    ∃ u : PreTilt 𝓞_ℂ_[p] p, flatAct p σ ν = ν * u ∧ PreTilt.untilt u = 1 := by
  have hvu : IsUnit (PreTilt.untilt ν) := by
    rw [hν]
    exact (v.isUnit.map (zpToW p)).map (theta p)
  have hνu := isUnit_of_isUnit_untilt p hvu
  refine ⟨flatAct p σ ν * ↑hνu.unit⁻¹, ?_, ?_⟩
  · rw [mul_comm, mul_assoc, hνu.val_inv_mul, mul_one]
  · have hσν : PreTilt.untilt (flatAct p σ ν) = PreTilt.untilt ν := by
      rw [DR.untilt_preTiltMap, hν, ← PanBergerSplit.theta_wittMap, wittMap_zpToW]
    rw [map_mul, hσν, ← map_mul, hνu.mul_val_inv, map_one]

/-- **The unit analogue of `log [p̃]`.** For every unit `v ∈ ℤ_p^×` there are `ν ∈ 𝓞_ℂ_p♭` with `ν♯ = v` and
`w = log([ν]/v) ∈ A_max` such that, for every `σ`, `σ(w) = w + log [u]` with `u♯ = 1` — the shape of
`bdrAct_logPTilde`. -/
theorem unit_log_mem_amax (v : ℤ_[p]ˣ) :
    ∃ (ν : PreTilt 𝓞_ℂ_[p] p) (hν : PreTilt.untilt ν = theta p (zpToW p v)),
      logOne p (theta_unit p hν) ∈ Amax p ∧
      ∀ σ : GQp p, ∃ (u : PreTilt 𝓞_ℂ_[p] p) (hu : PreTilt.untilt u = 1),
        bdrAct p σ (toBdR p (logOne p (theta_unit p hν))) =
          toBdR p (logOne p (theta_unit p hν)) + toBdR p (logTeich p hu) := by
  refine ⟨flatOf p (theta p (zpToW p v)), untilt_flatOf p _, logOne_mem_amax p _, fun σ => ?_⟩
  obtain ⟨u, hσ, hu⟩ := exists_uSigma_unit p σ (untilt_flatOf p (theta p (zpToW p v)))
  exact ⟨u, hu, bdrAct_logUnit p σ (untilt_flatOf p _) hσ hu⟩

end Units

end LogPTransc
end PkgI4
end HDec

end
