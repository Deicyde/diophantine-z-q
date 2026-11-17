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

end LogPTransc
end PkgI4
end HDec

end

#print axioms HDec.PkgI4.LogPTransc.acrisOf_le_amax_any
#print axioms HDec.PkgI4.LogPTransc.bcrisPlusOf_le_bmaxPlus
#print axioms HDec.PkgI4.LogPTransc.bcrisOf_le_bmax
#print axioms HDec.PkgI4.LogPTransc.bstFOf_le_bst
#print axioms HDec.PkgI4.LogPTransc.coeff_taylor_pred
#print axioms HDec.PkgI4.LogPTransc.GStable
#print axioms HDec.PkgI4.LogPTransc.sigB
#print axioms HDec.PkgI4.LogPTransc.sigB_coe
#print axioms HDec.PkgI4.LogPTransc.bdrAct_injective
#print axioms HDec.PkgI4.LogPTransc.sigB_injective
#print axioms HDec.PkgI4.LogPTransc.aeval_map_sigB
#print axioms HDec.PkgI4.LogPTransc.LogCore
#print axioms HDec.PkgI4.LogPTransc.top_coeff_relation
#print axioms HDec.PkgI4.LogPTransc.transcendental_of_logCore
#print axioms HDec.PkgI4.LogPTransc.logCore_of_transcendental
#print axioms HDec.PkgI4.LogPTransc.NotInFrac
#print axioms HDec.PkgI4.LogPTransc.logCore_of_notInFrac
#print axioms HDec.PkgI4.LogPTransc.bmax_gStable
#print axioms HDec.PkgI4.LogPTransc.logPTilde_shift
#print axioms HDec.PkgI4.LogPTransc.logTeich_mem_bmax
#print axioms HDec.PkgI4.LogPTransc.logPTildeTranscendental_of_core
#print axioms HDec.PkgI4.LogPTransc.logCore_mono
#print axioms HDec.PkgI4.LogPTransc.bcris_gStable
#print axioms HDec.PkgI4.LogPTransc.transcendental_bcris_of_core
#print axioms HDec.PkgI4.LogPTransc.transcendental_of_le
#print axioms HDec.PkgI4.LogPTransc.transcendental_bcrisOf
#print axioms HDec.PkgI4.LogPTransc.bstFOf_eq_adjoin
#print axioms HDec.PkgI4.LogPTransc.bcrisPolyEquiv
#print axioms HDec.PkgI4.LogPTransc.bcrisPolyEquiv_X
