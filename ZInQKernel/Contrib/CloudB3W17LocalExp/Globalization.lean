import ZInQKernel.Contrib.CloudB3W17Lattice.TorusBridge

/-!
# Globalizing a local analytic homomorphism into a compact connected complex Lie group

A **conditional** theorem. Nothing here constructs an exponential map, assumes any analytification, or
proves commutativity of a compact complex Lie group: the local analytic homomorphism `L` is *given*.

Setting: `E` a finite-dimensional complex normed space, `G` a commutative complex Lie group charted on `E`
(`IsManifold 𝓘(ℂ, E) ω`, `LieGroup 𝓘(ℂ, E) ω`), compact and connected. Given `r > 0` and **any** function
`L : E → G` with

* `L 0 = 1`,
* `ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω L (ball 0 r)`,
* `L (x + y) = L x * L y` whenever `x`, `y` and `x + y` all lie in `ball 0 r`,
* `IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω L 0`,

(no hypothesis whatsoever on `L` outside `ball 0 r`), the map `Φ v = L (v / n) ^ n` is a global analytic
homomorphism `E → G` extending `L|ball 0 r`, it is the unique homomorphism doing so, it is surjective, its
kernel is a discrete full lattice `Λ`, and `Torus Λ ≃ₘ^ω G` as groups — the conclusion of
`UnifPrinted.MumfordComplexTorus` for `E = Fin g → ℂ`.

Commutativity of `G` is used exactly twice: in `glob_add` (`mul_pow`) and through `CommGroup` in the lattice
package. `T2Space G` is *not* needed.

Main results (namespace `CloudB3W17LocalExp`):

* `glob`, `glob_eq_self`, `glob_add`, `glob_contMDiff` — the globalization and its analyticity;
* `glob_unique` — uniqueness among homomorphisms extending `L|ball 0 r`;
* `glob_surjective`, `glob_isOpenMap`, `glob_injOn` — surjectivity by connectedness, openness, injectivity
  near `0`;
* `exists_torus_diffeo_of_localExp` — the packaged conclusion.

The lattice half (`DiscreteTopology`, `IsZLattice`, `E ⧸ ker ≃ₜ+ G`) is *not* re-proved here: it is
`CloudB3W17Lattice.isZLattice_of_exp`. The torus's own analytic structure is Mathlib + `BPAnalytic.Torus`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Metric

noncomputable section

namespace CloudB3W17LocalExp

open BPAnalytic CloudB3W17Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]

/-! ## 1. Scaling -/

/-- `v / n`, as a complex scalar multiple. -/
def invSmul (n : ℕ) (v : E) : E := ((n : ℂ))⁻¹ • v

theorem norm_invSmul (n : ℕ) (v : E) : ‖invSmul n v‖ = ‖v‖ / n := by
  rw [invSmul, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]

theorem natCast_smul_invSmul {n : ℕ} (hn : n ≠ 0) (v : E) : ((n : ℂ)) • invSmul n v = v := by
  rw [invSmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

theorem invSmul_mem_ball {r : ℝ} {n : ℕ} {v : E} (h : ‖v‖ / n < r) : invSmul n v ∈ ball (0 : E) r := by
  rw [mem_ball_zero_iff, norm_invSmul]
  exact h

theorem norm_div_lt_of_le {r : ℝ} {m n : ℕ} {v : E} (hm : 0 < m) (hmn : m ≤ n) (h : ‖v‖ / m < r) :
    ‖v‖ / n < r :=
  lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg v) (by exact_mod_cast hm)
    (by exact_mod_cast hmn)) h

/-- A denominator that works for `v`: `‖v‖ / nOf r v < r`. -/
def nOf (r : ℝ) (v : E) : ℕ := ⌈‖v‖ / r⌉₊ + 1

theorem nOf_pos (r : ℝ) (v : E) : 0 < nOf r v := Nat.succ_pos _

theorem norm_div_nOf {r : ℝ} (hr : 0 < r) (v : E) : ‖v‖ / (nOf r v) < r := by
  have h1 : ‖v‖ / r < (nOf r v : ℝ) := by
    have := Nat.le_ceil (‖v‖ / r)
    have : (⌈‖v‖ / r⌉₊ : ℝ) < (nOf r v : ℝ) := by
      simp only [nOf, Nat.cast_add, Nat.cast_one]
      linarith
    linarith [Nat.le_ceil (‖v‖ / r)]
  have hn : (0 : ℝ) < (nOf r v : ℝ) := by exact_mod_cast nOf_pos r v
  rw [div_lt_iff₀ hn]
  rw [div_lt_iff₀ hr] at h1
  linarith

/-! ## 2. The local power law -/

variable {r : ℝ} {L : E → G}

/-- The local homomorphism law, as a hypothesis bundle. -/
structure IsLocalHom (r : ℝ) (L : E → G) : Prop where
  map_one : L 0 = 1
  map_add : ∀ x ∈ ball (0 : E) r, ∀ y ∈ ball (0 : E) r, x + y ∈ ball (0 : E) r →
    L (x + y) = L x * L y

theorem IsLocalHom.pow_smul (hL : IsLocalHom r L) :
    ∀ (k : ℕ) (w : E), ‖w‖ * k < r → L ((k : ℂ) • w) = L w ^ k := by
  intro k
  induction k with
  | zero => intro w _; simpa using hL.map_one
  | succ k ih =>
    intro w hw
    have hnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
    have hk : ‖w‖ * k < r := by
      refine lt_of_le_of_lt ?_ hw
      have : (k : ℝ) ≤ ((k : ℝ) + 1) := by linarith
      push_cast
      nlinarith
    have hw1 : ‖w‖ < r := by
      refine lt_of_le_of_lt ?_ hw
      push_cast
      nlinarith
    have hsum : ‖(k : ℂ) • w + w‖ < r := by
      have : ((k : ℂ)) • w + w = ((k + 1 : ℕ) : ℂ) • w := by push_cast; module
      rw [this, norm_smul, Complex.norm_natCast]
      push_cast at hw ⊢
      nlinarith
    have hmem1 : ((k : ℂ)) • w ∈ ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul, Complex.norm_natCast]
      nlinarith
    have hmem2 : w ∈ ball (0 : E) r := mem_ball_zero_iff.mpr hw1
    have hmem3 : ((k : ℂ)) • w + w ∈ ball (0 : E) r := mem_ball_zero_iff.mpr hsum
    have hsplit : (((k + 1 : ℕ)) : ℂ) • w = ((k : ℂ)) • w + w := by push_cast; module
    rw [hsplit, hL.map_add _ hmem1 _ hmem2 hmem3, ih w hk, pow_succ]

/-! ## 3. The globalization -/

/-- `Φ v = L (v / n) ^ n` for a denominator `n` large enough that `v / n` lies in the ball. -/
def glob (r : ℝ) (L : E → G) (v : E) : G := L (invSmul (nOf r v) v) ^ (nOf r v)

/-- Any admissible denominator computes `glob`. -/
theorem glob_eq_of (hr : 0 < r) (hL : IsLocalHom r L) {n : ℕ} (hn : 0 < n) {v : E}
    (h : ‖v‖ / n < r) : glob r L v = L (invSmul n v) ^ n := by
  set m := nOf r v with hm
  have hmpos : 0 < m := nOf_pos r v
  have hmlt : ‖v‖ / m < r := norm_div_nOf hr v
  -- both sides equal `L (v / (n * m)) ^ (n * m)`
  have key : ∀ (a b : ℕ), 0 < a → 0 < b → ‖v‖ / a < r →
      L (invSmul a v) ^ a = L (invSmul (a * b) v) ^ (a * b) := by
    intro a b ha hb halt
    have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    have hA : (0 : ℝ) < a := by exact_mod_cast ha
    have hB : (0 : ℝ) < b := by exact_mod_cast hb
    have hA' : (a : ℝ) ≠ 0 := ne_of_gt hA
    have hB' : (b : ℝ) ≠ 0 := ne_of_gt hB
    have hsmul : ((b : ℂ)) • invSmul (a * b) v = invSmul a v := by
      simp only [invSmul, smul_smul, Nat.cast_mul]
      congr 1
      field_simp
    have hnorm : ‖invSmul (a * b) v‖ * b < r := by
      rw [norm_invSmul]
      have hrw : ‖v‖ / ((a * b : ℕ) : ℝ) * b = ‖v‖ / a := by
        push_cast
        field_simp
      rw [hrw]
      exact halt
    have := hL.pow_smul b (invSmul (a * b) v) hnorm
    rw [hsmul] at this
    rw [this, ← pow_mul, mul_comm b a]
  have h1 := key n m hn hmpos h
  have h2 := key m n hmpos hn hmlt
  rw [glob, ← hm, h2, h1, mul_comm m n]

/-- On the ball, `glob` is `L`. -/
theorem glob_eq_self (hr : 0 < r) (hL : IsLocalHom r L) {v : E} (hv : v ∈ ball (0 : E) r) :
    glob r L v = L v := by
  have h : ‖v‖ / (1 : ℕ) < r := by simpa using mem_ball_zero_iff.mp hv
  rw [glob_eq_of hr hL Nat.one_pos h]
  simp [invSmul]

theorem glob_zero (hr : 0 < r) (hL : IsLocalHom r L) : glob r L 0 = 1 := by
  rw [glob_eq_self hr hL (by simpa using hr), hL.map_one]

/-- **`glob` is a homomorphism.** This is where commutativity of `G` is used. -/
theorem glob_add (hr : 0 < r) (hL : IsLocalHom r L) (u v : E) :
    glob r L (u + v) = glob r L u * glob r L v := by
  set n := nOf r u + nOf r v + nOf r (u + v) with hn
  have hnpos : 0 < n := by
    have := nOf_pos r u
    omega
  have hu : ‖u‖ / n < r :=
    norm_div_lt_of_le (nOf_pos r u) (by omega) (norm_div_nOf hr u)
  have hv : ‖v‖ / n < r :=
    norm_div_lt_of_le (nOf_pos r v) (by omega) (norm_div_nOf hr v)
  have huv : ‖u + v‖ / n < r :=
    norm_div_lt_of_le (nOf_pos r (u + v)) (by omega) (norm_div_nOf hr (u + v))
  have hsum : invSmul n u + invSmul n v = invSmul n (u + v) := by
    simp [invSmul, smul_add]
  rw [glob_eq_of hr hL hnpos hu, glob_eq_of hr hL hnpos hv, glob_eq_of hr hL hnpos huv,
    ← hsum, hL.map_add _ (invSmul_mem_ball hu) _ (invSmul_mem_ball hv)
      (hsum ▸ invSmul_mem_ball huv), mul_pow]

/-- **Uniqueness.** Any homomorphism agreeing with `L` on the ball is `glob`. -/
theorem glob_unique (hr : 0 < r) (hL : IsLocalHom r L) {Φ : E → G}
    (hhom : ∀ u v, Φ (u + v) = Φ u * Φ v) (hagree : ∀ v ∈ ball (0 : E) r, Φ v = L v) :
    Φ = glob r L := by
  have hΦ0 : Φ 0 = 1 := by
    have := hhom 0 0
    simpa using this.symm
  have hpow : ∀ (k : ℕ) (w : E), Φ ((k : ℂ) • w) = Φ w ^ k := by
    intro k
    induction k with
    | zero => intro w; simpa using hΦ0
    | succ k ih =>
      intro w
      have hsplit : (((k + 1 : ℕ)) : ℂ) • w = ((k : ℂ)) • w + w := by push_cast; module
      rw [hsplit, hhom, ih w, pow_succ]
  funext v
  set n := nOf r v with hn
  have hnpos : 0 < n := nOf_pos r v
  have hlt : ‖v‖ / n < r := norm_div_nOf hr v
  have hmem : invSmul n v ∈ ball (0 : E) r := invSmul_mem_ball hlt
  have : Φ v = Φ (invSmul n v) ^ n := by
    rw [← hpow n (invSmul n v), natCast_smul_invSmul hnpos.ne' v]
  rw [this, hagree _ hmem, glob_eq_of hr hL hnpos hlt]

/-! ## 4. Analyticity, openness, surjectivity -/

section Manifold

variable [LieGroup 𝓘(ℂ, E) ω G]

/-- **`glob` is analytic**: near `v₀` it is `L (· / n) ^ n` for a fixed `n`. -/
theorem glob_contMDiff (hr : 0 < r) (hL : IsLocalHom r L)
    (hLsm : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω L (ball (0 : E) r)) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (glob r L) := by
  intro v₀
  set n := nOf r v₀ with hn
  have hnpos : 0 < n := nOf_pos r v₀
  have hsmulC : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun v : E => invSmul n v) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.const_smul _)
  have hUopen : IsOpen ((fun v : E => invSmul n v) ⁻¹' ball (0 : E) r) :=
    Metric.isOpen_ball.preimage hsmulC.continuous
  have hv₀ : invSmul n v₀ ∈ ball (0 : E) r := invSmul_mem_ball (norm_div_nOf hr v₀)
  have heq : glob r L =ᶠ[𝓝 v₀] fun v => L (invSmul n v) ^ n := by
    filter_upwards [hUopen.mem_nhds hv₀] with v hv
    have hlt : ‖v‖ / n < r := by
      have := mem_ball_zero_iff.mp hv
      rwa [norm_invSmul] at this
    exact glob_eq_of hr hL hnpos hlt
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  have h2 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω L (invSmul n v₀) :=
    hLsm.contMDiffAt (Metric.isOpen_ball.mem_nhds hv₀)
  have h3 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun g : G => g ^ n) (L (invSmul n v₀)) :=
    (contMDiff_pow n).contMDiffAt
  have := h3.comp v₀ (h2.comp v₀ hsmulC.contMDiffAt)
  simpa [Function.comp_def] using this

variable {Ψ : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) E G ω}

/-- The part of `Ψ.target` whose preimage under the local inverse lies in the ball: there the local
inverse of `Ψ` is a section of `glob`. -/
def sect (r : ℝ) (Ψ : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, E) E G ω) : Set G :=
  Ψ.target ∩ Ψ.invFun ⁻¹' ball (0 : E) r

theorem isOpen_sect : IsOpen (sect r Ψ) :=
  Ψ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage Ψ.open_target Metric.isOpen_ball

theorem apply_zero_eq_one (hL : IsLocalHom r L) (h0 : (0 : E) ∈ Ψ.source)
    (hEq : EqOn L Ψ Ψ.source) : Ψ (0 : E) = 1 := by
  rw [← hEq h0, hL.map_one]

theorem invFun_one (hL : IsLocalHom r L) (h0 : (0 : E) ∈ Ψ.source) (hEq : EqOn L Ψ Ψ.source) :
    Ψ.invFun (1 : G) = 0 := by
  rw [← apply_zero_eq_one hL h0 hEq]
  exact Ψ.toPartialEquiv.left_inv h0

theorem one_mem_sect (hr : 0 < r) (hL : IsLocalHom r L) (h0 : (0 : E) ∈ Ψ.source)
    (hEq : EqOn L Ψ Ψ.source) : (1 : G) ∈ sect r Ψ := by
  refine ⟨?_, ?_⟩
  · rw [← apply_zero_eq_one hL h0 hEq]
    exact Ψ.toPartialEquiv.map_source h0
  · show Ψ.invFun (1 : G) ∈ ball (0 : E) r
    rw [invFun_one hL h0 hEq]
    simpa using hr

/-- On `sect r Ψ`, the local inverse of `Ψ` is a section of `glob`. -/
theorem glob_sect (hr : 0 < r) (hL : IsLocalHom r L) (hEq : EqOn L Ψ Ψ.source) {g : G}
    (hg : g ∈ sect r Ψ) : glob r L (Ψ.invFun g) = g := by
  have hsrc : Ψ.invFun g ∈ Ψ.source := Ψ.toPartialEquiv.map_target hg.1
  rw [glob_eq_self hr hL hg.2, hEq hsrc]
  exact Ψ.toPartialEquiv.right_inv hg.1

/-- **`glob` is an open map**: it is open at `0` by the local section, hence everywhere by
translation. -/
theorem glob_isOpenMap (hr : 0 < r) (hL : IsLocalHom r L) (h0 : (0 : E) ∈ Ψ.source)
    (hEq : EqOn L Ψ Ψ.source) : IsOpenMap (glob r L) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro g ⟨v₀, hv₀U, rfl⟩
  set S : Set G := Ψ.target ∩ Ψ.invFun ⁻¹' (ball (0 : E) r ∩ (fun w : E => v₀ + w) ⁻¹' U) with hS
  have hSopen : IsOpen S :=
    Ψ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage Ψ.open_target
      (Metric.isOpen_ball.inter (hU.preimage (continuous_const.add continuous_id)))
  have h1S : (1 : G) ∈ S := by
    refine ⟨(one_mem_sect hr hL h0 hEq).1, ?_⟩
    show Ψ.invFun (1 : G) ∈ ball (0 : E) r ∩ (fun w : E => v₀ + w) ⁻¹' U
    rw [invFun_one hL h0 hEq]
    exact ⟨by simpa using hr, by simpa using hv₀U⟩
  have hsub : (fun h : G => glob r L v₀ * h) '' S ⊆ glob r L '' U := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨v₀ + Ψ.invFun h, hh.2.2, ?_⟩
    rw [glob_add hr hL, glob_sect hr hL hEq ⟨hh.1, hh.2.1⟩]
  refine Filter.mem_of_superset ?_ hsub
  refine ((isOpenMap_mul_left (glob r L v₀)) S hSopen).mem_nhds ⟨1, h1S, by simp⟩

/-- **`glob` is surjective**: its range is an open, hence closed, subgroup of a connected group. -/
theorem glob_surjective [ConnectedSpace G] (hr : 0 < r) (hL : IsLocalHom r L)
    (h0 : (0 : E) ∈ Ψ.source) (hEq : EqOn L Ψ Ψ.source) : Function.Surjective (glob r L) := by
  have : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  have hinv : ∀ v : E, glob r L (-v) = (glob r L v)⁻¹ := by
    intro v
    have h : glob r L v * glob r L (-v) = 1 := by
      rw [← glob_add hr hL]
      simpa using glob_zero hr hL
    exact (inv_eq_of_mul_eq_one_right h).symm
  let H : Subgroup G :=
    { carrier := Set.range (glob r L)
      one_mem' := ⟨0, glob_zero hr hL⟩
      mul_mem' := by
        rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u + v, glob_add hr hL u v⟩
      inv_mem' := by
        rintro a ⟨v, rfl⟩
        exact ⟨-v, hinv v⟩ }
  have hnhds : (H : Set G) ∈ 𝓝 (1 : G) := by
    refine Filter.mem_of_superset (isOpen_sect.mem_nhds (one_mem_sect hr hL h0 hEq)) ?_
    intro g hg
    exact ⟨Ψ.invFun g, glob_sect hr hL hEq hg⟩
  have hopen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hnhds
  have hcl : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  have huniv : (H : Set G) = Set.univ := IsClopen.eq_univ ⟨hcl, hopen⟩ ⟨1, H.one_mem⟩
  intro g
  have : g ∈ (H : Set G) := huniv ▸ Set.mem_univ g
  exact this

/-- **`glob` is injective near `0`.** -/
theorem glob_injOn (hr : 0 < r) (hL : IsLocalHom r L) (hEq : EqOn L Ψ Ψ.source) :
    Set.InjOn (glob r L) (Ψ.source ∩ ball (0 : E) r) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ hxy
  rw [glob_eq_self hr hL hx2, glob_eq_self hr hL hy2, hEq hx1, hEq hy1] at hxy
  exact Ψ.toPartialEquiv.injOn hx1 hy1 hxy

/-! ## 5. The torus: discrete full-lattice kernel and the analytic isomorphism -/

section Main

variable [FiniteDimensional ℂ E]

/-- **Main theorem (conditional).** Let `G` be a compact connected commutative complex Lie group
charted on a finite-dimensional complex normed space `E`, and suppose we are *given* `r > 0` and a
function `L : E → G` which on `ball 0 r` is analytic, sends `0` to `1`, is additive wherever the sum
stays in the ball, and is a local biholomorphism at `0` (no assumption outside the ball). Then there
is a discrete full lattice `Λ ⊂ E` and an analytic group isomorphism `Torus Λ ≃ₘ^ω G`.

For `E = Fin g → ℂ` this is the conclusion of `UnifPrinted.MumfordComplexTorus` in the commutative
case. The local analytic homomorphism `L` — the exponential map — is **not** constructed here. -/
theorem exists_torus_diffeo_of_localExp [CompactSpace G] [ConnectedSpace G]
    (hr : 0 < r) (hL : IsLocalHom r L)
    (hLsm : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω L (ball (0 : E) r))
    (hLloc : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω L 0) :
    ∃ (Λ : Submodule ℤ E) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (e : Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E)⟯ G), ∀ a b, e (a + b) = e a * e b := by
  have htop : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℂ, E) ω
  obtain ⟨Ψ, h0, hEq⟩ := hLloc
  have hΦsm : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (glob r L) := glob_contMDiff hr hL hLsm
  have hΦopen : IsOpenMap (glob r L) := glob_isOpenMap hr hL h0 hEq
  have hΦsurj : Function.Surjective (glob r L) := glob_surjective hr hL h0 hEq
  have h1T : (1 : G) ∈ sect r Ψ := one_mem_sect hr hL h0 hEq
  -- `glob r L`, as an additive homomorphism into `Additive G`
  let π : E →+ Additive G :=
    { toFun := fun v => Additive.ofMul (glob r L v)
      map_zero' := congrArg Additive.ofMul (glob_zero hr hL)
      map_add' := fun u v => congrArg Additive.ofMul (glob_add hr hL u v) }
  have hπapp : ∀ v : E, π v = Additive.ofMul (glob r L v) := fun _ => rfl
  set Λ : Submodule ℤ E := AddSubgroup.toIntSubmodule π.ker with hΛdef
  have hker : ∀ x : E, π x = 0 ↔ x ∈ Λ := by
    intro x
    rw [hΛdef]
    exact AddMonoidHom.mem_ker.symm
  have hπcont : Continuous (π : E → Additive G) := by
    have h := hΦsm.continuous
    exact h
  have hπopen : IsOpenMap (π : E → Additive G) := by
    have h := hΦopen
    exact h
  have hπsurj : Function.Surjective (π : E → Additive G) := by
    have h := hΦsurj
    exact h
  have hUnhds : (Ψ.source ∩ ball (0 : E) r) ∈ nhds (0 : E) :=
    (Ψ.open_source.inter Metric.isOpen_ball).mem_nhds ⟨h0, by simpa using hr⟩
  have hπinj : Set.InjOn (π : E → Additive G) (Ψ.source ∩ ball (0 : E) r) := by
    have h := glob_injOn hr hL hEq (Ψ := Ψ)
    exact h
  have hcompact : CompactSpace (Additive G) := inferInstanceAs (CompactSpace G)
  obtain ⟨hd, hZ, -⟩ := isZLattice_of_exp Λ π hker hπcont hπopen hπsurj hUnhds hπinj
  have hd' := hd
  -- the induced analytic isomorphism
  have hFmk : ∀ v : E, Additive.toMul (liftKer Λ π hker (proj Λ v)) = glob r L v := fun _ => rfl
  have hFbij : Function.Bijective (fun q : Torus Λ => Additive.toMul (liftKer Λ π hker q)) := by
    refine ⟨fun a b hab => liftKer_injective Λ π hker hab, fun g => ?_⟩
    obtain ⟨q, hq⟩ := liftKer_surjective Λ π hker hπsurj (Additive.ofMul g)
    exact ⟨q, congrArg Additive.toMul hq⟩
  have hFsm : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
      (fun q : Torus Λ => Additive.toMul (liftKer Λ π hker q)) := by
    refine contMDiff_of_comp_proj Λ ?_
    have hcomp : ((fun q : Torus Λ => Additive.toMul (liftKer Λ π hker q)) ∘ proj Λ)
        = glob r L := rfl
    rw [hcomp]
    exact hΦsm
  have hFinvsm : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
      (Equiv.ofBijective _ hFbij).symm := by
    intro g₀
    obtain ⟨v₀, rfl⟩ := hΦsurj g₀
    have hWopen : IsOpen ((fun g : G => (glob r L v₀)⁻¹ * g) ⁻¹' sect r Ψ) :=
      isOpen_sect.preimage (continuous_const.mul continuous_id)
    have hmemW : glob r L v₀ ∈ (fun g : G => (glob r L v₀)⁻¹ * g) ⁻¹' sect r Ψ := by
      simpa using h1T
    have hform : ∀ g ∈ (fun g : G => (glob r L v₀)⁻¹ * g) ⁻¹' sect r Ψ,
        (Equiv.ofBijective _ hFbij).symm g
          = proj Λ (v₀ + Ψ.invFun ((glob r L v₀)⁻¹ * g)) := by
      intro g hg
      refine (Equiv.symm_apply_eq _).mpr ?_
      show g = glob r L (v₀ + Ψ.invFun ((glob r L v₀)⁻¹ * g))
      rw [glob_add hr hL, glob_sect hr hL hEq hg, mul_inv_cancel_left]
    have m1 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun g : G => (glob r L v₀)⁻¹ * g) (glob r L v₀) :=
      contMDiff_mul_left.contMDiffAt
    have m2 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω Ψ.invFun ((glob r L v₀)⁻¹ * glob r L v₀) := by
      rw [inv_mul_cancel]
      exact Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds h1T.1)
    have m3 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun w : E => v₀ + w)
        (Ψ.invFun ((glob r L v₀)⁻¹ * glob r L v₀)) :=
      (contMDiff_iff_contDiff.mpr (contDiff_const.add contDiff_id)).contMDiffAt
    have m4 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (proj Λ)
        (v₀ + Ψ.invFun ((glob r L v₀)⁻¹ * glob r L v₀)) := (contMDiff_proj Λ).contMDiffAt
    have hsm : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω
        (fun g : G => proj Λ (v₀ + Ψ.invFun ((glob r L v₀)⁻¹ * g))) (glob r L v₀) := by
      have := m4.comp (glob r L v₀) (m3.comp (glob r L v₀) (m2.comp (glob r L v₀) m1))
      simpa [Function.comp_def] using this
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hWopen.mem_nhds hmemW] with g hg
    exact hform g hg
  refine ⟨Λ, hd, hZ, ⟨Equiv.ofBijective _ hFbij, hFsm, hFinvsm⟩, ?_⟩
  intro a b
  show Additive.toMul (liftKer Λ π hker (a + b))
      = Additive.toMul (liftKer Λ π hker a) * Additive.toMul (liftKer Λ π hker b)
  rw [map_add]
  rfl

end Main

end Manifold

end CloudB3W17LocalExp


