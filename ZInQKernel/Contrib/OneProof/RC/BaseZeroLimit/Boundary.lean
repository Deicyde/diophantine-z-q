import ZInQKernel.Contrib.OneProof.RC.BaseZeroLimit.InnerLimit
import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Boundary45

/-!
# Lane RC30 (base zero, inner limit), part 2: the retained boundaries (4.5) survive the inner limit

Lane RC25 (`RC/BaseZeroAssembly/Boundary45.lean`) took the limit statement of (4.5) at the base as
the ELLIOT input `Boundary45Base.hlim : z̄ = lim_i L κ(W_i)` (along `atTop`). This file proves it
from the text's argument (Lemma `ex:arith-central-specialization`, `diophantine_zq.tex`, 11/5
version, tex 3912–3921 and 3952–3968) and lane RC6's inner limit (Lemma `ex:limits-inner-limit`,
tex 4401–4406, 4444–4450):

1. at every finite stage `i`, the retained boundary (4.5) in the fibre `t = 0`,
   `z_i(0) − L m_i j_i(b₁) = d v_i`, `m_i = a_{r_i} − 2` (tex 3912–3916 at `h = 1`), in the
   coordinates of the retained finite free model of the stage's Selmer cone (lifted to `ℤ₂`,
   modulo the stage ideal `(2^i)`): this is the field `hstage`, and it is PROVED per stage from
   lane RC25's `boundary45_finite` (`RetainedStage45.exists_witness`, `InnerLimit45Base.ofStages`);
2. "Retain `v_i`" (tex 3919): the witnesses `vv i` are part of the retained data;
3. the identity survives the inner limit along the fixed nonprincipal ultrafilter (tex 4447–4448,
   "Every polynomial identity between the matrices survives"): `limit_identity`, PROVED with lane
   RC6's ultralimits; the limit multiplier is `m = lim_U m_i ∈ ℤ₂` (`mu`);
4. the central comparison (tex 3952–3962: the comparison `i : K₀ → R₀`, in the coordinates of the
   two-term model at the centre) kills the degree-zero boundaries, sends the actual central cycle
   to the model's `z̄` and the Kummer cycle of `P` to `κ(P)` (fields `pi0`, `hpi`, `hz`, `kappa`,
   `hkappa`): hence "The boundary (4.5) gives `z₀ = i(LmP)`" (tex 3968), `central`, PROVED;
5. RC25's limit: `L κ(W_i) → z̄` along the ultrafilter (`tendsto_ultra`), hence along a strictly
   increasing sequence of stages; `toBoundary45Base` is RC25's `Boundary45Base` (field `hlim`
   included), PROVED.

Also PROVED, for the sentence "The uniform trace bound bounds `v₂(m_i)` and the local determinants
by `c_E`; their adjugate identities multiplied by a fixed power of two survive the limit"
(tex 3919–3921): `mu_not_dvd`, `mu_ne_zero` (the limit multiplier has `v₂(m) ≤ c_E`, in particular
`m ≠ 0`) and `localDet_survives` (`det X_i ∣ 2^c` for `U`-many stages gives a limit `X` with
`X Y = 2^c` and `det X ≠ 0`). They are not used by the bridge to lane RC25 (base zero uses only
`z̄ ∈ ℚ₂ · κ(P)`).

DEPARTUREs (form):
* the limit is the ultrafilter limit of Lemma `ex:limits-inner-limit` (faithful); lane RC25's
  field `hlim` is a limit along `atTop`; `toBoundary45Base` passes to a subsequence of stages
  (`exists_strictMono_tendsto_of_ultrafilter`), which only re-indexes the stages: the stages are
  indexed by the precision and the moving prime varies with it (tex 2739–2740);
* the stage data are taken in the fibre `t = 0`, over `ℤ/2^i`, as in (4.5); the inner limit over
  `Λ` followed by `t ↦ 0` is the same (`ulim_constantCoeff`, file `InnerLimit.lean`);
* the retained model ranks `N`, `M0` are fixed (the text fixes bounded ranks on a set in the
  ultrafilter, tex 4444–4445, lane RC6's `bounded_ranks_fixed`); `hstage` is required only on a
  set in the ultrafilter;
* the comparison is recorded through its degree-one component at the centre (a `ℚ₂`-linear map
  from the model coordinates of the actual cone to those of the two-term model); its chain-map
  property is `hpi`.

ELLIOT gap (definition supplied): the multiplier `m` of `z₀ = i(LmP)` (tex 3901, 3968) is not
defined in the text when the moving prime varies; here `m = lim_U m_i ∈ ℤ₂` (`mu`). Lane RC25
read it as the `atTop` limit when `κ(P) ≠ 0`; both agree along the subsequence of
`toBoundary45Base` (`Boundary45Base.tendsto_multiplier`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroLimit

open Filter Topology Matrix ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.BaseZeroAssembly

/-- The coordinatewise inclusion `ℤ₂ⁿ → ℚ₂ⁿ`. Kind: definition. -/
def toQVec {N : ℕ} (x : Fin N → ℤ_[2]) : Fin N → ℚ_[2] :=
  fun a => ((x a : ℤ_[2]) : ℚ_[2])

/-- `toQVec` is composition with the ring map `ℤ₂ → ℚ₂`. PROVED. -/
theorem toQVec_eq {N : ℕ} (x : Fin N → ℤ_[2]) : toQVec x = PadicInt.Coe.ringHom ∘ x :=
  rfl

/-! ## The retained inner-limit data of (4.5) at the base -/

/-- **The retained inner-limit data of the boundary (4.5) at the base** (tex 3912–3921,
3952–3968; Lemma `ex:limits-inner-limit`, tex 4401–4406, 4444–4450), for the specified point
`P : G` and the model's central cycle `z̄ ∈ ℚ₂ⁿ`. Fields, with kinds:

* `U`, `hU`: the one fixed nonprincipal ultrafilter on the coefficient stages (tex 4403–4404,
  4444; definition);
* `stage i`: the data of the `i`-th finite stage at the base (lane RC25's `SplitNormStage`: (4.1)
  at `(1, r_i)`, PRINT, Cai–Chen–Liu, Trans. AMS 370 (2018), Theorem 2.15, p. 3730, through `φ`,
  unweighted, so the print once `u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`; the ring-class data,
  definition; tex 2915–2932, 3904);
* `L`, `hL`: the fixed multiplier of Proposition `ex:arith-finite-heegner` ("with the same fixed
  `L`", tex 2860, 3897; definition);
* `N`, `M0`: the ranks, in degrees one and zero, of the retained finite free model of the stage
  Selmer cones in the fibre `t = 0`, fixed on a set in the ultrafilter (tex 4401–4402,
  4444–4445; definition; DEPARTURE: fixed for all stages);
* `zeta i`, `jay i`, `dd i`: lifts to `ℤ₂` of the model coordinates of the stage cycle `z_i(0)`,
  of the stage Kummer cycle `j_i(b₁)` of `b₁ = P`, and of the model differential from degree zero
  to degree one, over `ℤ/2^i` (definition);
* `vv i`: the retained witness `v_i` ("Retain `v_i`", tex 3919; definition);
* `hstage`: the finite-stage boundary (4.5), `z_i(0) − L m_i j_i(b₁) = d v_i` with
  `m_i = a_{r_i} − 2` (tex 3912–3918 at `h = 1`), modulo `(2^i)`, on a set in the ultrafilter
  (ELLIOT; PROVED per stage by lane RC25's `boundary45_finite`: `RetainedStage45.exists_witness`,
  `InnerLimit45Base.ofStages`);
* `pi0`: the central comparison in degree one: the actual Selmer cone in the fibre `t = 0`
  (tensored with `ℚ₂`) to the two-term model at the centre, through `i : K₀ → R₀` and the
  minimal-model comparison (tex 3952–3962, 4353–4360; definition);
* `hpi`: it kills the degree-zero boundaries of the limit cone (it is a chain map and the two-term
  model has no degree-zero term; definition);
* `hz`: it sends the actual central cycle (the inner limit of the retained stage cycles
  `z_i(0)`, tex 4274–4277) to the model's central cycle `z̄` (tex 4342–4343, 3961–3968;
  definition);
* `kappa`: the central Kummer comparison `i ∘ κ_K : E(K) → ℚ₂ⁿ` in the model's coordinates
  (tex 3952–3966; additive; definition);
* `hkappa`: the comparison of the `2`-adic Kummer cycle of `P` (the inner limit of the stage
  Kummer cycles `j_i(b₁)`) is `κ(P)` (tex 3965–3966, "`c(iP) = q c_K(P)`"; definition). -/
structure InnerLimit45Base {G : Type} [AddCommGroup G] (P : G) (n : ℕ) (zbar : Fin n → ℚ_[2]) :
    Type 1 where
  /-- the fixed ultrafilter on the coefficient stages -/
  U : Ultrafilter ℕ
  /-- it is nonprincipal -/
  hU : (U : Filter ℕ) ≤ cofinite
  /-- the finite stages at the base -/
  stage : ℕ → SplitNormStage P
  /-- the fixed multiplier `L` -/
  L : ℤ
  /-- `L ≠ 0` -/
  hL : L ≠ 0
  /-- the degree-one rank of the retained stage models -/
  N : ℕ
  /-- the degree-zero rank of the retained stage models -/
  M0 : ℕ
  /-- the model coordinates of `z_i(0)` -/
  zeta : ℕ → Fin N → ℤ_[2]
  /-- the model coordinates of `j_i(b₁)` -/
  jay : ℕ → Fin N → ℤ_[2]
  /-- the model differential from degree zero to degree one -/
  dd : ℕ → Matrix (Fin N) (Fin M0) ℤ_[2]
  /-- the retained witnesses `v_i` -/
  vv : ℕ → Fin M0 → ℤ_[2]
  /-- (4.5) at stage `i`, modulo `(2^i)` -/
  hstage : ∀ᶠ i in (U : Filter ℕ), ∀ a : Fin N,
    zeta i a - ((L * ((stage i).a - 2) : ℤ) : ℤ_[2]) * jay i a - (dd i *ᵥ vv i) a ∈
      twoAdicStage i
  /-- the central comparison in degree one -/
  pi0 : (Fin N → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2])
  /-- it kills the degree-zero boundaries of the limit cone -/
  hpi : ∀ v : Fin M0 → ℚ_[2], pi0 ((ulimMat U dd).map PadicInt.Coe.ringHom *ᵥ v) = 0
  /-- it sends the actual central cycle to `z̄` -/
  hz : pi0 (toQVec (ulimVec U zeta)) = zbar
  /-- the central Kummer comparison -/
  kappa : G →+ (Fin n → ℚ_[2])
  /-- it sends the Kummer cycle of `P` to `κ(P)` -/
  hkappa : pi0 (toQVec (ulimVec U jay)) = kappa P

namespace InnerLimit45Base

variable {G : Type} [AddCommGroup G] {P : G} {n : ℕ} {zbar : Fin n → ℚ_[2]}
  (B : InnerLimit45Base P n zbar)

/-- The moving multiplier `m_i = a_{r_i} − 2χ₁(r_i) = a_{r_i} − 2` of the `i`-th stage, in `ℤ₂`
(tex 3915 at `h = 1`). Kind: definition. -/
def mult (i : ℕ) : ℤ_[2] :=
  (((B.stage i).a - 2 : ℤ) : ℤ_[2])

/-- **The limit multiplier `m = lim_U m_i ∈ ℤ₂`** (the `m` of `z₀ = i(LmP)`, tex 3901, 3968; ELLIOT
gap, definition supplied). Kind: definition. -/
def mu : ℤ_[2] :=
  ulim B.U B.mult

/-- **The retained boundary survives the inner limit** (tex 3919–3921 with tex 4447–4448): in the
limit model coordinates, `z(0) − L m j(b₁) = d v` exactly, with `z(0)`, `j(b₁)`, `d`, `v` the
ultralimits of the retained stage data and `m = lim_U m_i`. PROVED (lane RC6's ultralimits:
`tendsto_ulim`, `ulimVec_mulVec`, `tendsto_zero_of_eventually_mem`). -/
theorem limit_identity (a : Fin B.N) :
    ulimVec B.U B.zeta a - (B.L : ℤ_[2]) * B.mu * ulimVec B.U B.jay a -
      (ulimMat B.U B.dd *ᵥ ulimVec B.U B.vv) a = 0 := by
  have hT : Tendsto (fun i => B.zeta i a - (B.L : ℤ_[2]) * B.mult i * B.jay i a -
      (B.dd i *ᵥ B.vv i) a) (B.U : Filter ℕ)
      (𝓝 (ulimVec B.U B.zeta a - (B.L : ℤ_[2]) * B.mu * ulimVec B.U B.jay a -
        (ulimMat B.U B.dd *ᵥ ulimVec B.U B.vv) a)) := by
    have h1 : Tendsto (fun i => B.zeta i a) (B.U : Filter ℕ) (𝓝 (ulimVec B.U B.zeta a)) :=
      tendsto_ulim B.U (fun i => B.zeta i a)
    have h2 : Tendsto B.mult (B.U : Filter ℕ) (𝓝 B.mu) := tendsto_ulim B.U B.mult
    have h3 : Tendsto (fun i => B.jay i a) (B.U : Filter ℕ) (𝓝 (ulimVec B.U B.jay a)) :=
      tendsto_ulim B.U (fun i => B.jay i a)
    have h4 : Tendsto (fun i => (B.dd i *ᵥ B.vv i) a) (B.U : Filter ℕ)
        (𝓝 ((ulimMat B.U B.dd *ᵥ ulimVec B.U B.vv) a)) := by
      rw [← ulimVec_mulVec]
      exact tendsto_ulim B.U (fun i => (B.dd i *ᵥ B.vv i) a)
    exact (h1.sub ((tendsto_const_nhds.mul h2).mul h3)).sub h4
  have h0 : Tendsto (fun i => B.zeta i a - (B.L : ℤ_[2]) * B.mult i * B.jay i a -
      (B.dd i *ᵥ B.vv i) a) (B.U : Filter ℕ) (𝓝 0) := by
    refine tendsto_zero_of_eventually_mem twoAdicStage_tendsToZero B.hU
      (B.hstage.mono fun i hi => ?_)
    have h := hi a
    simp only [mult]
    push_cast at h ⊢
    exact h
  exact tendsto_nhds_unique hT h0

/-- The limit identity, after `ℤ₂ → ℚ₂`: the actual central cycle is `L m` times the Kummer cycle
of `P` plus a boundary of the limit cone. PROVED. -/
theorem limit_identity_rat :
    toQVec (ulimVec B.U B.zeta) =
      ((B.L : ℚ_[2]) * (B.mu : ℚ_[2])) • toQVec (ulimVec B.U B.jay) +
        (ulimMat B.U B.dd).map PadicInt.Coe.ringHom *ᵥ toQVec (ulimVec B.U B.vv) := by
  funext a
  have h' : ulimVec B.U B.zeta a = (B.L : ℤ_[2]) * B.mu * ulimVec B.U B.jay a +
      (ulimMat B.U B.dd *ᵥ ulimVec B.U B.vv) a := by
    rw [← sub_eq_zero, ← B.limit_identity a]
    ring
  have hm := RingHom.map_mulVec (PadicInt.Coe.ringHom (p := 2)) (ulimMat B.U B.dd)
    (ulimVec B.U B.vv) a
  rw [← toQVec_eq] at hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hm]
  change PadicInt.Coe.ringHom (ulimVec B.U B.zeta a) = _
  rw [h', map_add, map_mul, map_mul, map_intCast]
  rfl

/-- **"The boundary (4.5) gives `z₀ = i(LmP)`"** (tex 3968), at the base: the model's central
cycle is `L m κ(P)` with `m = lim_U m_i` (`mu`). PROVED from the limit identity and the comparison
fields `hpi`, `hz`, `hkappa`. -/
theorem central : zbar = (B.L : ℚ_[2]) • ((B.mu : ℚ_[2]) • B.kappa P) := by
  have h := B.hz
  rw [B.limit_identity_rat, map_add, map_smul, B.hpi, add_zero, B.hkappa] at h
  exact h.symm.trans (smul_smul _ _ _).symm

/-- The central comparisons of the stages are `L m_i κ(P)` (lane RC25's
`SplitNormStage.weightedPoint_eq`). PROVED. -/
theorem stage_eq (i : ℕ) :
    (B.L : ℚ_[2]) • B.kappa (B.stage i).W = ((B.L : ℚ_[2]) * (B.mult i : ℚ_[2])) • B.kappa P := by
  have hm : (B.mult i : ℚ_[2]) = (((B.stage i).a - 2 : ℤ) : ℚ_[2]) := PadicInt.coe_intCast _
  rw [hm, (B.stage i).weightedPoint_eq, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ_[2], smul_smul]

/-- **The retained boundaries survive the limit at the centre, along the ultrafilter**: the
central comparisons `L κ(W_i)` of the stage classes converge to `z̄` along `U` (the inner-limit
form of lane RC25's `hlim`). PROVED. -/
theorem tendsto_ultra :
    Tendsto (fun i => (B.L : ℚ_[2]) • B.kappa (B.stage i).W) (B.U : Filter ℕ) (𝓝 zbar) := by
  have h : Tendsto (fun i => (B.L : ℚ_[2]) • B.kappa (B.stage i).W) (B.U : Filter ℕ)
      (𝓝 (((B.L : ℚ_[2]) * (B.mu : ℚ_[2])) • B.kappa P)) :=
    (((tendsto_coe_ulim B.U B.mult).const_mul (B.L : ℚ_[2])).smul_const
      (B.kappa P)).congr fun i => (B.stage_eq i).symm
  have hz : ((B.L : ℚ_[2]) * (B.mu : ℚ_[2])) • B.kappa P = zbar :=
    (B.central.trans (smul_smul _ _ _)).symm
  rwa [hz] at h

/-- The limit is attained along a strictly increasing sequence of stages. PROVED. -/
theorem exists_subseq : ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun k => (B.L : ℚ_[2]) • B.kappa (B.stage (φ k)).W) atTop (𝓝 zbar) :=
  exists_strictMono_tendsto_of_ultrafilter B.hU B.tendsto_ultra

/-- The chosen sequence of stages. Kind: definition. -/
def subseq : ℕ → ℕ :=
  Classical.choose B.exists_subseq

/-- The chosen sequence of stages is strictly increasing. PROVED. -/
theorem subseq_strictMono : StrictMono B.subseq :=
  (Classical.choose_spec B.exists_subseq).1

/-- **Bridge to lane RC25: `Boundary45Base` (with its field `hlim`) from the inner-limit data**
(tex 3912–3921, 3961–3968). The stages are those of the chosen subsequence; `L` and `κ` are
unchanged. PROVED. -/
def toBoundary45Base : Boundary45Base P n zbar where
  stage := fun k => B.stage (B.subseq k)
  L := B.L
  hL := B.hL
  kappa := B.kappa
  hlim := (Classical.choose_spec B.exists_subseq).2

/-- The bridge keeps the multiplier `L`. PROVED. -/
@[simp] theorem toBoundary45Base_L : B.toBoundary45Base.L = B.L :=
  rfl

/-- The bridge keeps the central Kummer comparison. PROVED. -/
@[simp] theorem toBoundary45Base_kappa : B.toBoundary45Base.kappa = B.kappa :=
  rfl

/-- **Lane RC25's field `hlim`, as a theorem** for the bridged stages:
`L κ(W_{φ(k)}) → z̄` along `atTop`. PROVED. -/
theorem hlim :
    Tendsto (fun k => (B.toBoundary45Base.L : ℚ_[2]) •
      B.toBoundary45Base.kappa (B.toBoundary45Base.stage k).W) atTop (𝓝 zbar) :=
  B.toBoundary45Base.hlim

/-- **The two readings of `m` agree** (ELLIOT gap, tex 3901, 3968): when `κ(P) ≠ 0`, the moving
multipliers of the bridged stages converge along `atTop` to the ultralimit `m = lim_U m_i` (lane
RC25's reading through `Boundary45Base.tendsto_multiplier`). PROVED. -/
theorem tendsto_mult_subseq (hP : B.kappa P ≠ 0) :
    Tendsto (fun k => ((((B.stage (B.subseq k)).a - 2 : ℤ)) : ℚ_[2])) atTop
      (𝓝 (B.mu : ℚ_[2])) :=
  Boundary45Base.tendsto_multiplier B.toBoundary45Base B.central hP

/-- **The use of (4.5) in the base-zero lemma** (tex 4345–4348): for a torsion specified point
the central cycle vanishes. PROVED (through the bridge, lane RC25's
`Boundary45Base.central_eq_zero_of_torsion`). -/
theorem central_eq_zero_of_torsion (B : InnerLimit45Base P n zbar) (hP : IsOfFinAddOrder P) :
    zbar = 0 :=
  Boundary45Base.central_eq_zero_of_torsion B.toBoundary45Base hP

/-! ## The uniform trace bound in the limit (tex 3919–3921) -/

/-- **The uniform trace bound passes to the limit multiplier** (tex 3919–3920: "The uniform trace
bound bounds `v₂(m_i)` … by `c_E`"): if `2^{c+1} ∤ m_i` for the stages of a set in the
ultrafilter, then `2^{c+1} ∤ m` in `ℤ₂`, i.e. `v₂(m) ≤ c`. PROVED (the limit is congruent to
`U`-many `m_i` modulo `2^{c+1}`: lane RC6's `eventually_sub_ulim_mem`). -/
theorem mu_not_dvd {c : ℕ}
    (hc : ∀ᶠ i in (B.U : Filter ℕ), ¬ (2 : ℤ) ^ (c + 1) ∣ ((B.stage i).a - 2)) :
    ¬ (2 : ℤ_[2]) ^ (c + 1) ∣ B.mu := by
  intro hdvd
  have hev := eventually_sub_ulim_mem (twoAdicStage_isOpen (c + 1)) B.U B.mult
  obtain ⟨i, hi, hi'⟩ := (hc.and hev).exists
  apply hi
  have hmem : B.mult i ∈ twoAdicStage (c + 1) := by
    have hsplit : B.mult i = (B.mult i - ulim B.U B.mult) + B.mu := by
      rw [mu]
      ring
    rw [hsplit]
    exact Ideal.add_mem _ hi' (mem_twoAdicStage_iff.mpr hdvd)
  have h1 : ‖B.mult i‖ ≤ ((2 : ℕ) : ℝ) ^ (-((c + 1 : ℕ) : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    simpa [twoAdicStage] using hmem
  have h2 := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := (B.stage i).a - 2)
    (n := c + 1)).mp (by simpa [mult] using h1)
  exact_mod_cast h2

/-- Under the uniform trace bound, the limit multiplier is nonzero. PROVED. -/
theorem mu_ne_zero {c : ℕ}
    (hc : ∀ᶠ i in (B.U : Filter ℕ), ¬ (2 : ℤ) ^ (c + 1) ∣ ((B.stage i).a - 2)) : B.mu ≠ 0 :=
  fun h => B.mu_not_dvd hc (h ▸ dvd_zero _)

end InnerLimit45Base

/-- **An adjugate identity multiplied by `2^c`** (tex 3919–3921): if `det X ∣ 2^c` in `ℤ₂`
(`v₂ det X ≤ c`), then `X (u · adj X) = 2^c` with `2^c = u det X`. PROVED. -/
theorem exists_mul_eq_two_pow_of_det_dvd {k : ℕ} (X : Matrix (Fin k) (Fin k) ℤ_[2]) {c : ℕ}
    (h : X.det ∣ (2 : ℤ_[2]) ^ c) :
    ∃ Y : Matrix (Fin k) (Fin k) ℤ_[2],
      X * Y = (2 : ℤ_[2]) ^ c • (1 : Matrix (Fin k) (Fin k) ℤ_[2]) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u • X.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hu, mul_comm]

/-- **The local determinants survive the limit** (tex 3919–3921: "The uniform trace bound bounds
… the local determinants by `c_E`; their adjugate identities multiplied by a fixed power of two
survive the limit"): if the stage matrices `X_i` (lifts to `ℤ₂` of the local blocks) have
`det X_i ∣ 2^c` for the stages of a set in the ultrafilter, then their ultralimit `X` satisfies
`X Y = 2^c` for the ultralimit `Y` of the multiplied adjugates, and `det X ≠ 0`. PROVED (lane
RC6's `matrix_identity_survives`). -/
theorem localDet_survives {k : ℕ} {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (X : ℕ → Matrix (Fin k) (Fin k) ℤ_[2]) {c : ℕ}
    (hdet : ∀ᶠ i in (U : Filter ℕ), (X i).det ∣ (2 : ℤ_[2]) ^ c) :
    ∃ Y : Matrix (Fin k) (Fin k) ℤ_[2],
      ulimMat U X * Y = (2 : ℤ_[2]) ^ c • (1 : Matrix (Fin k) (Fin k) ℤ_[2]) ∧
        (ulimMat U X).det ≠ 0 := by
  have hex : ∀ i, ∃ Y : Matrix (Fin k) (Fin k) ℤ_[2], (X i).det ∣ (2 : ℤ_[2]) ^ c →
      X i * Y = (2 : ℤ_[2]) ^ c • (1 : Matrix (Fin k) (Fin k) ℤ_[2]) := fun i => by
    by_cases h : (X i).det ∣ (2 : ℤ_[2]) ^ c
    · obtain ⟨Y, hY⟩ := exists_mul_eq_two_pow_of_det_dvd _ h
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Yi hYi using hex
  have hY : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      (X i * Yi i - (2 : ℤ_[2]) ^ c • (1 : Matrix (Fin k) (Fin k) ℤ_[2])) a b ∈ twoAdicStage i := by
    refine hdet.mono fun i hi a b => ?_
    rw [hYi i hi, sub_self, Matrix.zero_apply]
    exact Ideal.zero_mem _
  have hXY : ulimMat U X * ulimMat U Yi =
      (2 : ℤ_[2]) ^ c • (1 : Matrix (Fin k) (Fin k) ℤ_[2]) := by
    rw [← ulimMat_const U ((2 : ℤ_[2]) ^ c • (1 : Matrix (Fin k) (Fin k) ℤ_[2]))]
    exact matrix_identity_survives twoAdicStage_tendsToZero hU X Yi _ hY
  refine ⟨ulimMat U Yi, hXY, fun h0 => ?_⟩
  have hd := congrArg Matrix.det hXY
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero) hd.symm

/-! ## One retained stage: (4.5) in the model coordinates, from `boundary45_finite` -/

/-- **One retained finite stage of (4.5) at the base, at precision `i`** (tex 3912–3919, with the
finite free models of Lemma `ex:limits-inner-limit`, tex 4391–4399, 4428–4442). Fields, with
kinds:

* `S`: the stage data (lane RC25's `SplitNormStage`; PRINT (4.1), unweighted, so the print once
  `u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`; + definitions);
* the Selmer cone of the stage in the fibre `t = 0` (coefficients `ℤ/2^i`), exactly as in lane
  RC25's `boundary45_finite`: global cochains `G0 → G1 → G2`, local-condition cochains
  `U0 → U1 → U2`, local cochains `L0 → L1`, the maps `loc`, `ι` (chain maps: `hloc`, `hι`), the
  class map `cls` with `hexact` (`H¹ = Z¹/B¹`; definition), the Kummer map `δ` (definition), the
  two local facts `honto` (degree-zero local maps onto) and `hinj` (degree-one local maps inject)
  of tex 3917–3918 (ELLIOT), the cone cycles of `z_i(0)` and of `j_i(b₁)` (definition), the class
  of `z_i(0)` (`hzcls`: Proposition `ex:arith-finite-heegner` for `I = ∅`, the Kummer class of the
  `L`-multiplied weighted point; PROVED from the construction by lane RC25's
  `classAtBase_of_construction`) and the class of `j_i(b₁)` (`hjcls`: definition);
* `p1`, `p0`: the projections of the actual cone onto the retained finite free model, in degrees
  one and zero (tex 4428–4437: `p = p₀(1 + εh₀)⁻¹`), with values in `(ℤ/2^i)^N`, `(ℤ/2^i)^{M0}`;
  `dC`: a lift to `ℤ₂` of the model differential; `hdC`: `p` is a chain map (definition);
* `zeta`, `jay`: lifts to `ℤ₂` of the model coordinates of the two cycles (`hzeta`, `hjay`;
  definition). -/
structure RetainedStage45 {G : Type} [AddCommGroup G] (P : G) (L : ℤ) (i N M0 : ℕ) :
    Type 1 where
  /-- the stage data -/
  S : SplitNormStage P
  /-- global cochains, degree zero -/
  G0 : Type
  /-- global cochains, degree one -/
  G1 : Type
  /-- global cochains, degree two -/
  G2 : Type
  /-- local-condition cochains, degree zero -/
  U0 : Type
  /-- local-condition cochains, degree one -/
  U1 : Type
  /-- local-condition cochains, degree two -/
  U2 : Type
  /-- local cochains, degree zero -/
  L0 : Type
  /-- local cochains, degree one -/
  L1 : Type
  /-- global cohomology in degree one -/
  H1 : Type
  [aG0 : AddCommGroup G0]
  [aG1 : AddCommGroup G1]
  [aG2 : AddCommGroup G2]
  [aU0 : AddCommGroup U0]
  [aU1 : AddCommGroup U1]
  [aU2 : AddCommGroup U2]
  [aL0 : AddCommGroup L0]
  [aL1 : AddCommGroup L1]
  [aH1 : AddCommGroup H1]
  /-- global differential, degree zero -/
  dG0 : G0 →+ G1
  /-- global differential, degree one -/
  dG1 : G1 →+ G2
  /-- local-condition differential, degree zero -/
  dU0 : U0 →+ U1
  /-- local-condition differential, degree one -/
  dU1 : U1 →+ U2
  /-- local differential, degree zero -/
  dL0 : L0 →+ L1
  /-- localization, degree zero -/
  loc0 : G0 →+ L0
  /-- localization, degree one -/
  loc1 : G1 →+ L1
  /-- the local condition, degree zero -/
  ι0 : U0 →+ L0
  /-- the local condition, degree one -/
  ι1 : U1 →+ L1
  /-- localization is a chain map -/
  hloc : ∀ g, loc1 (dG0 g) = dL0 (loc0 g)
  /-- the local condition is a chain map -/
  hι : ∀ u, ι1 (dU0 u) = dL0 (ι0 u)
  /-- the local degree-zero maps are onto -/
  honto : ∀ c : L0, dL0 c = 0 → ∃ w : U0, dU0 w = 0 ∧ ι0 w = c
  /-- the local degree-one maps inject -/
  hinj : ∀ u : U1, dU1 u = 0 → (∃ c : L0, ι1 u = dL0 c) → ∃ w : U0, dU0 w = u
  /-- the class map -/
  cls : G1 →+ H1
  /-- a cocycle with zero class is a coboundary -/
  hexact : ∀ c : G1, dG1 c = 0 → cls c = 0 → ∃ g : G0, dG0 g = c
  /-- the global Kummer map -/
  δ : G →+ H1
  /-- the global part of `z_i(0)` -/
  zG : G1
  /-- the global part of `j_i(b₁)` -/
  jG : G1
  /-- the local-condition part of `z_i(0)` -/
  zU : U1
  /-- the local-condition part of `j_i(b₁)` -/
  jU : U1
  /-- the local part of `z_i(0)` -/
  zL : L0
  /-- the local part of `j_i(b₁)` -/
  jL : L0
  /-- cycle condition -/
  hzG : dG1 zG = 0
  /-- cycle condition -/
  hjG : dG1 jG = 0
  /-- cycle condition -/
  hzU : dU1 zU = 0
  /-- cycle condition -/
  hjU : dU1 jU = 0
  /-- cone cycle condition -/
  hz : loc1 zG - ι1 zU = dL0 zL
  /-- cone cycle condition -/
  hj : loc1 jG - ι1 jU = dL0 jL
  /-- the class of `z_i(0)` is the Kummer class of the `L`-multiplied weighted point -/
  hzcls : cls zG = δ (L • S.W)
  /-- the class of `j_i(b₁)` is the Kummer class of `P` -/
  hjcls : cls jG = δ P
  /-- the model projection in degree one -/
  p1 : G1 × U1 × L0 →+ (Fin N → ℤ_[2] ⧸ twoAdicStage i)
  /-- the model projection in degree zero -/
  p0 : G0 × U0 →+ (Fin M0 → ℤ_[2] ⧸ twoAdicStage i)
  /-- a lift of the model differential -/
  dC : Matrix (Fin N) (Fin M0) ℤ_[2]
  /-- the projection is a chain map -/
  hdC : ∀ (v : G0) (w : U0), p1 (dG0 v, dU0 w, loc0 v - ι0 w) =
    dC.map (Ideal.Quotient.mk (twoAdicStage i)) *ᵥ p0 (v, w)
  /-- lifted model coordinates of `z_i(0)` -/
  zeta : Fin N → ℤ_[2]
  /-- lifted model coordinates of `j_i(b₁)` -/
  jay : Fin N → ℤ_[2]
  /-- they are the coordinates of the cycle of `z_i(0)` -/
  hzeta : p1 (zG, zU, zL) = fun a => Ideal.Quotient.mk (twoAdicStage i) (zeta a)
  /-- they are the coordinates of the cycle of `j_i(b₁)` -/
  hjay : p1 (jG, jU, jL) = fun a => Ideal.Quotient.mk (twoAdicStage i) (jay a)

attribute [instance] RetainedStage45.aG0 RetainedStage45.aG1 RetainedStage45.aG2
  RetainedStage45.aU0 RetainedStage45.aU1 RetainedStage45.aU2 RetainedStage45.aL0
  RetainedStage45.aL1 RetainedStage45.aH1

/-- **(4.5) at one stage, in the retained model coordinates** (tex 3912–3919): there is a
retained witness `v` with `ζ − L m_i j − d v ≡ 0 (mod 2^i)`. PROVED from lane RC25's
`boundary45_finite` (the cone boundary `(v, w)`), the chain-map property of the model projection,
and lifting `p₀(v, w)` to `ℤ₂`. -/
theorem RetainedStage45.exists_witness {G : Type} [AddCommGroup G] {P : G} {L : ℤ} {i N M0 : ℕ}
    (C : RetainedStage45 P L i N M0) :
    ∃ v : Fin M0 → ℤ_[2], ∀ a : Fin N,
      C.zeta a - ((L * (C.S.a - 2) : ℤ) : ℤ_[2]) * C.jay a - (C.dC *ᵥ v) a ∈ twoAdicStage i := by
  obtain ⟨v, w, h1, h2, h3⟩ := boundary45_finite C.S C.dG0 C.dG1 C.dU0 C.dU1 C.dL0 C.loc0 C.loc1
    C.ι0 C.ι1 C.hloc C.hι C.honto C.hinj C.cls C.hexact C.δ L C.hzG C.hjG C.hzU C.hjU C.hz C.hj
    C.hzcls C.hjcls
  choose lift hlift using fun b => Ideal.Quotient.mk_surjective (C.p0 (v, w) b)
  refine ⟨lift, fun a => ?_⟩
  set c : ℤ := L * (C.S.a - 2) with hc
  have key : C.p1 (C.zG, C.zU, C.zL) - c • C.p1 (C.jG, C.jU, C.jL) =
      C.p1 (C.dG0 v, C.dU0 w, C.loc0 v - C.ι0 w) := by
    rw [← map_zsmul, ← map_sub]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.fst_sub, Prod.smul_fst]
      exact h1
    · simp only [Prod.snd_sub, Prod.fst_sub, Prod.smul_snd, Prod.smul_fst]
      exact h2
    · simp only [Prod.snd_sub, Prod.smul_snd]
      exact h3.symm
  rw [C.hzeta, C.hjay, C.hdC] at key
  have hp0 : C.p0 (v, w) = fun b => Ideal.Quotient.mk (twoAdicStage i) (lift b) :=
    funext fun b => (hlift b).symm
  have ha := congrFun key a
  simp only [Pi.sub_apply, Pi.smul_apply] at ha
  rw [zsmul_eq_mul, hp0] at ha
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, map_mul, map_intCast,
    RingHom.map_mulVec, ha]
  exact sub_self _

namespace InnerLimit45Base

/-- **The inner-limit data from retained stages** (tex 3912–3921): the field `hstage` (with the
retained witnesses `vv`) is supplied by `RetainedStage45.exists_witness`, i.e. by lane RC25's
`boundary45_finite`, at every stage; the remaining fields are the comparison data at the limit.
PROVED (a constructor). -/
def ofStages {G : Type} [AddCommGroup G] {P : G} {n : ℕ} {zbar : Fin n → ℚ_[2]}
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (L : ℤ) (hL : L ≠ 0) (N M0 : ℕ)
    (C : ∀ i, RetainedStage45 P L i N M0)
    (pi0 : (Fin N → ℚ_[2]) →ₗ[ℚ_[2]] (Fin n → ℚ_[2]))
    (hpi : ∀ v : Fin M0 → ℚ_[2],
      pi0 ((ulimMat U fun i => (C i).dC).map PadicInt.Coe.ringHom *ᵥ v) = 0)
    (hz : pi0 (toQVec (ulimVec U fun i => (C i).zeta)) = zbar)
    (kappa : G →+ (Fin n → ℚ_[2]))
    (hkappa : pi0 (toQVec (ulimVec U fun i => (C i).jay)) = kappa P) :
    InnerLimit45Base P n zbar where
  U := U
  hU := hU
  stage := fun i => (C i).S
  L := L
  hL := hL
  N := N
  M0 := M0
  zeta := fun i => (C i).zeta
  jay := fun i => (C i).jay
  dd := fun i => (C i).dC
  vv := fun i => Classical.choose (C i).exists_witness
  hstage := Eventually.of_forall fun i a => Classical.choose_spec (C i).exists_witness a
  pi0 := pi0
  hpi := hpi
  hz := hz
  kappa := kappa
  hkappa := hkappa

end InnerLimit45Base

end ZInQ.Manuscript.RC.BaseZeroLimit
