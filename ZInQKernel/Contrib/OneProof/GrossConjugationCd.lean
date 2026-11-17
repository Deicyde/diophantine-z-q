import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Heegner
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilParam
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice
import ZInQKernel.Contrib.GZStatements.Level
import ZInQKernel.Contrib.OneProof.FHNonvanishing.FE
import ZInQKernel.Contrib.HeckeAll.Provider

/-!
# gz-conj: Gross's conjugation relation on the curves `C_d` (`GZHL3.GrossConjugationCd`), proved

Task gz-conj (2026-11-16). Report: `docs/research/gz-conj.md`; scratch and log: `scratch/gz-conj/`.

`ZInQ.GZHL3.GrossConjugationCd` (`GrossZagierHeegner/Cd.lean`) is gz-hl3's leaf `GrossConjugationAt`
(Gross 1984 §5: `ȳ_K = −ε y_K` modulo torsion) for `E = C_d : y² = x³ − d²x`, `d ≡ 5 (mod 8)`
squarefree, stated for the analytic Heegner sum `Σ_{Q ∈ S} weierPt(c φ_f(τ_Q))`. It is a theorem
(`grossConjugationCd`), with no new leaf:

* **the root number** (§6): `rootNumber f = −1` for every newform `f` of `C_d`
  (`rootNumber_cd`): Tau Ceti's functional equation `Λ_N(2 − s) = ε Λ_N(s)` against the proved
  `FunctionalEquation5` at the level `N = 32 d²` forced by `level_eq_of_coeff_cd`, and
  `L(f, s) ≢ 0`. So the clause `ε = +1` is vacuous, and the Fricke sign is `+1`;
* **the Fricke involution** (§3): `f(−1/(Nz)) = ε_N N z² f(z)` (`fricke_apply`); for `ε_N = 1`
  the Eichler integral is `W_N`-invariant (`eichler_fricke`: zero derivative, fixed point
  `i/√N`); with real coefficients `conj φ_f(τ) = φ_f(−τ̄) = φ_f(1/(N τ̄))` (`conj_eichler_psi`);
* **the lattice** (§1, §2): a lattice is determined by `g₂, g₃` (`lattice_eq_of_g`: local
  uniqueness for `℘'² = 4℘³ − g₂℘ − g₃`, identity theorem off a countable set, poles), so the
  period lattice of `E/ℚ` is stable under conjugation and `conj ∘ weierPt = weierPt ∘ conj`
  (`map_conj_weierPt`);
* **the Heegner forms** (§4): `Q* = [N C, B, A/N]` has `τ_{Q*} = 1/(N τ̄_Q)`, the same residue,
  and `Q ↦ Q*` permutes the `Γ₀(N)`-classes (`sum_star_eq`); hence complex conjugation fixes the
  Heegner sum (`map_conj_heegnerC`) and `σ y = y` (`conj_clause`, for every `E/ℚ` with root
  number `−1`).

No `sorry`, no `axiom`.
-/

noncomputable section

open Filter Topology Complex UpperHalfPlane HeckeRing.GL2 CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped ComplexConjugate MatrixGroups

namespace ZInQ.GZConj

/-! ## §1. A lattice is determined by `g₂` and `g₃` -/

section Lattice

variable (L L' : PeriodPair)

theorem exists_deriv_ne : ∃ z ∉ L.lattice, L.derivWeierstrassP z ≠ 0 := by
  by_contra! h
  apply GZWeil.weierstrassP_not_const L
  have hUo : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hc := (GZWeil.isConnected_compl_lattice L).isPreconnected
  refine ⟨L.weierstrassP (L.ω₁ / 2), fun z hz => ?_⟩
  exact hUo.is_const_of_deriv_eq_zero hc
    (fun w hw => (GZWeil.hasDerivAt_wp L hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by rw [(GZWeil.hasDerivAt_wp L hw).deriv]; exact h w hw) hz
    L.ω₁_div_two_notMem_lattice

/-- **Local uniqueness.** Two Weierstrass functions with the same `g₂, g₃` and the same value and
derivative at a point (`℘' ≠ 0` there) agree near it, after the shift. -/
theorem local_eq_shift (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) {z0 δ : ℂ} (hz0 : z0 ∉ L.lattice)
    (hz1 : z0 + δ ∉ L'.lattice) (hx : L'.weierstrassP (z0 + δ) = L.weierstrassP z0)
    (hy : L'.derivWeierstrassP (z0 + δ) = L.derivWeierstrassP z0)
    (hy0 : L.derivWeierstrassP z0 ≠ 0) :
    ∀ᶠ z in 𝓝 z0, L'.weierstrassP (z + δ) = L.weierstrassP z := by
  set Ψ : ℂ → ℂ := fun z => L'.weierstrassP (z + δ) - L.weierstrassP z with hΨ
  have hwa : AnalyticAt ℂ (fun z : ℂ => z + δ) z0 := analyticAt_id.add analyticAt_const
  have hP'a : AnalyticAt ℂ (fun z => L'.weierstrassP (z + δ)) z0 :=
    AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_weierstrassP _ hz1) hwa
  have hpa : AnalyticAt ℂ L.weierstrassP z0 := L.analyticOnNhd_weierstrassP _ hz0
  have hD'a : AnalyticAt ℂ (fun z => L'.derivWeierstrassP (z + δ)) z0 :=
    AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_derivWeierstrassP _ hz1) hwa
  have hDa : AnalyticAt ℂ L.derivWeierstrassP z0 := L.analyticOnNhd_derivWeierstrassP _ hz0
  have hΨa : AnalyticAt ℂ Ψ z0 := hP'a.sub hpa
  have hΨ0 : Ψ z0 = 0 := by simp [hΨ, hx]
  have hevL : ∀ᶠ z in 𝓝 z0, z ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz0
  have hevL' : ∀ᶠ z in 𝓝 z0, z + δ ∉ L'.lattice :=
    (continuous_id.add continuous_const : Continuous fun z : ℂ => z + δ).continuousAt.eventually
      (L'.isClosed_lattice.isOpen_compl.mem_nhds hz1)
  have hden0 : L'.derivWeierstrassP (z0 + δ) + L.derivWeierstrassP z0 ≠ 0 := by
    rw [hy]; intro h; apply hy0; linear_combination h / 2
  have hevD : ∀ᶠ z in 𝓝 z0, L'.derivWeierstrassP (z + δ) + L.derivWeierstrassP z ≠ 0 :=
    (hD'a.add hDa).continuousAt.eventually_ne hden0
  set h : ℂ → ℂ := fun z => (4 * (L'.weierstrassP (z + δ) ^ 2 +
      L'.weierstrassP (z + δ) * L.weierstrassP z + L.weierstrassP z ^ 2) - L.g₂) /
      (L'.derivWeierstrassP (z + δ) + L.derivWeierstrassP z) with hh
  have hha : AnalyticAt ℂ h z0 := by
    refine AnalyticAt.div ?_ (hD'a.add hDa) hden0
    exact (analyticAt_const.mul (((hP'a.pow 2).add (hP'a.mul hpa)).add (hpa.pow 2))).sub
      analyticAt_const
  have hderiv : deriv Ψ =ᶠ[𝓝 z0] h * Ψ := by
    filter_upwards [hevL.eventually_nhds, hevL'.eventually_nhds, hevD] with z hzL hzL' hzD
    have hL0 : z ∉ L.lattice := hzL.self_of_nhds
    have hL1 : z + δ ∉ L'.lattice := hzL'.self_of_nhds
    have hcomp : HasDerivAt (fun z => L'.weierstrassP (z + δ)) (L'.derivWeierstrassP (z + δ) * 1) z :=
      HasDerivAt.comp (h := fun x : ℂ => x + δ) z (GZWeil.hasDerivAt_wp L' hL1) ((hasDerivAt_id' z).add_const δ)
    have hdΨ : HasDerivAt Ψ (L'.derivWeierstrassP (z + δ) * 1 - L.derivWeierstrassP z) z :=
      hcomp.sub (GZWeil.hasDerivAt_wp L hL0)
    rw [hdΨ.deriv]
    have r1 := L.derivWeierstrassP_sq z hL0
    have r2 := L'.derivWeierstrassP_sq (z + δ) hL1
    rw [← h2, ← h3] at r2
    simp only [Pi.mul_apply, hh, hΨ]
    field_simp
    linear_combination r2 - r1
  suffices hΨev : ∀ᶠ z in 𝓝 z0, Ψ z = 0 by
    filter_upwards [hΨev] with z hz
    exact sub_eq_zero.mp hz
  rw [← analyticOrderAt_eq_top]
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := (hΨa.analyticOrderAt_eq_zero).mp (by rw [← hm]; rfl)
    exact this hΨ0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have h1 : analyticOrderAt (deriv Ψ) z0 = n :=
    analyticOrderAt_deriv_of_pos hΨa (by rw [← hm]; rfl)
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hha hΨa, ← hm] at h1
  have : ((n.succ : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← h1]; exact le_add_self
  norm_cast at this
  omega

/-- **A lattice is determined by `g₂` and `g₃`** (one inclusion). -/
theorem lattice_le_of_g (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  obtain ⟨z0, hz0, hy0⟩ := exists_deriv_ne L
  obtain ⟨z1, hz1, hx1⟩ := GZWeil.weierstrassP_surjective L' (L.weierstrassP z0)
  have hsq : L'.derivWeierstrassP z1 ^ 2 = L.derivWeierstrassP z0 ^ 2 := by
    rw [L'.derivWeierstrassP_sq z1 hz1, L.derivWeierstrassP_sq z0 hz0, hx1, h2, h3]
  obtain ⟨z2, hz2, hx2, hy2⟩ : ∃ z2 ∉ L'.lattice, L'.weierstrassP z2 = L.weierstrassP z0 ∧
      L'.derivWeierstrassP z2 = L.derivWeierstrassP z0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨z1, hz1, hx1, h⟩
    · refine ⟨-z1, fun hm => hz1 (by simpa using L'.lattice.neg_mem hm), ?_, ?_⟩
      · rw [L'.weierstrassP_neg, hx1]
      · rw [L'.derivWeierstrassP_neg, h, neg_neg]
  set δ := z2 - z0 with hδdef
  have e : z0 + δ = z2 := by simp [δ]
  have hloc := local_eq_shift L L' h2 h3 hz0 (e ▸ hz2) (e ▸ hx2) (e ▸ hy2) hy0
  set U : Set ℂ := (L.lattice : Set ℂ)ᶜ ∩ ((fun z => z + δ) ⁻¹' (L'.lattice : Set ℂ))ᶜ with hU
  have hcount : ((L.lattice : Set ℂ) ∪ (fun z => z + δ) ⁻¹' (L'.lattice : Set ℂ)).Countable :=
    (GZWeil.countable_lattice L).union ((GZWeil.countable_lattice L').preimage (add_left_injective δ))
  have hUeq : U = ((L.lattice : Set ℂ) ∪ (fun z => z + δ) ⁻¹' (L'.lattice : Set ℂ))ᶜ := by
    rw [hU, Set.compl_union]
  have hUc : IsConnected U := hUeq ▸ hcount.isConnected_compl_of_one_lt_rank (by simp)
  have hΨa : AnalyticOnNhd ℂ (fun z => L'.weierstrassP (z + δ) - L.weierstrassP z) U :=
    fun z hz => (AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_weierstrassP _ hz.2)
      (analyticAt_id.add analyticAt_const)).sub (L.analyticOnNhd_weierstrassP z hz.1)
  have hz0U : z0 ∈ U := ⟨hz0, show z0 + δ ∉ L'.lattice by rw [e]; exact hz2⟩
  have heq : Set.EqOn (fun z => L'.weierstrassP (z + δ) - L.weierstrassP z) 0 U :=
    hΨa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected hz0U
      (by filter_upwards [hloc] with z hz; simp [hz])
  have key : ∀ l ∈ L.lattice, l + δ ∈ L'.lattice := by
    intro l hl
    by_contra hl'
    have hT := GZWeil.tendsto_weierstrassP_cobounded L hl
    have hc : ContinuousAt (fun z => L'.weierstrassP (z + δ)) l :=
      (AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_weierstrassP _ hl')
        (analyticAt_id.add analyticAt_const)).continuousAt
    have hev : (fun z => L'.weierstrassP (z + δ)) =ᶠ[𝓝[≠] l] L.weierstrassP := by
      have e1 : ∀ᶠ z in 𝓝[≠] l, z ∉ L.lattice := by
        filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l),
          self_mem_nhdsWithin] with z hz hzl
        exact fun hm => hz ⟨hm, hzl⟩
      have e2 : ∀ᶠ z in 𝓝[≠] l, z + δ ∉ L'.lattice :=
        ((continuous_id.add continuous_const : Continuous fun z : ℂ => z + δ).continuousAt.eventually
          (L'.isClosed_lattice.isOpen_compl.mem_nhds hl')).filter_mono nhdsWithin_le_nhds
      filter_upwards [e1, e2] with z hz1 hz2
      have := heq ⟨hz1, hz2⟩
      simpa [sub_eq_zero] using this
    have hT' := hT.congr' hev.symm
    have hb : Tendsto (fun z => L'.weierstrassP (z + δ)) (𝓝[≠] l)
        (𝓝 (L'.weierstrassP (l + δ))) := hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [← tendsto_norm_atTop_iff_cobounded] at hT'
    exact not_tendsto_atTop_of_tendsto_nhds hb.norm hT'
  have hδ : δ ∈ L'.lattice := by simpa using key 0 L.lattice.zero_mem
  intro l hl
  simpa using L'.lattice.sub_mem (key l hl) hδ

/-- **A lattice is determined by `g₂` and `g₃`.** -/
theorem lattice_eq_of_g (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) : L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g L L' h2 h3) (lattice_le_of_g L' L h2.symm h3.symm)

end Lattice


/-! ## §2. The conjugate lattice; conjugation of `weierPt` -/

section ConjLattice

open scoped ComplexConjugate

/-- The complex conjugate `L̄` of a period pair. -/
def conjPP (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    have := L.indep.map' Complex.conjLIE.toLinearEquiv.toLinearMap
      Complex.conjLIE.toLinearEquiv.ker
    convert this using 1
    ext i; fin_cases i <;> rfl

theorem mem_conjPP {L : PeriodPair} {x : ℂ} : x ∈ (conjPP L).lattice ↔ conj x ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, e⟩
    refine ⟨m, n, ?_⟩
    rw [← e]; simp [conjPP]
  · rintro ⟨m, n, e⟩
    refine ⟨m, n, ?_⟩
    have := congrArg conj e
    simp only [map_add, map_mul, map_intCast, Complex.conj_conj] at this
    simpa [conjPP] using this

/-- `l ↦ l̄`, `L → L̄`. -/
def conjEquiv (L : PeriodPair) : L.lattice ≃ (conjPP L).lattice where
  toFun l := ⟨conj (l : ℂ), mem_conjPP.2 (by simp)⟩
  invFun l := ⟨conj (l : ℂ), mem_conjPP.1 l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

theorem G_conjPP (L : PeriodPair) (n : ℕ) : (conjPP L).G n = conj (L.G n) := by
  rw [PeriodPair.G, PeriodPair.G, Complex.conj_tsum, ← (conjEquiv L).tsum_eq]
  congr 1
  ext l
  simp [conjEquiv]

theorem g₂_conjPP (L : PeriodPair) : (conjPP L).g₂ = conj L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_conjPP, map_mul, map_ofNat]

theorem g₃_conjPP (L : PeriodPair) : (conjPP L).g₃ = conj L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_conjPP, map_mul, map_ofNat]

/-- **A lattice with real `g₂, g₃` is stable under complex conjugation.** -/
theorem conj_mem_iff_of_real {L : PeriodPair} (h2 : conj L.g₂ = L.g₂) (h3 : conj L.g₃ = L.g₃)
    (x : ℂ) : conj x ∈ L.lattice ↔ x ∈ L.lattice := by
  have h := lattice_eq_of_g (conjPP L) L (by rw [g₂_conjPP, h2]) (by rw [g₃_conjPP, h3])
  rw [← mem_conjPP, h]

variable {L : PeriodPair} (hc : ∀ x, conj x ∈ L.lattice ↔ x ∈ L.lattice)

/-- `l ↦ l̄` on a conjugation-stable lattice. -/
def conjSelf : L.lattice ≃ L.lattice where
  toFun l := ⟨conj (l : ℂ), (hc l).2 l.2⟩
  invFun l := ⟨conj (l : ℂ), (hc l).2 l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

include hc in
theorem weierstrassP_conj (z : ℂ) : L.weierstrassP (conj z) = conj (L.weierstrassP z) := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, Complex.conj_tsum,
    ← (conjSelf hc).tsum_eq]
  congr 1
  ext l
  simp [conjSelf]

include hc in
theorem derivWeierstrassP_conj (z : ℂ) :
    L.derivWeierstrassP (conj z) = conj (L.derivWeierstrassP z) := by
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, map_neg, Complex.conj_tsum,
    ← (conjSelf hc).tsum_eq]
  congr 2
  ext l
  simp [conjSelf, map_ofNat]

end ConjLattice

section WeierPtConj

open scoped ComplexConjugate WeierstrassCurve.Affine
open WeierstrassCurve

/-- Complex conjugation as a `ℚ`-algebra map. -/
abbrev cq : ℂ →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom

theorem cq_apply (z : ℂ) : cq z = conj z := rfl

theorem conj_algebraMap (q : ℚ) : conj (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q := cq.commutes q

/-- The period lattice of `E/ℚ` is stable under complex conjugation. -/
theorem conj_mem_iff_of_isPeriodLattice {E : WeierstrassCurve ℚ} {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (x : ℂ) : conj x ∈ L.lattice ↔ x ∈ L.lattice := by
  refine conj_mem_iff_of_real ?_ ?_ x
  · rw [hL.1, show (E⁄ℂ).c₄ = algebraMap ℚ ℂ E.c₄ from E.map_c₄ _, map_div₀, conj_algebraMap,
      map_ofNat]
  · rw [hL.2, show (E⁄ℂ).c₆ = algebraMap ℚ ℂ E.c₆ from E.map_c₆ _, map_div₀, conj_algebraMap,
      map_ofNat]

/-- **Complex conjugation commutes with `z ↦ (℘(z) − b₂/12, …)`** for the period lattice of a
curve over `ℚ`. -/
theorem map_conj_weierPt (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (z : ℂ) :
    Affine.Point.map cq (ZInQ.GZHL3.weierPt E L z) = ZInQ.GZHL3.weierPt E L (conj z) := by
  have hc := conj_mem_iff_of_isPeriodLattice hL
  by_cases hz : z ∈ L.lattice
  · rw [GZHeegner.weierPt_eq_zero E L hz, GZHeegner.weierPt_eq_zero E L ((hc z).2 hz),
      Affine.Point.map_zero]
  · have hz' : conj z ∉ L.lattice := fun h => hz ((hc z).1 h)
    rw [GZHeegner.weierPt_eq_some E hL hz, GZHeegner.weierPt_eq_some E hL hz',
      Affine.Point.map_some]
    have hb : conj (E⁄ℂ).b₂ = (E⁄ℂ).b₂ := by
      rw [show (E⁄ℂ).b₂ = algebraMap ℚ ℂ E.b₂ from E.map_b₂ _, conj_algebraMap]
    have ha1 : conj (E⁄ℂ).a₁ = (E⁄ℂ).a₁ := conj_algebraMap _
    have ha3 : conj (E⁄ℂ).a₃ = (E⁄ℂ).a₃ := conj_algebraMap _
    simp only [cq_apply, map_sub, map_div₀, map_mul, map_ofNat, hb, ha1,
      ha3, weierstrassP_conj hc, derivWeierstrassP_conj hc]

end WeierPtConj

/-! ## §3. The Eichler integral under conjugation and under `W_N` -/

section Eichler

variable {N : ℕ} [NeZero N]

/-- `τ ↦ −τ̄` on `ℍ`. -/
def negConjH (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

theorem im_fricke_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / ((N : ℂ) * z)).im := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hz0 : (N : ℂ) * z ≠ 0 :=
    mul_ne_zero (by exact_mod_cast NeZero.ne N) (fun h => by simp [h] at hz)
  have hpos : 0 < Complex.normSq ((N : ℂ) * z) := Complex.normSq_pos.mpr hz0
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero, zero_mul, zero_div, zero_sub,
    neg_mul, one_mul, neg_div, neg_neg]
  positivity

/-- The Fricke involution `W_N : τ ↦ −1/(Nτ)` on `ℍ`. -/
def frickeH (τ : ℍ) : ℍ := ⟨-1 / ((N : ℂ) * τ), im_fricke_pos τ.im_pos⟩

/-- `ψ(τ) = W_N(−τ̄) = 1/(N τ̄)`. -/
def psiH (τ : ℍ) : ℍ := frickeH (N := N) (negConjH τ)

theorem coe_psiH (τ : ℍ) : (psiH (N := N) τ : ℂ) = 1 / ((N : ℂ) * conj (τ : ℂ)) := by
  show -1 / ((N : ℂ) * -conj (τ : ℂ)) = _
  rw [mul_neg, div_neg, neg_div, neg_neg]

variable (f : Newform N 2)

theorem conj_eichler
    (hreal : ∀ n : ℕ, n ≠ 0 → conj (ZInQ.GZDecomp.coeff f n) = ZInQ.GZDecomp.coeff f n)
    (τ : ℍ) : conj (ZInQ.GZHL3.eichler f τ) = ZInQ.GZHL3.eichler f (negConjH τ) := by
  rw [ZInQ.GZHL3.eichler, ZInQ.GZHL3.eichler, Complex.conj_tsum]
  congr 1
  ext n
  have h1 : conj ((n : ℂ) + 1) = (n : ℂ) + 1 := by simp
  rw [map_mul, map_div₀, hreal _ (Nat.succ_ne_zero n), h1, ← Complex.exp_conj]
  congr 2
  simp only [negConjH, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, h1]
  show _ = _ * -conj (τ : ℂ)
  ring

/-- `f(−1/(Nz)) = ε_N N z² f(z)` (the Fricke sign). -/
theorem fricke_apply (hχ : f.χ = 1) (z : ℂ) (hz : 0 < z.im)
    (hz' : 0 < (-1 / ((N : ℂ) * z)).im) :
    f.toCuspForm ⟨-1 / ((N : ℂ) * z), hz'⟩ = f.frickeSign hχ * N * z ^ 2 * f.toCuspForm ⟨z, hz⟩ := by
  have hfr := f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ
  set ε := f.frickeSign hχ
  have hnorm : TauCeti.atkinLehnerNormalizer N 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  have hM0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h := congrArg (fun F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 => (⇑F) ⟨z, hz⟩) hfr
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, hnorm, one_smul] at h
  rw [ModularForm.slash_apply] at h
  have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ N).det : ℝ) := TauCeti.val_det_frickeGL_pos
  have hσ : ∀ w : ℂ, σ (TauCeti.frickeGL ℝ N) w = w := fun w => by
    simp only [σ, if_pos hdet]; rfl
  have hpt : (TauCeti.frickeGL ℝ N • (⟨z, hz⟩ : ℍ)) = ⟨-1 / ((N : ℂ) * z), hz'⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom,
      TauCeti.coe_frickeGL]
    simp
  have hden : denom (TauCeti.frickeGL ℝ N) (⟨z, hz⟩ : ℍ) = (N : ℂ) * z := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL]
    simp
  have hdetv : |((TauCeti.frickeGL ℝ N).det : ℝ)| = N := by
    rw [TauCeti.val_det_frickeGL, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hσ, hpt, hden, hdetv, CuspForm.smul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  generalize f.toCuspForm ⟨-1 / ((N : ℂ) * z), hz'⟩ = A at h ⊢
  generalize f.toCuspForm ⟨z, hz⟩ = B at h ⊢
  push_cast at h
  have hne : ((N : ℂ) * z) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hM0 hz0)
  simp only [zpow_one, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h

/-- **For Fricke sign `+1` the Eichler integral is `W_N`-invariant**: `φ_f(−1/(Nτ)) = φ_f(τ)`
(the derivative of the difference is `2πi(ε_N − 1) f = 0`, and `i/√N` is fixed by `W_N`). -/
theorem eichler_fricke (hχ : f.χ = 1) (hε : f.frickeSign hχ = 1) (τ : ℍ) :
    ZInQ.GZHL3.eichler f (frickeH (N := N) τ) = ZInQ.GZHL3.eichler f τ := by
  set U : Set ℂ := {w : ℂ | 0 < w.im} with hU
  set F : ℂ → ℂ := fun w => (ZInQ.GZHL3.eichler f ∘ ofComplex) (-1 / ((N : ℂ) * w)) -
    (ZInQ.GZHL3.eichler f ∘ ofComplex) w with hF
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hd : ∀ w ∈ U, HasDerivAt F 0 w := by
    intro w hw
    have hw' : 0 < w.im := hw
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw'
    have hNw : (N : ℂ) * w ≠ 0 := mul_ne_zero hN0 hw0
    have hg : HasDerivAt (fun x : ℂ => -1 / ((N : ℂ) * x)) (1 / ((N : ℂ) * w ^ 2)) w := by
      have := (((hasDerivAt_id' w).const_mul (N : ℂ)).inv hNw).neg
      convert this using 1
      · funext x; simp only [Pi.neg_apply, Pi.inv_apply]; rw [neg_div, one_div]
      · field_simp
    have hwi := im_fricke_pos (N := N) hw'
    have h1 := HasDerivAt.comp (h := fun x : ℂ => -1 / ((N : ℂ) * x)) w
      (GZHeegner.hasDerivAt_eichler f ⟨-1 / ((N : ℂ) * w), hwi⟩) hg
    have h2 := GZHeegner.hasDerivAt_eichler f ⟨w, hw'⟩
    have h3 := h1.sub h2
    convert h3 using 1
    · funext x; rfl
    have hf := fricke_apply f hχ w hw' hwi
    rw [hf, hε]
    field_simp
    ring
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hc : ∀ x ∈ U, ∀ y ∈ U, F x = F y := fun x hx y hy =>
    hUo.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).deriv) hx hy
  -- the fixed point `i/√N`
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set s : ℝ := Real.sqrt N with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hNr
  have hs2 : ((s : ℂ)) ^ 2 = N := by
    rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hNr.le]; simp
  set w0 : ℂ := Complex.I / s with hw0
  have hw0im : 0 < w0.im := by
    rw [hw0, Complex.div_ofReal_im]; simp [hs0]
  have hfix : -1 / ((N : ℂ) * w0) = w0 := by
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [hw0, ← hs2]
    field_simp
    rw [Complex.I_sq]
  have hF0 : F w0 = 0 := by simp only [hF, hfix, sub_self]
  have hFτ := hc _ (show (τ : ℂ) ∈ U from τ.im_pos) _ (show w0 ∈ U from hw0im)
  rw [hF0] at hFτ
  have hτ' : 0 < (-1 / ((N : ℂ) * τ)).im := im_fricke_pos τ.im_pos
  simp only [hF, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hτ',
    UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos, sub_eq_zero] at hFτ
  exact hFτ

/-- **Conjugation of the Eichler integral, Fricke sign `+1`**: `conj φ_f(τ) = φ_f(1/(N τ̄))`. -/
theorem conj_eichler_psi (hχ : f.χ = 1) (hε : f.frickeSign hχ = 1)
    (hreal : ∀ n : ℕ, n ≠ 0 → conj (ZInQ.GZDecomp.coeff f n) = ZInQ.GZDecomp.coeff f n)
    (τ : ℍ) : conj (ZInQ.GZHL3.eichler f τ) = ZInQ.GZHL3.eichler f (psiH (N := N) τ) := by
  rw [conj_eichler f hreal, psiH, eichler_fricke f hχ hε]

end Eichler


/-! ## §4. The Heegner forms `Q* = [N C, B, A/N]` -/

section Forms

open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)

variable {N : ℕ} [NeZero N] {D : ℤ}

omit [NeZero N] in
theorem C_pos (Q : HeegnerForm N D) : 0 < Q.C := by
  have h := Q.disc
  have hD := Q.D_neg
  have hA := Q.A_pos
  by_contra hC
  have hC' : Q.C ≤ 0 := le_of_not_gt hC
  nlinarith [sq_nonneg Q.B, mul_nonpos_of_nonneg_of_nonpos hA.le hC']

omit [NeZero N] in
theorem star_disc (Q : HeegnerForm N D) : Q.B ^ 2 - 4 * ((N : ℤ) * Q.C) * (Q.A / N) = D := by
  have hA : (N : ℤ) * (Q.A / N) = Q.A := Int.mul_ediv_cancel' Q.N_dvd
  linear_combination Q.disc - 4 * Q.C * hA

/-- **`Q* = [N C, B, A/N]`**: the Heegner form with `τ_{Q*} = W_N(−τ̄_Q) = 1/(N τ̄_Q)` (same
discriminant, same `B`, hence the same residue). -/
def starForm (hsq : Squarefree D) (Q : HeegnerForm N D) : HeegnerForm N D where
  A := N * Q.C
  B := Q.B
  C := Q.A / N
  A_pos := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) (C_pos Q)
  N_dvd := dvd_mul_right _ _
  disc := star_disc Q
  D_neg := Q.D_neg
  primitive := GZHeegner.gcd_eq_one_of_squarefree hsq (star_disc Q)

theorem star_tauH (hsq : Squarefree D) (Q : HeegnerForm N D) :
    (starForm hsq Q).tauH = psiH (N := N) Q.tauH := by
  apply UpperHalfPlane.ext
  rw [coe_psiH]
  show cmPoint ((N : ℤ) * Q.C) Q.B D = 1 / ((N : ℂ) * conj (cmPoint Q.A Q.B D))
  have hD0 : (0 : ℝ) ≤ -(D : ℝ) := by
    have : (D : ℝ) < 0 := by exact_mod_cast Q.D_neg
    linarith
  set s : ℝ := Real.sqrt (-(D : ℝ)) with hs
  have hDr : (D : ℝ) < 0 := by exact_mod_cast Q.D_neg
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : (s : ℂ) ^ 2 = -(D : ℂ) := by
    rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hD0]; push_cast; ring
  have hconj : conj (cmPoint Q.A Q.B D) = (-(Q.B : ℂ) - Complex.I * s) / (2 * (Q.A : ℂ)) := by
    rw [ZInQ.Contrib.TYZGenus.CM.cmPoint]
    simp only [map_div₀, map_add, map_neg, map_mul, map_intCast, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  rw [hconj, ZInQ.Contrib.TYZGenus.CM.cmPoint, ← hs]
  have hA : (Q.A : ℂ) ≠ 0 := by exact_mod_cast Q.A_pos.ne'
  have hC : (Q.C : ℂ) ≠ 0 := by exact_mod_cast (C_pos Q).ne'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hden : -(Q.B : ℂ) - Complex.I * s ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hspos.ne' this
  have hdisc : ((Q.B : ℂ)) ^ 2 - 4 * Q.A * Q.C = D := by exact_mod_cast Q.disc
  push_cast
  field_simp
  linear_combination hdisc + hs2 - (s : ℂ) ^ 2 * Complex.I_sq

theorem psiH_psiH (τ : ℍ) : psiH (N := N) (psiH (N := N) τ) = τ := by
  apply UpperHalfPlane.ext
  rw [coe_psiH, coe_psiH]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  simp only [map_div₀, map_one, map_mul, map_natCast, Complex.conj_conj]
  field_simp

theorem psiH_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ γ' ∈ Gamma0 N, ∀ u : ℍ, psiH (N := N) (γ • u) = γ' • psiH (N := N) u := by
  obtain ⟨c₀, hc₀⟩ := GZHeegner.gamma0_dvd hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  let γ' : SL(2, ℤ) := ⟨!![γ 1 1, c₀; (N : ℤ) * γ 0 1, γ 0 0], by
    rw [Matrix.det_fin_two_of]; rw [hc₀] at hdet; linear_combination hdet⟩
  refine ⟨γ', ?_, fun u => ?_⟩
  · rw [Gamma0_mem]
    simp [γ']
  · apply UpperHalfPlane.ext
    rw [GZWeil.coe_smul_eq_moeb, coe_psiH, coe_psiH, GZWeil.coe_smul_eq_moeb, GZWeil.moeb,
      GZWeil.moeb]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hu : (u : ℂ) ≠ 0 := u.ne_zero
    have hcd := GZWeil.denom_ne_zero' γ u.im_pos
    have hab : ((γ 0 0 : ℤ) : ℂ) * u + ((γ 0 1 : ℤ) : ℂ) ≠ 0 := by
      intro h
      apply (γ • u).ne_zero
      rw [GZWeil.coe_smul_eq_moeb, GZWeil.moeb, h, zero_div]
    have hab' : ((γ 0 0 : ℤ) : ℂ) * conj (u : ℂ) + ((γ 0 1 : ℤ) : ℂ) ≠ 0 := by
      intro h; apply hab
      have := congrArg conj h
      simpa using this
    have hcd' : ((γ 1 0 : ℤ) : ℂ) * conj (u : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      intro h; apply hcd
      have := congrArg conj h
      simpa using this
    have hu' : conj (u : ℂ) ≠ 0 := by simpa using hu
    simp only [γ', Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    simp only [map_div₀, map_add, map_mul, map_intCast]
    rw [hc₀]
    push_cast
    rw [hc₀] at hcd'
    push_cast at hcd'
    have hab'' : conj (u : ℂ) * ((γ 0 0 : ℤ) : ℂ) + ((γ 0 1 : ℤ) : ℂ) ≠ 0 := by
      rwa [mul_comm]
    generalize conj (u : ℂ) = w at hab' hu' hcd' hab'' ⊢
    generalize ((γ 0 0 : ℤ) : ℂ) = a at hab' hab'' ⊢
    generalize ((γ 0 1 : ℤ) : ℂ) = b at hab' hab'' ⊢
    generalize ((γ 1 1 : ℤ) : ℂ) = d at hcd' ⊢
    generalize (c₀ : ℂ) = c at hcd' ⊢
    have h1 : (N : ℂ) * b * (1 / ((N : ℂ) * w)) + a = (a * w + b) / w := by field_simp; ring
    have h2 : d * (1 / ((N : ℂ) * w)) + c = ((N : ℂ) * c * w + d) / ((N : ℂ) * w) := by
      field_simp; ring
    rw [h1, h2]
    field_simp

theorem star_equiv_rev (hsq : Squarefree D) {Q₁ Q₂ : HeegnerForm N D}
    (h : ZInQ.GZHL3.Gamma0Equiv (starForm hsq Q₁) (starForm hsq Q₂)) :
    ZInQ.GZHL3.Gamma0Equiv Q₁ Q₂ := by
  obtain ⟨γ, hγ, he⟩ := h
  rw [star_tauH, star_tauH] at he
  obtain ⟨γ', hγ', hψ⟩ := psiH_smul (N := N) hγ
  refine ⟨γ', hγ', ?_⟩
  have := congrArg (psiH (N := N)) he
  rw [psiH_psiH, hψ, psiH_psiH] at this
  exact this

/-- **`Q ↦ Q*` permutes the `Γ₀(N)`-classes of residue `β`**: for a `Γ₀(N)`-invariant `g`, the
sum of `g(τ_{Q*})` over a complete set of representatives is the sum of `g(τ_Q)`. -/
theorem sum_star_eq {M : Type*} [AddCommMonoid M] (hsq : Squarefree D) {β : ℤ}
    {S : Finset (HeegnerForm N D)} (hS : ZInQ.GZHL3.IsHeegnerReps N D β S) (g : ℍ → M)
    (hg : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, g (γ • τ) = g τ) :
    ∑ Q ∈ S, g (starForm hsq Q).tauH = ∑ Q ∈ S, g Q.tauH := by
  classical
  have hrep : ∀ Q ∈ S, ∃ R ∈ S, ZInQ.GZHL3.Gamma0Equiv (starForm hsq Q) R := fun Q hQ => by
    obtain ⟨R, ⟨hR, hE⟩, -⟩ := hS.2 (starForm hsq Q) (hS.1 Q hQ)
    exact ⟨R, hR, hE⟩
  choose! π hπS hπE using hrep
  have hπg : ∀ Q ∈ S, g (starForm hsq Q).tauH = g (π Q).tauH := by
    intro Q hQ
    obtain ⟨γ, hγ, hγe⟩ := hπE Q hQ
    rw [← hγe, hg γ hγ]
  have hπinj : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, π Q₁ = π Q₂ → Q₁ = Q₂ := by
    intro Q₁ h1 Q₂ h2 hπ
    have hE : ZInQ.GZHL3.Gamma0Equiv (starForm hsq Q₁) (starForm hsq Q₂) :=
      ZInQ.GZHL3.Reps.equiv_trans (hπE Q₁ h1)
        (by rw [hπ]; exact ZInQ.GZHL3.Reps.equiv_symm (hπE Q₂ h2))
    have hE' := star_equiv_rev hsq hE
    obtain ⟨R, -, huniq⟩ := hS.2 Q₁ (hS.1 Q₁ h1)
    exact (huniq Q₁ ⟨h1, ZInQ.GZHL3.Reps.equiv_refl Q₁⟩).trans (huniq Q₂ ⟨h2, hE'⟩).symm
  refine Finset.sum_bij (fun Q _ => π Q) hπS (fun Q₁ h1 Q₂ h2 h => hπinj Q₁ h1 Q₂ h2 h) ?_ ?_
  · intro R hR
    obtain ⟨Q, hQ, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun Q _ => π Q) hπS
      (fun a₁ a₂ ha₁ ha₂ h => hπinj a₁ ha₁ a₂ ha₂ h) le_rfl R hR
    exact ⟨Q, hQ, h.symm⟩
  · intro Q hQ; exact hπg Q hQ

end Forms


/-! ## §5. Conjugation of the Heegner point -/

section HeegnerConj

open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine
open WeierstrassCurve ZInQ.GZDecomp

/-- **Complex conjugation fixes the Heegner sum when the Fricke sign is `+1`** (root number
`−1`): `conj (Σ_{Q ∈ S} φ(τ_Q)) = Σ_{Q ∈ S} φ(τ_{Q*}) = Σ_{Q ∈ S} φ(τ_Q)`. -/
theorem map_conj_heegnerC (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1) (hε : f.frickeSign hχ = 1)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) {D β : ℤ} (hsq : Squarefree D)
    {S : Finset (HeegnerForm N D)} (hS : ZInQ.GZHL3.IsHeegnerReps N D β S) {L : PeriodPair}
    {c : ℚ} (hL : ZInQ.GZHL3.IsPeriodLattice E L) (hP : ZInQ.GZHL3.PeriodsIn f c L) :
    Affine.Point.map cq (ZInQ.GZHL3.heegnerC E L f (c : ℂ) S) =
      ZInQ.GZHL3.heegnerC E L f (c : ℂ) S := by
  have hreal : ∀ n : ℕ, n ≠ 0 → conj (coeff f n) = coeff f n := fun n hn => by
    rw [hcoeff n hn, map_intCast]
  unfold ZInQ.GZHL3.heegnerC
  rw [map_sum]
  have step : ∀ Q ∈ S, Affine.Point.map cq (ZInQ.GZHL3.weierPt E L ((c : ℂ) * ZInQ.GZHL3.eichler f Q.tauH)) =
      ZInQ.GZHL3.weierPt E L ((c : ℂ) * ZInQ.GZHL3.eichler f (starForm hsq Q).tauH) := by
    intro Q _
    rw [map_conj_weierPt E hL, map_mul, map_ratCast, conj_eichler_psi f hχ hε hreal, star_tauH]
  rw [Finset.sum_congr rfl step]
  exact sum_star_eq hsq hS (fun τ => ZInQ.GZHL3.weierPt E L ((c : ℂ) * ZInQ.GZHL3.eichler f τ))
    (fun γ hγ τ => GZHeegner.weierPt_smul hL hP hγ τ)

/-- On a quadratic field `K = ℚ(δ)`, `δ² = D < 0`, with `ι(δ) = i√|D|` and `σ(δ) = −δ`:
`ι ∘ σ = conj ∘ ι`. -/
theorem iota_comp_sigma {K : Type} [Field K] [NumberField K] {D : ℤ} (hD : D < 0)
    (hK2 : Module.finrank ℚ K = 2) (δ : K) (hδ : δ ^ 2 = (D : K)) (ι : K →ₐ[ℚ] ℂ)
    (hι : ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) (σ : K ≃ₐ[ℚ] K) (hσ : σ δ = -δ) :
    ι.comp σ.toAlgHom = cq.comp ι := by
  have hδQ : ∀ q : ℚ, algebraMap ℚ K q ≠ δ := by
    intro q hq
    have h1 : q ^ 2 = (D : ℚ) := by
      apply (algebraMap ℚ K).injective
      rw [map_pow, hq, hδ, map_intCast]
    have h2 : (0 : ℚ) ≤ D := h1 ▸ sq_nonneg q
    have h3 : (0 : ℤ) ≤ D := by exact_mod_cast h2
    omega
  have hli : LinearIndependent ℚ ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hδQ (-s / t)
      have : t • δ = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
      have ht' : algebraMap ℚ K t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg, eq_comm, ← this]
      field_simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK2])
  apply AlgHom.toLinearMap_injective
  refine b.ext fun i => ?_
  fin_cases i
  · simp [b]
  · simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hσ, map_neg, hι, cq_apply,
      map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

/-- **The `ε = −1` half of Gross's conjugation relation, for every `E/ℚ`.** In the Heegner setting,
if the root number of `f` is `−1` (Fricke sign `+1`), then `σ y = y` for the Heegner point `y`. -/
theorem conj_clause (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2)
    (hχ : f.χ = 1) (hε : f.frickeSign hχ = 1)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) {D β : ℤ}
    (hDf : IsOddImagFundDisc D) {S : Finset (HeegnerForm N D)}
    (hS : ZInQ.GZHL3.IsHeegnerReps N D β S) {L : PeriodPair} {c : ℚ}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (hP : ZInQ.GZHL3.PeriodsIn f c L)
    {K : Type} [Field K] [NumberField K] [DecidableEq K] (hK2 : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = (D : K)) (ι : K →ₐ[ℚ] ℂ)
    (hι : ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) (y : (E⁄K).Point)
    (hy : Affine.Point.map ι y = ZInQ.GZHL3.heegnerC E L f c S) (σ : K ≃ₐ[ℚ] K)
    (hσ : σ δ = -δ) : Affine.Point.map σ.toAlgHom y - y = 0 := by
  have hισ := iota_comp_sigma hDf.1 hK2 δ hδ ι hι σ hσ
  apply Affine.Point.map_injective (f := ι)
  rw [map_sub, Affine.Point.map_map, hισ, ← Affine.Point.map_map, hy,
    map_conj_heegnerC E f hχ hε hcoeff hDf.2.2 hS hL hP, sub_self, map_zero]

end HeegnerConj

/-! ## §6. The root number of `C_d` -/

section RootNumber

open WeierstrassCurve ZInQ.GZDecomp

/-- **The root number of the newform of `C_d`, `d ≡ 5 (mod 8)`, is `−1`**: Tau Ceti's functional
equation `Λ_N(2 − s) = ε Λ_N(s)` against the proved `FunctionalEquation5` (`Λ(2 − s) = −Λ(s)` at
`N = 32 d²`, the level forced by `level_eq_of_coeff_cd`), and `L(f, s) ≢ 0`. -/
theorem rootNumber_cd {d : ℕ} (hd : d % 8 = 5) (hsq : Squarefree d) {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    rootNumber f hχ = -1 := by
  have hd4 : d % 4 = 1 := by omega
  have hd0 : d ≠ 0 := by omega
  have hN := ZInQ.GZStatements.level_eq_of_coeff_cd hd4 hsq f hχ hf
  obtain ⟨F, hF⟩ := ZInQ.Contrib.heckeContinuation d hd0
  have hFf : IsEntireCont (coeff f) 2 F := isEntireCont_of_isLContinuation hf hF
  have key : ∀ s : ℂ, 0 < s.re → s.re < 2 →
      (rootNumber f hχ + 1) * ZInQ.Literature.completedL N F s = 0 := by
    intro s h1 h2
    have e1 := ZInQ.GZFH.completedL_newform_sub f hχ hFf h1 h2
    have e2 := ZInQ.Contrib.functionalEquation5 d hd hsq F hF s h1 h2
    rw [← hN] at e2
    linear_combination e2 - e1
  by_contra hr
  have hr1 : rootNumber f hχ + 1 ≠ 0 := fun h => hr (by linear_combination h)
  have hN0 : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hF0 : ∀ s : ℂ, 0 < s.re → s.re < 2 → F s = 0 := by
    intro s h1 h2
    have h := (mul_eq_zero.mp (key s h1 h2)).resolve_left hr1
    simp only [ZInQ.Literature.completedL] at h
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    have hc1 : (N : ℂ) ^ (s / 2) ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
      (by intro h0; simp at h0; rw [h0] at h1; simp at h1)).mpr hN0
    have hc2 : (2 * Real.pi : ℂ) ^ (-s) ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero
      (by intro h0; rw [neg_eq_zero] at h0; rw [h0] at h1; simp at h1)).mpr hpi
    have hc3 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero hc1 hc2) hc3)
  have hFa : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hFf.1
  have hU : {s : ℂ | 0 < s.re ∧ s.re < 2} ∈ 𝓝 (1 : ℂ) :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds (by norm_num)
  have hev : F =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [hU] with s hs
    exact hF0 s hs.1 hs.2
  have hFz : ∀ s, F s = 0 := fun s =>
    hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 1) hev
      (Set.mem_univ s)
  have hLz : (fun x : ℝ => LSeries (coeff f) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    rw [← hFf.2 x (by simpa using hx)]
    exact hFz x
  rcases LSeries_eventually_eq_zero_iff'.mp hLz with h | h
  · have h1 := h 1 one_ne_zero
    rw [hf 1 one_ne_zero, ZInQ.GZStatements.LFunction_cd_eq_heckeCoeff hd4 hsq one_ne_zero,
      ZInQ.Contrib.HeckeFE.heckeCoeff_one] at h1
    exact one_ne_zero h1
  · have hab := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le f.toCuspForm
    simp only [strictWidthInfty_Gamma1] at hab
    have hab' : LSeries.abscissaOfAbsConv (coeff f) ≤ (((2 : ℤ) : ℝ) / 2 : ℝ) + 1 := hab
    rw [h] at hab'
    have h2 : ((((2 : ℤ) : ℝ) / 2 : ℝ) : EReal) + 1 = ((2 : ℝ) : EReal) := by
      rw [← EReal.coe_one, ← EReal.coe_add]; norm_num
    rw [h2] at hab'
    exact absurd hab' (not_le.mpr (EReal.coe_lt_top 2))

end RootNumber

/-! ## §7. `GrossConjugationCd` -/

section Main

open WeierstrassCurve ZInQ.GZDecomp
open scoped WeierstrassCurve.Affine

/-- **`GrossConjugationCd`, proved.** -/
theorem grossConjugationCd : ZInQ.GZHL3.GrossConjugationCd := by
  intro d hd hsq
  have := ZInQ.GZDecomp.shortCurve_cd_isElliptic (d := d) (by omega)
  intro N _ f hχ hcoeff D β hDf hD4 hHH hβ S hS L c hL hc hP K _ _ _ hK2 δ hδ ι hι y hy σ hσ
  have hr := rootNumber_cd hd hsq f hχ hcoeff
  refine ⟨fun h1 => absurd (h1.symm.trans hr) (by norm_num), fun _ => ?_⟩
  have hε : f.frickeSign hχ = 1 := by
    have : rootNumber f hχ = Complex.I ^ (2 : ℤ) * f.frickeSign hχ := rfl
    rw [hr, zpow_two, Complex.I_mul_I] at this
    linear_combination this
  rw [conj_clause _ f hχ hε hcoeff hDf hS hL hP hK2 δ hδ ι hι y hy σ hσ]
  exact IsOfFinAddOrder.zero

end Main

/-- **gz-weil's `C_d` split of `hL3` with `GrossConjugationCd` proved**: two leaves remain. -/
theorem grossZagierHeegnerCd_of_twoLeaves (hHP : ZInQ.GZHL3.HeegnerPointRationalCd)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) : ZInQ.GZStatements.GrossZagierHeegnerCd :=
  ZInQ.GZWeil.grossZagierHeegnerCd_of_threeLeaves hHP hGZ grossConjugationCd

/-- **The same, with gz-heegner's `HeegnerPointRationalCd`** (from `ShimuraMainCM`, already the
hypothesis `hCM` of `frozenTarget`, and the printed canonical model `X0ModuliGaloisMero`). -/
theorem grossZagierHeegnerCd_of_printed (hCM : T5Glue.ShimuraMainCM)
    (hX : ZInQ.GZHeegner.X0ModuliGaloisMero) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_twoLeaves (ZInQ.GZHeegner.heegnerPointRationalCd_of_printed hCM hX) hGZ

end ZInQ.GZConj
