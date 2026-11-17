import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi

/-!
# gz-weil: a period lattice of `C_d` without the uniformization theorem; `hL3` (`C_d` form) from
# gz-hl3's three Heegner-point leaves

Task gz-weil (2026-11-15). Report: `docs/research/gz-weil.md`; scratch and log: `scratch/gz-weil/`.

gz-hl3's `heegner_at` takes `WeierstrassUniformization` only to produce a period lattice of `E`.
For `E = C_d` one is constructed here:
* L1 the square lattice `ℤ + ℤi` has `g₃ = 0` (it is stable under `i`), and every lattice with
  `g₃ = 0` has `g₂ ≠ 0` (`g₂_ne_zero_of_g₃_eq_zero`: otherwise `℘'² = 4℘³`, and at a zero of `℘`, which
  exists since `℘` is onto, the orders would satisfy `2(n − 1) = 3n`);
* L2 rescaling by a fourth root gives `g₂ = 4d²`, `g₃ = 0` (`exists_isPeriodLattice_cd`);
* L3 `heegner_at_of_lattice` (gz-hl3's proof with the lattice given) and
  `grossZagierHeegnerCd_of_threeLeaves : HeegnerPointRationalCd → GrossZagierFormulaCd →
  GrossConjugationCd → GZStatements.GrossZagierHeegnerCd`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Complex Filter Topology
open scoped Real

namespace ZInQ.GZWeil

/-! ## L1. A lattice with `g₃ = 0`, `g₂ ≠ 0` -/

/-- The square lattice `ℤ + ℤi`. -/
def squarePP : PeriodPair where
  ω₁ := 1
  ω₂ := I
  indep := by
    have := Complex.basisOneI.linearIndependent
    rwa [Complex.coe_basisOneI] at this

theorem G_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n := by
  let e : L.lattice ≃ L'.lattice :=
    { toFun := fun l => ⟨l, h ▸ l.2⟩
      invFun := fun l => ⟨l, h.symm ▸ l.2⟩
      left_inv := fun l => rfl
      right_inv := fun l => rfl }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq]
  rfl

theorem squarePP_lattice_I : (scalePP squarePP I I_ne_zero).lattice = squarePP.lattice := by
  ext x
  rw [mem_scalePP]
  simp only [PeriodPair.mem_lattice, squarePP]
  constructor
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    refine ⟨-n, m, ?_⟩
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨n * 1 + (-m) * I, ⟨n, -m, by push_cast; ring⟩, ?_⟩
    ring_nf
    rw [Complex.I_sq]
    ring

theorem g₃_squarePP : squarePP.g₃ = 0 := by
  have h := g₃_scalePP squarePP I_ne_zero
  rw [PeriodPair.g₃, PeriodPair.g₃, G_congr squarePP_lattice_I] at h
  have hI6 : (I ^ 6)⁻¹ = (-1 : ℂ) := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]; norm_num
  rw [hI6] at h
  rw [PeriodPair.g₃]
  linear_combination h / 2

/-- **`(g₂, g₃) ≠ (0, 0)` for every lattice**: if both vanished, `℘'² = 4℘³`, and at a zero of
`℘` (`℘` is onto) the orders of vanishing would satisfy `2(n − 1) = 3n`. -/
theorem g₂_ne_zero_of_g₃_eq_zero (L : PeriodPair) (h3 : L.g₃ = 0) : L.g₂ ≠ 0 := by
  intro h2
  obtain ⟨z1, hz1, hp⟩ := weierstrassP_surjective L 0
  have hrel : ∀ z ∉ L.lattice, L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 := by
    intro z hz; rw [L.derivWeierstrassP_sq z hz, h2, h3]; ring
  have ha : AnalyticAt ℂ L.weierstrassP z1 := L.analyticOnNhd_weierstrassP z1 hz1
  have hev : ∀ᶠ z in 𝓝 z1, z ∉ L.lattice :=
    L.isClosed_lattice.isOpen_compl.mem_nhds hz1
  -- order of `℘` at `z₁`
  rcases hord : analyticOrderAt L.weierstrassP z1 with _ | n
  · -- `℘ ≡ 0` near `z₁`, hence on the connected `ℂ ∖ L`
    have h0 : ∀ᶠ z in 𝓝 z1, L.weierstrassP z = 0 := analyticOrderAt_eq_top.mp hord
    apply weierstrassP_not_const L
    refine ⟨0, fun z hz => ?_⟩
    have := L.analyticOnNhd_weierstrassP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_lattice L).isPreconnected hz1 h0 hz
    simpa using this
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact ((ha.analyticOrderAt_eq_zero).mp (by rw [hord]; rfl)) hp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hd : analyticOrderAt (deriv L.weierstrassP) z1 = m :=
      analyticOrderAt_deriv_of_pos ha (by rw [hord]; rfl)
    rw [L.deriv_weierstrassP] at hd
    have hda : AnalyticAt ℂ L.derivWeierstrassP z1 := L.analyticOnNhd_derivWeierstrassP z1 hz1
    have heq : (fun z => L.derivWeierstrassP z ^ 2) =ᶠ[𝓝 z1] fun z => 4 * L.weierstrassP z ^ 3 := by
      filter_upwards [hev] with z hz using hrel z hz
    have h1 := analyticOrderAt_congr heq
    rw [show (fun z => L.derivWeierstrassP z ^ 2) = L.derivWeierstrassP ^ 2 from rfl,
      analyticOrderAt_pow hda, hd] at h1
    have h4 : analyticOrderAt (fun z => (4 : ℂ) * L.weierstrassP z ^ 3) z1 =
        analyticOrderAt L.weierstrassP z1 * 3 := by
      have := analyticOrderAt_mul (f := fun _ => (4 : ℂ)) (g := L.weierstrassP ^ 3)
        analyticAt_const (ha.pow 3)
      rw [show (fun z => (4 : ℂ) * L.weierstrassP z ^ 3) = (fun _ => (4 : ℂ)) *
        L.weierstrassP ^ 3 from rfl, this, analyticOrderAt_pow ha,
        (analyticAt_const.analyticOrderAt_eq_zero).mpr (by norm_num), zero_add]
      rw [nsmul_eq_mul, mul_comm]; norm_num
    rw [h4, hord] at h1
    have hc : (some m.succ : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := rfl
    rw [hc, nsmul_eq_mul] at h1
    have : ((2 * m : ℕ) : ℕ∞) = (((m + 1) * 3 : ℕ) : ℕ∞) := by push_cast; exact h1
    have := Nat.cast_injective this
    omega


/-! ## L2. A period lattice of `C_d` exists (no uniformization theorem needed) -/

theorem exists_isPeriodLattice_cd {d : ℕ} (hd : d ≠ 0) :
    ∃ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L := by
  have hg2 := g₂_ne_zero_of_g₃_eq_zero squarePP g₃_squarePP
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  set x : ℂ := squarePP.g₂ / (4 * (d : ℂ) ^ 2) with hx
  have hx0 : x ≠ 0 := div_ne_zero hg2 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd'))
  set lam : ℂ := x ^ ((4 : ℕ) : ℂ)⁻¹ with hlam
  have hl4 : lam ^ 4 = x := Complex.cpow_nat_inv_pow x (by norm_num)
  have hl0 : lam ≠ 0 := by
    intro h; rw [h] at hl4; exact hx0 (by rw [← hl4]; norm_num)
  refine ⟨scalePP squarePP lam hl0, (isPeriodLattice_cd_iff d _).mpr ⟨?_, ?_⟩⟩
  · rw [g₂_scalePP, hl4, hx]
    field_simp
  · rw [g₃_scalePP, g₃_squarePP, mul_zero]


/-! ## L3. `GrossZagierHeegnerCd` from gz-hl3's three Heegner-point leaves alone -/

section Heegner

open UpperHalfPlane HeckeRing.GL2 WeierstrassCurve ZInQ.GZDecomp ZInQ.GZHL3
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)
open scoped WeierstrassCurve.Affine Modular MatrixGroups

/-- gz-hl3's `heegner_at` with the period lattice given instead of the uniformization theorem
(verbatim proof otherwise). -/
theorem heegner_at_of_lattice (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hLat : ∃ L : PeriodPair, IsPeriodLattice E L)
    (hES : EichlerShimuraParamAt E) (hHP : HeegnerPointRationalAt E)
    (hGZ : GrossZagierFormulaAt E) (hGC : GrossConjugationAt E) :
    ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, n ≠ 0 → coeff f n = (E.LFunction n : ℂ)) →
    ∀ D : ℤ, IsOddImagFundDisc D → D < -4 → HeegnerHyp N D →
    ∀ F G : ℂ → ℂ, IsEntireCont (coeff f) 2 F → IsEntireCont (twistCoeff f D) 2 G →
      analyticOrderAt F 1 = 1 → G 1 ≠ 0 →
    ∀ (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K], Module.finrank ℚ K = 2 →
      (∃ δ : K, δ ^ 2 = algebraMap ℚ K D) →
      ∃ y : (E⁄K).Point, ¬IsOfFinAddOrder y ∧
        ∀ σ : K ≃ₐ[ℚ] K, IsOfFinAddOrder (Affine.Point.map σ.toAlgHom y - y) := by
  intro N _ f hχ hf D hDisc hD4 hHeeg F G hF hG h1 hG1 K _ _ instAlg hK2 ⟨δ, hδ⟩
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain rfl : instAlg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have : FiniteDimensional ℚ K := Module.finite_of_finrank_eq_succ hK2
  have : NumberField K := ⟨⟩
  have hδ' : δ ^ 2 = (D : K) := by rw [hδ]; simp
  obtain ⟨β, hβ⟩ := ZInQ.GZStatements.exists_sq_mod_four_mul_of_heegnerHyp (NeZero.ne N) hDisc hHeeg
  obtain ⟨S, hS⟩ := heegnerRepsExist N D β hDisc hβ
  obtain ⟨L, hL⟩ := hLat
  obtain ⟨c, hc, hcL⟩ := hES N f hχ hf L hL
  obtain ⟨ι, hι⟩ := exists_embedding hDisc.1 δ hδ'
  obtain ⟨y, hy⟩ := hHP N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι hι
  refine ⟨y, ?_, ?_⟩
  · -- infinite order: `ĥ(y) ≠ 0` since `L'(E/K, 1) = κ ĥ(y) ≠ 0`
    obtain ⟨κ, -, hκ⟩ := hGZ N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι
      hι y hy F G hF hG
    intro htors
    rw [WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_of_isOfFinAddOrder htors,
      Complex.ofReal_zero, mul_zero] at hκ
    exact deriv_mul_ne_zero hF.1 hG.1 h1 hG1 hκ
  · intro σ
    have hσ2 : (σ δ - δ) * (σ δ + δ) = 0 := by
      have : σ δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ', map_intCast]
      linear_combination this
    rcases mul_eq_zero.mp hσ2 with h | h
    · -- `σ = 1`
      have hnr : δ ∉ Set.range (algebraMap ℚ K) := by
        rintro ⟨q, rfl⟩
        have hq : q ^ 2 = (D : ℚ) := by
          apply (algebraMap ℚ K).injective
          rw [map_pow, hδ', map_intCast]
        have : (D : ℚ) < 0 := by exact_mod_cast hDisc.1
        nlinarith [sq_nonneg q]
      have := algEquiv_eq_one_of_fix hK2 hnr σ (sub_eq_zero.mp h)
      subst this
      rw [map_one_apply, sub_self]
      exact IsOfFinAddOrder.zero
    · have hw : rootNumber f hχ = -1 := signOfSimpleZero N f hχ F hF h1
      exact (hGC N f hχ hf D β hDisc hD4 hHeeg hβ S hS L c hL hc hcL K hK2 δ hδ' ι hι y hy σ
        (eq_neg_of_add_eq_zero_left h)).2 hw


/-- **`GZStatements.GrossZagierHeegnerCd` from gz-hl3's three Heegner-point leaves for `C_d`
alone**: the parametrization is proved (`shimuraCMParamCd_proved`) and a period lattice of `C_d`
is constructed (`exists_isPeriodLattice_cd`), so neither `WeierstrassUniformization` nor
`StrongWeilCurve`/`IsogenyLattice` is needed. -/
theorem grossZagierHeegnerCd_of_threeLeaves (hHP : HeegnerPointRationalCd)
    (hGZ : GrossZagierFormulaCd) (hGC : GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd := by
  intro d hd hsq
  have : (shortCurve (-(d : ℚ) ^ 2)).IsElliptic := shortCurve_cd_isElliptic (by omega)
  exact heegner_at_of_lattice _ (exists_isPeriodLattice_cd (by omega)) (shimuraCMParamCd_proved d hd hsq)
    (hHP d hd hsq) (hGZ d hd hsq) (hGC d hd hsq)

end Heegner

end ZInQ.GZWeil
