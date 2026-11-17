import ZInQKernel.Contrib.OneProof.Gamma0QExp.LevelOne
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# gamma0-qexp, part 4: meromorphic level-one functions are rational in `j`

`levelOne_mero`: an `SL₂(ℤ)`-invariant function `F` on `ℍ`, meromorphic at every point, with
`ModGrowth F`, satisfies `B(j)·F = A(j)` on punctured neighbourhoods of every point of `ℍ`, for
polynomials `A, B ∈ ℂ[X]` with `B ≠ 0`.

Proof (pole clearing). The points of the truncated fundamental domain
`K = {|Re z| ≤ 1/2, 1/2 ≤ Im z ≤ T₀}` where `F` is not analytic are finitely many (`K` compact,
non-analytic points discrete); above `T₀` the growth bound makes `F` bounded. With
`Q = ∏_{z} (X − j(z))^M` (`M` the sum of the pole orders), `G = Q(j)·F` is invariant and locally
bounded on `ℍ` (reduce to the fundamental domain), so (Riemann's removable singularity theorem) it
agrees off its non-analytic points with a holomorphic invariant function of moderate growth, which
is a polynomial in `j` by `levelOne_hol`.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology Asymptotics Set
open scoped MatrixGroups Manifold

namespace ZInQ.Gamma0QExp

/-- The upper half plane as a subset of `ℂ`. -/
def UH : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_UH : IsOpen UH := isOpen_lt continuous_const Complex.continuous_im

theorem coe_mem_UH (τ : ℍ) : (τ : ℂ) ∈ UH := τ.im_pos

/-- **`P` holds on a punctured neighbourhood of every point of `ℍ`.** -/
def EvNe (P : ℍ → Prop) : Prop := ∀ w : ℍ, ∀ᶠ z in 𝓝[≠] (w : ℂ), P (ofComplex z)

theorem EvNe.and {P P' : ℍ → Prop} (h : EvNe P) (h' : EvNe P') : EvNe (fun τ => P τ ∧ P' τ) :=
  fun w => (h w).and (h' w)

theorem EvNe.mono {P P' : ℍ → Prop} (h : EvNe P) (hPP' : ∀ τ, P τ → P' τ) : EvNe P' :=
  fun w => (h w).mono fun _ hz => hPP' _ hz

theorem EvNe.finset {ι : Type*} (s : Finset ι) {P : ι → ℍ → Prop} (h : ∀ i ∈ s, EvNe (P i)) :
    EvNe (fun τ => ∀ i ∈ s, P i τ) :=
  fun w => (Filter.eventually_all_finset s).2 fun i hi => h i hi w

theorem EvNe.exists_im_gt {P : ℍ → Prop} (h : EvNe P) (Y : ℝ) : ∃ τ : ℍ, Y < τ.im ∧ P τ := by
  set w : ℍ := ⟨(max Y 0 + 1 : ℝ) * Complex.I, by simp; positivity⟩
  have h1 : ∀ᶠ z in 𝓝[≠] (w : ℂ), max Y 0 < z.im := by
    refine nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds ?_)
    show max Y 0 < (((max Y 0 + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    linarith
  obtain ⟨z, hz1, hz2⟩ := ((h w).and h1).exists
  have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right Y 0) hz2
  refine ⟨ofComplex z, ?_, hz1⟩
  rw [ofComplex_apply_of_im_pos hz0]
  exact lt_of_le_of_lt (le_max_left Y 0) hz2

theorem evNe_of_mem_codiscreteWithin {S : Set ℂ} (hS : S ∈ codiscreteWithin UH) (w : ℍ) :
    ∀ᶠ z in 𝓝[≠] (w : ℂ), z ∈ S ∧ z ∈ UH := by
  have h1 := (mem_codiscreteWithin.1 hS) w (coe_mem_UH w)
  rw [disjoint_principal_right] at h1
  have h2 : ∀ᶠ z in 𝓝[≠] (w : ℂ), z ∈ UH := nhdsWithin_le_nhds (isOpen_UH.mem_nhds (coe_mem_UH w))
  filter_upwards [h1, h2] with z hz1 hz2
  exact ⟨by by_contra hc; exact hz1 ⟨hz2, hc⟩, hz2⟩

/-! ### Möbius maps on `ℂ` -/

theorem continuousAt_ofComplex {z : ℂ} (hz : 0 < z.im) : ContinuousAt ofComplex z := by
  rw [isEmbedding_coe.continuousAt_iff]
  exact continuousAt_id.congr (eventuallyEq_coe_comp_ofComplex hz).symm

theorem continuous_SL_smul (γ : SL(2, ℤ)) : Continuous (fun τ : ℍ => γ • τ) := by
  simp_rw [ModularGroup.sl_moeb]
  exact continuous_const_smul _

/-- `z ↦ γ z` on `ℂ` (through `ofComplex`). -/
def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := ((γ • ofComplex z : ℍ) : ℂ)

theorem mob_coe (γ : SL(2, ℤ)) (τ : ℍ) : mob γ τ = ((γ • τ : ℍ) : ℂ) := by
  simp [mob]

theorem continuousAt_mob (γ : SL(2, ℤ)) (τ : ℍ) : ContinuousAt (mob γ) (τ : ℂ) :=
  continuous_coe.continuousAt.comp ((continuous_SL_smul γ).continuousAt.comp
    (continuousAt_ofComplex τ.im_pos))

theorem tendsto_mob (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (mob γ) (𝓝 (τ : ℂ)) (𝓝 ((γ • τ : ℍ) : ℂ)) := by
  have := (continuousAt_mob γ τ).tendsto
  rwa [mob_coe] at this

theorem tendsto_mob_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (mob γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((tendsto_mob γ τ).mono_left nhdsWithin_le_nhds) ?_
  have h2 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    nhdsWithin_le_nhds (isOpen_UH.mem_nhds (coe_mem_UH τ))
  filter_upwards [self_mem_nhdsWithin, h2] with z hz hzim
  intro h
  apply hz
  have h' : γ • ofComplex z = γ • τ := UpperHalfPlane.ext h
  have h'' := smul_left_cancel γ h'
  rw [ofComplex_apply_of_im_pos hzim] at h''
  exact congrArg UpperHalfPlane.coe h''

theorem eventually_mob_eq {G : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G (γ • τ) = G τ)
    (γ : SL(2, ℤ)) (τ : ℍ) : ∀ᶠ z in 𝓝 (τ : ℂ), (G ∘ ofComplex) (mob γ z) = (G ∘ ofComplex) z := by
  filter_upwards [isOpen_UH.mem_nhds (coe_mem_UH τ)] with z hz
  simp only [Function.comp_apply, mob, ofComplex_apply, hinv]

theorem eq_of_eventually_nhdsNE {f g : ℂ → ℂ} {z₀ : ℂ} (hf : ContinuousAt f z₀)
    (hg : ContinuousAt g z₀) (h : ∀ᶠ z in 𝓝[≠] z₀, f z = g z) : f z₀ = g z₀ :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ hz => hz.symm))

/-! ### The truncated fundamental domain -/

theorem isCompact_truncFd (T : ℝ) :
    IsCompact {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ T} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · refine (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |T|)).subset ?_
    rintro z ⟨h1, h2, h3⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h4 : |z.im| ≤ |T| := by
      rw [abs_of_pos (by linarith)]; exact le_trans h3 (le_abs_self T)
    have := Complex.norm_le_abs_re_add_abs_im z
    linarith

theorem im_gt_half_of_mem_fd {w : ℍ} (hw : w ∈ ModularGroup.fd) : 1 / 2 ≤ w.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hw
  nlinarith [w.im_pos]

/-! ### Local boundedness after pole clearing -/

theorem isBigO_one_of_continuousAt {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    f =O[𝓝 z] (fun _ => (1 : ℂ)) :=
  hf.tendsto.isBigO_one ℂ

/-- **Meromorphic level-one functions are rational in `j`.** -/
theorem levelOne_mero (F : ℍ → ℂ) (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) (hgr : ModGrowth F) :
    ∃ A B : Polynomial ℂ, B ≠ 0 ∧ EvNe (fun τ => B.eval (jf τ) * F τ = A.eval (jf τ)) := by
  classical
  obtain ⟨k, C, T₀', hb⟩ := hgr.exists_bound
  set T₀ := max T₀' 1
  set K : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ T₀}
  have hK : IsCompact K := isCompact_truncFd T₀
  have hKU : K ⊆ UH := fun z hz => lt_of_lt_of_le (by norm_num) hz.2.1
  set Fh : ℂ → ℂ := F ∘ ofComplex
  have hmerOn : MeromorphicOn Fh UH := fun z hz => hmer ⟨z, hz⟩
  set S : Set ℂ := {z | AnalyticAt ℂ Fh z}
  have hS : S ∈ codiscreteWithin UH := hmerOn.analyticAt_mem_codiscreteWithin
  have hZfin : (K \ S).Finite := hK.finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono hKU hS)
  set Z := hZfin.toFinset
  have hZ : ∀ z, z ∈ Z ↔ z ∈ K ∧ z ∉ S := fun z => by simp [Z]
  -- pole orders
  set n : ℂ → ℕ := fun z => if h : z ∈ UH then Classical.choose (hmerOn z h) else 0
  have hn : ∀ z ∈ UH, AnalyticAt ℂ (fun u => (u - z) ^ n z • Fh u) z := fun z hz => by
    simp only [n, dite_eq_left_iff, hz]
    exact Classical.choose_spec (hmerOn z hz)
  set M := ∑ z ∈ Z, n z
  set Q : Polynomial ℂ := ∏ z ∈ Z, (Polynomial.X - Polynomial.C (jf (ofComplex z))) ^ M
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun z _ =>
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  set G : ℍ → ℂ := fun τ => Q.eval (jf τ) * F τ
  set Gh : ℂ → ℂ := G ∘ ofComplex
  have hGinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G (γ • τ) = G τ := fun γ τ => by
    simp only [G, jf_smul, hinv]
  -- analyticity of `j` and of `Q(j)` on `ℍ`
  have hjA : ∀ z ∈ UH, AnalyticAt ℂ (jf ∘ ofComplex) z := fun z hz =>
    DifferentiableOn.analyticAt (fun u hu => (jf_differentiableAt ⟨u, hu⟩).differentiableWithinAt)
      (isOpen_UH.mem_nhds hz)
  have hQjA : ∀ (P : Polynomial ℂ), ∀ z ∈ UH, AnalyticAt ℂ (fun u => P.eval (jf (ofComplex u))) z :=
    fun P z hz => ((Polynomial.differentiable P).analyticAt _).comp (hjA z hz)
  have hGmer : MeromorphicOn Gh UH := fun z hz =>
    (hQjA Q z hz).meromorphicAt.mul (hmerOn z hz)
  -- local boundedness at points of the fundamental domain
  have hbddFd : ∀ w : ℍ, w ∈ ModularGroup.fd → Gh =O[𝓝 (w : ℂ)] (fun _ => (1 : ℂ)) := by
    intro w hw
    by_cases hw0 : T₀ < w.im
    · -- above `T₀`: `F` is bounded by the growth estimate
      have hF : Fh =O[𝓝 (w : ℂ)] (fun _ => (1 : ℂ)) := by
        refine IsBigO.of_bound (|C| * Real.exp (2 * Real.pi * k * (w.im + 1))) ?_
        have hnb : {u : ℂ | T₀ < u.im ∧ u.im < w.im + 1} ∈ 𝓝 (w : ℂ) :=
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds ⟨hw0, by
              show w.im < w.im + 1; linarith⟩
        filter_upwards [hnb] with u hu
        have hu0 : 0 < u.im := lt_of_lt_of_le (by positivity) (le_trans (le_max_right _ _) hu.1.le)
        simp only [Fh, Function.comp_apply, ofComplex_apply_of_im_pos hu0, norm_one, mul_one]
        have h1 := hb ⟨u, hu0⟩ (le_trans (le_max_left _ _) hu.1.le)
        refine le_trans h1 ?_
        have h2 : Real.exp (2 * Real.pi * k * u.im) ≤ Real.exp (2 * Real.pi * k * (w.im + 1)) := by
          rw [Real.exp_le_exp]
          have : (0 : ℝ) ≤ 2 * Real.pi * k := by positivity
          exact mul_le_mul_of_nonneg_left hu.2.le this
        calc C * Real.exp (2 * Real.pi * k * u.im) ≤ |C| * Real.exp (2 * Real.pi * k * u.im) :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      exact (isBigO_one_of_continuousAt (hQjA Q _ (coe_mem_UH w)).continuousAt).mul hF |>.trans
        (by simp [isBigO_refl])
    · push Not at hw0
      have hwK : (w : ℂ) ∈ K := ⟨hw.2, im_gt_half_of_mem_fd hw, hw0⟩
      by_cases hwS : (w : ℂ) ∈ S
      · exact isBigO_one_of_continuousAt
          (((hQjA Q _ (coe_mem_UH w)).mul hwS).continuousAt)
      · -- a pole: `Q(j)` vanishes to order `M ≥ n w` at `w`
        have hwZ : (w : ℂ) ∈ Z := (hZ _).2 ⟨hwK, hwS⟩
        set R : Polynomial ℂ := ∏ z ∈ Z.erase (w : ℂ),
          (Polynomial.X - Polynomial.C (jf (ofComplex z))) ^ M
        have hQR : Q = (Polynomial.X - Polynomial.C (jf w)) ^ M * R := by
          rw [show Q = ∏ z ∈ Z, (Polynomial.X - Polynomial.C (jf (ofComplex z))) ^ M from rfl,
            ← Finset.mul_prod_erase Z _ hwZ, ofComplex_apply]
        have hnM : n w ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hwZ
        have hj : (fun u => jf (ofComplex u) - jf w) =O[𝓝 (w : ℂ)] (fun u => u - w) := by
          have := (jf_differentiableAt w).isBigO_sub
          simpa only [Function.comp_apply, ofComplex_apply] using this
        have hQb : (fun u => Q.eval (jf (ofComplex u))) =O[𝓝 (w : ℂ)]
            (fun u => (u - w) ^ M) := by
          have h1 := (hj.pow M).mul (isBigO_one_of_continuousAt (hQjA R _ (coe_mem_UH w)).continuousAt)
          refine h1.congr (fun u => ?_) (fun u => by simp)
          rw [hQR, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C]
        have hFb : (fun u => (u - w) ^ n w * Fh u) =O[𝓝 (w : ℂ)] (fun _ => (1 : ℂ)) :=
          isBigO_one_of_continuousAt (hn _ (coe_mem_UH w)).continuousAt
        have hpow : (fun u : ℂ => (u - w) ^ (M - n w)) =O[𝓝 (w : ℂ)] (fun _ => (1 : ℂ)) :=
          isBigO_one_of_continuousAt ((continuous_id.sub continuous_const).pow _).continuousAt
        have h2 := hQb.mul (isBigO_refl Fh (𝓝 (w : ℂ)))
        refine h2.trans ?_
        refine ((hpow.mul hFb).congr (fun u => ?_) (fun u => by simp))
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnM]
  -- local boundedness everywhere
  have hbdd : ∀ τ : ℍ, Gh =O[𝓝 (τ : ℂ)] (fun _ => (1 : ℂ)) := by
    intro τ
    obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
    have h1 := (hbddFd _ hγ).comp_tendsto (tendsto_mob γ τ)
    refine (h1.congr' (eventually_mob_eq hGinv γ τ) (Eventually.of_forall fun _ => rfl))
  -- removable singularities
  set Gt : ℂ → ℂ := fun z => limUnder (𝓝[≠] z) Gh
  have hloc : ∀ z₀ ∈ UH, DifferentiableAt ℂ Gt z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, Gt z = Gh z := by
    intro z₀ hz₀
    obtain ⟨C', hC'⟩ := (hbdd ⟨z₀, hz₀⟩).bound
    have hev : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt ℂ Gh z ∧ ‖Gh z‖ ≤ C' := by
      exact (hGmer z₀ hz₀).eventually_analyticAt.and
        (nhdsWithin_le_nhds (hC'.mono fun x hx => by simpa using hx))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hεb⟩ := hev
    set s := Metric.ball z₀ ε
    have hs : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hε
    have hd := Complex.differentiableOn_update_limUnder_of_bddAbove hs
      (fun z hz => ((hεb hz.1 hz.2).1.differentiableAt).differentiableWithinAt)
      ⟨C', by rintro _ ⟨z, hz, rfl⟩; exact (hεb hz.1 hz.2).2⟩
    have heq : ∀ z ∈ s, Gt z = Function.update Gh z₀ (limUnder (𝓝[≠] z₀) Gh) z := by
      intro z hz
      by_cases hzz : z = z₀
      · subst hzz; simp [Gt]
      · rw [Function.update_of_ne hzz]
        exact ((hεb hz hzz).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
    refine ⟨((hd.differentiableAt hs).congr_of_eventuallyEq
      (Filter.eventually_of_mem hs heq)), ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hs] with z hz hzz
    rw [heq z hz, Function.update_of_ne hzz]
  have hGt_an : ∀ z ∈ UH, AnalyticAt ℂ Gh z → Gt z = Gh z := fun z _ hz =>
    (hz.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  -- the holomorphic invariant function on `ℍ`
  set G' : ℍ → ℂ := fun τ => Gt τ
  have hG'eq : ∀ z ∈ UH, (G' ∘ ofComplex) z = Gt z := fun z hz => by
    simp [G', ofComplex_apply_of_im_pos hz]
  have hG'md : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' := fun τ => mdifferentiableAt_iff.mpr <|
    ((hloc _ (coe_mem_UH τ)).1).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_UH.mem_nhds (coe_mem_UH τ)) hG'eq)
  have hG'inv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), G' (γ • τ) = G' τ := by
    intro γ τ
    have hc1 : ContinuousAt (Gt ∘ mob γ) (τ : ℂ) := by
      have := (hloc _ (coe_mem_UH (γ • τ))).1.continuousAt
      rw [← mob_coe] at this
      exact this.comp (continuousAt_mob γ τ)
    have hc2 := (hloc _ (coe_mem_UH τ)).1.continuousAt
    have h := eq_of_eventually_nhdsNE hc1 hc2 (by
      have e1 := (tendsto_mob_nhdsNE γ τ).eventually (hloc _ (coe_mem_UH (γ • τ))).2
      have e2 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), Gh (mob γ z) = Gh z :=
        nhdsWithin_le_nhds (eventually_mob_eq hGinv γ τ)
      filter_upwards [e1, e2, (hloc _ (coe_mem_UH τ)).2] with z h1 h2 h3
      simp only [Function.comp_apply] at h1 h2 ⊢
      rw [h1, h3]
      exact h2)
    simpa [G', Function.comp_apply, mob_coe] using h
  have hG'gr : ModGrowth G' := by
    have hGgr : ModGrowth G := (jf_modGrowth.polyEval Q).mul hgr
    obtain ⟨K', C2, T2, hb2⟩ := hGgr.exists_bound
    have hb' : ∀ τ : ℍ, T2 + 1 ≤ τ.im → ‖G' τ‖ ≤ C2 * Real.exp (2 * Real.pi * K' * τ.im) := by
      intro τ hτ
      have hc := (hloc _ (coe_mem_UH τ)).1.continuousAt
      have hGh : Tendsto Gh (𝓝[≠] (τ : ℂ)) (𝓝 (Gt τ)) :=
        (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' (hloc _ (coe_mem_UH τ)).2
      have hbc : Tendsto (fun z : ℂ => C2 * Real.exp (2 * Real.pi * K' * z.im)) (𝓝[≠] (τ : ℂ))
          (𝓝 (C2 * Real.exp (2 * Real.pi * K' * (τ : ℂ).im))) :=
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
          Complex.continuous_im))).tendsto _).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖Gh z‖ ≤ C2 * Real.exp (2 * Real.pi * K' * z.im) := by
        have hnb : {u : ℂ | T2 < u.im} ∈ 𝓝 (τ : ℂ) :=
          (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by
            show T2 < (τ : ℂ).im; rw [coe_im]; linarith)
        filter_upwards [nhdsWithin_le_nhds hnb,
          nhdsWithin_le_nhds (isOpen_UH.mem_nhds (coe_mem_UH τ))] with z hz hzU
        have hz' : (ofComplex z).im = z.im := by rw [ofComplex_apply_of_im_pos hzU]; rfl
        have := hb2 (ofComplex z) (by rw [hz']; exact hz.le)
        show ‖G (ofComplex z)‖ ≤ _
        rw [← hz']; exact this
      exact le_of_tendsto_of_tendsto hGh.norm hbc hev
    refine ⟨K', IsBigO.of_bound |C2| ((atImInfty_mem _).2 ⟨T2 + 1, fun τ hτ => ?_⟩)⟩
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact le_trans (hb' τ hτ) (mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le)
  obtain ⟨P, hP⟩ := levelOne_hol G' hG'md hG'inv hG'gr
  refine ⟨P, Q, hQ0, fun w => ?_⟩
  filter_upwards [evNe_of_mem_codiscreteWithin hGmer.analyticAt_mem_codiscreteWithin w]
    with z ⟨hzA, hzU⟩
  have h1 := hGt_an z hzU hzA
  have h2 := hP (ofComplex z)
  rw [show G' (ofComplex z) = Gt z from hG'eq z hzU] at h2
  rw [← h2, h1]
  rfl

end ZInQ.Gamma0QExp
