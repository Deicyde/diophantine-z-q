import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd

/-!
# heegner-32: `HeegnerPointRationalCd` from `hCM` and the used instance of the canonical model

`GZHeegner.heegnerPointRationalCd_of_printed` (gz-heegner) proves `GZHL3.HeegnerPointRationalCd` from
`T5Glue.ShimuraMainCM` (`hCM`) and `GZHeegner.X0ModuliGaloisMero` (the canonical model of `X₀(N)` for every
level `N` and every `g ∈ ℚ(X₀(N))` regular at the two points). The proof applies the latter only:

* at the level `N` of the newform `f` of `C_d` (forced to be `32 d²`: gz-statements' `level_eq_of_coeff_cd`),
* to the three functions `x∘φ`, `y∘φ`, `1/(x∘φ − t)` (`t ∈ {0, 1}`) of the parametrization
  `φ(τ) = weierPt C_d L (c φ_f(τ))`,
* at Heegner points `τ_Q`, `τ_{Q'}` of level `N` and one odd fundamental discriminant `D`.

`X0ModuliGaloisParamCd` is that instance; `heegnerPointRationalCd_of_used` proves `HeegnerPointRationalCd` from
`hCM` and it, and `x0ModuliGaloisParamCd_of_mero` shows it is implied by `X0ModuliGaloisMero`.
-/

noncomputable section

open UpperHalfPlane Complex WeierstrassCurve
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm cmPoint)
open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2
  ZInQ.Contrib.TYZDecomp.CurveA
open TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField
open ZInQ.GZHeegner
open scoped WeierstrassCurve.Affine MatrixGroups

namespace ZInQ.Heegner32

/-! ## §1. The used instance -/

/-- **The canonical model of `X₀(N)` for one function `g`, at Heegner points of one odd fundamental
discriminant.** The statement of `GZHeegner.X0ModuliGaloisMero` with `N` and `g` fixed, without the
hypothesis `g ∈ ℚ(X₀(N))`, and with `τ = τ_Q`, `τ' = τ_{Q'}` for Heegner forms `Q, Q'` of level `N` and the same
odd fundamental discriminant `D`: if `g` is regular at `τ_Q` and `τ_{Q'}`, the point `(E_{τ_Q}, ⟨1/N⟩)` of
`Y₀(N)` is algebraic, and `σ ∈ Aut(ℂ)` carries it to `(E_{τ_{Q'}}, ⟨k/N⟩)` (Weierstrass coordinates, as in
`X0ModuliGaloisMero`), then `σ(g(τ_Q)) = g(τ_{Q'})`. -/
def X0ModuliGaloisHeegnerMeroAt (N : ℕ) (g : UpperHalfPlane → ℂ) : Prop :=
  ∀ (σ : ℂ ≃+* ℂ) (D : ℤ), ZInQ.GZDecomp.IsOddImagFundDisc D →
    ∀ (Q Q' : HeegnerForm N D) (μ : ℂ), RegularAt g Q.tauH → RegularAt g Q'.tauH →
      (∀ i < N, ∃ a : Qbar, ιC a = T5Glue.modCoord N Q.tauH i) →
      T5Glue.IsConjModel (σ : ℂ →+* ℂ) (T5Glue.pp Q.tauH) (T5Glue.pp Q'.tauH) μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((T5Glue.pp Q.tauH).weierstrassP (1 / N)) = μ ^ 2 * (T5Glue.pp Q'.tauH).weierstrassP (k / N) ∧
        σ ((T5Glue.pp Q.tauH).derivWeierstrassP (1 / N)) =
          μ ^ 3 * (T5Glue.pp Q'.tauH).derivWeierstrassP (k / N)) →
      σ (g Q.tauH) = g Q'.tauH

/-- **CANONICAL MODEL OF `X₀(32 d²)` FOR THE COORDINATES OF THE PARAMETRIZATION OF `C_d`, AT HEEGNER POINTS**
(the used instance of `GZHeegner.X0ModuliGaloisMero`; kind: consequence, GLUE, not a print). For
`d ≡ 5 (mod 8)` squarefree, a newform `f` of `C_d : y² = x³ − d²x` (level `N`, forced to be `32 d²`), a period
lattice `L` of `C_d` and `c ∈ ℚ^×` with `c Λ_f ⊆ L` (`ParamSetting`), the three functions
`x∘φ`, `y∘φ`, `1/(x∘φ − t)` of `φ(τ) = weierPt C_d L (c φ_f(τ))` satisfy `X0ModuliGaloisHeegnerAt`.

Content: `x∘φ, y∘φ, 1/(x∘φ − t) ∈ ℚ(X₀(N))` (proved: `GZHeegner.isRatModFnMero_coords`) and `X₀(N)_ℚ` is the coarse
moduli space of pairs `(E, C)` compatibly with `Aut(ℂ)`, so `g(x)^σ = g(x^σ)` for `g ∈ ℚ(X₀(N))` regular at `x`
(Shimura 1971 §6.7, Prop. 6.9, Thm. 6.23; Deligne–Rapoport LNM 349 VI.6, VII; Diamond–Shurman §7.5–7.7; numbers
UNVERIFIED), applied at the CM points `τ_Q` of `X₀(32 d²)`. Implied by `X0ModuliGaloisMero`
(`x0ModuliGaloisParamCd_of_mero`). -/
def X0ModuliGaloisParamCd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d →
    ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (L : PeriodPair) (c : ℚ),
      ParamSetting (shortCurve (-(d : ℚ) ^ 2)) f L c →
      X0ModuliGaloisHeegnerMeroAt N (xPar (shortCurve (-(d : ℚ) ^ 2)) L f c) ∧
      X0ModuliGaloisHeegnerMeroAt N (yPar (shortCurve (-(d : ℚ) ^ 2)) L f c) ∧
      ∀ t : ℚ, X0ModuliGaloisHeegnerMeroAt N (gPar (shortCurve (-(d : ℚ) ^ 2)) L f c t)

/-- `X0ModuliGaloisMero` gives its instance at one `(N, g)` with `g ∈ ℚ(X₀(N))`. -/
theorem x0ModuliGaloisHeegnerMeroAt_of (h : X0ModuliGaloisMero) {N : ℕ} {g : UpperHalfPlane → ℂ}
    (hg : IsRatModFnMero N g) : X0ModuliGaloisHeegnerMeroAt N g :=
  fun σ _ _ Q Q' μ h1 h2 h3 h4 h5 =>
    h N (T5Glue.heegnerForm_level_pos Q) g hg σ Q.tauH Q'.tauH μ h1 h2 h3 h4 h5

/-- **The used instance is implied by the printed form.** -/
theorem x0ModuliGaloisParamCd_of_mero (h : X0ModuliGaloisMero) : X0ModuliGaloisParamCd := by
  intro d hd hsq N _ f L c hs
  have := ZInQ.GZDecomp.shortCurve_cd_isElliptic (d := d) (by omega)
  obtain ⟨mx, my, mg⟩ := isRatModFnMero_coords paramRegular paramCuspGrowth paramQExpansion _ f L c hs
  exact ⟨x0ModuliGaloisHeegnerMeroAt_of h mx, x0ModuliGaloisHeegnerMeroAt_of h my,
    fun t => x0ModuliGaloisHeegnerMeroAt_of h (mg t)⟩

/-! ## §2. The point transport from the three functions -/

/-- `GZHeegner.point_transport` with the hypothesis only for `x∘φ`, `y∘φ`, `1/(x∘φ − t)`. -/
theorem point_transport3 (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2)
    (L : PeriodPair) (c : ℚ) (hs : ParamSetting E f L c) (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane)
    (hσx : RegularAt (xPar E L f c) τ → RegularAt (xPar E L f c) τ' →
      σ (xPar E L f c τ) = xPar E L f c τ')
    (hσy : RegularAt (yPar E L f c) τ → RegularAt (yPar E L f c) τ' →
      σ (yPar E L f c τ) = yPar E L f c τ')
    (hσg : ∀ t : ℚ, RegularAt (gPar E L f c t) τ → RegularAt (gPar E L f c t) τ' →
      σ (gPar E L f c t τ) = gPar E L f c t τ') :
    Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c τ)) =
      ZInQ.GZHL3.weierPt E L (zPar f c τ') := by
  obtain ⟨-, hreg, hgreg⟩ := paramRegular E N f L c hs
  have hL := hs.2.2.1
  have avoid : ∀ w : ℂ, ∃ t : ℚ, w ≠ t := fun w => by
    by_cases h : w = ((0 : ℚ) : ℂ)
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨0, h⟩
  by_cases hz : zPar f c τ ∈ L.lattice <;> by_cases hz' : zPar f c τ' ∈ L.lattice
  · rw [weierPt_eq_zero E L hz, weierPt_eq_zero E L hz', map_zero]
  · exfalso
    obtain ⟨t, ht⟩ := avoid (xPar E L f c τ')
    have h := hσg t (hgreg t τ (Or.inl hz)) (hgreg t τ' (Or.inr ht))
    simp only [gPar, hz, hz', ite_true, ite_false, map_zero] at h
    exact inv_ne_zero (sub_ne_zero.2 ht) h.symm
  · exfalso
    obtain ⟨t, ht⟩ := avoid (xPar E L f c τ)
    have h := hσg t (hgreg t τ (Or.inr ht)) (hgreg t τ' (Or.inl hz'))
    simp only [gPar, hz, hz', ite_true, ite_false, map_eq_zero_iff _ σ.injective] at h
    exact inv_ne_zero (sub_ne_zero.2 ht) h
  · have hx := hσx (hreg τ hz).1 (hreg τ' hz').1
    have hy := hσy (hreg τ hz).2 (hreg τ' hz').2
    rw [weierPt_eq_some E hL hz, weierPt_eq_some E hL hz', Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩

/-! ## §3. The Heegner sum is fixed (gz-heegner's `heegnerC_fixed` with the used instance) -/

/-- The three instances for one `(E, f, L, c)`. -/
def Used3 (E : WeierstrassCurve ℚ) {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair) (c : ℚ) : Prop :=
  X0ModuliGaloisHeegnerMeroAt N (xPar E L f c) ∧ X0ModuliGaloisHeegnerMeroAt N (yPar E L f c) ∧
    ∀ t : ℚ, X0ModuliGaloisHeegnerMeroAt N (gPar E L f c t)

theorem heegnerC_fixed3 (hCM : T5Glue.ShimuraMainCM)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N] (f : Newform N 2) (L : PeriodPair)
    (c : ℚ) (hs : ParamSetting E f L c) (hU : Used3 E f L c) {m : ℕ} [NeZero m] (hsq : Squarefree m)
    (hm3 : m % 4 = 3) {β : ℤ} (S : Finset (HeegnerForm N (-(m : ℤ))))
    (hS : ZInQ.GZHL3.IsHeegnerReps N (-(m : ℤ)) β S)
    (σ : ℂ ≃+* ℂ) (hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k) :
    Affine.Point.map (sigA σ) (ZInQ.GZHL3.heegnerC E L f c S) =
      ZInQ.GZHL3.heegnerC E L f c S := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  obtain ⟨τg, hτg⟩ := T5Glue.exists_tau_of_sigma e he σ hσK
  obtain ⟨ρ, hρ⟩ := exists_galQ_of_sigma σ
  have hρe : ∀ x, ρ (e x) = e (τg x) := fun x => ιC.injective (by rw [← hρ, hτg])
  set O := conductorOrder (QNeg m) 1 with hO
  set cl : Pic O := (ringClassArtinEquiv O).symm
    (AlgEquiv.restrictNormalHom (ringClassField O) τg) with hcl
  set M : ℤ := ∏ Q ∈ S, Q.A with hMdef
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q _ => Q.A_pos.ne'
  obtain ⟨J, a, b, hJc, ha, hab, hcop, hJlat⟩ := heegnerClassJ m hsq hm3 M hM cl
  have hArt : ∀ x : ringClassField O,
      ρ (e x) = e (ringClassArtinEquiv O (O.picClass J) x) := by
    intro x
    rw [hJc, hρe, hcl, MulEquiv.apply_symm_apply]
    congr 1
    exact (AlgEquiv.restrictNormalHom_apply _ τg x).symm
  have hsqD : Squarefree (-(m : ℤ)) := squarefree_neg_iff.2 (Int.squarefree_natCast.2 hsq)
  have hfund : ZInQ.GZDecomp.IsOddImagFundDisc (-(m : ℤ)) := ⟨by
    have : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    omega, by omega, hsqD⟩
  have hdisc : -(m : ℤ) = discOf m 1 := by simp [discOf, hm3]
  have hCMM := T5Glue.cmModuli_of_t5 hCM
    (T5Glue.ideleLatticeScale_of T5Glue.ringClassLattice T5Glue.invertibleColon)
  have step : ∀ Q ∈ S, ∃ Q' : HeegnerForm N (-(m : ℤ)), ZInQ.GZHL3.HasResidue β Q' ∧
      jLat (-(m : ℤ)) a b * Q'.lat = Q.lat ∧ jLat (-(m : ℤ)) a b * Q'.latN = Q.latN ∧
      Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c Q.tauH)) =
        ZInQ.GZHL3.weierPt E L (zPar f c Q'.tauH) := by
    intro Q hQS
    have hcopQ : IsCoprime a Q.A :=
      IsCoprime.of_isCoprime_of_dvd_right hcop (Finset.dvd_prod_of_mem _ hQS)
    obtain ⟨Q', hBB, hlat, hlatN⟩ := exists_compose Q hsqD ha hab hcopQ
    have hres : ZInQ.GZHL3.HasResidue β Q' := by
      have h1 := hS.1 Q hQS
      obtain ⟨A₁, hA₁⟩ := Q.N_dvd
      show (2 * N : ℤ) ∣ Q'.B - β
      have : Q'.B - β = (Q'.B - Q.B) + (Q.B - β) := by ring
      rw [this]
      exact dvd_add (dvd_trans ⟨A₁, by rw [hA₁]; ring⟩ hBB) h1
    refine ⟨Q', hres, hlat, hlatN, ?_⟩
    obtain ⟨x, hx, hx'⟩ := hCMM N hN m 1 hsq e he J ρ hArt (-(m : ℤ)) hdisc Q Q' 1
      (by rw [map_mulLeft_one, hJlat]; exact hlat) (by rw [map_mulLeft_one, hJlat]; exact hlatN)
    have hmod : ∀ i < N, (σ : ℂ →+* ℂ) (T5Glue.modCoord N Q.tauH i) =
        T5Glue.modCoord N Q'.tauH i := by
      intro i hi; rw [← hx i hi, ← hx' i hi]; exact hρ (x i)
    obtain ⟨μ, hμ, hk⟩ := T5Glue.moduli_transport T5Glue.discNeZero (σ : ℂ →+* ℂ) hN hmod
    have halg : ∀ i < N, ∃ a : Qbar, ιC a = T5Glue.modCoord N Q.tauH i := fun i hi => ⟨x i, hx i hi⟩
    exact point_transport3 E f L c hs σ Q.tauH Q'.tauH
      (fun h1 h2 => hU.1 σ _ hfund Q Q' μ h1 h2 halg hμ hk)
      (fun h1 h2 => hU.2.1 σ _ hfund Q Q' μ h1 h2 halg hμ hk)
      (fun t h1 h2 => hU.2.2 t σ _ hfund Q Q' μ h1 h2 halg hμ hk)
  choose! Q' hQ'res hQ'lat hQ'latN hQ'pt using step
  have hrep : ∀ Q ∈ S, ∃ R ∈ S, ZInQ.GZHL3.Gamma0Equiv (Q' Q) R := fun Q hQ => by
    obtain ⟨R, ⟨hR, hE⟩, -⟩ := hS.2 (Q' Q) (hQ'res Q hQ)
    exact ⟨R, hR, hE⟩
  choose! π hπS hπE using hrep
  have hπpt : ∀ Q ∈ S, Affine.Point.map (sigA σ) (ZInQ.GZHL3.weierPt E L (zPar f c Q.tauH)) =
      ZInQ.GZHL3.weierPt E L (zPar f c (π Q).tauH) := by
    intro Q hQ
    rw [hQ'pt Q hQ]
    obtain ⟨γ, hγ, hγe⟩ := hπE Q hQ
    rw [← hγe, weierPt_smul hs.2.2.1 hs.2.2.2.2 hγ]
  have hπinj : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S, π Q₁ = π Q₂ → Q₁ = Q₂ := by
    intro Q₁ h1 Q₂ h2 hπ
    have hE : ZInQ.GZHL3.Gamma0Equiv (Q' Q₁) (Q' Q₂) :=
      ZInQ.GZHL3.Reps.equiv_trans (hπE Q₁ h1)
        (by rw [hπ]; exact ZInQ.GZHL3.Reps.equiv_symm (hπE Q₂ h2))
    obtain ⟨j, -, hjL, hjN⟩ := pairHom_of_equiv hE
    have hP : PairHom Q₁ Q₂ j := by
      constructor
      · rw [← hQ'lat Q₁ h1, ← hQ'lat Q₂ h2, hjL, mul_map_mulLeft]
      · rw [← hQ'latN Q₁ h1, ← hQ'latN Q₂ h2, hjN, mul_map_mulLeft]
    have hE' := equiv_of_pairHom hP
    obtain ⟨R, -, huniq⟩ := hS.2 Q₁ (hS.1 Q₁ h1)
    exact (huniq Q₁ ⟨h1, ZInQ.GZHL3.Reps.equiv_refl Q₁⟩).trans (huniq Q₂ ⟨h2, hE'⟩).symm
  unfold ZInQ.GZHL3.heegnerC
  rw [map_sum]
  refine Finset.sum_bij (fun Q _ => π Q) hπS (fun Q₁ h1 Q₂ h2 h => hπinj Q₁ h1 Q₂ h2 h) ?_ ?_
  · intro R hR
    obtain ⟨Q, hQ, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun Q _ => π Q) hπS
      (fun a₁ a₂ ha₁ ha₂ h => hπinj a₁ ha₁ a₂ ha₂ h) le_rfl R hR
    exact ⟨Q, hQ, h.symm⟩
  · intro Q hQ; exact hπpt Q hQ

/-! ## §4. `HeegnerPointRationalAt E` from `hCM` and the three instances -/

/-- **A point of `E(ℂ)` fixed by `Aut(ℂ/κ(ℚ(√−m)))` comes from `E(K)`** (the tail of gz-heegner's
`heegnerPointRational_of`). -/
theorem exists_point_of_fixed (E : WeierstrassCurve ℚ) {m : ℕ} [NeZero m]
    (P : (E⁄ℂ).toAffine.Point)
    (hfix : ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) →
      Affine.Point.map (sigA σ) P = P)
    (K : Type) [Field K] [NumberField K] [DecidableEq K] (δ : K) (hδ : δ ^ 2 = ((-(m : ℤ) : ℤ) : K))
    (ι : K →ₐ[ℚ] ℂ) (hι : ι δ = Complex.I * (Real.sqrt (-((-(m : ℤ) : ℤ) : ℝ)) : ℂ)) :
    ∃ y : (E⁄K).toAffine.Point, Affine.Point.map ι y = P := by
  have hδ' : δ * δ = (-(m : ℚ)) • (1 : K) + (0 : ℚ) • δ := by
    rw [← sq, hδ]; simp [Rat.smul_def]
  let θ : QNeg m →ₐ[ℚ] K := QuadraticAlgebra.lift ⟨δ, hδ'⟩
  have hιθ : ∀ k : QNeg m, ι (θ k) = kappa m k := by
    have h : ι.comp θ = kappaAlg m := by
      apply QuadraticAlgebra.algHom_ext
      rw [kappaAlg_apply, T5Glue.kappa_omega, AlgHom.comp_apply]
      have : θ QuadraticAlgebra.omega = δ := by simp [θ]
      rw [this, hι]
      push_cast; simp
    intro k
    rw [← kappaAlg_apply, ← h]; rfl
  rcases hZ : P with _ | ⟨x, y, hxy⟩
  · exact ⟨0, by rw [map_zero]; rfl⟩
  · have hfx : ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) → σ x = x ∧ σ y = y := by
      intro σ hσ
      have h := hfix σ hσ
      rw [hZ, Affine.Point.map_some] at h
      simp only [Affine.Point.some.injEq] at h
      exact h
    obtain ⟨k₁, hk₁⟩ := mem_kappa_of_fixed x (fun σ hσ => (hfx σ hσ).1)
    obtain ⟨k₂, hk₂⟩ := mem_kappa_of_fixed y (fun σ hσ => (hfx σ hσ).2)
    have hns : (E⁄K).Nonsingular (θ k₁) (θ k₂) := by
      rw [← WeierstrassCurve.Affine.baseChange_nonsingular (W := E) (f := ι) ι.injective,
        hιθ, hιθ, hk₁, hk₂]
      exact hxy
    refine ⟨.some _ _ hns, ?_⟩
    rw [Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨(hιθ k₁).trans hk₁, (hιθ k₂).trans hk₂⟩

theorem heegnerPointRationalAt_of_used (hCM : T5Glue.ShimuraMainCM) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hU : ∀ (N : ℕ) [NeZero N] (f : Newform N 2) (L : PeriodPair) (c : ℚ), ParamSetting E f L c →
      Used3 E f L c) :
    ZInQ.GZHL3.HeegnerPointRationalAt E := by
  intro N _ f hχ hcoeff D β hDf hD4 hHH hβ S hS L c hL hc hPer K _ _ _ hK2 δ hδ ι hι
  obtain ⟨hD0, hD1, hDsq⟩ := hDf
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, D = -(m : ℤ) := ⟨D.natAbs, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have : NeZero m := ⟨hm0⟩
  have hsq : Squarefree m := Int.squarefree_natCast.1 (squarefree_neg_iff.1 hDsq)
  have hm3 : m % 4 = 3 := by omega
  have hs : ParamSetting E f L c := ⟨hχ, hcoeff, hL, hc, hPer⟩
  exact exists_point_of_fixed E _ (heegnerC_fixed3 hCM E f L c hs (hU N f L c hs) hsq hm3 S hS)
    K δ hδ ι hι

/-! ## §5. The main theorem -/

/-- **`HeegnerPointRationalCd` from the main theorem of CM and the used instance of the canonical model.** -/
theorem heegnerPointRationalCd_of_used (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisParamCd) :
    ZInQ.GZHL3.HeegnerPointRationalCd := by
  intro d hd hsq
  have := ZInQ.GZDecomp.shortCurve_cd_isElliptic (d := d) (by omega)
  exact heegnerPointRationalAt_of_used hCM _ fun N _ f L c hs => hX d hd hsq N f L c hs

end ZInQ.Heegner32
