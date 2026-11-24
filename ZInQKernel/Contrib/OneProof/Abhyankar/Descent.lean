import ZInQKernel.Contrib.OneProof.Abhyankar.Defs

/-!
# abhyankar: `BranchDescent` (descent of unique normal branches along `S ⊆ S'`)

`S = A^L ⊆ S' = (A'')^Ω`. Uniqueness: going down (`Algebra.HasGoingDown` for an integral torsion-free
extension of the integrally closed `S`). Normality: for `z = a/b` integral over `S/Q`, the set
`I = {s : ∃ y ∈ S', s·a − b·y ∈ J}`, `J` the intersection of the primes of `S'` over `Q`, is not inside `𝔓`
(else a maximal `𝔓' ⊇ I S'` over `𝔓` contradicts the normality of the unique branch at `𝔓'`, the other primes
over `Q` being avoided by prime avoidance); then the trace `Tr_{Ω/L}`, which maps `S'` to `S` and `J` to `Q`
(trace as the sum of the conjugates, each in every prime over `Q` of the integral closure in `L̄`), gives
`(d s)·a ≡ b·Tr(y) mod Q`, `d = [Ω : L] ∉ 𝔓`.
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem transfer_rel {R S : Type} [CommRing R] [CommRing S] (Q : Ideal R) (Q' 𝔓' : Ideal S)
    [Q.IsPrime] [hQ' : Q'.IsPrime] (ι : R →+* S) (hle : Q ≤ Q'.comap ι) (a b : R) (hb : ι b ∉ Q')
    (P : (R ⧸ Q)[X]) (hPm : P.Monic)
    (h0 : (P.scaleRoots (Ideal.Quotient.mk Q b)).eval (Ideal.Quotient.mk Q a) = 0)
    (hnorm : ∀ (F : Type) [CommRing F] [Algebra (S ⧸ Q') F] [IsFractionRing (S ⧸ Q') F] (z : F),
      IsIntegral (S ⧸ Q') z → ∃ a s : S, s ∉ 𝔓' ∧
        algebraMap _ F (Ideal.Quotient.mk Q' s) * z = algebraMap _ F (Ideal.Quotient.mk Q' a)) :
    ∃ a' s' : S, s' ∉ 𝔓' ∧ s' * ι a - ι b * a' ∈ Q' := by
  let θ : R ⧸ Q →+* S ⧸ Q' := Ideal.quotientMap Q' ι hle
  have hθ : ∀ x : R, θ (Ideal.Quotient.mk Q x) = Ideal.Quotient.mk Q' (ι x) :=
    fun x => Ideal.quotientMap_mk
  let fF : S ⧸ Q' →+* FractionRing (S ⧸ Q') := algebraMap (S ⧸ Q') (FractionRing (S ⧸ Q'))
  have hfinj : Function.Injective fF := IsFractionRing.injective _ _
  have hb0' : θ (Ideal.Quotient.mk Q b) ≠ 0 := by
    rw [hθ]
    intro h
    exact hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hfb : fF (θ (Ideal.Quotient.mk Q b)) ≠ 0 := by
    rw [Ne, ← map_zero fF]; exact fun h => hb0' (hfinj h)
  let z' : FractionRing (S ⧸ Q') := fF (θ (Ideal.Quotient.mk Q a)) / fF (θ (Ideal.Quotient.mk Q b))
  have hz'mul : fF (θ (Ideal.Quotient.mk Q b)) * z' = fF (θ (Ideal.Quotient.mk Q a)) := by
    simp only [z']; field_simp
  have hz' : IsIntegral (S ⧸ Q') z' := by
    refine ⟨P.map θ, hPm.map θ, ?_⟩
    have hsc : (P.map θ).scaleRoots (θ (Ideal.Quotient.mk Q b)) =
        (P.scaleRoots (Ideal.Quotient.mk Q b)).map θ :=
      (map_scaleRoots P _ θ (by rw [hPm.leadingCoeff, map_one]; exact one_ne_zero)).symm
    have h2 := scaleRoots_eval₂_mul (p := P.map θ) fF z' (θ (Ideal.Quotient.mk Q b))
    rw [hsc, hz'mul, eval₂_at_apply, eval_map, eval₂_at_apply, h0, map_zero, map_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hfb)
  obtain ⟨a', s', hs', hsa⟩ := hnorm _ z' hz'
  refine ⟨a', s', hs', ?_⟩
  have e : fF (Ideal.Quotient.mk Q' (s' * ι a)) = fF (Ideal.Quotient.mk Q' (ι b * a')) := by
    have h3 := congrArg (· * fF (θ (Ideal.Quotient.mk Q b))) hsa
    rw [mul_assoc, mul_comm z', hz'mul, hθ, hθ] at h3
    rw [map_mul, map_mul, map_mul, map_mul, h3, mul_comm]
  exact Ideal.Quotient.eq.mp (hfinj e)

/-- **`BranchDescent` is proved.** -/
theorem branchDescent : BranchDescent := by
  intro A K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A'' hA'' hnoeth 𝔮 h𝔮 hbr 𝔓 h𝔓 Q hQ hQu hQ𝔓 hd
  classical
  haveI := hA''
  haveI := hnoeth
  haveI := h𝔓.isPrime
  haveI := hQ
  haveI : IsScalarTower A L Ω := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L Ω])
  have hintΩ : ∀ x : (integralClosure A L), IsIntegral A'' (algebraMap L Ω x) := fun x =>
    ((x.2 : IsIntegral A (x : L)).map (IsScalarTower.toAlgHom A L Ω)).tower_top
  let ι : (integralClosure A L) →+* (integralClosure A'' Ω) := RingHom.codRestrict ((algebraMap L Ω).comp (algebraMap (integralClosure A L) L)) (integralClosure A'' Ω).toSubring
    (fun x => hintΩ x)
  have hι : ∀ x : (integralClosure A L), ((ι x : (integralClosure A'' Ω)) : Ω) = algebraMap L Ω x := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro x y h
    have := congrArg (fun w : (integralClosure A'' Ω) => (w : Ω)) h
    simp only [hι] at this
    exact Subtype.ext ((algebraMap L Ω).injective this)
  letI : Algebra (integralClosure A L) (integralClosure A'' Ω) := ι.toAlgebra
  haveI : IsScalarTower A (integralClosure A L) (integralClosure A'' Ω) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    show algebraMap A'' Ω (algebraMap A A'' a) = algebraMap L Ω (algebraMap A L a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
  haveI : Algebra.IsIntegral A (integralClosure A'' Ω) := Algebra.IsIntegral.trans A''
  haveI : Algebra.IsIntegral (integralClosure A L) (integralClosure A'' Ω) := Algebra.IsIntegral.tower_top A
  haveI : FaithfulSMul (integralClosure A L) (integralClosure A'' Ω) := (faithfulSMul_iff_algebraMap_injective (integralClosure A L) (integralClosure A'' Ω)).mpr hιinj
  haveI : IsIntegrallyClosed (integralClosure A L) := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hunderι : ∀ Q' : Ideal (integralClosure A'' Ω), (Q'.under (integralClosure A L)).under A = Q'.under A := by
    intro Q'
    rw [Ideal.under_under]
  -- a maximal ideal of `(integralClosure A'' Ω)` over `𝔓`
  have hover : ∀ I' : Ideal (integralClosure A'' Ω), I'.under (integralClosure A L) ≤ 𝔓 →
      ∃ 𝔓' : Ideal (integralClosure A'' Ω), I' ≤ 𝔓' ∧ 𝔓'.IsMaximal ∧ 𝔓'.under (integralClosure A L) = 𝔓 := by
    intro I' hI'
    obtain ⟨𝔓', hge, hp, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔓 I' hI'
    refine ⟨𝔓', hge, ?_, hc⟩
    haveI := hp
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := (integralClosure A L)) 𝔓' (by rw [hc]; exact h𝔓)
  have hdown : ∀ (𝔓' : Ideal (integralClosure A'' Ω)), 𝔓'.IsMaximal → 𝔓'.under (integralClosure A L) = 𝔓 → ∀ Q₁ : Ideal (integralClosure A L), Q₁.IsPrime →
      Q₁ ≤ 𝔓 → ∃ Q' : Ideal (integralClosure A'' Ω), Q' ≤ 𝔓' ∧ Q'.IsPrime ∧ Q'.under (integralClosure A L) = Q₁ := by
    intro 𝔓' h𝔓' hc Q₁ hQ₁ hle
    haveI : 𝔓'.LiesOver 𝔓 := ⟨hc.symm⟩
    haveI := hQ₁
    obtain ⟨Q', hQ'le, hQ'p, hQ'o⟩ := Ideal.exists_ideal_le_liesOver_of_le 𝔓' hle
    exact ⟨Q', hQ'le, hQ'p, hQ'o.over.symm⟩
  obtain ⟨𝔓₀, -, h𝔓₀, h𝔓₀c⟩ := hover ⊥ (Ideal.comap_bot_le_of_injective _ hιinj)
  refine ⟨fun Q₂ hQ₂ hQ₂u hQ₂𝔓 => ?_, ?_⟩
  · -- uniqueness by going down
    obtain ⟨Q'₁, h1le, h1p, h1c⟩ := hdown 𝔓₀ h𝔓₀ h𝔓₀c Q hQ hQ𝔓
    obtain ⟨Q'₂, h2le, h2p, h2c⟩ := hdown 𝔓₀ h𝔓₀ h𝔓₀c Q₂ hQ₂ hQ₂𝔓
    have hu1 : Q'₁.under A = 𝔮 := by rw [← hunderι, h1c, hQu]
    have hu2 : Q'₂.under A = 𝔮 := by rw [← hunderι, h2c, hQ₂u]
    have := (hbr 𝔓₀ h𝔓₀ Q'₁ h1p hu1 h1le).1 Q'₂ h2p hu2 h2le
    rw [← h2c, ← h1c, this]
  · intro F _ _ _ z hz
    obtain ⟨⟨a', ⟨b', hb'⟩⟩, hab'⟩ := IsLocalization.surj (nonZeroDivisors (↥(integralClosure A L) ⧸ Q)) z
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b'
    have hab : z * algebraMap (↥(integralClosure A L) ⧸ Q) F (Ideal.Quotient.mk Q b₀) =
        algebraMap (↥(integralClosure A L) ⧸ Q) F (Ideal.Quotient.mk Q a₀) := hab'
    have hb₀ : b₀ ∉ Q := fun h => nonZeroDivisors.ne_zero hb' (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    obtain ⟨P, hPm, hPz⟩ := hz
    have h0 : (P.scaleRoots (Ideal.Quotient.mk Q b₀)).eval (Ideal.Quotient.mk Q a₀) = 0 := by
      have h1 := scaleRoots_aeval_eq_zero (r := Ideal.Quotient.mk Q b₀)
        (show aeval z P = 0 by rw [aeval_def]; exact hPz)
      rw [mul_comm, hab, aeval_algebraMap_apply, ← map_zero (algebraMap (↥(integralClosure A L) ⧸ Q) F)] at h1
      have h2 := IsFractionRing.injective (↥(integralClosure A L) ⧸ Q) F h1
      rwa [coe_aeval_eq_eval] at h2
    -- the intersection `J` of the primes over `Q`, and the ideal `I'`
    let J : Ideal (integralClosure A'' Ω) := ⨅ (Q' : {Q' : Ideal (integralClosure A'' Ω) // Q'.IsPrime ∧ Q'.under (integralClosure A L) = Q}), Q'.1
    have hJ : ∀ x : (integralClosure A'' Ω), x ∈ J ↔ ∀ Q' : Ideal (integralClosure A'' Ω), Q'.IsPrime → Q'.under (integralClosure A L) = Q → x ∈ Q' := by
      intro x
      simp only [J, Submodule.mem_iInf, Subtype.forall]
      exact ⟨fun h Q' hp hc => h Q' ⟨hp, hc⟩, fun h Q' hpc => h Q' hpc.1 hpc.2⟩
    let I' : Ideal (integralClosure A'' Ω) := (Ideal.span {ι b₀} ⊔ J).colon {ι a₀}
    have hI' : ∀ r : (integralClosure A'' Ω), r ∈ I' ↔ ∃ y : (integralClosure A'' Ω), r * ι a₀ - ι b₀ * y ∈ J := by
      intro r
      rw [Submodule.mem_colon_singleton, Submodule.mem_sup]
      constructor
      · rintro ⟨c, hc, j, hj, hcj⟩
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hc
        refine ⟨y, ?_⟩
        have : r * ι a₀ - ι b₀ * y = j := by rw [smul_eq_mul] at hcj; rw [← hcj]; ring
        rw [this]; exact hj
      · rintro ⟨y, hy⟩
        refine ⟨y * ι b₀, Ideal.mem_span_singleton'.mpr ⟨y, rfl⟩, _, hy, ?_⟩
        rw [smul_eq_mul]; ring
    -- Claim A
    have claimA : ∃ s : (integralClosure A L), s ∉ 𝔓 ∧ ι s ∈ I' := by
      by_contra hcon
      push Not at hcon
      have hle : I'.under (integralClosure A L) ≤ 𝔓 := fun s hs => by
        by_contra h
        exact hcon s h hs
      obtain ⟨𝔓', hI'le, h𝔓'm, h𝔓'c⟩ := hover I' hle
      obtain ⟨Q'₀, hQ0le, hQ0p, hQ0c⟩ := hdown 𝔓' h𝔓'm h𝔓'c Q hQ hQ𝔓
      have hu0 : Q'₀.under A = 𝔮 := by rw [← hunderι, hQ0c, hQu]
      obtain ⟨hub, hnorm⟩ := hbr 𝔓' h𝔓'm Q'₀ hQ0p hu0 hQ0le
      haveI := hQ0p
      obtain ⟨a', s', hs', hrel⟩ := transfer_rel Q Q'₀ 𝔓' ι hQ0c.ge a₀ b₀
        (fun h => hb₀ (by rw [← hQ0c]; exact h)) P hPm h0 hnorm
      -- prime avoidance
      let T : Set (Ideal (integralClosure A'' Ω)) := {Q' | Q'.IsPrime ∧ Q'.under (integralClosure A L) = Q ∧ Q' ≠ Q'₀}
      have hTfin : T.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing (integralClosure A'' Ω)
          (Q.map (algebraMap (integralClosure A L) (integralClosure A'' Ω)))).subset (by
        rintro Q' ⟨hp, hc, -⟩
        haveI := hp
        have := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := (integralClosure A L)) Q'
        rwa [hc] at this)
      have hnotle : ¬ (hTfin.toFinset.inf id ≤ 𝔓') := by
        rw [h𝔓'm.isPrime.inf_le']
        rintro ⟨i, hi, hle⟩
        rw [Set.Finite.mem_toFinset] at hi
        obtain ⟨hp, hc, hne⟩ := hi
        exact hne (hub i hp (by rw [← hunderι, hc, hQu]) hle)
      obtain ⟨w, hw, hw𝔓⟩ := SetLike.not_le_iff_exists.mp hnotle
      have hwT : ∀ Q' ∈ T, w ∈ Q' := fun Q' hQ' =>
        Finset.inf_le (f := id) (hTfin.mem_toFinset.mpr hQ') hw
      have hmem : w * s' ∈ I' := by
        rw [hI']
        refine ⟨w * a', ?_⟩
        rw [hJ]
        intro Q' hQ'p hQ'c
        have e : w * s' * ι a₀ - ι b₀ * (w * a') = w * (s' * ι a₀ - ι b₀ * a') := by ring
        rw [e]
        by_cases hq : Q' = Q'₀
        · subst hq; exact Ideal.mul_mem_left _ _ hrel
        · exact Ideal.mul_mem_right _ _ (hwT Q' ⟨hQ'p, hQ'c, hq⟩)
      rcases h𝔓'm.isPrime.mem_or_mem (hI'le hmem) with h | h
      · exact hw𝔓 h
      · exact hs' h
    obtain ⟨s, hs𝔓, hsI⟩ := claimA
    obtain ⟨y, hy⟩ := (hI' (ι s)).mp hsI
    -- the trace
    have hTrInt : ∀ y : (integralClosure A'' Ω), IsIntegral A (Algebra.trace L Ω (y : Ω)) := fun y =>
      Algebra.isIntegral_trace (isIntegral_trans (y : Ω) y.2)
    let tr : (integralClosure A'' Ω) → (integralClosure A L) := fun y => ⟨Algebra.trace L Ω y, hTrInt y⟩
    have htrJ : ∀ x ∈ J, tr x ∈ Q := by
      intro x hx
      let E := AlgebraicClosure L
      have hintE : ∀ c : (integralClosure A L), IsIntegral A (algebraMap L E c) := fun c =>
        (c.2 : IsIntegral A (c : L)).map (IsScalarTower.toAlgHom A L E)
      let j : (integralClosure A L) →+* integralClosure A E := RingHom.codRestrict ((algebraMap L E).comp
        (algebraMap (integralClosure A L) L)) (integralClosure A E).toSubring (fun c => hintE c)
      have hjinj : Function.Injective j := by
        intro c c' h
        have := congrArg (fun w : integralClosure A E => (w : E)) h
        exact Subtype.ext ((algebraMap L E).injective this)
      letI : Algebra (integralClosure A L) (integralClosure A E) := j.toAlgebra
      haveI : IsScalarTower A (integralClosure A L) (integralClosure A E) := IsScalarTower.of_algebraMap_eq (fun a => by
        apply Subtype.ext
        show algebraMap A E a = algebraMap L E (algebraMap A L a)
        rw [← IsScalarTower.algebraMap_apply])
      haveI : Algebra.IsIntegral (integralClosure A L) (integralClosure A E) := Algebra.IsIntegral.tower_top A
      obtain ⟨Phat, -, hPhatp, hPhatc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q
        (⊥ : Ideal (integralClosure A E)) (Ideal.comap_bot_le_of_injective _ hjinj)
      haveI := hPhatp
      have hσ : ∀ σ : Ω →ₐ[L] E, ∃ hσx : IsIntegral A (σ x),
          (⟨σ x, hσx⟩ : integralClosure A E) ∈ Phat := by
        intro σ
        have hint : ∀ y : (integralClosure A'' Ω), IsIntegral A (σ y) := fun y =>
          (isIntegral_trans (y : Ω) y.2).map (σ.restrictScalars A)
        let σ' : (integralClosure A'' Ω) →+* integralClosure A E := RingHom.codRestrict
          ((σ : Ω →+* E).comp (algebraMap (integralClosure A'' Ω) Ω)) (integralClosure A E).toSubring hint
        have hcomp : σ'.comp ι = j := by
          ext c
          show σ (algebraMap L Ω c) = algebraMap L E c
          exact σ.commutes c
        have hover' : (Phat.comap σ').under (integralClosure A L) = Q := by
          show (Phat.comap σ').comap ι = Q
          rw [Ideal.comap_comap, hcomp]
          exact hPhatc
        exact ⟨hint x, (hJ x).mp hx _ (Ideal.comap_isPrime σ' Phat) hover'⟩
      have hsum : algebraMap L E (Algebra.trace L Ω x) = ∑ σ : Ω →ₐ[L] E, σ x :=
        trace_eq_sum_embeddings (E := E)
      have hmemP : j (tr x) ∈ Phat := by
        have e : j (tr x) = ∑ σ : Ω →ₐ[L] E, (⟨σ x, (hσ σ).1⟩ : integralClosure A E) := by
          apply Subtype.ext
          rw [AddSubmonoidClass.coe_finset_sum]
          exact hsum
        rw [e]
        exact Ideal.sum_mem _ (fun σ _ => (hσ σ).2)
      rw [← hPhatc]
      exact hmemP
    have htr_eq : tr (ι s * ι a₀ - ι b₀ * y) =
        (Module.finrank L Ω : (integralClosure A L)) * (s * a₀) - b₀ * tr y := by
      apply Subtype.ext
      show Algebra.trace L Ω ((ι s * ι a₀ - ι b₀ * y : (integralClosure A'' Ω)) : Ω) =
        ((Module.finrank L Ω : (integralClosure A L)) : L) * ((s : L) * (a₀ : L)) - (b₀ : L) * Algebra.trace L Ω (y : Ω)
      have e1 : ((ι s * ι a₀ - ι b₀ * y : (integralClosure A'' Ω)) : Ω) =
          algebraMap L Ω ((s : L) * (a₀ : L)) - (b₀ : L) • (y : Ω) := by
        rw [Algebra.smul_def, map_mul]
        rfl
      rw [e1, map_sub, LinearMap.map_smul, Algebra.trace_algebraMap, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    have hQrel : (Module.finrank L Ω : (integralClosure A L)) * (s * a₀) - b₀ * tr y ∈ Q := htr_eq ▸ htrJ _ hy
    refine ⟨tr y, (Module.finrank L Ω : (integralClosure A L)) * s, fun h => (h𝔓.isPrime.mem_or_mem h).elim hd hs𝔓, ?_⟩
    have hu : IsUnit (algebraMap (↥(integralClosure A L) ⧸ Q) F (Ideal.Quotient.mk Q b₀)) :=
      IsLocalization.map_units F (⟨Ideal.Quotient.mk Q b₀, hb'⟩ : nonZeroDivisors (↥(integralClosure A L) ⧸ Q))
    apply hu.mul_right_cancel
    rw [mul_assoc, hab, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    rw [Ideal.Quotient.eq]
    convert hQrel using 1
    ring

end Abhyankar
