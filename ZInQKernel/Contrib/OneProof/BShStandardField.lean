import ZInQKernel.Contrib.OneProof.BShStandardWeber
import ZInQKernel.Contrib.OneProof.ShimuraPointDictField
import ZInQKernel.Contrib.OneProof.HeckePin

/-! ON THE SPOT (c): realize the rational diamond substitution on the given
function field, with its compatibility at every punctured germ. -/

noncomputable section

namespace BShStandard

open scoped MatrixGroups Topology
open Filter UpperHalfPlane CategoryTheory AlgebraicGeometry Polynomial Matrix
open LeafModCurves AfTateLam T5Glue X1Igusa.Weber ShimuraPointDict

set_option backward.isDefEq.respectTransparency false

private theorem eventually_good_on_H (τ : ℍ) :
    ∀ᶠ σ in 𝓝[≠] τ, (pp σ).g₂ ≠ 0 ∧ (pp σ).g₃ ≠ 0 := by
  let F : ℂ → ℂ := fun z => G2f z * G3f z
  have hF : DifferentiableOn ℂ F Hs := diffOn_G2f.mul diffOn_G3f
  have ha := hF.analyticOnNhd isOpen_Hs (τ : ℂ) τ.coe_im_pos
  rcases ha.meromorphicAt.eventually_eq_zero_or_eventually_ne_zero with h | h
  · obtain ⟨z, hz, h2, h3⟩ := exists_good_point
    exact (mul_ne_zero h2 h3 (eq_zero_of_eventually hF τ.coe_im_pos
      ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp h) z hz)).elim
  · have ht : Tendsto ((↑) : ℍ → ℂ) (𝓝[≠] τ) (𝓝[≠] (τ : ℂ)) := (map_punctured_coe τ).le
    filter_upwards [Tendsto.eventually ht h] with σ hσ
    have : (pp σ).g₂ * (pp σ).g₃ ≠ 0 := by simpa [F, G2f, G3f, ofComplex_apply] using hσ
    exact ⟨fun h => this (by rw [h, zero_mul]), fun h => this (by rw [h, mul_zero])⟩

private def precomp {α β : Type*} {l : Filter α} {m : Filter β}
    (f : α → β) (hf : Tendsto f l m) : Germ m ℂ →+* Germ l ℂ where
  toFun x := x.compTendsto f hf
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by induction x using Germ.inductionOn; induction y using Germ.inductionOn; rfl
  map_mul' x y := by induction x using Germ.inductionOn; induction y using Germ.inductionOn; rfl

private theorem precomp_tendsto {α β : Type*} {l : Filter α} {m : Filter β}
    (f : α → β) (hf : map f l = m) (x : Germ m ℂ) (c : ℂ) :
    (precomp f hf.le x).Tendsto (𝓝 c) ↔ x.Tendsto (𝓝 c) := by
  induction x using Germ.inductionOn with
  | _ x =>
    change Tendsto (x ∘ f) l (𝓝 c) ↔ Tendsto x m (𝓝 c)
    rw [← hf, tendsto_map'_iff]

variable {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField} {N : ℕ}

private local instance : CharZero X.left.functionField :=
  charZero_of_injective_ringHom
    ((Spec.preimage (X.left.fromSpecFunctionField ≫ X.hom)).hom : ℚ →+* X.left.functionField).injective

private abbrev ugerm (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    X.left.functionField →+* Germ (𝓝[≠] τ) ℂ :=
  (precomp ((↑) : ℍ → ℂ) (map_punctured_coe τ).le).comp (fieldGerm hN hG τ)

private theorem ugerm_gen (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ) :
    ugerm hN hG τ jX = ((fun σ : ℍ => Jf σ) : Germ (𝓝[≠] τ) ℂ) ∧
      ugerm hN hG τ tX = ((fun σ : ℍ => Wf N σ) : Germ (𝓝[≠] τ) ℂ) := by
  have e (P : Polynomial (Polynomial ℤ)) :
      ugerm hN hG τ (algEval jX tX P) = ((fun σ : ℍ => ez N σ (AfTateOr.toQ P)) :
        Germ (𝓝[≠] τ) ℂ) := by
    have h := fieldGerm_fraction hN hG τ P 1 (show algEval jX tX 1 ≠ 0 by simp)
    simp only [map_one, div_one] at h
    change precomp ((↑) : ℍ → ℂ) (map_punctured_coe τ).le (fieldGerm hN hG τ (algEval jX tX P)) = _
    rw [h]
    rfl
  exact ⟨by simpa [algEval, ez, AfTateOr.toQ] using e (C Polynomial.X), by
    simpa [algEval, ez, AfTateOr.toQ] using e Polynomial.X⟩

private theorem eval₂_natural {R S T : Type*} [Semiring R] [CommSemiring S] [CommSemiring T]
    (h : S →+* T) (f : R →+* S) (x : S) (P : R[X]) :
    h (P.eval₂ f x) = P.eval₂ (h.comp f) (h x) := by
  rw [eval₂_eq_sum, eval₂_eq_sum, Polynomial.sum, Polynomial.sum, map_sum]
  simp [map_mul, map_pow]

/-- The rational polynomial evaluations used by the coordinate calculation represent
the corresponding function field elements in punctured germs. -/
private theorem ugerm_eval (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : ℍ)
    (P : Polynomial (Polynomial ℚ)) :
    ugerm hN hG τ (X1Igusa.Weber.ev2 jX tX P) =
      ((fun σ : ℍ => ez N σ P) : Germ (𝓝[≠] τ) ℂ) := by
  let l : Filter ℍ := 𝓝[≠] τ
  let u := ugerm hN hG τ
  let q : ℚ →+* (ℍ → ℂ) := RingHom.pi (fun _ => Rat.castHom ℂ)
  let k : (ℍ → ℂ) →+* Germ l ℂ := Germ.coeRingHom l
  let j : ℍ → ℂ := fun σ => Jf σ
  let t : ℍ → ℂ := fun σ => Wf N σ
  have hq : u.comp (Rat.castHom _) = k.comp q := RingHom.ext_rat _ _
  have he (p : Polynomial ℚ) :
      u (p.eval₂ (Rat.castHom _) jX) = k (p.eval₂ q j) := by
    rw [eval₂_natural, eval₂_natural, hq]
    congr 1
    exact (ugerm_gen hN hG τ).1
  have hh : u.comp (eval₂RingHom (Rat.castHom _) jX) = k.comp (eval₂RingHom q j) :=
    RingHom.ext he
  change u (P.eval₂ (eval₂RingHom (Rat.castHom _) jX) tX) = _
  have hv : (fun σ : ℍ => ez N σ P) = P.eval₂ (eval₂RingHom q j) t := by
    funext σ
    let e : (ℍ → ℂ) →+* ℂ := Pi.evalRingHom (fun _ => ℂ) σ
    have heq : e.comp (eval₂RingHom q j) = eval₂RingHom (Rat.castHom ℂ) (Jf σ) := by
      apply RingHom.ext
      intro p
      exact eval₂_natural e q j p
    change _ = e _
    rw [eval₂_natural, heq]
    rfl
  rw [hv]
  change u (P.eval₂ _ _) = k (P.eval₂ _ _)
  rw [eval₂_natural, eval₂_natural, hh]
  congr 1
  exact (ugerm_gen hN hG τ).2

private theorem sl_map_nhds (g : SL(2, ℤ)) (τ : ℍ) :
    map (fun σ : ℍ => g • σ) (𝓝[≠] τ) = 𝓝[≠] (g • τ) := by
  exact (Homeomorph.smul (α := ℍ) (SpecialLinearGroup.mapGL ℝ g)).map_punctured_nhds_eq τ

private abbrev diamondGerm (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (g : SL(2, ℤ)) (τ : ℍ) :
    X.left.functionField →+* Germ (𝓝[≠] τ) ℂ :=
  (precomp (fun σ : ℍ => g • σ) (sl_map_nhds g τ).le).comp (ugerm hN hG (g • τ))

/-- The diamond pullback on the rational function field gives the analytic pullback
at every punctured parameter, including at exceptional Weber parameters. -/
private theorem exists_diamond_germs (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (d : (ZMod N)ˣ) :
    ∃ f : X.left.functionField →+* X.left.functionField,
      ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → (g 1 1 : ZMod N) = (d : ZMod N) →
        ∀ τ : ℍ, (ugerm hN hG τ).comp f = diamondGerm hN hG g τ := by
  letI : NeZero N := ⟨by omega⟩
  let n : ℤ := (d : ZMod N).val
  have hn : (n : ZMod N) = (d : ZMod N) := by simp [n]
  obtain ⟨g₀, hg₀, hd₀⟩ := HeckePin.exists_gamma_unit N d
  obtain ⟨A, B, hAB⟩ := diamond_fraction n
  let a := X1Igusa.Weber.ev2 jX tX A
  let b := X1Igusa.Weber.ev2 jX tX B
  have hf (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0) (hd : (g 1 1 : ZMod N) = (d : ZMod N))
      (τ : ℍ) :
      ∀ᶠ σ : ℍ in 𝓝[≠] τ, ez N σ B ≠ 0 ∧ Wf N ((g • σ : ℍ) : ℂ) * ez N σ B = ez N σ A := by
    filter_upwards [eventually_good_on_H τ] with σ hσ
    obtain ⟨hb, hval⟩ := hAB hN g hg (hd.trans hn.symm) σ hσ.1 hσ.2
    have hgσ := (diamond_good g σ).mpr hσ
    rw [weber_eq_Wf _ hgσ.1 hgσ.2] at hval
    exact ⟨hb, (eq_div_iff hb).mp hval⟩
  have hb : b ≠ 0 := by
    intro he
    have hz := ugerm_eval hN hG UpperHalfPlane.I B
    change ugerm hN hG UpperHalfPlane.I b = _ at hz
    rw [he, map_zero] at hz
    have hzero : (fun σ : ℍ => ez N σ B) =ᶠ[𝓝[≠] UpperHalfPlane.I] (fun _ => 0) :=
      Germ.coe_eq.mp hz.symm
    exact (Filter.Eventually.exists ((hf g₀ hg₀ hd₀ UpperHalfPlane.I).and hzero)).elim
      (fun _ h => h.1.1 h.2)
  let v := a / b
  have hj (g : SL(2, ℤ)) (τ : ℍ) : diamondGerm hN hG g τ jX = ugerm hN hG τ jX := by
    change precomp (fun σ : ℍ => g • σ) (sl_map_nhds g τ).le (ugerm hN hG (g • τ) jX) = _
    rw [(ugerm_gen hN hG (g • τ)).1, (ugerm_gen hN hG τ).1]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun σ => by simpa [Jf, ofComplex_apply] using j_diamond g σ
  have hv (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0) (hd : (g 1 1 : ZMod N) = (d : ZMod N))
      (τ : ℍ) : diamondGerm hN hG g τ tX = ugerm hN hG τ v := by
    let u := ugerm hN hG τ
    have h : diamondGerm hN hG g τ tX * u b = u a := by
      change precomp (fun σ : ℍ => g • σ) (sl_map_nhds g τ).le (ugerm hN hG (g • τ) tX) * _ = _
      rw [(ugerm_gen hN hG (g • τ)).2, ugerm_eval hN hG τ B, ugerm_eval hN hG τ A]
      apply Germ.coe_eq.mpr
      exact (hf g hg hd τ).mono fun _ h => h.2
    have hunit : IsUnit (u b) := (isUnit_iff_ne_zero.mpr hb).map u
    apply hunit.mul_left_inj.mp
    rw [h, ← map_mul, div_mul_cancel₀ _ hb]
  let e := AfTateOr.evHom jX tX
  let e' := AfTateOr.evHom jX v
  have h_eval (P : Polynomial (Polynomial ℤ)) :
      diamondGerm hN hG g₀ UpperHalfPlane.I (e P) = ugerm hN hG UpperHalfPlane.I (e' P) := by
    let τ := UpperHalfPlane.I
    let u := ugerm hN hG τ
    let w := diamondGerm hN hG g₀ τ
    change w (P.eval₂ _ _) = u (P.eval₂ _ _)
    rw [eval₂_natural, eval₂_natural, hv g₀ hg₀ hd₀ τ]
    congr 1
    apply RingHom.ext
    intro p
    change w (p.eval₂ _ jX) = u (p.eval₂ _ jX)
    rw [eval₂_natural, eval₂_natural, hj g₀ τ]
    congr 1
    exact Subsingleton.elim _ _
  have hker : RingHom.ker e.rangeRestrict ≤ RingHom.ker e' := by
    intro P hP
    apply RingHom.mem_ker.mpr
    apply (ugerm hN hG UpperHalfPlane.I).injective
    have hp : e P = 0 := congrArg Subtype.val (RingHom.mem_ker.mp hP)
    rw [← h_eval, hp, map_zero, map_zero]
  let s : e.range →+* X.left.functionField :=
    e.rangeRestrict.liftOfSurjective e.rangeRestrict_surjective ⟨e', hker⟩
  have hs (P) : s (e.rangeRestrict P) = e' P :=
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  letI := AfTateOr.isFractionRing_range jX tX hG.1
  have hsU (m : nonZeroDivisors e.range) : IsUnit (s m) := by
    apply isUnit_iff_ne_zero.mpr
    intro hm
    obtain ⟨P, hP⟩ := e.rangeRestrict_surjective m.val
    have he : e' P = 0 := by rw [← hs P, hP]; exact hm
    have hz : e P = 0 := (diamondGerm hN hG g₀ UpperHalfPlane.I).injective
      (by rw [h_eval, he, map_zero, map_zero])
    exact (mem_nonZeroDivisors_iff_ne_zero.mp m.property)
      (hP ▸ (Subtype.ext hz : e.rangeRestrict P = 0))
  let f : X.left.functionField →+* X.left.functionField := IsLocalization.lift hsU
  have hgen (P) : f (e P) = e' P := by
    change f (algebraMap e.range _ (e.rangeRestrict P)) = _
    exact (IsLocalization.lift_eq _ _).trans (hs P)
  refine ⟨f, fun g hg hd τ => RingHom.eq_of_eqOn_of_field_closure_eq_top hG.1 ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h <;> subst x
  · have h : f jX = jX := by simpa [e, e', AfTateOr.evHom] using hgen (C Polynomial.X)
    exact (congrArg (ugerm hN hG τ) h).trans (hj g τ).symm
  · have h : f tX = v := by simpa [e, e', AfTateOr.evHom] using hgen Polynomial.X
    exact (congrArg (ugerm hN hG τ) h).trans (hv g hg hd τ).symm

/-- A rational field pullback for a diamond, preserving all finite germ values. -/
theorem exists_diamond_fieldMap (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (d : (ZMod N)ˣ) :
    ∃ f : X.left.functionField →+* X.left.functionField,
      ∀ g : SL(2, ℤ), (N : ℤ) ∣ g 1 0 → (g 1 1 : ZMod N) = (d : ZMod N) →
        ∀ (τ : ℍ) (a : X.left.functionField) (c : ℂ),
          HasValue (fieldGerm hN hG τ (f a)) c ↔ HasValue (fieldGerm hN hG (g • τ) a) c := by
  obtain ⟨f, hf⟩ := exists_diamond_germs hN hG d
  refine ⟨f, fun g hg hd τ a c => ?_⟩
  change (fieldGerm hN hG τ (f a)).Tendsto _ ↔ (fieldGerm hN hG (g • τ) a).Tendsto _
  rw [← precomp_tendsto _ (map_punctured_coe τ)]
  change (ugerm hN hG τ (f a)).Tendsto _ ↔ _
  rw [show ugerm hN hG τ (f a) = diamondGerm hN hG g τ a from DFunLike.congr_fun (hf g hg hd τ) a]
  change (precomp (fun σ : ℍ => g • σ) (sl_map_nhds g τ).le
    (ugerm hN hG (g • τ) a)).Tendsto _ ↔ _
  rw [precomp_tendsto _ (sl_map_nhds g τ)]
  apply precomp_tendsto _ (map_punctured_coe _)

#print axioms eventually_good_on_H
#print axioms precomp_tendsto
#print axioms ugerm_gen
#print axioms eval₂_natural
#print axioms ugerm_eval
#print axioms sl_map_nhds
#print axioms exists_diamond_germs
#print axioms exists_diamond_fieldMap

end BShStandard
