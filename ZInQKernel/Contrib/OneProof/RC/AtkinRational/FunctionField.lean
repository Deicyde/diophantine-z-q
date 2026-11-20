import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Matrix
import ZInQKernel.Contrib.OneProof.RC.X0Model2.SectionExpansion

/-! Pullback on the rational function field by composition on meromorphic
germs, including the local compatibility for the valuative chart.
Tex 2943–2944; on the spot (c). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Filter Function UpperHalfPlane ModularCurve ShimuraPointDict
open scoped Topology MatrixGroups TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ModFnClassify
open ZInQ.Manuscript.RC.X0Model

namespace ZInQ.Manuscript.RC.AtkinRational

variable {N Q : ℕ} [NeZero N]

/-- A dilated Laurent series realizes the corresponding analytic germ at
every interior point, even when it is expressed in the generators at a
larger level. Uniqueness of the Laurent sum gives agreement on a tail;
the identity theorem then gives agreement of the meromorphic germs. -/
theorem fieldGerm_jqN {m : ℕ} [NeZero m] (hm : m ∣ N) (τ : ℍ) :
    meromorphicIncl (τ : ℂ) (fieldGerm N τ ⟨jqN m, jqN_mem_of_dvd hm⟩) =
      ((analyticJN m ∘ ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) := by
  let a : modularFunctionField N := ⟨jqN m, jqN_mem_of_dvd hm⟩
  obtain ⟨g, T, hg, he, hsum⟩ := X0Model2.exists_hasSum_meromorphicContinuation N a
  let u : ℂ → ℂ := analyticJN m ∘ ofComplex
  have htail : Set.EqOn g u {z : ℂ | T < z.im ∧ 0 < z.im} := by
    intro z hz
    let t : ℍ := ⟨z, hz.2⟩
    have ht : ofComplex z = t := ofComplex_apply_of_im_pos hz.2
    exact (hsum t hz.1).unique (by
      simpa only [a, u, Function.comp_apply, ht] using hasSum_jN m t)
  let t : ℍ := ⟨⟨0, max T 0 + 1⟩, by change 0 < max T 0 + 1; positivity⟩
  have ht₁ : T < t.im := by
    change T < max T 0 + 1
    linarith [le_max_left T 0]
  have hT : ∀ᶠ z in 𝓝 (t : ℂ), T < z.im ∧ 0 < z.im :=
    Filter.Eventually.and
      ((Complex.continuous_im.isOpen_preimage (Set.Ioi T) isOpen_Ioi).mem_nhds ht₁)
      (isOpen_upperHalfPlaneSet.mem_nhds t.im_pos)
  have hmOn : MeromorphicOn (g - u) upperDomain :=
    hg.meromorphicOn.sub (analyticOn_jN m).meromorphicOn
  have ho : meromorphicOrderAt (g - u) (t : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr
      ((hT.filter_mono nhdsWithin_le_nhds).mono fun z hz => sub_eq_zero.mpr (htail hz))
  have hτ := meromorphicOrderAt_eq_top_iff.mp
    (hmOn.meromorphicOrderAt_eq_top_of_isPreconnected
      (convex_halfSpace_im_gt 0).isPreconnected t.im_pos τ.im_pos ho)
  exact (he τ).symm.trans (Germ.coe_eq.mpr (hτ.mono fun z hz => sub_eq_zero.mp hz))

abbrev mobius (hQ : Q ∥ N) : ℂ → ℂ :=
  fun z => ((atkinGL hQ • ofComplex z : ℍ) : ℂ)

omit [NeZero N] in
theorem mobius_tendsto (hQ : Q ∥ N) (τ : ℍ) :
    Tendsto (mobius hQ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (↑(atkinGL hQ • τ) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have ha := τ.analyticAt_smul (TauCeti.val_det_atkinLehnerGL_pos hQ.pos
        (TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix hQ))
    have hc : mobius hQ τ = ((atkinGL hQ • τ : ℍ) : ℂ) := by
      simp only [mobius, ofComplex_apply]
    rw [← hc]
    exact (show AnalyticAt ℂ (mobius hQ) (τ : ℂ) from ha).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [mem_nhdsWithin_of_mem_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos),
      self_mem_nhdsWithin] with z hz hne
    intro he
    apply hne
    have h := congrArg (fun u : ℍ => (atkinGL hQ)⁻¹ • u) (UpperHalfPlane.coe_injective he)
    simp only [inv_smul_smul] at h
    have hz' : 0 < z.im := hz
    have h' := congrArg UpperHalfPlane.coe h
    rw [ofComplex_apply_of_im_pos hz'] at h'
    exact h'

def pullPuncturedGerm (hQ : Q ∥ N) (τ : ℍ) :
    PuncturedGerm (↑(atkinGL hQ • τ) : ℂ) →+* PuncturedGerm (τ : ℂ) where
  toFun f := f.compTendsto (mobius hQ) (mobius_tendsto hQ τ)
  map_zero' := rfl
  map_one' := rfl
  map_add' f g := Germ.inductionOn₂ f g fun _ _ => rfl
  map_mul' f g := Germ.inductionOn₂ f g fun _ _ => rfl

/-- Pull a meromorphic germ back along the interior Möbius transformation. -/
def pullGerm (hQ : Q ∥ N) (τ : ℍ) :
    MeromorphicGerm (↑(atkinGL hQ • τ) : ℂ) →+* MeromorphicGerm (τ : ℂ) where
  toFun f := ⟨pullPuncturedGerm hQ τ f.val, by
    obtain ⟨g, he, hg⟩ := f.property
    refine ⟨g ∘ mobius hQ, congrArg (pullPuncturedGerm hQ τ) he, ?_⟩
    apply MeromorphicAt.comp_analyticAt (g := mobius hQ)
    · simpa only [mobius, ofComplex_apply] using hg
    · exact τ.analyticAt_smul (TauCeti.val_det_atkinLehnerGL_pos hQ.pos _)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' f g := Subtype.ext ((pullPuncturedGerm hQ τ).map_add f.val g.val)
  map_mul' f g := Subtype.ext ((pullPuncturedGerm hQ τ).map_mul f.val g.val)

private theorem fieldGerm_first (τ : ℍ) :
    meromorphicIncl (τ : ℂ) (fieldGerm N τ ⟨jq, jq_mem N⟩) =
      ((analyticJ ∘ ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) := by
  rw [fieldGerm_j]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => by simp)

set_option maxHeartbeats 550000 in
private theorem exists_pullback (hQ : Q ∥ N) (a : modularFunctionField N) :
    ∃ b : modularFunctionField N, ∀ τ : ℍ,
      fieldGerm N τ b = pullGerm hQ τ (fieldGerm N (atkinGL hQ • τ) a) := by
  let : NeZero Q := ⟨hQ.pos.ne'⟩
  have hm : (N / Q) ∣ N := ⟨Q, by rw [mul_comm, Nat.mul_div_cancel' hQ.dvd]⟩
  let : NeZero (N / Q) := ⟨fun h => NeZero.ne N (by simpa [h] using hm)⟩
  let p (τ : ℍ) := (pullGerm hQ τ).comp (fieldGerm N (atkinGL hQ • τ))
  let R (a : modularFunctionField N) := ∃ b : modularFunctionField N,
    ∀ τ : ℍ, fieldGerm N τ b = p τ a
  change R a
  exact IntermediateField.adjoin_induction ℚ (s := {jq, jqN N})
    (motive := fun x hx => R ⟨x, hx⟩)
    (fun x hx => by
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · refine ⟨⟨jqN Q, jqN_mem_of_dvd hQ.dvd⟩, fun τ => Subtype.ext ?_⟩
        change meromorphicIncl _ (fieldGerm N τ _) =
          pullPuncturedGerm hQ τ (meromorphicIncl _ (fieldGerm N (atkinGL hQ • τ) _))
        rw [fieldGerm_jqN hQ.dvd, fieldGerm_first]
        change _ = (((analyticJ ∘ ofComplex) ∘ mobius hQ : ℂ → ℂ) : PuncturedGerm _)
        exact Germ.coe_eq.mpr (Eventually.of_forall fun z => by
          simpa only [Function.comp_apply, mobius, ofComplex_apply] using
            (chart_coordinates hQ (ofComplex z)).1.symm)
      · obtain rfl := Set.mem_singleton_iff.mp hx
        refine ⟨⟨jqN (N / Q), jqN_mem_of_dvd hm⟩, fun τ => Subtype.ext ?_⟩
        change meromorphicIncl _ (fieldGerm N τ _) =
          pullPuncturedGerm hQ τ (meromorphicIncl _ (fieldGerm N (atkinGL hQ • τ) _))
        rw [fieldGerm_jqN hm, fieldGerm_jN]
        exact Germ.coe_eq.mpr (Eventually.of_forall fun z => by
          simpa only [Function.comp_apply, mobius, ofComplex_apply] using
            (chart_coordinates hQ (ofComplex z)).2.symm))
    (fun c => by
      have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, (modularFunctionField N).algebraMap_mem c⟩ :
          modularFunctionField N) = (c : modularFunctionField N) := by
        apply Subtype.ext
        exact DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries ℚ))
          ((modularFunctionField N).subtype.comp (Rat.castHom (modularFunctionField N)))) c
      change R _
      rw [hc]
      exact ⟨c, fun τ => by simp only [map_ratCast]⟩)
    (fun x y hx hy ⟨b, hb⟩ ⟨c, hc⟩ => by
      refine ⟨b + c, fun τ => ?_⟩
      change fieldGerm N τ (b + c) =
        p τ ((⟨x, hx⟩ : modularFunctionField N) + ⟨y, hy⟩)
      rw [(fieldGerm N τ).map_add, (p τ).map_add, hb τ, hc τ])
    (fun x hx ⟨b, hb⟩ => by
      refine ⟨b⁻¹, fun τ => ?_⟩
      change fieldGerm N τ b⁻¹ = p τ ((⟨x, hx⟩ : modularFunctionField N)⁻¹)
      rw [map_inv₀ (fieldGerm N τ), map_inv₀ (p τ), hb τ])
    (fun x y hx hy ⟨b, hb⟩ ⟨c, hc⟩ => by
      refine ⟨b * c, fun τ => ?_⟩
      change fieldGerm N τ (b * c) =
        p τ ((⟨x, hx⟩ : modularFunctionField N) * ⟨y, hy⟩)
      rw [(fieldGerm N τ).map_mul, (p τ).map_mul, hb τ, hc τ])
    a.property

/-- The rational pullback determined by its values in every local field of
meromorphic germs. -/
def pullback (hQ : Q ∥ N) : modularFunctionField N →+* modularFunctionField N where
  toFun a := (exists_pullback hQ a).choose
  map_zero' := (fieldGerm N ⟨Complex.I, by simp⟩).injective (by
    rw [(exists_pullback hQ 0).choose_spec]; simp)
  map_one' := (fieldGerm N ⟨Complex.I, by simp⟩).injective (by
    rw [(exists_pullback hQ 1).choose_spec]; simp)
  map_add' a b := (fieldGerm N ⟨Complex.I, by simp⟩).injective (by
    rw [(fieldGerm N _).map_add, (exists_pullback hQ (a + b)).choose_spec,
      (exists_pullback hQ a).choose_spec, (exists_pullback hQ b).choose_spec]
    rw [(fieldGerm N _).map_add, (pullGerm hQ _).map_add])
  map_mul' a b := (fieldGerm N ⟨Complex.I, by simp⟩).injective (by
    rw [(fieldGerm N _).map_mul, (exists_pullback hQ (a * b)).choose_spec,
      (exists_pullback hQ a).choose_spec, (exists_pullback hQ b).choose_spec]
    rw [(fieldGerm N _).map_mul, (pullGerm hQ _).map_mul])

theorem fieldGerm_pullback (hQ : Q ∥ N) (τ : ℍ) (a : modularFunctionField N) :
    fieldGerm N τ (pullback hQ a) =
      pullGerm hQ τ (fieldGerm N (atkinGL hQ • τ) a) :=
  (exists_pullback hQ a).choose_spec τ


end ZInQ.Manuscript.RC.AtkinRational
