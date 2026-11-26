import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.PairJ

/-! # Geometric readings of the pinned rational quotient -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open ModelGeneric ModelTorsion RC.ModelInvariants

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

variable {k : Type*} [Field k] [Algebra ℚ k] [DecidableEq k] [IsAlgClosed k]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The rational geometric reading and its computation on every lift to the pinned cover. -/
noncomputable def rationalPointReading {n : ℕ} [NeZero (n + 2)] (h₂ : 2 ≤ n + 2) :
    {e : (Y0RationalAlgebra h₂ →ₐ[ℚ] k) ≃ PairClasses k (n + 2) //
      ∀ f : rationalCover (n + 2) →ₐ[ℚ] k,
        e (f.comp (Y0RationalInclusion h₂)) = Quot.mk _ (shortCoverPair rationalLevel_isUnit f)} := by
  let S := rationalCover (n + 2)
  let hn := rationalLevel_isUnit (N := n + 2)
  let gr := rationalGrading h₂
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  let δ : Sˣ := shortExactOrderDiscriminantUnit (R := ℚ) hn
  have hδ : (δ : S) ∈ gr 12 := shortExactOrderDiscriminantUnit_mem (R := ℚ) hn
  let restrict (f : S →ₐ[ℚ] k) := f.comp (Y0RationalInclusion h₂)
  let read (f : S →ₐ[ℚ] k) : PairClasses k (n + 2) := Quot.mk _ (shortCoverPair hn f)
  have hlift : Function.Surjective restrict :=
    degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ) gr (by decide) hδ
  letI : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  have hcard : IsUnit (Fintype.card (ZMod (n + 2))ˣ : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have compatible (f g : S →ₐ[ℚ] k) : restrict f = restrict g ↔ read f = read g := by
    change _ ↔ (Quot.mk _ (shortCoverPair hn f) : PairClasses k (n + 2)) =
      Quot.mk _ (shortCoverPair hn g)
    rw [shortCoverPairClass_eq_iff hn (by norm_num) (by norm_num)]
    have eqOrbit := degreeZeroInvariants_restrict_eq_iff gr (by decide) hδ hcard f g
    change restrict f = restrict g ↔ _ at eqOrbit
    rw [eqOrbit]
    constructor
    · rintro ⟨a, u, hu⟩
      refine ⟨a⁻¹, u, AlgHom.ext fun x => ?_⟩
      refine DirectSum.Decomposition.inductionOn (ℳ := gr) ?_ ?_ ?_ x
      · simp
      · intro i y
        rw [hu i y y.property, scaleShortExactOrderPoint_homogeneous hn u _ y.property,
          Units.val_zpow_eq_zpow_val]
        rfl
      · intro y z hy hz
        simp only [map_add, hy, hz]
    · rintro ⟨a, u, ha⟩
      refine ⟨a⁻¹, u, fun i x hx => ?_⟩
      have hact : a⁻¹ • f = f.comp (shortLevelUnitAut hn a).toAlgHom := by
        change f.comp (shortLevelUnitAut hn (a⁻¹)⁻¹).toAlgHom = _
        rw [inv_inv]
      rw [ha, hact, scaleShortExactOrderPoint_homogeneous hn u _ hx, Units.val_zpow_eq_zpow_val]
  let value (x : Y0RationalAlgebra h₂ →ₐ[ℚ] k) := read (hlift x).choose
  have value_restrict (f : S →ₐ[ℚ] k) : value (restrict f) = read f :=
    (compatible _ _).1 (hlift (restrict f)).choose_spec
  refine ⟨Equiv.ofBijective value ⟨?_, ?_⟩, value_restrict⟩
  · intro x y he
    obtain ⟨f, rfl⟩ := hlift x
    obtain ⟨g, rfl⟩ := hlift y
    rw [value_restrict, value_restrict] at he
    exact (compatible _ _).2 he
  · intro x
    obtain ⟨f, hf⟩ := shortCoverPairClass_surjective hn (k := k) (by norm_num) (by norm_num) x
    exact ⟨restrict f, (value_restrict f).trans hf⟩

/-- The point reading belongs to the single rational quotient. -/
noncomputable def rationalPoints {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) :
    (Y0RationalAlgebra h₂ →ₐ[ℚ] k) ≃ PairClasses k N := by
  obtain _ | _ | n := N
  · omega
  · omega
  · exact (rationalPointReading h₂).val

set_option backward.isDefEq.respectTransparency false in
/-- The pinned rational coordinate reads the source curve's invariant at every geometric point. -/
theorem rationalPoints_j {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)
    (x : Y0RationalAlgebra h₂ →ₐ[ℚ] k) :
    pairJ (rationalPoints h₂ x) = x (Y0RationalJ h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  let hn := rationalLevel_isUnit (N := n + 2)
  let gr := rationalGrading h₂
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  have hδ : (↑(shortExactOrderDiscriminantUnit (R := ℚ) hn) : rationalCover (n + 2)) ∈
      gr 12 := shortExactOrderDiscriminantUnit_mem (R := ℚ) hn
  obtain ⟨f, rfl⟩ := degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ)
    (k := k) gr (by decide) hδ x
  change pairJ ((rationalPointReading h₂).val (f.comp (Y0RationalInclusion h₂))) = _
  rw [(rationalPointReading h₂).property, pairJ_mk]
  exact (WeierstrassCurve.map_j (shortFamily ℚ) (f.domRestrict (ShortBase ℚ)).toRingHom)

#print axioms rationalPointReading
#print axioms rationalPoints
#print axioms rationalPoints_j

end WeierstrassCurve.ModelLevels.ModelGeneric2
