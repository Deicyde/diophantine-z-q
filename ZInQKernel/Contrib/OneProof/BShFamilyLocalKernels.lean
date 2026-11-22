import ZInQKernel.Contrib.OneProof.BShFamilyAtlas
import ZInQKernel.Contrib.OneProof.BShTraces

/-! ON THE SPOT (provenance (c)): the local embedding of the splitting
field identifies each surviving multiset kernel with exactly one branch. -/

noncomputable section

namespace BShFamily

open Filter Polynomial UpperHalfPlane PeriodPair T5Glue X1Igusa.Weber
open BShTraces ShimuraPointDict LeafModCurves AlgebraicGeometry CategoryTheory
open WeierstrassCurve AfTateLam
open scoped Topology

/-- The analytic multiset contains the x-coordinate of each nonzero residue
in this line, with the same weights as the short Vélu sum. -/
def analyticCluster {p : ℕ} (hp : p.Prime) (τ : ℍ) (i : Line p) :
    Multiset (MeromorphicGerm (τ : ℂ)) :=
  (Finset.univ : Finset (Multiple p)).val.map (sectionAt hp τ i)

theorem analyticCluster_injective {p : ℕ} (hp : p.Prime) (τ : ℍ) :
    Function.Injective (analyticCluster hp τ) := by
  intro i j e
  have h : sectionAt hp τ i (oneMultiple hp) ∈ analyticCluster hp τ j := by
    rw [← e]
    exact Multiset.mem_map.mpr ⟨_, by simp, rfl⟩
  obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp h
  exact (line_eq_of_sectionAt_eq hp τ hk).symm

/-- The algebraic cluster of any analytic root is the analytic multiset
for its line, independently of the root chosen as generator. -/
theorem cluster_sectionAt {X : Over SpecQ} [IsIntegral X.left]
    {N p : ℕ} {jX tX : X.left.functionField}
    (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (hp : p.Prime)
    (τ : ℍ) (i : Line p) (k : Multiple p) :
    cluster (localCurve hN hG τ) p (sectionAt hp τ i k) = analyticCluster hp τ i := by
  unfold cluster analyticCluster
  simp_rw [mulX_sectionAt hN hG hp τ i k]
  change (Finset.univ : Finset (Multiple p)).val.map
    ((sectionAt hp τ i) ∘ multiplePerm hp k) = _
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- On the bad prime, multiplying the mark by the level divided by the
prime gives the horizontal section. -/
theorem mark_multiple_section {X : Over SpecQ} [IsIntegral X.left]
    {N p : ℕ} {jX tX : X.left.functionField}
    (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (hp : p.Prime) (hpN : p ∣ N) (τ : ℍ) :
    mulX (localCurve hN hG τ) (N / p : ℕ)
      (meromorphicFieldGerm hN hG τ (modelX jX tX)) =
      sectionAt hp τ none (oneMultiple hp) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he : ((N / p : ℕ) : ℂ) * (p : ℂ) = N := by exact_mod_cast Nat.div_mul_cancel hpN
  have he' : ((N / p : ℕ) : ℂ) * (1 / (N : ℂ)) = 1 / (p : ℂ) := by
    field_simp
    exact he
  apply (restrict τ).injective
  rw [restrict_mulX hN hG τ _ (restrict_modelX hN hG τ), restrict_sectionAt]
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_good τ] with s hs
  have hm : (1 / (N : ℂ)) ∉ (pp s).lattice := by
    simpa using div_nat_not_mem s (a := 1) (N := N) one_pos (by omega)
  have ht : (1 / (p : ℂ)) ∉ (pp s).lattice := by
    simpa only [oneMultiple_val, generator, Option.elim_none, Nat.cast_one, one_mul] using
      multiple_notMem hp.pos none s (oneMultiple hp)
  simpa only [Int.cast_natCast, he', oneMultiple_val, generator, Option.elim_none,
    Nat.cast_one, one_mul] using
    (mulX_pointwise s hs.1 hs.2 ((N / p : ℕ) : ℤ) hm
      (by simpa only [Int.cast_natCast, he'] using ht)).2

/-- The analytic line corresponding to an allowed branch. -/
def branchLine {N p : ℕ} : PrimeBranch N p → Line p
  | .inl i => some i
  | .inr _ => none

theorem branchLine_injective {N p : ℕ} : Function.Injective (@branchLine N p) := by
  intro i j he
  cases i <;> cases j <;> simp_all [branchLine]
  exact Subsingleton.elim _ _

variable {X : Over SpecQ} [IsIntegral X.left] {N p : ℕ} {jX tX : X.left.functionField}
local notation "K" => X.left.functionField
local instance : CharZero K := charZero_of_injective_ringHom (baseMap X).injective

/-- The splitting field of the full prime division polynomial. -/
abbrev DivisionField (j : K) (p : ℕ) :=
  ((curveG (modelG j)).ΨSq p).SplittingField

/-- Each surviving kernel has a unique match among the local branches,
with agreement of the whole weighted multiset of kernel x-coordinates. -/
theorem exists_local_kernel_equiv
    (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (hp : p.Prime) (τ : ℍ) :
    let L := DivisionField jX p
    let W := (curveG (modelG jX)).map (algebraMap K L)
    let y := algebraMap K L (modelX jX tX)
    ∃ (u : L →+* MeromorphicGerm (τ : ℂ))
      (e : PrimeBranch N p ≃ Kernel W p N y),
      u.comp (algebraMap K L) = meromorphicFieldGerm hN hG τ ∧
        ∀ i, (e i).val.map u = analyticCluster hp τ (branchLine i) := by
  classical
  let E := curveG (modelG jX)
  let P := E.ΨSq p
  let L := P.SplittingField
  let W := E.map (algebraMap K L)
  let y := algebraMap K L (modelX jX tX)
  let M := MeromorphicGerm (τ : ℂ)
  let m := meromorphicFieldGerm hN hG τ
  letI : Algebra K M := m.toAlgebra
  let v := Polynomial.SplittingField.lift P (splits_local hN hG hp τ)
  let u : L →+* M := v.toRingHom
  have hu : u.comp (algebraMap K L) = m := v.comp_algebraMap
  have hW : W.map u = localCurve hN hG τ := by
    rw [show W = E.map (algebraMap K L) by rfl, WeierstrassCurve.map_map, hu]
    rfl
  have hy : u y = m (modelX jX tX) := v.commutes _
  have hmap : (W.ΨSq p).map u = (localCurve hN hG τ).ΨSq p := by rw [← map_ΨSq, hW]
  have hs : (W.ΨSq p).Splits := by
    rw [map_ΨSq]
    exact Polynomial.SplittingField.splits P
  have hpL : ((p : ℤ) : L) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn : W.ΨSq p ≠ 0 := W.ΨSq_ne_zero hpL
  have heval (r : L) : u ((W.ΨSq p).eval r) =
      ((localCurve hN hG τ).ΨSq p).eval (u r) := by
    rw [← hmap, Polynomial.eval_map, eval₂_at_apply]
  have hmark (S : Multiset L) (i : Line p)
      (he : S.map u = analyticCluster hp τ i) :
      (¬ p ∣ N ∨ mulX W (N / p : ℕ) y ∉ S) ↔ (¬ p ∣ N ∨ i ≠ none) := by
    by_cases hbad : p ∣ N
    · simp only [hbad, not_true_eq_false, false_or]
      have hm : u (mulX W (N / p : ℕ) y) = sectionAt hp τ none (oneMultiple hp) := by
        rw [map_mulX, hW, hy, mark_multiple_section hN hG hp hbad τ]
      have ht : mulX W (N / p : ℕ) y ∈ S ↔ i = none := by
        constructor
        · intro hmem
          have he' : sectionAt hp τ none (oneMultiple hp) ∈ analyticCluster hp τ i :=
            he ▸ hm ▸ Multiset.mem_map.mpr ⟨_, hmem, rfl⟩
          obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp he'
          exact line_eq_of_sectionAt_eq hp τ hk
        · rintro rfl
          have hmem : u (mulX W (N / p : ℕ) y) ∈ S.map u := by
            rw [he, hm]
            exact Multiset.mem_map.mpr ⟨_, by simp, rfl⟩
          obtain ⟨z, hz, hz'⟩ := Multiset.mem_map.mp hmem
          exact (u.injective hz') ▸ hz
      exact not_congr ht
    · simp [hbad]
  let U := Kernel W p N y
  let Rel (i : PrimeBranch N p) (S : U) : Prop :=
    S.val.map u = analyticCluster hp τ (branchLine i)
  have all (i : PrimeBranch N p) : ∃ S : U, Rel i S := by
    let t := sectionAt hp τ (branchLine i) (oneMultiple hp)
    have hr : ((localCurve hN hG τ).ΨSq p).eval t = 0 :=
      (local_roots hN hG hp τ t).mpr ⟨_, _, rfl⟩
    have hr' : ((W.ΨSq p).map u).IsRoot t := by rwa [IsRoot, hmap]
    obtain ⟨r, hre⟩ := hs.mem_range_of_isRoot hn hr'
    have hr₀ : (W.ΨSq p).eval r = 0 := u.injective (by rw [heval, hre, hr, map_zero])
    let S := cluster W p r
    have hR : S.map u = analyticCluster hp τ (branchLine i) := by
      rw [show S = cluster W p r by rfl, map_cluster, hW, hre, cluster_sectionAt hN hG hp]
    have hi : ¬ p ∣ N ∨ branchLine i ≠ none := by
      cases i with
      | inl i => exact Or.inr (by simp [branchLine])
      | inr i => exact Or.inl i.property
    exact ⟨⟨S, ⟨⟨r, hr₀, rfl⟩, (hmark _ _ hR).mpr hi⟩⟩, hR⟩
  choose f hf using all
  have inj : Function.Injective f := by
    intro i j h
    apply branchLine_injective
    apply analyticCluster_injective hp τ
    rw [← hf i, h, hf j]
  have surj : Function.Surjective f := by
    intro S
    obtain ⟨r,hr,hc⟩ := S.property.1
    obtain ⟨i,k,he⟩ := (local_roots hN hG hp τ (u r)).mp
      (by rw [← heval, hr, map_zero])
    have hR : S.val.map u = analyticCluster hp τ i := by
      rw [hc, map_cluster, hW, he, cluster_sectionAt hN hG hp]
    have hi := (hmark _ _ hR).mp S.property.2
    have hex : ∃ j : PrimeBranch N p, branchLine j = i := by
      cases i with
      | none => exact ⟨.inr ⟨(), hi.resolve_right (not_not_intro rfl)⟩, rfl⟩
      | some k => exact ⟨.inl k, rfl⟩
    obtain ⟨j,hj⟩ := hex
    refine ⟨j, Subtype.ext (Multiset.map_injective u.injective ?_)⟩
    rw [hf j, hj, hR]
  exact ⟨u, Equiv.ofBijective f ⟨inj,surj⟩, hu, hf⟩

#print axioms analyticCluster_injective
#print axioms cluster_sectionAt
#print axioms mark_multiple_section
#print axioms branchLine_injective
#print axioms exists_local_kernel_equiv

end BShFamily
