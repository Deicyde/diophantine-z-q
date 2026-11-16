import ZInQKernel.Contrib.OneProof.ShimuraMainCMPrinted
import Mathlib.Analysis.Complex.Cardinality

noncomputable section
set_option linter.all false

namespace MainCMPolar

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open ZInQ.LeafPush2 (CPts IsUniformization)
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E]

theorem countable_E : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

/-- A `ℂ`-linear map whose values lie in a countable set is `0`. -/
theorem linear_eq_zero_of_countable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (L : V →ₗ[ℂ] W) {S : Set W} (hS : S.Countable) (h : ∀ v, L v ∈ S) : L = 0 := by
  ext v
  by_contra hv
  have hinj : Function.Injective fun t : ℂ => t • L v := fun s t hst => smul_left_injective ℂ hv hst
  have hc : (Set.univ : Set ℂ).Countable :=
    (hS.preimage hinj).mono fun t _ => h (t • v) |> fun ht => by simpa [map_smul] using ht
  exact not_countable_complex hc

theorem cmVec_injective {g : ℕ} (Φ : Fin g → E →+* ℂ) (hg : 0 < g) : Function.Injective (cmVec Φ) := by
  intro x y hxy
  have := congrFun hxy ⟨0, hg⟩
  exact (Φ ⟨0, hg⟩).injective this

theorem mem_cmLat {g : ℕ} {Φ : Fin g → E →+* ℂ} {𝔞 : AddSubgroup E} {z : Fin g → ℂ} :
    z ∈ cmLat Φ 𝔞 ↔ ∃ x ∈ 𝔞, cmVec Φ x = z := by
  show z ∈ 𝔞.map (cmVec Φ) ↔ _
  rw [AddSubgroup.mem_map]

theorem cmVec_mem_cmLat {g : ℕ} {Φ : Fin g → E →+* ℂ} (hg : 0 < g) {𝔞 : AddSubgroup E} {x : E} :
    cmVec Φ x ∈ cmLat Φ 𝔞 ↔ x ∈ 𝔞 := by
  rw [mem_cmLat]
  exact ⟨fun ⟨y, hy, e⟩ => cmVec_injective Φ hg e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem cmVec_ratSmul {g : ℕ} (Φ : Fin g → E →+* ℂ) (q : ℚ) (x : E) :
    cmVec Φ (q • x) = (q : ℝ) • cmVec Φ x := by
  funext i
  show Φ i (q • x) = (q : ℝ) • Φ i x
  rw [Rat.smul_def, map_mul, map_ratCast, Complex.real_smul]
  push_cast; rfl

/-- `ψ(a) = ψ(b) ↔ ψ(a − b) = 1` for a homomorphism `ψ`. -/
theorem hom_eq_iff {G : Type*} [Group G] {n : ℕ} {ψ : (Fin n → ℂ) → G}
    (h : ∀ z w, ψ (z + w) = ψ z * ψ w) (a b : Fin n → ℂ) : ψ a = ψ b ↔ ψ (a - b) = 1 := by
  have e : ψ a = ψ (a - b) * ψ b := by rw [← h, sub_add_cancel]
  rw [e]
  constructor
  · intro h1; exact mul_right_cancel (h1.trans (_root_.one_mul _).symm)
  · intro h1; rw [h1, _root_.one_mul]

/-- `x ∈ span_ℚ 𝔞` has a positive integer multiple in `𝔞`. -/
theorem exists_nat_mul_mem {𝔞 : AddSubgroup E} {x : E} (hx : x ∈ Submodule.span ℚ (𝔞 : Set E)) :
    ∃ n : ℕ, 0 < n ∧ (n : E) * x ∈ 𝔞 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : ((n * m : ℕ) : E) * (x + y) = (m : ℤ) • ((n : E) * x) + (n : ℤ) • ((m : E) * y) := by
      push_cast; simp only [zsmul_eq_mul]; push_cast; ring
    rw [e]; exact add_mem (AddSubgroup.zsmul_mem _ hnx _) (AddSubgroup.zsmul_mem _ hmy _)
  | smul q x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n * q.den, Nat.mul_pos hn q.den_pos, ?_⟩
    have e : ((n * q.den : ℕ) : E) * (q • x) = q.num • ((n : E) * x) := by
      rw [Rat.smul_def, zsmul_eq_mul]
      have : ((q.den : ℚ) : E) * (q : E) = (q.num : E) := by
        rw [← Rat.cast_mul, mul_comm, Rat.mul_den_eq_num]; push_cast; rfl
      push_cast
      calc (n : E) * (q.den : E) * ((q : E) * x) = (n : E) * (((q.den : ℚ) : E) * (q : E)) * x := by
            push_cast; ring
        _ = _ := by rw [this]; ring
    rw [e]; exact AddSubgroup.zsmul_mem _ hnx _


open ZInQ.HomLattice (IsAnalyticHom isAnalyticHom_of_unif analyticHomLiftC_of_leaf)

theorem finrank_real_pi (g : ℕ) : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]; simp [mul_comm]

/-- **The lattice of a uniformization** (glue): if `ℂ^g/Φ(𝔞)` uniformizes an abelian variety then
`N 𝓞_E ⊆ 𝔞 ⊆ d⁻¹ 𝓞_E` for some positive integers `N`, `d` (by comparison with the full lattice of
`UniformizationLeafAll`). -/
theorem lattice_of_unif (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) {g : ℕ}
    (Φ : Fin g → E →+* ℂ) (hg : 0 < g) (hdeg : Module.finrank ℚ E = 2 * g)
    {A : PkgI3.AbVar ℂ} {𝔞 : AddSubgroup E} {θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)}
    (hθ : IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ) :
    (∃ N : ℕ, 0 < N ∧ ∀ o : 𝓞 E, (N : E) * o ∈ 𝔞) ∧
    (∃ d : ℕ, 0 < d ∧ ∀ x ∈ 𝔞, IsIntegral ℤ ((d : E) * x)) := by
  obtain ⟨g', Λ', Ψ, hd, hz, hΨ⟩ := ZInQ.LeafPush2.exists_isUniformization_of_leaf hUL A
  obtain ⟨M, hM⟩ := analyticHomLiftC_of_leaf hUL A g' g (cmLat Φ 𝔞) θ hθ Ψ (isAnalyticHom_of_unif hΨ)
  obtain ⟨M', hM'⟩ := analyticHomLiftC_of_leaf hUL A g g' Λ' Ψ hΨ θ (isAnalyticHom_of_unif hθ)
  have hcΛ : (Λ' : Set (Fin g' → ℂ)).Countable := by
    have : Countable Λ' := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
    exact Set.countable_coe_iff.1 this
  have hcL : (cmLat Φ 𝔞 : Set (Fin g → ℂ)).Countable := by
    haveI := countable_E (E := E)
    exact (Set.countable_range (cmVec Φ)).mono fun z hz => by
      obtain ⟨x, -, rfl⟩ := mem_cmLat.1 hz; exact ⟨x, rfl⟩
  have h1 : M'.comp M = LinearMap.id := by
    have := linear_eq_zero_of_countable (M'.comp M - LinearMap.id) hcΛ (fun w => by
      show M' (M w) - w ∈ Λ'
      rw [← hΨ.2.1, ← hom_eq_iff hΨ.1, hM', hM])
    exact sub_eq_zero.1 this
  have h2 : M.comp M' = LinearMap.id := by
    have := linear_eq_zero_of_countable (M.comp M' - LinearMap.id) hcL (fun z => by
      show M (M' z) - z ∈ cmLat Φ 𝔞
      rw [← hθ.2.1, ← hom_eq_iff hθ.1, hM, hM'])
    exact sub_eq_zero.1 this
  have hMM' : ∀ z, M (M' z) = z := fun z => LinearMap.congr_fun h2 z
  have hM'M : ∀ w, M' (M w) = w := fun w => LinearMap.congr_fun h1 w
  have hmem : ∀ z, z ∈ cmLat Φ 𝔞 ↔ M' z ∈ Λ' := fun z => by
    rw [← hθ.2.1, ← hΨ.2.1, hM']
  have hmap : cmLat Φ 𝔞 = Λ'.map (M.restrictScalars ℤ) := by
    ext z
    rw [Submodule.mem_map]
    constructor
    · intro hz; exact ⟨M' z, (hmem z).1 hz, hMM' z⟩
    · rintro ⟨w, hw, rfl⟩
      rw [hmem]
      show M' (M w) ∈ Λ'
      rw [hM'M]; exact hw
  refine ⟨?_, ?_⟩
  · -- spanning
    have hspanR : Submodule.span ℝ (cmLat Φ 𝔞 : Set (Fin g → ℂ)) = ⊤ := by
      rw [hmap, Submodule.map_coe]
      have e : ⇑(M.restrictScalars ℤ) = ⇑(M.restrictScalars ℝ) := rfl
      rw [e, Submodule.span_image, hz.span_top, Submodule.map_top, LinearMap.range_eq_top]
      intro z; exact ⟨M' z, hMM' z⟩
    let W := Submodule.span ℚ (𝔞 : Set E)
    let b := Module.finBasis ℚ W
    have hle : Submodule.span ℝ (cmLat Φ 𝔞 : Set (Fin g → ℂ)) ≤
        Submodule.span ℝ (Set.range fun j => cmVec Φ (b j : E)) := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz
      have hxW : x ∈ W := Submodule.subset_span hx
      have hx' : x = ∑ j, (b.repr ⟨x, hxW⟩ j) • (b j : E) := by
        have := congrArg Subtype.val (b.sum_repr ⟨x, hxW⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [hx', map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [cmVec_ratSmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hk : 2 * g ≤ Module.finrank ℚ W := by
      have h3 := Submodule.finrank_mono hle
      rw [hspanR, finrank_top, finrank_real_pi] at h3
      have h4 := finrank_range_le_card (R := ℝ) (fun j => cmVec Φ (b j : E))
      simp only [Fintype.card_fin] at h4
      unfold Set.finrank at h4
      omega
    have hW : W = ⊤ := Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le W) (hdeg ▸ hk))
    let bO := RingOfIntegers.basis E
    choose n hn hnb using fun k => exists_nat_mul_mem (𝔞 := 𝔞) (x := ((bO k : 𝓞 E) : E))
      (by rw [show Submodule.span ℚ (𝔞 : Set E) = W from rfl, hW]; trivial)
    refine ⟨∏ k, n k, Finset.prod_pos fun k _ => hn k, fun o => ?_⟩
    have ho : (o : E) = ∑ k, ((bO.repr o k : ℤ) : E) * ((bO k : 𝓞 E) : E) := by
      conv_lhs => rw [← bO.sum_repr o]
      push_cast; simp [zsmul_eq_mul]
    rw [ho, Finset.mul_sum]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    have e : ((∏ k, n k : ℕ) : E) * (((bO.repr o k : ℤ) : E) * ((bO k : 𝓞 E) : E)) =
        ((bO.repr o k : ℤ) * ((∏ j ∈ Finset.univ.erase k, n j : ℕ) : ℤ)) • ((n k : E) * ((bO k : 𝓞 E) : E)) := by
      rw [← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ k), zsmul_eq_mul]
      push_cast; ring
    rw [e]; exact AddSubgroup.zsmul_mem _ (hnb k) _
  · -- integrality
    haveI : Module.Finite ℤ Λ' := ZLattice.module_finite ℝ Λ'
    have hFGΛ : Λ'.FG := Module.Finite.iff_fg.1 inferInstance
    have hFGL : (cmLat Φ 𝔞).FG := hmap ▸ hFGΛ.map _
    have hFGa : 𝔞.toIntSubmodule.FG := by
      apply Submodule.fg_of_fg_map_injective (cmVec Φ).toIntLinearMap (cmVec_injective Φ hg)
      convert hFGL using 1
      ext z
      rw [Submodule.mem_map, mem_cmLat]
      rfl
    obtain ⟨S, hS⟩ := hFGa
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) S
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun x hx => ?_⟩
    have hx' : x ∈ Submodule.span ℤ (S : Set E) := by rw [hS]; exact hx
    have key : ∀ x ∈ Submodule.span ℤ (S : Set E), IsIntegral ℤ ((y : E) * x) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => have := hy x hx; rwa [zsmul_eq_mul] at this
      | zero => simp [isIntegral_zero]
      | add x x' _ _ h h' => rw [mul_add]; exact h.add h'
      | smul n x _ h =>
        rw [zsmul_eq_mul, mul_left_comm]
        have hn : IsIntegral ℤ (n : E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := n))
        exact hn.mul h
    have hxy := key x hx'
    rcases Int.natAbs_eq y with h | h
    · rw [h, Int.cast_natCast] at hxy; exact hxy
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at hxy
      have := hxy.neg; rwa [neg_neg] at this

end MainCMPolar
#print axioms MainCMPolar.lattice_of_unif
