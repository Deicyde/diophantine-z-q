import ZInQKernel.Contrib.OneProof.ShimuraMainCMPrinted
import ZInQKernel.Contrib.FrobChain.Rigidity
import Mathlib.Analysis.Complex.Cardinality

/-!
# mtcm-polar: the main theorem of CM for arbitrary lattices from the polarized, maximal-order print

Task mtcm-polar (2026-11-15). Report: `docs/research/mtcm-polar.md`; log: `scratch/mtcm-polar/log.md`.

qmrec-printed's leaf `QMRecPrinted.MainTheoremCM` and hcm-printed's `HcmPrinted.MainTheoremCMArith` (its `ε = 1`
form) quantify over every lattice `𝔞 ⊂ E` (any multiplier ring) and carry no polarization hypothesis, while
Shimura's main theorem (1971 Thm 5.15, 1998 Thm 18.6) is stated for polarized structures `(A, C, θ)` of a type
`(E, Φ; 𝔞, ζ)`. This file derives `MainTheoremCMArith` from

* `MainTheoremCMPolMax` (sign `ε = 1`) or `MainTheoremCMPol` (sign existential): the main theorem for `𝔞` a
  fractional `𝓞_E`-ideal and `(A, θ)` carrying a Riemann form `E(Φ(x), Φ(y)) = Tr_{E/ℚ}(ζ x ȳ)` (the polarized,
  maximal-order print);
* `CMAbVarExists`: Shimura's converse, the existence of a polarized abelian variety of type `(E, Φ; 𝔟, ζ)`;
* the textbook leaves `UniformizationLeafAll` and `GAGAMorphism` (hence `HomLatticeCorr`, `AvSplit.Final.h69`).

Glue proved here:
* (2) `exists_zeta`: every CM type `Φ` admits `ζ ∈ E` with `ζ̄ = −ζ` and `Im φᵢ(ζ) > 0` (weak approximation at the
  infinite places, Mathlib's `AbsoluteValue.denseRange_algebraMap_pi`); scaled into `𝓞_E` it is a Riemann datum for
  every `𝔟 = N𝓞_E`;
* `lattice_of_unif`: a lattice `𝔞` uniformizing an abelian variety satisfies `N𝓞_E ⊆ 𝔞 ⊆ d⁻¹𝓞_E`;
* (3) the isogeny `μ : B₀ = ℂ^g/Φ(N𝓞_E) → A` (from `HomLatticeCorr`), its conjugate `μ^σ : B₀^σ → A^σ` (pullback
  property and rigidity), and `θ' = μ^σ ∘ θ'_{B₀}`, with `𝔞̂ = 𝔞 + 𝔟̂` (`latHat_decomp`) and the density of `E` in
  `𝔸_f ⊗ E` modulo `𝔟̂` (`exists_approx_latHat`) for the kernel and the torsion relation.

Main results: `mainTheoremCMSign_of_polar` (every sign `ε`), `mainTheoremCMArith_of_polar`, `mainTheoremCM_of_pol`,
`mainTheoremCM_of_polar`, `qmReciprocityL3_of_pol`, `rayClassCMAb_of_polar`, `shimuraMainCM_of_polar` (the argument
`hCM` of `frozenTarget`); the new leaves are implied by the old ones (`mainTheoremCMPolMax_of_arith`,
`mainTheoremCMPol_of_mainTheoremCM`). No statement of the kernel is changed. No `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

noncomputable section

set_option linter.all false

namespace MainCMPolar

open ZInQ.HomLattice (IsAnalyticHom isAnalyticHom_of_unif analyticHomLiftC_of_leaf isAnalyticHom_comp
  isUniformization_iff map_nsmul_of_hom)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization cptObj)
open scoped TensorProduct ComplexConjugate

/-! ## §1 Lattices `𝔞̂ ⊂ 𝔸_f ⊗ E` -/

section Hat

variable {E : Type} [Field E] [NumberField E]

/-! ### `𝔞̂` -/

theorem one_tmul_mem_latHat {𝔞 : AddSubgroup E} {x : E} (hx : x ∈ 𝔞) : (1 : AQ) ⊗ₜ[ℚ] x ∈ latHat 𝔞 :=
  AddSubgroup.subset_closure ⟨1, ZhatS.one_mem, x, hx, rfl⟩

theorem latHat_mono {𝔞 𝔟 : AddSubgroup E} (h : 𝔞 ≤ 𝔟) : latHat 𝔞 ≤ latHat 𝔟 :=
  AddSubgroup.closure_mono fun _ ⟨c, hc, x, hx, e⟩ => ⟨c, hc, x, h hx, e⟩

theorem natCast_mul_tmul (m : ℕ) (b : AQ) (x : E) :
    ((m : AQ) * b) ⊗ₜ[ℚ] x = b ⊗ₜ[ℚ] ((m : E) * x) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul]

theorem intCast_tmul (n : ℤ) (x : E) : ((n : AQ)) ⊗ₜ[ℚ] x = (1 : AQ) ⊗ₜ[ℚ] ((n : E) * x) := by
  rw [← zsmul_eq_mul, ← mul_one (n : AQ), ← zsmul_eq_mul, TensorProduct.smul_tmul]

/-- **`𝔞̂ = 𝔞 + 𝔟̂` for `m𝔞 ⊆ 𝔟`** (approximation of `ℤ̂` by `ℤ` modulo `m`). -/
theorem latHat_decomp {𝔞 𝔟 : AddSubgroup E} {m : ℕ} (hm : 0 < m) (hab : ∀ x ∈ 𝔞, (m : E) * x ∈ 𝔟)
    {w : AQ ⊗[ℚ] E} (hw : w ∈ latHat 𝔞) : ∃ a ∈ 𝔞, w - (1 : AQ) ⊗ₜ[ℚ] a ∈ latHat 𝔟 := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hw
    obtain ⟨n, b, hb, hcb⟩ := exists_int_approx hc m hm
    refine ⟨(n : E) * x, ?_, ?_⟩
    · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ hx n
    · rw [hcb, TensorProduct.add_tmul, intCast_tmul, natCast_mul_tmul, add_sub_cancel_left]
      exact AddSubgroup.subset_closure ⟨b, hb, _, hab x hx, rfl⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, hau⟩ := hu
    obtain ⟨b, hb, hbv⟩ := hv
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have e : u + v - (1 : AQ) ⊗ₜ[ℚ] (a + b) = (u - 1 ⊗ₜ a) + (v - 1 ⊗ₜ b) := by
      rw [TensorProduct.tmul_add]; abel
    rw [e]; exact add_mem hau hbv
  | neg u _ hu =>
    obtain ⟨a, ha, hau⟩ := hu
    refine ⟨-a, neg_mem ha, ?_⟩
    have e : -u - (1 : AQ) ⊗ₜ[ℚ] (-a) = -(u - 1 ⊗ₜ a) := by
      rw [TensorProduct.tmul_neg]; abel
    rw [e]; exact neg_mem hau

/-- **Density** of `E` in `𝔸_f ⊗ E` modulo `𝔟̂`, for `𝔟` containing a multiple of every element. -/
theorem exists_approx_latHat {𝔟 : AddSubgroup E} (hb : ∀ e : E, ∃ k : ℕ, 0 < k ∧ (k : E) * e ∈ 𝔟)
    (w : AQ ⊗[ℚ] E) : ∃ x : E, w - (1 : AQ) ⊗ₜ[ℚ] x ∈ latHat 𝔟 := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a e =>
    obtain ⟨d, hd, hda⟩ := exists_den a
    obtain ⟨k, hk, hke⟩ := hb e
    obtain ⟨n, b, hbz, hab⟩ := exists_int_approx hda (d * k) (Nat.mul_pos hd hk)
    refine ⟨((n : ℚ) / d) • e, ?_⟩
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have ha : a = algebraMap ℚ AQ ((n : ℚ) / d) + (k : AQ) * b := by
      have h1 : (d : AQ) * a = (d : AQ) * (algebraMap ℚ AQ ((n : ℚ) / d) + (k : AQ) * b) := by
        rw [hab, mul_add, ← mul_assoc, ← Nat.cast_mul, ← map_natCast (algebraMap ℚ AQ) d, ← map_mul,
          mul_div_cancel₀ _ hd0, map_intCast]
      have hu : algebraMap ℚ AQ (d : ℚ)⁻¹ * (d : AQ) = 1 := by
        rw [← map_natCast (algebraMap ℚ AQ), ← map_mul, inv_mul_cancel₀ hd0, map_one]
      calc a = algebraMap ℚ AQ (d : ℚ)⁻¹ * ((d : AQ) * a) := by rw [← mul_assoc, hu, one_mul]
        _ = _ := by rw [h1, ← mul_assoc, hu, one_mul]
    rw [ha, TensorProduct.add_tmul, natCast_mul_tmul, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, add_sub_cancel_left]
    exact AddSubgroup.subset_closure ⟨b, hbz, _, hke, rfl⟩
  | add u v hu hv =>
    obtain ⟨x, hx⟩ := hu
    obtain ⟨y, hy⟩ := hv
    refine ⟨x + y, ?_⟩
    have e : u + v - (1 : AQ) ⊗ₜ[ℚ] (x + y) = (u - 1 ⊗ₜ x) + (v - 1 ⊗ₜ y) := by
      rw [TensorProduct.tmul_add]; abel
    rw [e]; exact add_mem hx hy


end Hat

/-! ## §2 The lattice of a uniformization -/

section Lattice

open MonObj

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


end Lattice

/-! ## §3 Step (2): the Riemann-form element `ζ` -/

section Zeta

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


theorem conj_emb (φ : E →+* ℂ) (x : E) : φ (IsCMField.complexConj E x) = conj (φ x) :=
  IsCMField.complexEmbedding_complexConj E φ x

/-- A nonzero totally imaginary element: `β̄ = −β`, `β ≠ 0`. -/
theorem exists_imag : ∃ β : E, IsCMField.complexConj E β = -β ∧ β ≠ 0 := by
  have hne := IsCMField.complexConj_ne_one E
  obtain ⟨α, hα⟩ : ∃ α : E, IsCMField.complexConj E α ≠ α := by
    by_contra h
    push Not at h
    exact hne (AlgEquiv.ext h)
  refine ⟨α - IsCMField.complexConj E α, ?_, ?_⟩
  · rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  · exact sub_ne_zero.2 (Ne.symm hα)

/-- **Step (2), the Riemann-form element** (weak approximation at the infinite places of `E`): for a CM type `Φ`
there is `ζ ∈ E` with `ζ̄ = −ζ` and `Im φᵢ(ζ) > 0` for all `i`. -/
theorem exists_zeta {g : ℕ} (Φ : Fin g → E →+* ℂ)
    (hinj : Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i))) :
    ∃ ζ : E, IsCMField.complexConj E ζ = -ζ ∧ ∀ i, 0 < (Φ i ζ).im := by
  obtain ⟨β, hβc, hβ0⟩ := exists_imag (E := E)
  let w : Fin g → InfinitePlace E := fun i => InfinitePlace.mk (Φ i)
  have hw : Function.Injective w := by
    intro i j hij
    rcases InfinitePlace.mk_eq_iff.1 hij with h | h
    · exact Sum.inl_injective (hinj (by simpa using h))
    · have : (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) (Sum.inr i) =
          (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) (Sum.inl j) := by
        simp only [Sum.elim_inr, Sum.elim_inl]
        rw [← h]; rfl
      exact absurd (hinj this) (by simp)
  let v : Fin g → AbsoluteValue E ℝ := fun i => (w i).1
  have hdense := AbsoluteValue.denseRange_algebraMap_pi (F := E) (v := v)
    (fun i => (w i).isNontrivial)
    (fun i j hij => by
      intro he
      exact hij (hw ((InfinitePlace.eq_iff_isEquiv (K := E)).2 he)))
  -- imaginary parts of `φᵢ(β)`
  have hre : ∀ i, (Φ i β).re = 0 := by
    intro i
    have h1 : conj (Φ i β) = -Φ i β := by rw [← conj_emb, hβc, map_neg]
    have h2 := congrArg Complex.re h1
    simp only [Complex.conj_re, Complex.neg_re] at h2
    linarith
  have him : ∀ i, (Φ i β).im ≠ 0 := by
    intro i h
    apply hβ0
    have : Φ i β = 0 := Complex.ext (hre i) h
    exact (map_eq_zero_iff _ (Φ i).injective).1 this
  let sβ : Fin g → E := fun i => if 0 < (Φ i β).im then β else -β
  have hsβ : ∀ i, (Φ i (sβ i)).im = |(Φ i β).im| := by
    intro i
    by_cases h : 0 < (Φ i β).im
    · simp [sβ, h, abs_of_pos h]
    · have h' : (Φ i β).im < 0 := lt_of_le_of_ne (not_lt.1 h) (him i)
      simp [sβ, h, abs_of_neg h']
  let z : (i : Fin g) → WithAbs (v i) := fun i => WithAbs.toAbs (v i) (sβ i)
  let U : Set ((i : Fin g) → WithAbs (v i)) :=
    Set.pi Set.univ fun i => Metric.ball (z i) (|(Φ i β).im| / 2)
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun i _ => Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨z, fun i _ => Metric.mem_ball_self (by
    have := abs_pos.2 (him i); linarith)⟩
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU hUne
  have hxi : ∀ i, 0 < (Φ i x).im := by
    intro i
    have h := hx i (Set.mem_univ i)
    rw [Metric.mem_ball, dist_eq_norm] at h
    have e : ‖(algebraMap E ((i : Fin g) → WithAbs (v i)) x) i - z i‖ = ‖Φ i x - Φ i (sβ i)‖ := by
      show v i (x - sβ i) = _
      show (InfinitePlace.mk (Φ i)) (x - sβ i) = _
      rw [InfinitePlace.apply, map_sub]
    rw [e] at h
    have h2 : |(Φ i x - Φ i (sβ i)).im| ≤ ‖Φ i x - Φ i (sβ i)‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hsβ] at h2
    have := abs_pos.2 (him i)
    have h3 := (abs_le.1 (h2.trans h.le)).1
    linarith
  refine ⟨x - IsCMField.complexConj E x, ?_, fun i => ?_⟩
  · rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  · rw [map_sub, conj_emb, Complex.sub_im, Complex.conj_im]
    linarith [hxi i]


end Zeta

/-! ## §4 The polarized, maximal-order print and Shimura's existence theorem (leaves) -/

section Leaves

variable {E : Type} [Field E] [NumberField E]

/-- **`𝔞` is a fractional `𝓞_E`-ideal** (an `𝓞_E`-stable lattice in `E`): `𝓞_E 𝔞 ⊆ 𝔞` and `c 𝓞_E ⊆ 𝔞 ⊆ d⁻¹ 𝓞_E`
for some positive integers `c`, `d`. -/
def IsOLattice (𝔞 : AddSubgroup E) : Prop :=
  (∀ o : 𝓞 E, ∀ x ∈ 𝔞, (o : E) * x ∈ 𝔞) ∧
  (∃ c : ℕ, 0 < c ∧ ∀ o : 𝓞 E, (c : E) * o ∈ 𝔞) ∧
  (∃ d : ℕ, 0 < d ∧ ∀ x ∈ 𝔞, IsIntegral ℤ ((d : E) * x))

variable [IsCMField E]

/-- **`ζ` is a Riemann-form datum for `(Φ, 𝔞)`** (Shimura's type `(E, Φ; 𝔞, ζ)`): `ζ̄ = −ζ`, `Im φᵢ(ζ) > 0` for every
`φᵢ ∈ Φ`, and `Tr_{E/ℚ}(ζ x ȳ) ∈ ℤ` for `x, y ∈ 𝔞`. Then `E(Φ(x), Φ(y)) = Tr_{E/ℚ}(ζ x ȳ)`, extended `ℝ`-linearly,
is a Riemann form on `ℂ^g/Φ(𝔞)` (Shimura 1998, §6.2; Shimura 1971, §5.5; with `−ζ` under the opposite sign
convention for `E`; the integrality clause is symmetric in `ζ ↦ −ζ`). -/
def IsRiemannDatum {g : ℕ} (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) (ζ : E) : Prop :=
  IsCMField.complexConj E ζ = -ζ ∧ (∀ i, 0 < (Φ i ζ).im) ∧
  ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (ζ * x * IsCMField.complexConj E y) = n

end Leaves

section Main

open MonObj

/-- **LEAF `MainTheoremCMPolMax` (the main theorem of complex multiplication for polarized CM abelian varieties of
type `(E, Φ; 𝔞, ζ)` with `𝔞` a fractional `𝓞_E`-ideal; printed form).** Let `E` be a CM field, `Φ` a CM type,
`(Er, κr)` its reflex field with a model `ρ` of `ℂ^Φ` (reflex norm `N = N_{Φ*}`), `σ ∈ Aut(ℂ)` and `s` an idele of
`E*` with `σ = [s, E*]` on `E*^ab` (Tau Ceti's arithmetic Artin map). Let `A/ℂ` be an abelian variety of dimension
`g` with `θ : ℂ^g/Φ(𝔞) ≅ A(ℂ)`, `(A, θ)` of type `(E, Φ)`, where `𝔞` is a fractional `𝓞_E`-ideal (`IsOLattice`)
and the polarization `C` of `A` is given through its Riemann form `Tr_{E/ℚ}(ζ x ȳ)` (`IsRiemannDatum`). Then
`A^σ` is uniformized by `θ' : ℂ^g/Φ(N(s)⁻¹𝔞) ≅ A^σ(ℂ)` with `θ(Φ(x))^σ = θ'(Φ(y))` whenever `N(s) y − x ∈ 𝔞̂`.

*Published statement*: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971),
Thm 5.15 (with §5.5: "Let `(A, C, θ)` be of type `(K, Φ; 𝔞, ζ)` …", `ξ(u)^σ = ξ'(N_{Φ*}(s)⁻¹u)`); G. Shimura,
*Abelian varieties with complex multiplication and modular functions* (1998), §18, Thm 18.6; Shimura–Taniyama
(1961), §§13–14 (numbers UNVERIFIED; this host has no network).

*Form*: the print restricted to maximal-order (`𝓞_E`-ideal) lattices and to structures with a polarization of
the given type, in Shimura's arithmetic normalization (`ε = 1`, hcm-printed's `MainTheoremCMArith`); the
polarization `C` is entered by its Riemann form with respect to `θ` (Riemann forms on `A(ℂ)` ↔ polarizations of
`A`: Mumford, *Abelian varieties*, §2–3, Shimura 1998, §3–4); the clauses on `C^σ`, on the type of `(A^σ, θ')`
and the uniqueness of `θ'` are dropped. Every other convention (reflex field and norm through a model, `A^σ` as a
pullback preserving the identity, torsion through `𝔞̂ = 𝔞 ⊗ ℤ̂`) is qmrec-printed's `MainTheoremCM`, verbatim. -/
def MainTheoremCMPolMax : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞))
      θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈
          latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- **LEAF `CMAbVarExists` (existence of a polarized abelian variety of a given CM type; printed form).** For a CM
field `E` with CM type `Φ`, a fractional `𝓞_E`-ideal `𝔟` and a Riemann-form datum `ζ` for `(Φ, 𝔟)`, the complex torus
`ℂ^g/Φ(𝔟)` is (analytically isomorphic to) the complex points of an abelian variety `B/ℂ` of dimension `g`.

*Published statement*: G. Shimura, *Abelian varieties with complex multiplication and modular functions* (1998),
§6.2, Theorem 4 (resp. Shimura–Taniyama 1961, §6.2, Thm 4): for `(K, Φ)`, a lattice `𝔞` in `K` and `ζ` with
`ζ̄ = −ζ`, `Im(ζ^{φᵢ}) > 0` and `Tr(ζ 𝔞 𝔞^ρ) ⊆ ℤ`, there is a polarized abelian variety `(A, C, θ)` of type
`(K, Φ; 𝔞, ζ)` with `ℂ^g/Φ(𝔞) ≅ A(ℂ)`; in general form, Riemann's theorem (a complex torus with a Riemann form is
an abelian variety: Mumford, *Abelian varieties*, §3, with GAGA/Chow for the scheme). Numbers UNVERIFIED.

*Form*: weaker than the print: only `𝓞_E`-ideal lattices, and only the existence of `B` with a uniformization by
`Φ(𝔟)` is kept (the polarization `C` and the action `θ` are dropped; the action is recovered from
`HomLatticeCorr`). -/
def CMAbVarExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ 𝔟 : AddSubgroup E, IsOLattice 𝔟 → (∃ ζ : E, IsRiemannDatum Φ 𝔟 ζ) →
  ∃ (B : PkgI3.AbVar ℂ) (θ : (Fin g → ℂ) → CPts B (RingHom.id ℂ)),
    B.dim = (g : WithBot ℕ∞) ∧ IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔟) θ

/-- `MainTheoremCMPolMax` at a sign `ε` (`t = N(s)^ε`): the body of `HcmPrinted.MainTheoremCMSign ε` with the two
hypotheses `IsOLattice 𝔞` and `∃ ζ, IsRiemannDatum Φ 𝔞 ζ` added. -/
def MainTheoremCMPolSign (ε : ℤˣ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

/-- **LEAF `MainTheoremCMPol` (the polarized, maximal-order print with the sign of the Artin map left open;
printed form).** `MainTheoremCMPolMax` with `t = N(s)^ε` for some `ε = ±1`, as in qmrec-printed's `MainTheoremCM`:
the same published statements (Shimura 1971 Thm 5.15 / §5.5, Shimura 1998 Thm 18.6, Milne's form with
`N(s)⁻¹` in the geometric normalization), weakened by the existential sign, so that no reading of the
normalization of `[s, E*]` is needed. Implied by `MainTheoremCMPolMax` (`mainTheoremCMPol_of_polMax`) and by
`QMRecPrinted.MainTheoremCM` (`mainTheoremCMPol_of_mainTheoremCM`). -/
def MainTheoremCMPol : Prop := ∃ ε : ℤˣ, MainTheoremCMPolSign ε

theorem polSign_one_of_polMax (h : MainTheoremCMPolMax) : MainTheoremCMPolSign 1 := by
  intro E _ _ _ g Φ hdeg hinj Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone
  simp only [Units.val_one, zpow_one]
  exact h E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype hO hζ A' hh hpb hone

theorem mainTheoremCMPol_of_polMax (h : MainTheoremCMPolMax) : MainTheoremCMPol := ⟨1, polSign_one_of_polMax h⟩

/-- `MainTheoremCMPol` is implied by qmrec-printed's `MainTheoremCM` (it only adds hypotheses). -/
theorem mainTheoremCMPol_of_mainTheoremCM (h : QMRecPrinted.MainTheoremCM) : MainTheoremCMPol := by
  obtain ⟨ε, h⟩ := h
  exact ⟨ε, fun E _ _ _ g Φ hdeg hinj Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype _ _ A' hh hpb hone =>
    h E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype A' hh hpb hone⟩

/-- The new leaf is implied by the old one (it only adds hypotheses): `MainTheoremCMArith → MainTheoremCMPolMax`. -/
theorem mainTheoremCMPolMax_of_arith (h : HcmPrinted.MainTheoremCMArith) : MainTheoremCMPolMax := by
  intro E _ _ _ g Φ hdeg hinj Er _ _ κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype _ _ A' hh hpb hone
  have := h E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs A hA 𝔞 θ hθ htype A' hh hpb hone
  simpa only [Units.val_one, zpow_one] using this

end Main

/-! ## §5 Step (3): arbitrary lattices from `N𝓞_E` through the isogeny `μ : B₀ → A` and its conjugate -/

section Proof

open MonObj HcmPrinted
open AvSplit.HomLatticeAN3 (bcC projC ptE ptE_left)

section Aux

variable {E : Type} [Field E] [NumberField E]

/-- `N 𝓞_E ⊂ E`. -/
def nO (N : ℕ) : AddSubgroup E :=
  ((AddMonoidHom.mulLeft (N : E)).comp (algebraMap (𝓞 E) E).toAddMonoidHom).range

theorem mem_nO {N : ℕ} {x : E} : x ∈ nO N ↔ ∃ o : 𝓞 E, (N : E) * (o : E) = x := by
  simp only [nO, AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]

theorem trace_int {z : E} (hz : IsIntegral ℤ z) : ∃ n : ℤ, Algebra.trace ℚ E z = n := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hz)
  exact ⟨n, by rw [← hn]; simp⟩

theorem natAbs_mul_integral {y : ℤ} {e : E} (h : IsIntegral ℤ (y • e)) :
    IsIntegral ℤ ((y.natAbs : E) * e) := by
  rcases Int.natAbs_eq y with hy | hy
  · rw [hy, zsmul_eq_mul, Int.cast_natCast] at h; exact h
  · rw [hy, zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    have := h.neg; rwa [neg_neg] at this

theorem coe_integral (o : 𝓞 E) : IsIntegral ℤ (o : E) := RingOfIntegers.isIntegral_coe o

/-- The identity `ℂ`-point is the unit section. -/
theorem one_left (X : PkgI3.AbVar ℂ) : (1 : CPts X (RingHom.id ℂ)).left = η[X.X].left := by
  rw [Hom.one_def, Over.comp_left]
  have h1 : (toUnit (cptObj (RingHom.id ℂ) : Over (Spec (CommRingCat.of ℂ)))).left = 𝟙 _ := by
    have h := Over.w (toUnit (cptObj (RingHom.id ℂ) : Over (Spec (CommRingCat.of ℂ))))
    have h' := (Category.comp_id _).symm.trans h
    rw [h']
    show Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
    rfl
  rw [h1]
  exact Category.id_comp _

/-- De-conjugation as a monoid homomorphism. -/
def ddHom (σ : ℂ ≃+* ℂ) (B : PkgI3.AbVar ℂ) :
    CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ) →* CPts B (RingHom.id ℂ) where
  toFun := dd σ B
  map_one' := dd_one σ B
  map_mul' := dd_mul σ B

end Aux

/-- **The main theorem of CM for arbitrary lattices from the polarized, maximal-order print, at any sign `ε`**
(steps (2) and (3)): `MainTheoremCMPolSign ε → MainTheoremCMSign ε`. -/
theorem mainTheoremCMSign_of_polar (ε : ℤˣ) (hP : MainTheoremCMPolSign ε) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    HcmPrinted.MainTheoremCMSign ε := by
  have hH : ZInQ.HomUnify.HomLatticeCorr := AvSplit.Final.h69 hUL hG
  intro E _ _ _ g Φ hdeg hinj Er _ _ κr hκ n ρ j hρ σ s hs A hdimA 𝔞 θ hθ htype A' h hpb hone
  set t : AQ ⊗[ℚ] E := ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) :
    AQ ⊗[ℚ] E) with ht
  have hg : 0 < g := by
    have := Module.finrank_pos (R := ℚ) (M := E); omega
  obtain ⟨⟨N, hN, hNa⟩, ⟨d, hd, hda⟩⟩ := lattice_of_unif hUL Φ hg hdeg hθ
  -- the `𝓞_E`-lattice `𝔟 = N 𝓞_E ⊆ 𝔞`
  let 𝔟 : AddSubgroup E := nO N
  have hb_le : 𝔟 ≤ 𝔞 := fun x hx => by obtain ⟨o, rfl⟩ := mem_nO.1 hx; exact hNa o
  have hm : ∀ x ∈ 𝔞, ((N * d : ℕ) : E) * x ∈ 𝔟 := by
    intro x hx
    refine mem_nO.2 ⟨⟨(d : E) * x, hda x hx⟩, ?_⟩
    show (N : E) * ((d : E) * x) = _
    push_cast; ring
  have hmpos : 0 < N * d := Nat.mul_pos hN hd
  have hbdense : ∀ e : E, ∃ k : ℕ, 0 < k ∧ (k : E) * e ∈ 𝔟 := by
    intro e
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hye := natAbs_mul_integral (hy e (Finset.mem_singleton_self e))
    refine ⟨N * y.natAbs, Nat.mul_pos hN (Int.natAbs_pos.2 hy0), mem_nO.2 ⟨⟨_, hye⟩, ?_⟩⟩
    show (N : E) * ((y.natAbs : E) * e) = _
    push_cast; ring
  have hOL : IsOLattice 𝔟 := by
    refine ⟨fun o x hx => ?_, ⟨N, hN, fun o => mem_nO.2 ⟨o, rfl⟩⟩, ⟨1, one_pos, fun x hx => ?_⟩⟩
    · obtain ⟨o', rfl⟩ := mem_nO.1 hx
      exact mem_nO.2 ⟨o * o', by push_cast; ring⟩
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      have := coe_integral ((N : 𝓞 E) * o)
      push_cast at this
      rw [Nat.cast_one, _root_.one_mul]; exact this
  -- step (2): the Riemann-form datum
  obtain ⟨ζ0, hζc, hζi⟩ := exists_zeta Φ hinj
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {ζ0}
  have hyζ := hy ζ0 (Finset.mem_singleton_self ζ0)
  have hζint : IsIntegral ℤ ((y * y) • ζ0) := by
    rw [mul_smul, zsmul_eq_mul]
    exact (by simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y)) : IsIntegral ℤ (y : E)).mul hyζ
  have hζ : IsRiemannDatum Φ 𝔟 ((y * y) • ζ0) := by
    refine ⟨by rw [map_zsmul, hζc, smul_neg], fun i => ?_, fun x hx x' hx' => ?_⟩
    · rw [map_zsmul, zsmul_eq_mul, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero]
      exact mul_pos (by exact_mod_cast mul_self_pos.2 hy0) (hζi i)
    · obtain ⟨o, rfl⟩ := mem_nO.1 hx
      obtain ⟨o', rfl⟩ := mem_nO.1 hx'
      apply trace_int
      have h1 : IsIntegral ℤ ((N : E) * (o : E)) := by
        have := coe_integral ((N : 𝓞 E) * o); push_cast at this; exact this
      have h2 : IsIntegral ℤ ((N : E) * (o' : E)) := by
        have := coe_integral ((N : 𝓞 E) * o'); push_cast at this; exact this
      exact (hζint.mul h1).mul (h2.map (IsCMField.complexConj E))
  -- the abelian variety `B₀ = ℂ^g/Φ(N𝓞_E)` and the isogeny `μ : B₀ → A`
  obtain ⟨B, θB, hdimB, hθB⟩ := hX E g Φ hdeg hinj 𝔟 hOL ⟨_, hζ⟩
  have htypeB : IsOfType Φ 𝔟 θB := by
    intro e he
    let Me : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun w i => Φ i e * w i
        map_add' := fun w w' => by funext i; simp [mul_add]
        map_smul' := fun c w => by funext i; simp; ring }
    obtain ⟨f, hf, -⟩ := hH.2 B B g g (cmLat Φ 𝔟) (cmLat Φ 𝔟) θB θB hdimB hdimB hθB hθB Me
      (fun z hz => by
        obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz
        exact mem_cmLat.2 ⟨e * x, he x hx, by funext i; simp [Me, cmVec]⟩)
    exact ⟨f, fun w => hf w⟩
  obtain ⟨mu, hμ, -⟩ := hH.2 B A g g (cmLat Φ 𝔟) (cmLat Φ 𝔞) θB θ hdimB hdimA hθB hθ LinearMap.id
    (fun z hz => by
      obtain ⟨x, hx, rfl⟩ := mem_cmLat.1 hz; exact mem_cmLat.2 ⟨x, hb_le hx, rfl⟩)
  have hμ' : ∀ z, θB z ≫ mu.hom = θ z := fun z => (hμ z).symm
  -- the main theorem for `B₀`
  obtain ⟨θB', hθB', hrelB⟩ := hP E g Φ hdeg hinj Er κr hκ n ρ j hρ σ s hs B hdimB 𝔟 θB hθB htypeB hOL
    ⟨_, hζ⟩ (bcC B (σ : ℂ →+* ℂ)) (projC B (σ : ℂ →+* ℂ)) (isPullback_bc σ B) (one_left_bc σ B)
  -- the conjugate isogeny `μ^σ : B₀^σ → A'`
  have hsq : (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) ≫ A.X.hom =
      (bcC B (σ : ℂ →+* ℂ)).X.hom ≫ Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) := by
    rw [Category.assoc, Over.w mu.hom]; exact (isPullback_bc σ B).w
  let muL := hpb.lift (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) (bcC B (σ : ℂ →+* ℂ)).X.hom hsq
  have hmuL : muL ≫ h = projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left := hpb.lift_fst _ _ _
  let muO : (bcC B (σ : ℂ →+* ℂ)).X ⟶ A'.X := Over.homMk muL (hpb.lift_snd _ _ _)
  have hηB : η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[B.X].left := by
    have := one_left_bc σ B
    simp only [pl, one_left] at this
    exact this
  have hηA : η[A'.X].left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
    have := hone
    simp only [one_left] at this
    exact this
  have hμη : η[B.X].left ≫ mu.hom.left = η[A.X].left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hη : η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO = η[A'.X] := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · calc (η[(bcC B (σ : ℂ →+* ℂ)).X] ≫ muO).left ≫ h
            = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ muL ≫ h := by
              rw [Over.comp_left, Category.assoc]; rfl
          _ = η[(bcC B (σ : ℂ →+* ℂ)).X].left ≫ projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left := by rw [hmuL]
          _ = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ η[A.X].left := by
              rw [← Category.assoc, hηB, Category.assoc, hμη]
          _ = η[A'.X].left ≫ h := hηA.symm
    · rw [Over.w, Over.w]
  haveI : IsMonHom muO := MulRigidity.isMonHom_of_geometricallyIntegral _ _ muO hη
  have key : ∀ P : CPts (bcC B (σ : ℂ →+* ℂ)) (RingHom.id ℂ),
      pl (P ≫ muO) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P ≫ mu.hom) := by
    intro P
    calc pl (P ≫ muO) ≫ h = (pl P ≫ muL) ≫ h := rfl
      _ = pl P ≫ (muL ≫ h) := Category.assoc _ _ _
      _ = pl P ≫ (projC B (σ : ℂ →+* ℂ) ≫ mu.hom.left) := by rw [hmuL]
      _ = (pl P ≫ projC B (σ : ℂ →+* ℂ)) ≫ mu.hom.left := (Category.assoc _ _ _).symm
      _ = (sp (σ : ℂ →+* ℂ) ≫ pl (dd σ B P)) ≫ mu.hom.left := by rw [dd_key σ B P]
      _ = sp (σ : ℂ →+* ℂ) ≫ (pl (dd σ B P) ≫ mu.hom.left) := Category.assoc _ _ _
  have hone' : pl (1 : CPts A' (RingHom.id ℂ)) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (1 : CPts A (RingHom.id ℂ)) :=
    hone
  have hddrel : ∀ x y : E, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔟 →
      dd σ B (θB' (cmVec Φ y)) = θB (cmVec Φ x) := by
    intro x y hxy
    apply dd_unique σ B
    exact hrelB x y hxy
  have hsp : ∀ {P Q : CPts A (RingHom.id ℂ)},
      sp (σ : ℂ →+* ℂ) ≫ pl P = sp (σ : ℂ →+* ℂ) ≫ pl Q → P = Q := by
    intro P Q hPQ
    apply pl_ext
    have := congrArg (fun r => sp (σ.symm : ℂ →+* ℂ) ≫ r) hPQ
    rwa [← Category.assoc, ← Category.assoc, sp_symm_comp, Category.id_comp, Category.id_comp] at this
  let θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ) := fun z => θB' z ≫ muO
  -- the kernel
  have hker : ∀ z, θ' z = 1 ↔ z ∈ cmLat Φ (latAct t 𝔞) := by
    intro z
    constructor
    · intro hz
      have e2 : dd σ B (θB' z) ≫ mu.hom = 1 := by
        apply hsp
        rw [← key]
        show pl (θ' z) ≫ h = _
        rw [hz]; exact hone'
      obtain ⟨v, hv⟩ := hθB.2.2.1 (dd σ B (θB' z))
      have hv1 : θ v = 1 := by rw [← hμ', hv, e2]
      obtain ⟨x0, hx0, rfl⟩ := mem_cmLat.1 ((hθ.2.1 v).1 hv1)
      have hcm : ∀ (k : ℕ) (x : E), cmVec Φ ((k : E) * x) = k • cmVec Φ x := by
        intro k x; rw [← nsmul_eq_mul, map_nsmul]
      have hpow : θB' ((N * d) • z) = 1 := by
        rw [map_nsmul_of_hom hθB'.1]
        apply dd_injective σ B
        change ddHom σ B _ = ddHom σ B 1
        rw [map_pow, map_one]
        change (dd σ B (θB' z)) ^ (N * d) = 1
        rw [← hv, ← map_nsmul_of_hom hθB.1, ← hcm]
        exact (hθB.2.1 _).2 ((cmVec_mem_cmLat hg).2 (hm x0 hx0))
      obtain ⟨y1, hy1, hcy1⟩ := mem_cmLat.1 ((hθB'.2.1 _).1 hpow)
      let y : E := ((N * d : ℕ) : ℚ)⁻¹ • y1
      have hk0 : ((N * d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
      have hcy : cmVec Φ y = z := by
        show cmVec Φ (((N * d : ℕ) : ℚ)⁻¹ • y1) = z
        rw [cmVec_ratSmul, hcy1, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ (by exact_mod_cast hk0), one_smul]
      obtain ⟨x, hx⟩ := exists_approx_latHat hbdense (t * (1 ⊗ₜ y))
      have h1 := hddrel x y hx
      rw [hcy] at h1
      have h2 : θB (cmVec Φ x) = θB (cmVec Φ x0) := by rw [← h1, hv]
      have hxx0 : x - x0 ∈ 𝔟 := by
        have := (hom_eq_iff hθB.1 _ _).1 h2
        rw [← map_sub] at this
        exact (cmVec_mem_cmLat hg).1 ((hθB.2.1 _).1 this)
      refine mem_cmLat.2 ⟨y, ?_, hcy⟩
      show t * (1 ⊗ₜ y) ∈ latHat 𝔞
      have e : t * (1 ⊗ₜ[ℚ] y) = (t * (1 ⊗ₜ y) - 1 ⊗ₜ x) + (1 : AQ) ⊗ₜ[ℚ] (x - x0) + (1 : AQ) ⊗ₜ[ℚ] x0 := by
        rw [TensorProduct.tmul_sub]; abel
      rw [e]
      exact add_mem (add_mem (latHat_mono hb_le hx) (latHat_mono hb_le (one_tmul_mem_latHat hxx0)))
        (one_tmul_mem_latHat hx0)
    · intro hz
      obtain ⟨y, hy, rfl⟩ := mem_cmLat.1 hz
      have hy' : t * (1 ⊗ₜ y) ∈ latHat 𝔞 := hy
      obtain ⟨x0, hx0, hrem⟩ := latHat_decomp hmpos hm hy'
      apply pt_ext hpb
      show pl (θB' (cmVec Φ y) ≫ muO) ≫ h = pl (1 : CPts A' (RingHom.id ℂ)) ≫ h
      rw [key, hddrel x0 y hrem, hμ', (hθ.2.1 _).2 (mem_cmLat.2 ⟨x0, hx0, rfl⟩), hone']
  -- surjectivity
  have hsurj : Function.Surjective θ' := by
    intro P
    have hQ : (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) ≫ A.X.hom = sp (RingHom.id ℂ) := by
      have hw : pl P ≫ A'.X.hom = sp (RingHom.id ℂ) := Over.w P
      rw [Category.assoc, Category.assoc, hpb.w, ← Category.assoc (pl P), hw, sp_id, Category.id_comp,
        sp_symm_comp]
    let Q : CPts A (RingHom.id ℂ) := Over.homMk (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) hQ
    obtain ⟨u, hu⟩ := hθ.2.2.1 Q
    obtain ⟨R, hR⟩ := dd_surjective σ B (θB u)
    obtain ⟨v, hv⟩ := hθB'.2.2.1 R
    refine ⟨v, pt_ext hpb ?_⟩
    show pl (θB' v ≫ muO) ≫ h = pl P ≫ h
    rw [key, hv, hR, hμ', hu]
    show sp (σ : ℂ →+* ℂ) ≫ (sp (σ.symm : ℂ →+* ℂ) ≫ pl P ≫ h) = pl P ≫ h
    rw [← Category.assoc, sp_comp_symm, Category.id_comp]
  -- the torsion relation
  have htors : ∀ x y : E, t * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
      (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left := by
    intro x y hxy
    obtain ⟨a, ha, hrem⟩ := latHat_decomp hmpos hm hxy
    have hrem' : t * (1 ⊗ₜ y) - 1 ⊗ₜ (x + a) ∈ latHat 𝔟 := by
      have e : t * (1 ⊗ₜ[ℚ] y) - (1 : AQ) ⊗ₜ[ℚ] (x + a) = t * (1 ⊗ₜ y) - 1 ⊗ₜ x - 1 ⊗ₜ a := by
        rw [TensorProduct.tmul_add]; abel
      rw [e]; exact hrem
    show pl (θB' (cmVec Φ y) ≫ muO) ≫ h = sp (σ : ℂ →+* ℂ) ≫ pl (θ (cmVec Φ x))
    rw [key, hddrel _ _ hrem', hμ', map_add, hθ.1, (hθ.2.1 _).2 (mem_cmLat.2 ⟨a, ha, rfl⟩), _root_.mul_one]
  exact ⟨θ', (isUniformization_iff _ _ _).2
    ⟨isAnalyticHom_comp (isAnalyticHom_of_unif hθB') muO, hker, hsurj⟩, htors⟩

/-- **`MainTheoremCMArith` from the polarized, maximal-order print** (`ε = 1`). -/
theorem mainTheoremCMArith_of_polar (hP : MainTheoremCMPolMax) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    HcmPrinted.MainTheoremCMArith :=
  mainTheoremCMSign_of_polar 1 (polSign_one_of_polMax hP) hX hUL hG

/-- **qmrec-printed's `MainTheoremCM` from the polarized, maximal-order print with existential sign.** -/
theorem mainTheoremCM_of_pol (hP : MainTheoremCMPol) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    QMRecPrinted.MainTheoremCM := by
  obtain ⟨ε, h⟩ := hP
  exact ⟨ε, mainTheoremCMSign_of_polar ε h hX hUL hG⟩

end Proof

/-! ## §6 Consequences: qmrec-printed's and hcm-printed's targets from the polarized print -/

section Consequences

/-- **qmrec-printed's `MainTheoremCM`** (existential sign) from the polarized, maximal-order print. -/
theorem mainTheoremCM_of_polar (hP : MainTheoremCMPolMax) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    QMRecPrinted.MainTheoremCM :=
  HcmPrinted.mainTheoremCM_of_arith (mainTheoremCMArith_of_polar hP hX hUL hG)

/-- **shimura-split2's `QMReciprocityL3`** (qmrec-printed's `qmReciprocityL3_of_textbook`) from the polarized,
maximal-order print with existential sign. -/
theorem qmReciprocityL3_of_pol (hP : MainTheoremCMPol) (hX : CMAbVarExists)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    ShimuraSplit2.QMReciprocityL3 :=
  QMRecPrinted.qmReciprocityL3_of_textbook (mainTheoremCM_of_pol hP hX hUL hG) hUL hG

/-- **The former field `rayClassCMAb`** (qmrec-printed's `rayClassCMAb_of_mainCM`) with `MainTheoremCM` derived from
the polarized, maximal-order print with existential sign. -/
theorem rayClassCMAb_of_polar (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : MainTheoremCMPol)
    (hX : CMAbVarExists) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) :
    ShimuraGlue.Ray.RayClassCMAb :=
  QMRecPrinted.rayClassCMAb_of_mainCM hR (mainTheoremCM_of_pol hP hX hUL hG) hUL hG hMum

/-- **`hCM = T5Glue.ShimuraMainCM`** (hcm-printed's `shimuraMainCM_of_textbook`) with `MainTheoremCMArith` derived
from the polarized, maximal-order print. -/
theorem shimuraMainCM_of_polar (hP : MainTheoremCMPolMax) (hX : CMAbVarExists)
    (hWU : HcmPrinted.WeierstrassUniformization) (hWP : HcmPrinted.WeierstrassParam)
    (hWA : HcmPrinted.WeierstrassAbVar) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) : T5Glue.ShimuraMainCM :=
  HcmPrinted.shimuraMainCM_of_textbook (mainTheoremCMArith_of_polar hP hX hUL hG) hWU hWP hWA hUL hG

end Consequences

end MainCMPolar
