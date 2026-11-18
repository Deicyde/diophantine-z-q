import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Invariant.Basic

/-!
# Inertia groups surject under restriction, profinite kernel

Let `f : G →* G'` be surjective, compatible with the actions on `S` and `R`, and let `H ≤ ker f` be
a profinite group acting on the discrete ring `S` with invariants `R`. For a prime `q` of `S` over
`p`, the image of the inertia group of `q` in `G` is the inertia group of `p` in `G'`
(`map_inertia_of_surjective_of_profinite`); likewise for decomposition groups
(`map_stabilizer_of_surjective_of_profinite`).

This is the profinite-kernel analogue of the finite-kernel statement in the invariant theory of
rings: the finite transitivity and residue-surjectivity steps are replaced by their profinite
counterparts (inverse limits of nonempty finite sets). It applies to restriction from the
automorphism group of an algebraic closure to that of a finite Galois subextension.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open MulAction Ideal Pointwise

variable {R S G G' : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [Group G'] [MulSemiringAction G S] [MulSemiringAction G' R]
  (f : G →* G') (H : Subgroup G)
  [TopologicalSpace H] [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul H S]
  [Algebra.IsInvariant R S H]
  (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime]

theorem map_stabilizer_of_surjective_of_profinite (hf_surj : Function.Surjective f)
    (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (stabilizer G q).map f = stabilizer G' p := by
  replace hf_ker (h : H) : f h = 1 := hf_ker h.2
  have : SMulCommClass H R S :=
    ⟨fun h x y ↦ by simp [Algebra.smul_def, H.smul_def, ← hf, hf_ker]⟩
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩
    ext x
    rw [SetLike.mem_coe, mem_stabilizer_iff] at hg
    simp_rw [mem_pointwise_smul_iff_inv_smul_mem, over_def q p, mem_under, ← map_inv, hf,
      ← mem_pointwise_smul_iff_inv_smul_mem, hg]
  · intro g hg
    obtain ⟨g, rfl⟩ := hf_surj g
    have : (g • q).under R = q.under R := by
      ext x
      rw [mem_under, mem_pointwise_smul_iff_inv_smul_mem, ← hf, ← mem_under, ← over_def q p,
        map_inv, ← mem_pointwise_smul_iff_inv_smul_mem, hg]
    obtain ⟨g', hg'⟩ :=
      Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R) (G := H) (g • q) q this
    exact ⟨g' * g, by simpa [mul_smul, eq_comm], by simp [hf_ker]⟩

theorem map_inertia_of_surjective_of_profinite (hf_surj : Function.Surjective f)
    (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (q.inertia G).map f = p.inertia G' := by
  have h_stab := (map_stabilizer_of_surjective_of_profinite f H p q hf_surj hf_ker hf).ge
  replace hf_ker (h : H) : f h = 1 := hf_ker h.2
  have : SMulCommClass H R S :=
    ⟨fun h x y ↦ by simp [Algebra.smul_def, H.smul_def, ← hf, hf_ker]⟩
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩ x
    simpa [over_def q p, map_sub, hf] using hg (algebraMap R S x)
  · intro g hg
    obtain ⟨g, rfl⟩ : ∃ g' : stabilizer G q, f g' = g := by
      simpa using h_stab.ge (p.inertia_le_stabilizer hg)
    let φ : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ q) :=
    { __ := Ideal.Quotient.stabilizerHom q (q.under ℤ) G g
      commutes' x := by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        specialize hg x
        rw [Submodule.mem_toAddSubgroup, over_def q p, mem_under, map_sub, hf,
          ← Ideal.Quotient.eq] at hg
        simpa }
    obtain ⟨g', hg'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) p q φ
    let v : stabilizer G q := ⟨g', g'.2⟩⁻¹ * g
    refine ⟨v, ?_, by simp [v, hf_ker]⟩
    rw [SetLike.mem_coe, coe_mem_inertia, ← Ideal.Quotient.ker_stabilizerHom q (q.under ℤ) G,
      MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    rw [AlgEquiv.ext_iff] at hg' ⊢
    assumption

end InertiaPointDescent
