import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.Kummer

/-!
# HeegnerCohomology, part 6: the adjusted representative at a derivative prime

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 6,
tex 3122–3128:

"Choose a continuous cocycle representing `b_{I∪{ℓ},a}` and choose `Z` with `2^a Z = L D_ℓ Y`.
Its restriction to `G_{H_{f n_I ℓ}}` is cohomologous to `g ↦ (g-1)Z`.  Their difference is the
coboundary of a single element of `E[2^a]`; subtract the same global coboundary to make the
restriction exactly this Kummer cocycle."

RC10 takes the outcome as the fields `cocycle`, `tors`, `kummer_upper` of its interface
`DerivativePrimeInput` (file `ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Interfaces.lean`), classified `ELLIOT`.  Here the step is `PROVED` over genuine continuous
cohomology (`exists_adjusted_rep`): for a short exact sequence `0 → A → B → C → 0` of discrete
`G`-modules (for `0 → E[2^a] → E → E → 0`), a subgroup `N` (for `G_{H_{f n_I ℓ}}`), a class
`v ∈ H¹(G, A)` (for `b_{I∪{ℓ},a}`) whose restriction to `N` is the Kummer class `δ⁰(x')`, and any
`Z ∈ B` lifting `x'` (for `2^a Z = L D_ℓ Y`), there is a continuous cocycle `b` representing `v`
whose restriction to `N` is exactly `h ↦ h Z - Z`.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open TauCeti.ContCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {B : Type*} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [DistribMulAction G B] [ContinuousSMul G B]
  {C : Type*} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction G C]

/-- **The adjusted representative** (tex 3122–3128), `PROVED`: if the restriction of `v` to `N`
is the Kummer class of `x' ∈ C^N` and `S.proj Z = x'`, then `v` has a continuous cocycle
representative `b` with `b(h) = h Z - Z` (in `B`) for every `h ∈ N`. -/
theorem exists_adjusted_rep (S : DiscreteShortExact G A B C) (N : Subgroup G)
    (v : H1 G A) (x' : H0 N C) (Z : B) (hZ : S.proj Z = (x' : C))
    (hv : explicitRes1 G A N v = (S.restrict N).explicitDelta0 x') :
    ∃ b : Z1 G A, (b : H1 G A) = v ∧ ∀ h : N, S.incl ((b : G → A) h) = (h : G) • Z - Z := by
  have hZmem : (S.restrict N).proj Z ∈ H0 N C := by
    rw [DiscreteShortExact.restrict_proj, hZ]; exact x'.2
  obtain ⟨a, -, ha⟩ := (S.restrict N).exists_continuous_incl_comp_eq
    (continuous_d0_apply (G := N) Z) ((S.restrict N).proj_d0_eq_zero hZmem)
  have ha' : ∀ h : N, (S.restrict N).incl (a h) = h • Z - Z := fun h => (ha h).trans (d0_apply Z h)
  rw [(S.restrict N).explicitDelta0_apply x' hZ ha'] at hv
  induction v using QuotientAddGroup.induction_on with
  | H b0 =>
    rw [explicitRes1_mk] at hv
    have hB := H1pi_eq_iff.mp hv
    obtain ⟨m, hm⟩ := mem_B1_iff.mp hB
    refine ⟨b0 - ⟨d0 G A m, B1_le_Z1 G A (AddMonoidHom.mem_range.mpr ⟨m, rfl⟩)⟩, ?_, fun h => ?_⟩
    · show H1pi G A _ = H1pi G A b0
      rw [map_sub, sub_eq_self]
      exact H1pi_eq_zero_iff.mpr (AddMonoidHom.mem_range.mpr ⟨m, rfl⟩)
    · have hmh := hm h
      simp only [Pi.sub_apply, cocyclesMap1_apply, AddMonoidHom.id_apply] at hmh
      have : (b0 : G → A) h - (h • m - m) = a h := by
        rw [hmh]
        show (b0 : G → A) h - ((b0 : G → A) h - a h) = a h
        abel
      show S.incl ((b0 : G → A) h - d0 G A m h) = _
      rw [d0_apply, ← Subgroup.smul_def h m] at *
      rw [this]
      exact ha' h

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
