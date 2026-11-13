import Mathlib
import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# Continuous `ℤ/2`-cochains on a profinite group are inflated from finite quotients (GLUE)

Kernel form: imports `ZInQKernel.HDecomp.Conductor.I6Base` and uses its `PkgI6.IsCocycle2`,
`IsCoboundary2`, `H2TwoClasses`, `LocalH2CardC` (nothing copied but the proofs).

Main results (compact, zero-dimensional topological group `G`, e.g. `Field.absoluteGaloisGroup K`):
* `exists_openNormalSubgroup_invariant₂`: a continuous `ε : G → G → ZMod 2` is bi-invariant
  under some open normal subgroup `N`;
* `isCocycle2_iff`: `IsCocycle2 ε` ↔ cocycle identity ∧ `ε` is `N`-bi-invariant for some open
  normal `N` (no topology on the right beyond "open normal subgroup");
* `isCoboundary2_iff`: `IsCoboundary2 ε` ↔ `ε = δf` for an `f` invariant under some open normal
  `N`.
So the cochain-level leaves T14/T15 are statements about the finite quotients `G/N`.
-/

open scoped Pointwise


namespace TPurity2K

open PkgI6

/-- A continuous map from a compact topological group to `ZMod 2` is invariant under right
multiplication by a neighbourhood of `1`. -/
theorem exists_nhds_one_invariant {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] (f : H → ZMod 2) (hf : Continuous f) :
    ∃ V ∈ nhds (1 : H), ∀ z, ∀ v ∈ V, f (z * v) = f z := by
  have key : ∀ c : ZMod 2, ∃ V ∈ nhds (1 : H), f ⁻¹' {c} * V ⊆ f ⁻¹' {c} := fun c => by
    have hcl : IsClosed (f ⁻¹' {c}) := (isClosed_discrete _).preimage hf
    have hop : IsOpen (f ⁻¹' {c}) := (isOpen_discrete _).preimage hf
    exact compact_open_separated_mul_right hcl.isCompact hop subset_rfl
  choose V hV hsub using key
  refine ⟨⋂ c, V c, Filter.iInter_mem.mpr hV, fun z v hv => ?_⟩
  have hv' : v ∈ V (f z) := Set.mem_iInter.mp hv (f z)
  have : z * v ∈ f ⁻¹' {f z} := hsub (f z) (Set.mul_mem_mul rfl hv')
  exact this

/-- A continuous `ε : G → G → ZMod 2` on a compact zero-dimensional group is bi-invariant under
an open normal subgroup. -/
theorem exists_openNormalSubgroup_invariant₂ {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] (ε : G → G → ZMod 2)
    (hε : Continuous (fun x : G × G => ε x.1 x.2)) :
    ∃ N : OpenNormalSubgroup G, ∀ x y, ∀ n ∈ N, ∀ m ∈ N, ε (x * n) (y * m) = ε x y := by
  obtain ⟨V, hV, hinv⟩ := exists_nhds_one_invariant _ hε
  rw [show (1 : G × G) = ((1 : G), (1 : G)) from rfl, mem_nhds_prod_iff] at hV
  obtain ⟨A, hA, B, hB, hAB⟩ := hV
  obtain ⟨U, hUsub, hUo, hU1⟩ := mem_nhds_iff.mp (Filter.inter_mem hA hB)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  refine ⟨N, fun x y n hn m hm => ?_⟩
  have h1 : n ∈ A := (hUsub (hN hn)).1
  have h2 : m ∈ B := (hUsub (hN hm)).2
  exact hinv (x, y) (n, m) (hAB ⟨h1, h2⟩)

/-- One-variable version. -/
theorem exists_openNormalSubgroup_invariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] (f : G → ZMod 2)
    (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup G, ∀ x, ∀ n ∈ N, f (x * n) = f x := by
  obtain ⟨N, hN⟩ := exists_openNormalSubgroup_invariant₂ (fun x _ => f x)
    (hf.comp continuous_fst)
  exact ⟨N, fun x n hn => hN x 1 n hn 1 (one_mem _)⟩

/-- Invariance under an open subgroup implies continuity (one variable). -/
theorem continuous_of_invariant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : G → ZMod 2) (N : OpenSubgroup G)
    (hN : ∀ x, ∀ n ∈ N, f (x * n) = f x) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hnhds : x • (N : Set G) ∈ nhds x := by
    have := (N.isOpen.smul x).mem_nhds (Set.smul_mem_smul_set (N.one_mem))
    simpa using this
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hnhds] with y hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact hN x n hn

/-- Invariance under an open subgroup implies continuity (two variables). -/
theorem continuous_of_invariant₂ {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (ε : G → G → ZMod 2) (N : OpenSubgroup G)
    (hN : ∀ x y, ∀ n ∈ N, ∀ m ∈ N, ε (x * n) (y * m) = ε x y) :
    Continuous (fun x : G × G => ε x.1 x.2) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : ∀ z : G, z • (N : Set G) ∈ nhds z := fun z => by
    have := (N.isOpen.smul z).mem_nhds (Set.smul_mem_smul_set (N.one_mem))
    simpa using this
  have hnhds : (x.1 • (N : Set G)) ×ˢ (x.2 • (N : Set G)) ∈ nhds x :=
    prod_mem_nhds (hmem x.1) (hmem x.2)
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hnhds] with y hy
  obtain ⟨⟨n, hn, h1⟩, ⟨m, hm, h2⟩⟩ := hy
  simp only [smul_eq_mul] at h1 h2
  rw [← h1, ← h2]
  exact hN x.1 x.2 n hn m hm

/-- **Cocycles are inflated from finite quotients.** -/
theorem isCocycle2_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] (ε : G → G → ZMod 2) :
    IsCocycle2 ε ↔ (∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0) ∧
      ∃ N : OpenNormalSubgroup G, ∀ x y, ∀ n ∈ N, ∀ m ∈ N, ε (x * n) (y * m) = ε x y := by
  constructor
  · rintro ⟨hc, hid⟩
    exact ⟨hid, exists_openNormalSubgroup_invariant₂ ε hc⟩
  · rintro ⟨hid, N, hN⟩
    exact ⟨continuous_of_invariant₂ ε N.toOpenSubgroup hN, hid⟩

/-- **Coboundaries come from finite quotients.** -/
theorem isCoboundary2_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] (ε : G → G → ZMod 2) :
    IsCoboundary2 ε ↔ ∃ N : OpenNormalSubgroup G, ∃ f : G → ZMod 2,
      (∀ x, ∀ n ∈ N, f (x * n) = f x) ∧ ∀ a b, ε a b = f b - f (a * b) + f a := by
  constructor
  · rintro ⟨f, hf, he⟩
    obtain ⟨N, hN⟩ := exists_openNormalSubgroup_invariant f hf
    exact ⟨N, f, hN, he⟩
  · rintro ⟨N, f, hN, he⟩
    exact ⟨f, continuous_of_invariant f N.toOpenSubgroup hN, he⟩

/-- `ε` is a 2-cocycle inflated from a finite quotient `G/N` (no topology). -/
def IsCocycle2Fin {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  (∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0) ∧
    ∃ N : OpenNormalSubgroup G, ∀ x y, ∀ n ∈ N, ∀ m ∈ N, ε (x * n) (y * m) = ε x y

/-- `ε` is the coboundary of a 1-cochain inflated from a finite quotient (no topology). -/
def IsCoboundary2Fin {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  ∃ N : OpenNormalSubgroup G, ∃ f : G → ZMod 2,
    (∀ x, ∀ n ∈ N, f (x * n) = f x) ∧ ∀ a b, ε a b = f b - f (a * b) + f a

/-- `H2TwoClasses` with continuity replaced by inflation from finite quotients. -/
def H2TwoClassesFin (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  (∃ ε, IsCocycle2Fin (G := G) ε ∧ ¬ IsCoboundary2Fin ε) ∧
  ∀ ε₁ ε₂, IsCocycle2Fin (G := G) ε₁ → IsCocycle2Fin ε₂ → ¬ IsCoboundary2Fin ε₁ →
    ¬ IsCoboundary2Fin ε₂ → IsCoboundary2Fin (ε₁ - ε₂)

theorem h2TwoClasses_iff_fin (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] :
    H2TwoClasses G ↔ H2TwoClassesFin G := by
  have e1 : ∀ ε : G → G → ZMod 2, IsCocycle2 ε ↔ IsCocycle2Fin ε := isCocycle2_iff
  have e2 : ∀ ε : G → G → ZMod 2, IsCoboundary2 ε ↔ IsCoboundary2Fin ε := isCoboundary2_iff
  simp only [H2TwoClasses, H2TwoClassesFin, e1, e2]

/-- The absolute Galois group of a field of characteristic zero is compact and zero-dimensional
(it is `Gal(K^al/K)` with the Krull topology). -/
instance compactSpace_absoluteGaloisGroup (K : Type*) [Field K] [CharZero K] :
    CompactSpace (Field.absoluteGaloisGroup K) := by
  have : IsGalois K (AlgebraicClosure K) := {}
  exact (inferInstance : CompactSpace Gal(AlgebraicClosure K/K))

instance zeroDimensionalSpace_absoluteGaloisGroup (K : Type*) [Field K] [CharZero K] :
    ZeroDimensionalSpace (Field.absoluteGaloisGroup K) := by
  have : IsGalois K (AlgebraicClosure K) := {}
  exact (inferInstance : ZeroDimensionalSpace Gal(AlgebraicClosure K/K))

/-- Hence for `G_{ℚ_p}`: -/
theorem isCocycle2_iff_Qp (p : ℕ) [Fact p.Prime]
    (ε : Field.absoluteGaloisGroup ℚ_[p] → Field.absoluteGaloisGroup ℚ_[p] → ZMod 2) :
    IsCocycle2 ε ↔ (∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0) ∧
      ∃ N : OpenNormalSubgroup (Field.absoluteGaloisGroup ℚ_[p]),
        ∀ x y, ∀ n ∈ N, ∀ m ∈ N, ε (x * n) (y * m) = ε x y :=
  isCocycle2_iff ε

/-- **T15's finite-place half, without topology**: `∀ p, H2TwoClasses G_{ℚ_p}` is equivalent to
the same statement for cochains inflated from finite quotients `G_{ℚ_p}/N` (`N` open normal, i.e.
`Gal(L/ℚ_p)` for finite Galois `L`). -/
theorem localH2CardC_finite_iff_fin :
    (∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])) ↔
      ∀ (p : ℕ) [Fact p.Prime], H2TwoClassesFin (Field.absoluteGaloisGroup ℚ_[p]) := by
  refine forall_congr' fun p => ?_
  exact forall_congr' fun _ => h2TwoClasses_iff_fin _

/-- **T15 without topology at the finite places** (kernel's `LocalH2CardC`). -/
theorem localH2CardC_iff_fin : PkgI6.LocalH2CardC ↔
    (∀ (p : ℕ) [Fact p.Prime], H2TwoClassesFin (Field.absoluteGaloisGroup ℚ_[p])) ∧
      H2TwoClasses (Field.absoluteGaloisGroup ℝ) := by
  unfold PkgI6.LocalH2CardC
  rw [localH2CardC_finite_iff_fin]

theorem isCocycle2_iff_fin {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] (ε : G → G → ZMod 2) :
    IsCocycle2 ε ↔ IsCocycle2Fin ε := isCocycle2_iff ε

theorem isCoboundary2_iff_fin {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [ZeroDimensionalSpace G] (ε : G → G → ZMod 2) :
    IsCoboundary2 ε ↔ IsCoboundary2Fin ε := isCoboundary2_iff ε

/-- T14 (Hasse half) without topology. -/
def BrauerHasse2Fin : Prop :=
  ∀ ε, IsCocycle2Fin ε → IsCoboundary2Fin (PkgI6.resC ℝ ε) →
    (∀ (p : ℕ) [Fact p.Prime], IsCoboundary2Fin (PkgI6.resC ℚ_[p] ε)) → IsCoboundary2Fin ε

open Classical in
/-- T14 (reciprocity half) without topology. -/
def BrauerReciprocity2Fin : Prop :=
  ∀ ε, IsCocycle2Fin ε →
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2Fin (PkgI6.resC ℚ_[(p : ℕ)] ε)}.Finite ∧
    Even ({p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2Fin (PkgI6.resC ℚ_[(p : ℕ)] ε)}.ncard
      + if IsCoboundary2Fin (PkgI6.resC ℝ ε) then 0 else 1)

theorem brauerHasse2C_iff_fin : PkgI6.BrauerHasse2C ↔ BrauerHasse2Fin := by
  simp only [PkgI6.BrauerHasse2C, BrauerHasse2Fin, isCocycle2_iff_fin, isCoboundary2_iff_fin]

theorem brauerReciprocity2C_iff_fin : PkgI6.BrauerReciprocity2C ↔ BrauerReciprocity2Fin := by
  unfold PkgI6.BrauerReciprocity2C BrauerReciprocity2Fin
  refine forall_congr' fun ε => ?_
  rw [isCocycle2_iff_fin]
  refine imp_congr_right fun _ => ?_
  simp only [isCoboundary2_iff_fin]
  have h := isCoboundary2_iff_fin (PkgI6.resC ℝ ε)
  by_cases hc : IsCoboundary2Fin (PkgI6.resC ℝ ε)
  · rw [if_pos (h.mpr hc), if_pos hc]
  · rw [if_neg (fun h' => hc (h.mp h')), if_neg hc]

end TPurity2K

#print axioms TPurity2K.isCocycle2_iff
#print axioms TPurity2K.isCoboundary2_iff
#print axioms TPurity2K.isCocycle2_iff_Qp
#print axioms TPurity2K.localH2CardC_finite_iff_fin
#print axioms TPurity2K.localH2CardC_iff_fin
#print axioms TPurity2K.brauerHasse2C_iff_fin
#print axioms TPurity2K.brauerReciprocity2C_iff_fin
