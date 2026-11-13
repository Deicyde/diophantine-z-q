import Mathlib
import ZInQKernel.HDecomp.Descent.WP3

/-!
# T14, T15 for the announcement: narrowed and topology-free (kernel form)

Concatenation of `ProfiniteKernel.lean` and `T14Narrow.lean` (scratch files cannot import each
other), plus the topology-free versions of the narrowed Props:
* `BrauerHasseFin2Fin` (T14 narrowed: no real place, no reciprocity; cochains inflated from
  finite quotients `G_ℚ/N`), `LocalTwo2Fin` (T15 narrowed: finite-place uniqueness half, cochains
  inflated from `G_{ℚ_p}/N`);
* `leaves_of_narrow_fin : BrauerHasseFin2Fin → LocalTwo2Fin → LeafHasse ∧ LeafLocalTwo` (what
  the consumer `GlueDescent.B3Q.b3_degree_le_QM` needs);
* `narrow_fin_of_T14_T15`: both are consequences of the announced T14, T15.
-/

open scoped Pointwise
open PkgI6 GlueDescent.B2 GlueDescent.B2Q

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


/-- **T14, narrowed** (cochain form of glue-descent's `LeafHasse`). -/
def BrauerHasseFin2C : Prop :=
  ∀ ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2, IsCocycle2 ε →
    (∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) → IsCoboundary2 ε

/-- **T15, narrowed** (finite-place uniqueness half of `LocalH2CardC`). -/
def LocalTwo2C : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ ε₁ ε₂, IsCocycle2 (G := Field.absoluteGaloisGroup ℚ_[p]) ε₁ → IsCocycle2 ε₂ →
      ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ → IsCoboundary2 (ε₁ - ε₂)

/-- The narrowed T14 is a consequence of T14. -/
theorem brauerHasseFin2C_of_T14 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) :
    BrauerHasseFin2C :=
  fun ε hε hp => hH ε hε (GlueWP3.real_of_finite hR ε hε hp) hp

/-- The narrowed T14 implies the Hasse half of T14 outright. -/
theorem brauerHasse2C_of_fin (h : BrauerHasseFin2C) : BrauerHasse2C :=
  fun ε hε _ hp => h ε hε hp

theorem leafHasse_of_brauerHasseFin2C (h : BrauerHasseFin2C) : LeafHasse := by
  intro η hη hloc
  obtain ⟨ε, hε, rfl⟩ := GlueWP3.exists_of_isSignCocycle hη
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε) := by
    intro p hpp
    rw [GlueWP3.isCoboundary2_iff]
    exact hloc ⟨p, hpp.out⟩
  rw [← GlueWP3.isCoboundary2_iff]
  exact h ε hε hp

theorem brauerHasseFin2C_of_leafHasse (h : LeafHasse) : BrauerHasseFin2C := by
  intro ε hε hp
  rw [GlueWP3.isCoboundary2_iff]
  rw [GlueWP3.isCocycle2_iff] at hε
  refine h _ hε fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [GlueWP3.pull_resp_sgnC, ← GlueWP3.isCoboundary2_iff]
  exact hp p

theorem leafHasse_iff_brauerHasseFin2C : LeafHasse ↔ BrauerHasseFin2C :=
  ⟨brauerHasseFin2C_of_leafHasse, leafHasse_of_brauerHasseFin2C⟩

theorem localTwo2C_of_T15 (hC : LocalH2CardC) : LocalTwo2C :=
  fun p _ => (hC.1 p).2

theorem leafLocalTwo_iff_localTwo2C : LeafLocalTwo ↔ LocalTwo2C :=
  GlueWP3.leafLocalTwo_iff

/-- **The consumer's two leaves from the narrowed Props.** -/
theorem leaves_of_narrow (hH : BrauerHasseFin2C) (hC : LocalTwo2C) :
    LeafHasse ∧ LeafLocalTwo :=
  ⟨leafHasse_of_brauerHasseFin2C hH, leafLocalTwo_iff_localTwo2C.mpr hC⟩


/-! ## The narrowed Props without topology -/

/-- `BrauerHasseFin2C` with continuity replaced by inflation from finite quotients. -/
def BrauerHasseFin2Fin : Prop :=
  ∀ ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2, IsCocycle2Fin ε →
    (∀ (p : ℕ) [Fact p.Prime], IsCoboundary2Fin (resC ℚ_[p] ε)) → IsCoboundary2Fin ε

/-- `LocalTwo2C` with continuity replaced by inflation from finite quotients. -/
def LocalTwo2Fin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ ε₁ ε₂, IsCocycle2Fin (G := Field.absoluteGaloisGroup ℚ_[p]) ε₁ → IsCocycle2Fin ε₂ →
      ¬ IsCoboundary2Fin ε₁ → ¬ IsCoboundary2Fin ε₂ → IsCoboundary2Fin (ε₁ - ε₂)

theorem brauerHasseFin2C_iff_fin : BrauerHasseFin2C ↔ BrauerHasseFin2Fin := by
  simp only [BrauerHasseFin2C, BrauerHasseFin2Fin, isCocycle2_iff_fin, isCoboundary2_iff_fin]

theorem localTwo2C_iff_fin : LocalTwo2C ↔ LocalTwo2Fin := by
  simp only [LocalTwo2C, LocalTwo2Fin, isCocycle2_iff_fin, isCoboundary2_iff_fin]

/-- **The consumer's leaves from the topology-free narrowed Props.** -/
theorem leaves_of_narrow_fin (hH : BrauerHasseFin2Fin) (hC : LocalTwo2Fin) :
    LeafHasse ∧ LeafLocalTwo :=
  leaves_of_narrow (brauerHasseFin2C_iff_fin.mpr hH) (localTwo2C_iff_fin.mpr hC)

/-- And they are consequences of T14, T15. -/
theorem narrow_fin_of_T14_T15 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C)
    (hC : LocalH2CardC) : BrauerHasseFin2Fin ∧ LocalTwo2Fin :=
  ⟨brauerHasseFin2C_iff_fin.mp (brauerHasseFin2C_of_T14 hH hR),
    localTwo2C_iff_fin.mp (localTwo2C_of_T15 hC)⟩

end TPurity2K

#print axioms TPurity2K.leaves_of_narrow_fin
#print axioms TPurity2K.narrow_fin_of_T14_T15
#print axioms TPurity2K.localH2CardC_iff_fin
