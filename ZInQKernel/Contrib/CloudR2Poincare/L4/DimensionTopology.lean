import Mathlib

/-!
# Quasi-finite image dimension and the full-dimension surjectivity criterion

H-72 round 2, lane L4. These are Mathlib-only lemmas about the actual topological
Krull dimension. No dimension, equidimensionality, or surjectivity statement is
assumed as a Fact. The proof maps chains of irreducible closed sets to their
image closures. A strict inclusion cannot collapse: their generic points would
then have the same image and specialize inside a discrete fibre.

For a proper closed subset of an irreducible finite-dimensional space, append
the whole space to a longest chain in the subset. This gives the strict
full-dimension criterion without importing a Stacks topology port.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Set Order

noncomputable section

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.style.haveILetI false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Discrete fibres prevent a continuous map from collapsing a strict chain of irreducible closed sets. -/
theorem strictMono_irreducibleCloseds_map_of_discrete_fibres [QuasiSober X] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hd : ∀ y, _root_.IsDiscrete (f ⁻¹' {y})) :
    StrictMono (IrreducibleCloseds.map f hf) := by
  intro A B hAB
  refine lt_of_le_of_ne (IrreducibleCloseds.map_mono hf hAB.le) ?_
  intro he
  obtain ⟨a, ha⟩ := QuasiSober.sober A.isIrreducible A.isClosed
  obtain ⟨b, hb⟩ := QuasiSober.sober B.isIrreducible B.isClosed
  have hec : closure (f '' (A : Set X)) = closure (f '' (B : Set X)) :=
    congrArg (fun C : IrreducibleCloseds Y => (C : Set Y)) he
  have hgb : IsGenericPoint (f b) (closure (f '' (A : Set X))) := by
    rw [hec]
    exact hb.image hf
  have hfb : f b = f a := hgb.eq (ha.image hf)
  have hba : b ⤳ a := hb.specializes (hAB.le ha.mem)
  haveI : DiscreteTopology (f ⁻¹' {f a}) := (hd (f a)).to_subtype
  have hsub : (⟨b, hfb⟩ : f ⁻¹' {f a}) ⤳ ⟨a, rfl⟩ :=
    (subtype_specializes_iff _ _).mpr hba
  have hsame : (⟨a, rfl⟩ : f ⁻¹' {f a}) = ⟨b, hfb⟩ := by
    exact hsub.mem_closed (s := {⟨b, hfb⟩}) isClosed_singleton rfl
  have hab : a = b := congrArg Subtype.val hsame
  exact hAB.ne (IrreducibleCloseds.ext (by rw [← ha.def, ← hb.def, hab]))

/-- A continuous map with discrete fibres cannot lower topological Krull dimension. -/
theorem topologicalKrullDim_le_of_discrete_fibres [QuasiSober X] [T0Space Y]
    (f : X → Y) (hf : Continuous f) (hd : ∀ y, _root_.IsDiscrete (f ⁻¹' {y})) :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  krullDim_le_of_strictMono _ (strictMono_irreducibleCloseds_map_of_discrete_fibres f hf hd)

/-- A locally quasi-finite morphism preserves the dimension of its source inside its image. -/
theorem topologicalKrullDim_le_range_of_locallyQuasiFinite {X Y : Scheme}
    (f : X ⟶ Y) [LocallyQuasiFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim (Set.range f) := by
  refine topologicalKrullDim_le_of_discrete_fibres (Set.rangeFactorization f)
    (f.continuous.subtype_mk _) fun y => ?_
  convert f.isDiscrete_preimage_singleton y.1 using 1
  ext x
  simp only [mem_preimage, mem_singleton_iff, rangeFactorization, Subtype.ext_iff]

/-- An irreducible nonempty space has non-bottom dimension. -/
theorem topologicalKrullDim_ne_bot_of_irreducible [IrreducibleSpace X] :
    topologicalKrullDim X ≠ ⊥ := by
  haveI : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  exact krullDim_ne_bot_iff.mpr inferInstance

/-- A closed subset of an irreducible finite-dimensional space with full dimension is the whole space. -/
theorem closed_eq_univ_of_topologicalKrullDim_le [IrreducibleSpace X]
    (hfin : topologicalKrullDim X ≠ ⊤) {S : Set X} (hS : IsClosed S)
    (hdim : topologicalKrullDim X ≤ topologicalKrullDim S) : S = univ := by
  classical
  by_contra hproper
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim X = (n : WithBot ℕ∞) := by
    cases he : topologicalKrullDim X with
    | bot => exact (topologicalKrullDim_ne_bot_of_irreducible he).elim
    | coe e =>
      cases e with
      | top => exact (hfin he).elim
      | coe n => exact ⟨n, rfl⟩
  obtain ⟨p, hp⟩ := le_krullDim_iff.mp (hn ▸ hdim)
  let F : IrreducibleCloseds S → IrreducibleCloseds X :=
    IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val
  have hF : StrictMono F := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let topX : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlastS : (F p.last : Set X) ⊆ S := by
    exact hS.closure_subset_iff.mpr (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  have hlast : (p.map F hF).last < topX := by
    rw [LTSeries.last_map]
    refine lt_of_le_of_ne (Set.subset_univ _) ?_
    intro he
    have hec : (F p.last : Set X) = univ := congrArg (fun C : IrreducibleCloseds X => (C : Set X)) he
    rw [hec] at hlastS
    exact hproper (Set.eq_univ_of_forall fun x => hlastS (Set.mem_univ x))
  let q : LTSeries (IrreducibleCloseds X) := (p.map F hF).snoc topX hlast
  have hq := LTSeries.length_le_krullDim q
  change (q.length : WithBot ℕ∞) ≤ topologicalKrullDim X at hq
  rw [hn] at hq
  have hbad : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    simpa only [q, RelSeries.snoc_length, LTSeries.map_length, hp] using hq
  exact (Nat.not_succ_le_self n) (by exact_mod_cast hbad)

/-- A finite morphism to an irreducible finite-dimensional scheme is surjective if its source has at least the target dimension. -/
theorem surjective_of_isFinite_of_topologicalKrullDim_le {X Y : Scheme}
    (f : X ⟶ Y) [IsFinite f] [IrreducibleSpace Y]
    (hfin : topologicalKrullDim Y ≠ ⊤) (hdim : topologicalKrullDim Y ≤ topologicalKrullDim X) :
    Surjective f := by
  have hrange : Set.range f = Set.univ :=
    closed_eq_univ_of_topologicalKrullDim_le hfin f.isClosedMap.isClosed_range
      (hdim.trans (topologicalKrullDim_le_range_of_locallyQuasiFinite f))
  constructor
  intro y
  have hy : y ∈ Set.range f := by rw [hrange]; trivial
  exact hy

end ZInQ.Contrib.CloudR2Poincare.L4
