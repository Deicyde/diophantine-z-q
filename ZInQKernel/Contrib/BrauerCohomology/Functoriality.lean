import ZInQKernel.Contrib.BrauerCohomology.Comparison

set_option autoImplicit false

/-!
# Naturality of the inhomogeneous description, and `H²` as `Z² / B²`

For continuous homomorphisms `φ : H →ₜ* G` and morphisms `f : res φ X ⟶ Y` of topological
representations with trivial actions, Mathlib's `ContinuousCohomology.map φ f 2` sends the class of
an inhomogeneous cocycle `ε` to the class of `pull2 φ f ε = (a, b) ↦ f (ε (φ a) (φ b))`
(`map_cls`). With `f = 𝟙` and `φ = Field.absoluteGaloisGroup.map (algebraMap ℚ F)` this is the
localization `PkgI6.loc F 2` against `PkgI6.resC F`; with `φ` a quotient map it is inflation.

`h2AddEquiv` packages the comparison as an additive equivalence between Mathlib's
`continuousCohomology 2 X` and the explicit quotient of continuous inhomogeneous 2-cocycles by
coboundaries of continuous 1-cochains (`G` locally compact).
-/

open CategoryTheory ContRepresentation

namespace ZInQ.Contrib.BrauerCohomology

universe u v

section Naturality

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {X : TopRep k G} {Y : TopRep k H}

/-- Pullback of an inhomogeneous 2-cochain along `φ`, followed by the coefficient map `f`. -/
def pull2 (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y) (ε : G → G → X) : H → H → Y :=
  fun a b => f.hom (ε (φ a) (φ b))

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem IsInhCocycle2.pull2 (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y)
    {ε : G → G → X} (hε : IsInhCocycle2 ε) : IsInhCocycle2 (pull2 φ f ε) := by
  refine ⟨?_, fun a b c => ?_⟩
  · exact (map_continuous f.hom).comp (hε.1.comp
      ((φ.continuous.comp continuous_fst).prodMk (φ.continuous.comp continuous_snd)))
  · have e := hε.2 (φ a) (φ b) (φ c)
    simp only [BrauerCohomology.pull2, map_mul]
    rw [← map_sub, ← map_add, ← map_sub, e, map_zero]

/-- The homogeneous cochain map of `ContinuousCohomology.cochainsMap φ f` in degree 2, on the
homogeneous form of an inhomogeneous cochain, is the homogeneous form of the pullback. -/
theorem cochainsMap_toHC2 (hX : IsTrivialAction X) (hY : IsTrivialAction Y) (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (ε : G → G → X)
    (hε : Continuous (fun p : G × G => ε p.1 p.2))
    (hε' : Continuous (fun p : H × H => pull2 φ f ε p.1 p.2)) :
    (((ContinuousCohomology.cochainsMap φ f).f 2).hom (toHC2 hX ε hε : HC2 X) : HC2 Y) =
      toHC2 hY (pull2 φ f ε) hε' := by
  apply Subtype.ext
  ext h₀ h₁ h₂
  simp only [ContinuousCohomology.cochainsMap_f, TopRep.invariantsResMap, TopModuleCat.hom_ofHom]
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply]
  simp only [ContinuousCohomology.resolutionMap_succ, TopRep.hom_ofHom,
    ContRepresentation.coind₁ResMap_apply, ContinuousCohomology.resolutionMap_zero,
    toHC2_apply, BrauerCohomology.pull2, map_mul, map_inv]

/-- **Naturality.** `ContinuousCohomology.map φ f 2` sends the class of `ε` to the class of the
pullback `(a, b) ↦ f (ε (φ a) (φ b))`. -/
theorem map_cls (hX : IsTrivialAction X) (hY : IsTrivialAction Y) (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (ε : G → G → X) (hε : IsInhCocycle2 ε) :
    (ContinuousCohomology.map φ f 2).hom (cls hX ε hε) =
      cls hY (pull2 φ f ε) (hε.pull2 φ f) := by
  unfold cls cyc2
  erw [TopHom.homologyMap_homologyπ_cyclesMkOfEq]
  congr 1
  apply TopHom.iCycles_injective'
  rw [TopHom.iCycles_cyclesMkOfEq', TopHom.iCycles_cyclesMkOfEq']
  exact cochainsMap_toHC2 hX hY φ f ε hε.1 (hε.pull2 φ f).1

/-- **Naturality, restriction or inflation along `φ` with the identity on coefficients.** For
`φ` the decomposition-group map `G_F → G_ℚ` this is localization; for `φ` a quotient map
`G → G/N` it is inflation. -/
theorem map_id_cls (hX : IsTrivialAction X) (φ : H →ₜ* G) (ε : G → G → X)
    (hε : IsInhCocycle2 ε) :
    (ContinuousCohomology.map φ (𝟙 (TopRep.res (φ : H →* G) X)) 2).hom (cls hX ε hε) =
      cls (X := TopRep.res (φ : H →* G) X) (fun h v => hX (φ h) v)
        (pull2 φ (𝟙 (TopRep.res (φ : H →* G) X)) ε) (hε.pull2 φ (𝟙 _)) :=
  map_cls hX (fun h v => hX (φ h) v) φ (𝟙 _) ε hε

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- With the identity on coefficients, the pullback is `(a, b) ↦ ε (φ a) (φ b)`. -/
@[simp]
theorem pull2_id_apply (φ : H →ₜ* G) (ε : G → G → X) (a b : H) :
    pull2 φ (𝟙 (TopRep.res (φ : H →* G) X)) ε a b = ε (φ a) (φ b) := rfl

end Naturality

section Explicit

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep k G)

/-- Continuous inhomogeneous 2-cocycles `Z²(G, X)` (trivial action). -/
def Z2inh : AddSubgroup (G → G → X) :=
  AddSubgroup.ofSub {ε | IsInhCocycle2 ε} ⟨0, IsInhCocycle2.zero⟩
    fun _ h₁ _ h₂ => by
      rw [← sub_eq_add_neg]
      exact IsInhCocycle2.sub h₁ h₂

/-- Coboundaries `B²(G, X)` of continuous inhomogeneous 1-cochains. -/
def B2inh : AddSubgroup (G → G → X) :=
  AddSubgroup.ofSub {ε | IsInhCoboundary2 ε} ⟨0, 0, continuous_const, fun _ _ => by simp⟩
    fun _ h₁ _ h₂ => by
      rw [← sub_eq_add_neg]
      obtain ⟨f₁, hf₁, e₁⟩ := h₁
      obtain ⟨f₂, hf₂, e₂⟩ := h₂
      refine ⟨f₁ - f₂, hf₁.sub hf₂, fun a b => ?_⟩
      simp only [Pi.sub_apply, e₁, e₂]
      abel

variable {X}

omit [IsTopologicalGroup G] in
theorem mem_Z2inh {ε : G → G → X} : ε ∈ Z2inh X ↔ IsInhCocycle2 ε := Iff.rfl

omit [IsTopologicalGroup G] in
theorem mem_B2inh {ε : G → G → X} : ε ∈ B2inh X ↔ IsInhCoboundary2 ε := Iff.rfl

/-- The class map `Z² → H²` as an additive homomorphism. -/
noncomputable def clsHom (hX : IsTrivialAction X) : Z2inh X →+ continuousCohomology 2 X :=
  AddMonoidHom.ofMapSub (fun ε => cls hX ε.1 ε.2) fun ε₁ ε₂ => cls_sub hX ε₁.2 ε₂.2

theorem clsHom_apply (hX : IsTrivialAction X) (ε : Z2inh X) : clsHom hX ε = cls hX ε.1 ε.2 := rfl

theorem ker_clsHom (hX : IsTrivialAction X) :
    (clsHom hX).ker = (B2inh X).addSubgroupOf (Z2inh X) := by
  ext ε
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, clsHom_apply]
  exact cls_eq_zero_iff hX ε.1 ε.2

theorem clsHom_surjective [LocallyCompactSpace G] (hX : IsTrivialAction X) :
    Function.Surjective (clsHom hX) := by
  intro x
  obtain ⟨ε, hε, rfl⟩ := cls_surjective hX x
  exact ⟨⟨ε, hε⟩, rfl⟩

/-- **Comparison.** For a locally compact group `G` and a topological representation `X` with
trivial action, Mathlib's `continuousCohomology 2 X` is the quotient of continuous inhomogeneous
2-cocycles by coboundaries of continuous 1-cochains. -/
noncomputable def h2AddEquiv [LocallyCompactSpace G] (hX : IsTrivialAction X) :
    (Z2inh X ⧸ (B2inh X).addSubgroupOf (Z2inh X)) ≃+ continuousCohomology 2 X :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_clsHom hX).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (clsHom_surjective hX))

theorem h2AddEquiv_mk [LocallyCompactSpace G] (hX : IsTrivialAction X) (ε : Z2inh X) :
    h2AddEquiv hX (QuotientAddGroup.mk ε) = cls hX ε.1 ε.2 := rfl

end Explicit

section TwoClasses

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : TopRep k G}

/-- An additive group has exactly two elements iff it has a nonzero element and any two nonzero
elements are equal. -/
theorem natCard_eq_two_iff_of_addGroup {A : Type*} [AddGroup A] :
    Nat.card A = 2 ↔ (∃ a : A, a ≠ 0) ∧ ∀ a b : A, a ≠ 0 → b ≠ 0 → a = b := by
  constructor
  · intro h
    obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp h
    refine ⟨?_, fun a b ha hb => ?_⟩
    · by_cases hx : x = 0
      · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
      · exact ⟨x, hx⟩
    · obtain ⟨u, v, -, huv⟩ := Nat.card_eq_two_iff.mp h
      have mem : ∀ z : A, z = u ∨ z = v := fun z => by
        have : z ∈ ({u, v} : Set A) := huv ▸ Set.mem_univ z
        simpa using this
      rcases mem 0 with h0 | h0 <;> rcases mem a with h1 | h1 <;> rcases mem b with h2 | h2 <;>
        first
        | exact h1.trans h2.symm
        | exact absurd (h1.trans h0.symm) ha
        | exact absurd (h2.trans h0.symm) hb
  · rintro ⟨⟨a, ha⟩, h⟩
    refine Nat.card_eq_two_iff.mpr ⟨0, a, Ne.symm ha, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hz : z = 0
    · exact Or.inl hz
    · exact Or.inr (h z a hz ha)

/-- "`H²(G, X)` has exactly two classes", on inhomogeneous cochains (the shape of
`PkgI6.H2TwoClasses`, for an arbitrary trivial-action coefficient module). -/
def H2TwoClassesOf (X : TopRep k G) : Prop :=
  (∃ ε : G → G → X, IsInhCocycle2 ε ∧ ¬ IsInhCoboundary2 ε) ∧
  ∀ ε₁ ε₂ : G → G → X, IsInhCocycle2 ε₁ → IsInhCocycle2 ε₂ → ¬ IsInhCoboundary2 ε₁ →
    ¬ IsInhCoboundary2 ε₂ → IsInhCoboundary2 (ε₁ - ε₂)

/-- **`Nat.card` of Mathlib's `H²` is `2` iff the inhomogeneous cochain statement holds.** -/
theorem natCard_eq_two_iff [LocallyCompactSpace G] (hX : IsTrivialAction X) :
    Nat.card (continuousCohomology 2 X) = 2 ↔ H2TwoClassesOf X := by
  rw [natCard_eq_two_iff_of_addGroup]
  constructor
  · rintro ⟨⟨a, ha⟩, huniq⟩
    refine ⟨?_, fun ε₁ ε₂ h₁ h₂ n₁ n₂ => ?_⟩
    · obtain ⟨ε, hε, rfl⟩ := cls_surjective hX a
      exact ⟨ε, hε, fun hc => ha ((cls_eq_zero_iff hX ε hε).2 hc)⟩
    · rw [← cls_eq_zero_iff hX _ (h₁.sub h₂), cls_sub hX h₁ h₂, sub_eq_zero]
      exact huniq _ _ (fun h => n₁ ((cls_eq_zero_iff hX _ h₁).1 h))
        (fun h => n₂ ((cls_eq_zero_iff hX _ h₂).1 h))
  · rintro ⟨⟨ε, hε, hn⟩, huniq⟩
    refine ⟨⟨cls hX ε hε, fun h => hn ((cls_eq_zero_iff hX ε hε).1 h)⟩, fun a b ha hb => ?_⟩
    obtain ⟨ε₁, h₁, rfl⟩ := cls_surjective hX a
    obtain ⟨ε₂, h₂, rfl⟩ := cls_surjective hX b
    rw [← sub_eq_zero, ← cls_sub hX h₁ h₂, cls_eq_zero_iff]
    exact huniq ε₁ ε₂ h₁ h₂ (fun h => ha ((cls_eq_zero_iff hX _ h₁).2 h))
      (fun h => hb ((cls_eq_zero_iff hX _ h₂).2 h))

end TwoClasses

end ZInQ.Contrib.BrauerCohomology
