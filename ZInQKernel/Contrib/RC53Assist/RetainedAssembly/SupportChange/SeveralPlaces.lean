import ZInQKernel.Contrib.RC53Assist.RetainedAssembly.SupportChange.Assembly

/-!
# Several-place residual support control

Residual comparisons are composed along finitely many actual stage complexes.
The supports, characters and old local conditions may vary with the coefficient
stage. Each added place contributes six support coordinates and an explicit
local-condition correction cost. The resulting width is
`6 * k + sum (range k) c`, and a base bound `B` gives the bound
`B + 6 * k + sum (range k) c`.

The cochain support and condition triangles are explicit inputs to the
arithmetic reduction. A collection of arbitrary residual embeddings alone is
not asserted to discharge a moving arithmetic family.

Sources: `diophantine_zq.tex`, lines 3483–3498, 4385–4451 and 4976–5135.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.SeveralPlaces

open CategoryTheory Matrix IsLocalRing Finset
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Contrib.RC53Assist.ResidualFiniteness
open ZInQ.Contrib.RC53Assist.ResidualBounds
open ZInQ.Contrib.RC53Assist.LocalDegreeTwo.SplitTrace
open ZInQ.Contrib.RC53Assist.OldOrthogonality.LocalTransport (ComplexIso)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Limits (residualCohomologyAt)
open ZInQ.Manuscript.RC.FibreDuality (finite_residualCohomologyAt_of)
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.KummerMaps (orthNeg)
open ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange

/-- Kind: definition. A family of actual cochain complexes at the coefficient
stages, with no fixed support or common character imposed; tex 2727–2741,
4255–4280, 4391–4406. -/
abbrev StageComplexFamily := ∀ i : ℕ, GCx (Acoef i)

/-- Kind: definition. The exact residual package of a stage-complex family.
On the global complexes of a moving family this is the moving residual
package: finiteness, range `[0,3]` and the displayed bound; tex 4401–4406. -/
def StageResidualPackage (G : StageComplexFamily) (B : ℕ) : Prop :=
  (∀ i [NeZero i], ResidualCohomologyFinite (G i)) ∧
    (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (G i) n) = 0) ∧
    (∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (G i) n) ≤ B)

/-- Kind: definition. Residual comparison between two arbitrary stage-complex
families. These are linear embeddings, not automatically arithmetic support
maps. The geometric constructors below provide them after cochain estimates;
tex 3483–3498, 4401–4406. -/
structure ResidualComparison (G H : StageComplexFamily) (width : ℕ) where
  /-- Kind: definition. The comparison with the specified residual-coordinate
  excess in the Selmer window; tex 4401–4406. -/
  map : ∀ i [NeZero i] (n : ℤ), residualCohomologyAt (G i) n →ₗ[ResidueField (Acoef i)]
    residualCohomologyAt (H i) n × (Fin (extraRank width n) → ResidueField (Acoef i))
  /-- Kind: PROVED. The comparison is injective in every degree and positive
  stage; tex 4401–4406. -/
  injective : ∀ i [NeZero i] (n : ℤ), Function.Injective (map i n)

/-- Kind: PROVED. Residual coordinate widths add in every degree, including
outside the Selmer window; tex 4401–4406. -/
theorem extraRank_add (a b : ℕ) (n : ℤ) :
    extraRank (a + b) n = extraRank a n + extraRank b n := by
  unfold extraRank
  split_ifs <;> simp

/-- Kind: definition. Join two blocks of finite residual coordinates without
changing their total dimension; tex 4401–4406. -/
def joinExtra {k : Type} [Field k] (a b : ℕ) (n : ℤ) :
    (Fin (extraRank a n) → k) × (Fin (extraRank b n) → k) →ₗ[k]
      (Fin (extraRank (a + b) n) → k) :=
  coordinateEmbedding ((Fin (extraRank a n) → k) × (Fin (extraRank b n) → k)) (by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
    exact le_of_eq (extraRank_add a b n).symm)

/-- Kind: PROVED. Joining residual coordinate blocks is injective;
tex 4401–4406. -/
theorem joinExtra_injective {k : Type} [Field k] (a b : ℕ) (n : ℤ) :
    Function.Injective (joinExtra (k := k) a b n) :=
  coordinateEmbedding_injective _ _

/-- Kind: PROVED. A family compares to itself with zero excess coordinates;
tex 4401–4406. -/
def ResidualComparison.refl (G : StageComplexFamily) : ResidualComparison G G 0 where
  map i _ n := (LinearMap.id).prod 0
  injective i _ n := by
    intro x y h
    exact congrArg Prod.fst h

/-- Kind: PROVED. Compose two residual comparisons, retaining the base
component and both extra-coordinate blocks. No finite-dimensionality of the
base residual groups is required for this composition; tex 4401–4406. -/
def ResidualComparison.comp {G H J : StageComplexFamily} {a b : ℕ}
    (S : ResidualComparison G H a) (T : ResidualComparison H J b) :
    ResidualComparison G J (b + a) where
  map i _ n :=
    let k := ResidueField (Acoef i)
    let V := residualCohomologyAt (H i) n
    let W := residualCohomologyAt (J i) n
    let EA := Fin (extraRank a n) → k
    let EB := Fin (extraRank b n) → k
    let f := S.map i n
    let g := (T.map i n).comp ((LinearMap.fst k V EA).comp f)
    let extras := ((LinearMap.snd k W EB).comp g).prod ((LinearMap.snd k V EA).comp f)
    ((LinearMap.fst k W EB).comp g).prod ((joinExtra b a n).comp extras)
  injective i _ n := by
    intro x y hxy
    change ((T.map i n ((S.map i n x).1)).1,
        joinExtra b a n ((T.map i n ((S.map i n x).1)).2, (S.map i n x).2)) =
      ((T.map i n ((S.map i n y).1)).1,
        joinExtra b a n ((T.map i n ((S.map i n y).1)).2, (S.map i n y).2)) at hxy
    have hb := congrArg Prod.fst hxy
    have he := joinExtra_injective b a n (congrArg Prod.snd hxy)
    have heA := congrArg Prod.snd he
    apply S.injective i n
    apply Prod.ext
    · apply T.injective i n
      exact Prod.ext hb (congrArg Prod.fst he)
    · exact heA

/-- Kind: PROVED. Transport a residual comparison along an equality of
coordinate widths; tex 4401–4406. -/
def ResidualComparison.castWidth {G H : StageComplexFamily} {a b : ℕ}
    (h : a = b) (S : ResidualComparison G H a) : ResidualComparison G H b := by
  subst h
  exact S

/-- Kind: definition. The cumulative cost of `k` support changes with their
own local-condition correction costs; tex 3483–3498, 4401–4406. -/
def totalWidth (c : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, (6 + c j)

/-- Kind: PROVED. The cumulative width is exactly six per added place plus
the sum of the condition costs; tex 3483–3498, 4401–4406. -/
theorem totalWidth_eq (c : ℕ → ℕ) (k : ℕ) :
    totalWidth c k = 6 * k + ∑ j ∈ Finset.range k, c j := by
  simp [totalWidth, Finset.sum_add_distrib, Nat.mul_comm]

/-- Kind: PROVED. Iterate `k` residual support comparisons with explicit
width `6k + sum c`. All stage supports and coefficient characters can vary;
this statement alone is conditional on the displayed comparisons and does
not claim their arithmetic production; tex 3483–3498, 4401–4406. -/
theorem iterate_residual_comparison (G : ℕ → StageComplexFamily) (c : ℕ → ℕ) (k : ℕ) :
    (∀ j, j < k → Nonempty (ResidualComparison (G (j + 1)) (G j) (6 + c j))) →
      Nonempty (ResidualComparison (G k) (G 0) (6 * k + ∑ j ∈ Finset.range k, c j)) := by
  have iterate : ∀ k : ℕ,
      (∀ j, j < k → Nonempty (ResidualComparison (G (j + 1)) (G j) (6 + c j))) →
        Nonempty (ResidualComparison (G k) (G 0) (totalWidth c k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa [totalWidth] using (⟨ResidualComparison.refl (G 0)⟩ :
        Nonempty (ResidualComparison (G 0) (G 0) 0))
    | succ k ih =>
      intro step
      obtain ⟨P⟩ := ih (fun j hj => step j (Nat.lt_succ_of_lt hj))
      obtain ⟨Q⟩ := step k (Nat.lt_succ_self k)
      simpa [totalWidth, Finset.sum_range_succ] using (⟨Q.comp P⟩ :
        Nonempty (ResidualComparison (G (k + 1)) (G 0) (totalWidth c k + (6 + c k))))
  simpa only [totalWidth_eq] using iterate k

/-- Kind: PROVED. A residual comparison and the base residual package give
finiteness, the same Selmer range and the bound increased by the exact width;
tex 4391–4406. -/
theorem ResidualComparison.residualPackage {G H : StageComplexFamily} {width B : ℕ}
    (T : ResidualComparison G H width) (hH : StageResidualPackage H B) :
    StageResidualPackage G (B + width) := by
  have hfin : ∀ i [NeZero i] (n : ℤ), Module.Finite (ResidueField (Acoef i))
      (residualCohomologyAt (G i) n) := by
    intro i _ n
    have : Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt (H i) n) :=
      finite_residualCohomologyAt_of (hH.1 i) n
    exact Module.Finite.of_injective (T.map i n) (T.injective i n)
  have hbound : ∀ i [NeZero i] (n : ℤ),
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (G i) n) ≤
        Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt (H i) n) +
          extraRank width n := by
    intro i _ n
    have := hfin i n
    have : Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt (H i) n) :=
      finite_residualCohomologyAt_of (hH.1 i) n
    have hr := LinearMap.finrank_le_finrank_of_injective (T.injective i n)
    rw [Module.finrank_prod, Module.finrank_fin_fun] at hr
    exact hr
  refine ⟨?_, ?_, ?_⟩
  · intro i _ n
    exact (Module.Finite.equiv_iff (residualHomologyEquiv (G i) n)).2 (hfin i n)
  · intro i _ n hn
    have hr := hbound i n
    rw [hH.2.1 i n hn, extraRank_outside width n hn, zero_add] at hr
    exact Nat.eq_zero_of_le_zero hr
  · intro i _ n
    exact (hbound i n).trans (Nat.add_le_add (hH.2.2 i n) (extraRank_le width n))

/-- Kind: PROVED. The uniform residual package after `k` comparisons has
bound `B + 6k + sum c`. Its three conclusions are exactly the moving residual
package applied to the terminal stage-global complex family;
tex 3483–3498, 4391–4406. -/
theorem residualPackage_of_comparison_steps (G : ℕ → StageComplexFamily)
    (c : ℕ → ℕ) (k B : ℕ) (hbase : StageResidualPackage (G 0) B)
    (step : ∀ j, j < k → Nonempty (ResidualComparison (G (j + 1)) (G j) (6 + c j))) :
    StageResidualPackage (G k) (B + 6 * k + ∑ j ∈ Finset.range k, c j) := by
  obtain ⟨T⟩ := iterate_residual_comparison G c k step
  simpa only [Nat.add_assoc] using T.residualPackage hbase

section ConditionTriangles

variable {k : Type} [Field k]

/-- Kind: definition. Explicit cohomology finiteness, range and rank bounds
for a local condition complex, not for the moving global target;
tex 3483–3498, 4391–4406, 4859–4873. -/
structure CohomologyBounds (Q : GCx k) (lo hi : ℤ) (B : ℕ) : Prop where
  /-- Kind: GLUE. Finite local cohomology in every degree; tex 4391–4406. -/
  finite : ∀ n : ℤ, Module.Finite k (Q.toCC.homology n)
  /-- Kind: GLUE. The uniform local rank allowance; tex 4391–4406. -/
  rank : ∀ n : ℤ, Module.finrank k (Q.toCC.homology n) ≤ B
  /-- Kind: GLUE. Vanishing outside the displayed local range;
  tex 3483–3498, 4391–4406. -/
  outside : ∀ n : ℤ, n < lo ∨ hi < n → Subsingleton (Q.toCC.homology n)

/-- Kind: definition. Exchange the global and condition summands, with
both maps negated, so the Selmer differential is unchanged after exchanging
the two coordinates; tex 3483–3498, 4391–4406. -/
def swapSelData (D : SelData k) : SelData k :=
  ⟨D.U, D.G, D.L, orthNeg D.ι, orthNeg D.res⟩

/-- Kind: PROVED. The coordinate exchange is an actual cochain map onto
the swapped datum's Selmer complex; tex 3483–3498, 4438–4442. -/
def swapSelCx (D : SelData k) : GHom (selCx D) (selCx (swapSelData D)) where
  f a b h := by
    subst h
    exact
      { toFun := fun x => (x.2.1, x.1, x.2.2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  comm a a₁ b b₁ hab ha hb hc x := by
    subst hab hc
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change D.res.f a (a₁ - 1) (by omega) x.1 -
        D.ι.f a (a₁ - 1) (by omega) x.2.1 -
          D.L.d (a - 1) (a₁ - 1) (by omega) x.2.2 =
      -(D.ι.f a (a₁ - 1) (by omega) x.2.1) -
        (-(D.res.f a (a₁ - 1) (by omega) x.1)) -
          D.L.d (a - 1) (a₁ - 1) (by omega) x.2.2
    abel

/-- Kind: PROVED. The cochain coordinate exchange is bijective in each
degree; tex 3483–3498, 4438–4442. -/
theorem swapSelCx_bijective (D : SelData k) (n : ℤ) :
    Function.Bijective ((swapSelCx D).f n n rfl) := by
  constructor
  · intro x y h
    rcases x with ⟨x, u, z⟩
    rcases y with ⟨y, v, w⟩
    change (u, x, z) = (v, y, w) at h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl
  · intro x
    exact ⟨(x.2.1, x.1, x.2.2), rfl⟩

/-- Kind: PROVED. Change the retained local condition from the unramified
condition to its own truncated condition. Both Selmer complexes have the
same compact complex. The two exact triangles bound the new complex
by the old one, shifted unramified cohomology and the new condition's own
cohomology. No additional full-local-complex cost is counted;
tex 3483–3498, 4391–4406, 4859–4873. -/
theorem conditionChange_cohomology (D : SelData k) (L U V : GCx k)
    (rq : GHom D.G L) (ιU : GHom U L) (ιV : GHom V L)
    (C₀ : GCx k) (j : GHom C₀ (selCx (withLocalCondition D L U rq ιU)))
    (hj : QuasiIso (GHom.toCC j)) (n : ℤ)
    (h₀ : Module.Finite k (C₀.toCC.homology n))
    (hU : Module.Finite k (U.toCC.homology (n - 1)))
    (hV : Module.Finite k (V.toCC.homology n)) :
    Module.Finite k ((selCx (withLocalCondition D L V rq ιV)).toCC.homology n) ∧
      Module.finrank k ((selCx (withLocalCondition D L V rq ιV)).toCC.homology n) ≤
        Module.finrank k (C₀.toCC.homology n) +
          Module.finrank k (U.toCC.homology (n - 1)) +
            Module.finrank k (V.toCC.homology n) := by
  let DU := swapSelData (relativeData D L U rq ιU)
  let DV := swapSelData (relativeData D L V rq ιV)
  let eU := ((homologyEquivOfQuasiIso j hj n).trans
    (homologyIsoOfBijective (flattenLocalCondition D L U rq ιU)
      (flattenLocalCondition_bijective D L U rq ιU) n).toLinearEquiv).trans
    (homologyIsoOfBijective (swapSelCx (relativeData D L U rq ιU))
      (swapSelCx_bijective (relativeData D L U rq ιU)) n).toLinearEquiv
  let eV := (homologyIsoOfBijective (flattenLocalCondition D L V rq ιV)
    (flattenLocalCondition_bijective D L V rq ιV) n).toLinearEquiv.trans
    (homologyIsoOfBijective (swapSelCx (relativeData D L V rq ιV))
      (swapSelCx_bijective (relativeData D L V rq ιV)) n).toLinearEquiv
  have hfU : Module.Finite k ((selCx DU).toCC.homology n) :=
    (Module.Finite.equiv_iff eU).1 h₀
  have heU := (sesTop_shortExact DU).homology_exact₁ (n - 1) n (by change n - 1 + 1 = n; omega)
  have hfC := exact_moduleFinite_middle heU hU hfU
  have hrC := exact_finrank_middle_le heU hU hfU
  have hcompact : locCx DU = locCx DV := rfl
  change Module.Finite k ((locCx DU).toCC.homology n) at hfC
  change Module.finrank k ((locCx DU).toCC.homology n) ≤
    Module.finrank k (U.toCC.homology (n - 1)) +
      Module.finrank k ((selCx DU).toCC.homology n) at hrC
  rw [hcompact] at hfC hrC
  have heV := (sesTop_shortExact DV).homology_exact₂ n
  have hfT := exact_moduleFinite_middle heV hfC hV
  have hrT := exact_finrank_middle_le heV hfC hV
  change Module.finrank k ((selCx DV).toCC.homology n) ≤
    Module.finrank k ((locCx DV).toCC.homology n) +
      Module.finrank k (V.toCC.homology n) at hrT
  rw [← eU.finrank_eq] at hrC
  refine ⟨(Module.Finite.equiv_iff eV).2 hfT, ?_⟩
  rw [eV.finrank_eq]
  change Module.finrank k ((selCx DV).toCC.homology n) ≤
    Module.finrank k (C₀.toCC.homology n) +
      Module.finrank k (U.toCC.homology (n - 1)) + Module.finrank k (V.toCC.homology n)
  omega

end ConditionTriangles

section ResidualCochainSteps

/-- Kind: definition. One residue-field support step with its own local
condition. The source support map is a quasi-isomorphism before any coefficient
change, and the target cochain comparison preserves the actual truncated
condition. No residual finiteness or rank bound of the new global complex is
assumed; tex 3483–3498, 4391–4406, 4859–4873. -/
structure SupportConditionStep (i : ℕ) [NeZero i]
    (X Y : GCx (Acoef i)) (c : ℕ) where
  /-- Kind: definition. The inflated old-place-only residual Selmer datum;
  tex 3483–3498, 4391–4406. -/
  oldDatum : SelData (ResidueField (Acoef i))
  /-- Kind: definition. The full local complex at the added place;
  tex 3483–3498, 4859–4873. -/
  localCx : GCx (ResidueField (Acoef i))
  /-- Kind: definition. Its unramified cochain condition;
  tex 3483–3498, 4391–4406. -/
  unramified : GCx (ResidueField (Acoef i))
  /-- Kind: definition. This label's actual truncated or full condition;
  tex 4859–4873, 5055–5059. -/
  condition : GCx (ResidueField (Acoef i))
  /-- Kind: GLUE. The actual restriction on the inflated old datum;
  tex 3483–3498, 4391–4406. -/
  restriction : GHom oldDatum.G localCx
  /-- Kind: GLUE. The unramified inclusion; tex 3483–3498, 4391–4406. -/
  unramifiedInclusion : GHom unramified localCx
  /-- Kind: GLUE. The actual condition inclusion at this label;
  tex 4859–4873, 5055–5059. -/
  conditionInclusion : GHom condition localCx
  /-- Kind: GLUE. The actual residue-field support comparison, with its
  coefficient and old-condition dictionary; tex 3483–3498, 4438–4442. -/
  sourceMap : GHom (gcxBaseChange (ResidueField (Acoef i)) X)
    (selCx (withLocalCondition oldDatum localCx unramified restriction unramifiedInclusion))
  /-- Kind: PRINT. Quasi-isomorphy of this residue-field support map. The
  canonical support-map constructor below supplies it from the printed support
  theorem; no nonflat tensor of a quasi-isomorphism is taken;
  tex 3483–3498, 4391–4406. -/
  source_quasiIso : QuasiIso (GHom.toCC sourceMap)
  /-- Kind: GLUE. Exact target cochain presentation with this label's own
  condition, not an equality of dimensions; tex 3483–3498, 4438–4442. -/
  targetMap : GHom (gcxBaseChange (ResidueField (Acoef i)) Y)
    (selCx (withLocalCondition oldDatum localCx condition restriction conditionInclusion))
  /-- Kind: GLUE. Quasi-isomorphy of the actual target cochain comparison.
  A full condition may use the canonical relaxed contraction rather than a
  degreewise isomorphism; tex 3483–3498, 4438–4442. -/
  target_quasiIso : QuasiIso (GHom.toCC targetMap)
  /-- Kind: GLUE. The procyclic unramified cohomology bound two;
  tex 3478–3481, 4391–4406. -/
  unramifiedBounds : CohomologyBounds unramified 0 1 2
  /-- Kind: GLUE. The condition's own cohomology is finite, in `[0,2]`,
  with allowance `4 + c`. A full local condition uses the baseline four; a
  truncated condition retains its additional specified cost `c`;
  tex 4391–4406, 4859–4873, 5055–5059. -/
  conditionBounds : CohomologyBounds condition 0 2 (4 + c)

/-- Kind: PROVED. The two actual cochain triangles give finiteness and
pointwise residual excess at most `6 + c`, vanishing outside `[0,3]`;
tex 3483–3498, 4391–4406, 4859–4873. -/
theorem SupportConditionStep.estimate {i : ℕ} [NeZero i] {X Y : GCx (Acoef i)} {c : ℕ}
    (S : SupportConditionStep i X Y c) (hX : ResidualCohomologyFinite X) (n : ℤ) :
    Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt Y n) ∧
      Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt Y n) ≤
        Module.finrank (ResidueField (Acoef i)) (residualCohomologyAt X n) +
          extraRank (6 + c) n := by
  let eX := residualHomologyEquiv X n
  let eY := (residualHomologyEquiv Y n).symm.trans
    (homologyEquivOfQuasiIso S.targetMap S.target_quasiIso n)
  obtain ⟨hf, hr⟩ := conditionChange_cohomology S.oldDatum S.localCx S.unramified S.condition
    S.restriction S.unramifiedInclusion S.conditionInclusion
    (gcxBaseChange (ResidueField (Acoef i)) X) S.sourceMap S.source_quasiIso n
    (hX n) (S.unramifiedBounds.finite (n - 1)) (S.conditionBounds.finite n)
  rw [eX.finrank_eq] at hr
  refine ⟨(Module.Finite.equiv_iff eY).2 hf, ?_⟩
  have he := eY.finrank_eq.trans_le hr
  by_cases hn : 0 ≤ n ∧ n ≤ 3
  · rw [extraRank, ite_eq_left hn]
    have hu := S.unramifiedBounds.rank (n - 1)
    have hv := S.conditionBounds.rank n
    omega
  · have hu := S.unramifiedBounds.outside (n - 1) (by omega)
    have hv := S.conditionBounds.outside n (by omega)
    have hru : Module.finrank (ResidueField (Acoef i))
        (S.unramified.toCC.homology (n - 1)) = 0 := Module.finrank_zero_of_subsingleton
    have hrv : Module.finrank (ResidueField (Acoef i))
        (S.condition.toCC.homology n) = 0 := Module.finrank_zero_of_subsingleton
    rw [hru, hrv, add_zero, add_zero] at he
    rw [extraRank, ite_eq_right hn, add_zero]
    exact he

/-- Kind: PROVED. The residue-field cochain support and condition steps
construct a residual comparison. Its coordinates are packaging after the
proved arithmetic rank estimate, not asserted to be an arithmetic support
map; tex 3483–3498, 4391–4406. -/
def residualComparison_of_cochain_steps {G H : StageComplexFamily} {c : ℕ}
    (step : ∀ i [NeZero i], SupportConditionStep i (G i) (H i) c)
    (hG : ∀ i [NeZero i], ResidualCohomologyFinite (G i)) :
    ResidualComparison H G (6 + c) where
  map i _ n := by
    let k := ResidueField (Acoef i)
    let V := residualCohomologyAt (H i) n
    let T := residualCohomologyAt (G i) n × (Fin (extraRank (6 + c) n) → k)
    have : Module.Finite k V := ((step i).estimate (hG i) n).1
    have : Module.Finite k (residualCohomologyAt (G i) n) :=
      finite_residualCohomologyAt_of (hG i) n
    exact embeddingOfFinrank V T (by
      rw [Module.finrank_prod, Module.finrank_fin_fun]
      exact ((step i).estimate (hG i) n).2)
  injective i _ n := by
    have : Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt (H i) n) :=
      ((step i).estimate (hG i) n).1
    have : Module.Finite (ResidueField (Acoef i)) (residualCohomologyAt (G i) n) :=
      finite_residualCohomologyAt_of (hG i) n
    exact embeddingOfFinrank_injective _ _ _

/-- Kind: PROVED. Iterate genuine residue-field cochain support steps and
preserve every label's own condition. The output width is `6k + sum c`, and
no global residual package for the intermediate or final enlarged support
is among the assumptions; tex 3483–3498, 4391–4406, 4859–4873. -/
theorem residualPackage_of_support_condition_steps (G : ℕ → StageComplexFamily)
    (c : ℕ → ℕ) (k B : ℕ) (hbase : StageResidualPackage (G 0) B) :
    (∀ j, j < k → ∀ i [NeZero i], Nonempty (SupportConditionStep i
      (G j i) (G (j + 1) i) (c j))) →
      Nonempty (ResidualComparison (G k) (G 0) (6 * k + ∑ j ∈ Finset.range k, c j)) ∧
        StageResidualPackage (G k) (B + 6 * k + ∑ j ∈ Finset.range k, c j) := by
  have iter : ∀ m : ℕ,
      (∀ j, j < m → ∀ i [NeZero i], Nonempty (SupportConditionStep i
        (G j i) (G (j + 1) i) (c j))) →
        Nonempty (ResidualComparison (G m) (G 0) (totalWidth c m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      simpa [totalWidth] using (⟨ResidualComparison.refl (G 0)⟩ :
        Nonempty (ResidualComparison (G 0) (G 0) 0))
    | succ m ih =>
      intro step
      obtain ⟨P⟩ := ih (fun j hj => step j (Nat.lt_succ_of_lt hj))
      have hp := P.residualPackage hbase
      let Q := residualComparison_of_cochain_steps
        (fun i _ => Classical.choice (step m (Nat.lt_succ_self m) i)) hp.1
      simpa [totalWidth, Finset.sum_range_succ] using (⟨Q.comp P⟩ :
        Nonempty (ResidualComparison (G (m + 1)) (G 0) (totalWidth c m + (6 + c m))))
  intro step
  obtain ⟨T⟩ := iter k step
  have ht : ResidualComparison (G k) (G 0) (6 * k + ∑ j ∈ Finset.range k, c j) :=
    ResidualComparison.castWidth (totalWidth_eq c k) T
  exact ⟨⟨ht⟩, by simpa only [Nat.add_assoc] using ht.residualPackage hbase⟩

end ResidualCochainSteps

section CanonicalSupportMap

variable {A : Type} [CommRing A] {C D E : GCx A}

/-- Kind: definition. Transport the target of an actual cochain map along
an equality of cochain presentations; tex 4438–4442. -/
def retargetHom (h : D = E) (f : GHom C D) : GHom C E := h ▸ f

/-- Kind: PROVED. Target presentation transport preserves quasi-isomorphy;
tex 4438–4442. -/
theorem retargetHom_quasiIso (h : D = E) (f : GHom C D)
    (hf : QuasiIso (GHom.toCC f)) : QuasiIso (GHom.toCC (retargetHom h f)) := by
  subst h
  exact hf

end CanonicalSupportMap

section LocalAllowance

/-- Kind: PROVED. Increase a proved local cohomology allowance without
changing the condition or its inclusion; tex 4391–4406, 4859–4873. -/
theorem CohomologyBounds.weaken {k : Type} [Field k] {Q : GCx k} {lo hi : ℤ} {a b : ℕ}
    (H : CohomologyBounds Q lo hi a) (h : a ≤ b) : CohomologyBounds Q lo hi b :=
  ⟨H.finite, fun n => (H.rank n).trans h, H.outside⟩

/-- Kind: PROVED. A truncated condition with its own allowance `c` supplies
the `4 + c` step allowance; the baseline four also admits a full local
condition of rank at most four; tex 4391–4406, 4859–4873, 5055–5059. -/
theorem CohomologyBounds.conditionAllowance {k : Type} [Field k] {Q : GCx k} {c : ℕ}
    (H : CohomologyBounds Q 0 2 c) : CohomologyBounds Q 0 2 (4 + c) :=
  H.weaken (by omega)

end LocalAllowance

section PrintedArithmeticStep

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (q : HeightOneSpectrum (𝓞 K))
  (i : ℕ) [NeZero i]
  (M : Type) [AddCommGroup M] [Module (ResidueField (Acoef i)) M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (ResidueField (Acoef i)) M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
  (Δ : GaloisLocalConditions K S (ResidueField (Acoef i)) M)

/-- Kind: PROVED. Construct the actual residue-field support step from the
printed support theorem with its canonical unramified factorizations. The old
support and coefficient module are stage-specific parameters, not one fixed
support or character. The remaining inputs are source/target cochain
presentations and local condition bounds; no support quasi-isomorphism or
new global residual estimate is assumed; tex 3483–3498, 4391–4406. -/
def supportConditionStep_of_print_ur (h788 : NekovarProp788ii K)
    (hK : IsTotallyComplex K) (hS : S.Finite)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {X Y : GCx (Acoef i)} {c : ℕ}
    (Dold : SelData (ResidueField (Acoef i))) (L U V : GCx (ResidueField (Acoef i)))
    (rq : GHom Dold.G L) (ιU : GHom U L) (ιV : GHom V L)
    (hDp : (galoisSupportDataUr K (Set.subset_insert q S) (ResidueField (Acoef i)) M Δ).Dp =
      withLocalCondition Dold L U rq ιU)
    (source : GHom (gcxBaseChange (ResidueField (Acoef i)) X)
      (selCx (galoisSupportDataUr K (Set.subset_insert q S) (ResidueField (Acoef i)) M Δ).D))
    (hsource : QuasiIso (GHom.toCC source))
    (target : GHom (gcxBaseChange (ResidueField (Acoef i)) Y)
      (selCx (withLocalCondition Dold L V rq ιV)))
    (htarget : QuasiIso (GHom.toCC target))
    (hU : CohomologyBounds U 0 1 2) (hV : CohomologyBounds V 0 2 (4 + c)) :
    SupportConditionStep i X Y c := by
  let SD := galoisSupportDataUr K (Set.subset_insert q S) (ResidueField (Acoef i)) M Δ
  have hmap : QuasiIso (GHom.toCC (supportMap SD)) :=
    supportChange_of_print_ur K h788 (Set.subset_insert q S) 2
      (residueFiniteSetting (S₀ := S) i hK hS h2) (hS.insert q) Δ
  have hcomp : QuasiIso (GHom.toCC (ghomComp source (supportMap SD))) := by
    have := hsource
    have := hmap
    rw [← GHom.toCC_comp]
    infer_instance
  let f := retargetHom (congrArg selCx hDp) (ghomComp source (supportMap SD))
  exact ⟨Dold, L, U, V, rq, ιU, ιV, f,
    retargetHom_quasiIso (congrArg selCx hDp) _ hcomp, target, htarget, hU, hV⟩

end PrintedArithmeticStep

section MovingPackageAdapter

/-- Kind: PROVED. Export the terminal package with exactly the three
hypothesis types of the moving-family consumer, without importing or redefining
that consumer. Set `terminal i` to its actual global complex at stage `i`;
tex 2727–2741, 4255–4280, 4391–4406. -/
theorem movingResidualPackage_of_cochain_steps (G : ℕ → StageComplexFamily)
    (terminal : StageComplexFamily) (c : ℕ → ℕ) (k B : ℕ)
    (hterminal : G k = terminal) (hbase : StageResidualPackage (G 0) B)
    (step : ∀ j, j < k → ∀ i [NeZero i], Nonempty (SupportConditionStep i
      (G j i) (G (j + 1) i) (c j))) :
    (∀ i [NeZero i], ResidualCohomologyFinite (terminal i)) ∧
      (∀ i [NeZero i] (n : ℤ), n < 0 ∨ 3 < n →
        Module.finrank (ResidueField (Acoef i))
          (residualCohomologyAt (terminal i) n) = 0) ∧
      (∀ i [NeZero i] (n : ℤ),
        Module.finrank (ResidueField (Acoef i))
          (residualCohomologyAt (terminal i) n) ≤ B + 6 * k + ∑ j ∈ Finset.range k, c j) := by
  have h := (residualPackage_of_support_condition_steps G c k B hbase step).2
  rw [hterminal] at h
  exact h

end MovingPackageAdapter

section ExistingControlAdapter

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.CoefModules (IsOpenKer)

variable {K : Type} [Field K] [NumberField K]
  {S₀ : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {α : ∀ i : ℕ, GKS K S₀ →* (Acoef i)ˣ} [∀ i, IsOpenKer (α i)]
  {F : ActualStageFamily S₀ W α} {R : StandardOldReference S₀ W α}

/-- Kind: PROVED. The original one-place residual comparison is the
corresponding comparison between its actual stage-complex families;
tex 3483–3498, 4391–4406. -/
def ResidualComparison.of_onePlace {width : ℕ} (T : ResidualSupportControl F R width) :
    ResidualComparison (fun i => F.globalCx i) (fun i => R.globalCx i) width :=
  ⟨T.map, T.injective⟩

/-- Kind: PROVED. Convert a several-place residual comparison on matching
actual endpoints to the original residual-support-control interface;
tex 3483–3498, 4391–4406. -/
def ResidualComparison.to_onePlace {width : ℕ}
    (T : ResidualComparison (fun i => F.globalCx i) (fun i => R.globalCx i) width) :
    ResidualSupportControl F R width := ⟨T.map, T.injective⟩

/-- Kind: PROVED. A finite chain of the specified support and local-condition
steps produces the original residual-support-control type with width
`6k + sum c`, when the initial and terminal complexes have the displayed
reference and actual cochain identifications; tex 3483–3498, 4391–4406. -/
theorem residualSupportControl_of_cochain_steps (G : ℕ → StageComplexFamily)
    (c : ℕ → ℕ) (k B : ℕ)
    (hstart : G 0 = fun i => R.globalCx i)
    (hfinish : G k = fun i => F.globalCx i)
    (hbase : StageResidualPackage (G 0) B)
    (step : ∀ j, j < k → ∀ i [NeZero i], Nonempty (SupportConditionStep i
      (G j i) (G (j + 1) i) (c j))) :
    Nonempty (ResidualSupportControl F R (6 * k + ∑ j ∈ Finset.range k, c j)) := by
  obtain ⟨T⟩ := (residualPackage_of_support_condition_steps G c k B hbase step).1
  have T' : ResidualComparison (fun i => F.globalCx i) (fun i => R.globalCx i)
      (6 * k + ∑ j ∈ Finset.range k, c j) := by
    rw [← hfinish, ← hstart]
    exact T
  exact ⟨ResidualComparison.to_onePlace T'⟩

end ExistingControlAdapter

end ZInQ.Contrib.RC53Assist.RetainedAssembly.SupportChange.SeveralPlaces


