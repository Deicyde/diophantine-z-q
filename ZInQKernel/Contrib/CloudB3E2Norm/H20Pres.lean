import ZInQKernel.Contrib.CloudB3E2Norm.H20Inertia
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate15Genuine

/-!
# The norm identity on the one presentation of the support complexes

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194): at each switch
`C_T ⊂ C_{T ∪ {p}}` of the support complexes, the relaxed class is the point factor times the
primitive class plus a boundary, `z_R = e · i(z) + d b` (tex 4169–4170), at a coefficient stage
ring (tex 4385–4451).

Lane RC32's one presentation (`CommonCoordinate15PresS.lean`: `presCondS`, `suppCxS`, `suppInclS`,
`suppSwitchS`) indexes the places by `Places K S₀ ⊕ (ι × Bool)` (the old places, and the two places
above each unused split prime), with the full condition at the two places above `p ∈ T` and the
genuine unramified condition at those above `p ∉ T`. Its consumer `CMStepHyps.hnorm`
(`CommonCoordinate15Holds.lean`) asks, at each switch, for the identity above in `C_{T ∪ {p}}`.

This file is the adapter from the norm identity in genuine continuous cochains (`GlobalCochain.lean`
`hG_of_transfer`, `LocalComponents.lean` `hzR_of_strictLifts`) to that presentation.

* `hnorm_changeIncl` (PROVED, generic): for any termwise injective inclusion of local conditions
  `F : Δ ⊆ Δ'` (lane RC26's `CondInclusion`, the switch `suppInclS = changeIncl`), strict lifts
  `(a_R, u_R, 0)` and `(a_P, u_P, 0)` with a global identity `a_R = e a_P + d b_G` satisfy
  `(a_R, u_R, 0) = e · changeIncl F (a_P, u_P, 0) + d (b_G, b_U, 0)`, when the conditions of `Δ'`
  are injective in degree one and `res b_G` lifts in degree zero.
* `piMap_injective`, `exists_piMap_lift` (PROVED): componentwise injectivity and lifts.
* `presι_injective`, `exists_presLift₀`, `exists_presLift₁` (PROVED): for the presentation, degree-one
  injectivity (old conditions, the identity, the split inclusions `EU`), degree-zero lifts (old
  conditions, the identity, `EU` surjective in degree zero) and degree-one lifts of a global class
  (old lifts, the identity at the full places, unramified lifts at the others).
* **`hnorm_pres`** (PROVED): the norm identity `z_R = e · i(z) + d b` at the switch `T → T ∪ {p}`
  of the presentation, for strict lifts of global classes `a_R` (relaxed) and `a_P` (primitive),
  from the global identity, the old lifts, and the unramified lifts of `a_R` at the places above
  `q ∉ T ∪ {p}` and of `a_P` at the places above `q ∉ T` (the inputs `hPw`).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Contrib.CloudB3RC53.PairedFunctional
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

/-! ### Componentwise injectivity and lifts -/

section Pi

variable {k : Type} [CommRing k] {ι : Type} {A B : ι → GCx k} (f : ∀ v, GHom (A v) (B v))

/-- `piMap` is injective in degree `n` when every component is. Kind: PROVED. -/
theorem piMap_injective (n : ℤ) (h : ∀ v, Function.Injective ((f v).f n n rfl)) :
    Function.Injective ((piMap f).f n n rfl) := fun _ _ hxy =>
  funext fun v => h v (congrFun hxy v)

/-- Componentwise lifts glue to a lift through `piMap`. Kind: PROVED. -/
theorem exists_piMap_lift (n : ℤ) (c : (piCx B).X n)
    (h : ∀ v, ∃ u : (A v).X n, (f v).f n n rfl u = c v) :
    ∃ u : (piCx A).X n, (piMap f).f n n rfl u = c := by
  choose u hu using h
  exact ⟨u, funext hu⟩

end Pi

/-! ### The norm identity across an inclusion of local conditions -/

section ChangeIncl

variable {k : Type} [CommRing k] {GS : Type} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  {Δ Δ' : LocalConditions k GS Gv loc M} (F : CondInclusion Δ Δ')

/-- **The norm identity across an inclusion of local conditions** (tex 4157–4170): strict lifts
of a relaxed and a primitive class with a global identity `a_R = e a_P + d b_G` satisfy
`(a_R, u_R, 0) = e · changeIncl F (a_P, u_P, 0) + d (b_G, b_U, 0)`. Kind: PROVED. -/
theorem hnorm_changeIncl (aR aP : (globalCx k GS M).X 1) (uR : (piCx Δ'.U).X 1)
    (uP : (piCx Δ.U).X 1) (e : k) (bG : (globalCx k GS M).X 0) (bU : (piCx Δ'.U).X 0)
    (hι : Function.Injective ((piMap Δ'.i).f 1 1 rfl))
    (hR : (piMap Δ'.i).f 1 1 rfl uR = (resS k GS Gv loc M).f 1 1 rfl aR)
    (hP : (piMap Δ.i).f 1 1 rfl uP = (resS k GS Gv loc M).f 1 1 rfl aP)
    (hG : aR = e • aP + (globalCx k GS M).d 0 1 rfl bG)
    (hbU : (piMap Δ'.i).f 0 0 rfl bU = (resS k GS Gv loc M).f 0 0 rfl bG) :
    (((aR, uR, 0) : selT (selData k GS Gv loc M Δ') 1) : (selCx (selData k GS Gv loc M Δ')).X 1) =
      e • (changeIncl F).f 1 1 rfl
        (((aP, uP, 0) : selT (selData k GS Gv loc M Δ) 1) : (selCx (selData k GS Gv loc M Δ)).X 1) +
      (selCx (selData k GS Gv loc M Δ')).d 0 1 rfl
        (((bG, bU, 0) : selT (selData k GS Gv loc M Δ') 0) :
          (selCx (selData k GS Gv loc M Δ')).X 0) := by
  have hP' : (piMap Δ'.i).f 1 1 rfl ((piMap F.φ).f 1 1 rfl uP) =
      (resS k GS Gv loc M).f 1 1 rfl aP := by
    rw [← hP]
    funext v
    exact F.compat v 1 (uP v)
  exact hzR_of_strictLifts (selData k GS Gv loc M Δ') (piMap F.φ) aR aP uR uP e bG bU hι hR hP'
    hG hbU

end ChangeIncl

/-! ### The presentation -/

section Presentation

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable (K : Type) [Field K] [NumberField K] (S₀ S : Set (HeightOneSpectrum (𝓞 K)))
  (k : Type) [CommRing k] [TopologicalSpace k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (GKS K S) M]
  (Δ : LocalConditions k (GKS K S) (fun v : Places K S₀ => Gloc K v.1)
    (fun v => locMap K S v.1) M)
  {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)
  (X : (j : ι × Bool) → TopRep.{0} k (GUr K (place j).1))
  (EU : ∀ j, SplitInclusion (genuineUq K S k (place j) (X j)) (genuineLq K S k M (place j)))

/-- **Degree-one injectivity of the conditions of the presentation** (PROVED): from the old
conditions, the identity (full places) and the split inclusions `EU` (unramified places). -/
theorem presι_injective (T : Finset ι)
    (hold : ∀ v₀, Function.Injective ((Δ.i v₀).f 1 1 rfl)) :
    Function.Injective ((piMap (presCondS K S₀ S k M Δ place X EU T).i).f 1 1 rfl) := by
  refine piMap_injective _ 1 fun v => ?_
  rcases v with v₀ | j
  · exact hold v₀
  · change Function.Injective ((condιS K S k M place X EU j (decide (j.1 ∈ T))).f 1 1 rfl)
    cases decide (j.1 ∈ T)
    · exact (EU j).inj 1
    · exact fun _ _ h => h

/-- **Degree-zero lifts for the presentation** (PROVED): every degree-zero local cochain lifts
when the old conditions and the split inclusions `EU` are surjective in degree zero. -/
theorem exists_presLift₀ (T : Finset ι)
    (hold : ∀ v₀, Function.Surjective ((Δ.i v₀).f 0 0 rfl))
    (hEU : ∀ j, Function.Surjective ((EU j).i.f 0 0 rfl))
    (c : (piCx fun v => localCx k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M v).X 0) :
    ∃ u, (piMap (presCondS K S₀ S k M Δ place X EU T).i).f 0 0 rfl u = c := by
  refine exists_piMap_lift _ 0 c fun v => ?_
  rcases v with v₀ | j
  · exact hold v₀ (c (.inl v₀))
  · change ∃ u, (condιS K S k M place X EU j (decide (j.1 ∈ T))).f 0 0 rfl u = c (.inr j)
    cases decide (j.1 ∈ T)
    · exact hEU j (c (.inr j))
    · exact ⟨c (.inr j), rfl⟩

/-- **Degree-one lifts of a global class for the presentation** (PROVED): from lifts at the old
places and at the places above the primes outside `T` (the full condition at the places above
`T` lifts everything). -/
theorem exists_presLift₁ (T : Finset ι) (a : (globalCx k (GKS K S) M).X 1)
    (hold : ∀ v₀, ∃ u, (Δ.i v₀).f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl a (.inl v₀))
    (hur : ∀ j, j.1 ∉ T → ∃ u, (EU j).i.f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl a (.inr j)) :
    ∃ u, (piMap (presCondS K S₀ S k M Δ place X EU T).i).f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl a := by
  refine exists_piMap_lift _ 1 _ fun v => ?_
  rcases v with v₀ | j
  · exact hold v₀
  · change ∃ u, (condιS K S k M place X EU j (decide (j.1 ∈ T))).f 1 1 rfl u = _
    by_cases hj : j.1 ∈ T
    · rw [decide_eq_true hj]
      exact ⟨_, rfl⟩
    · rw [decide_eq_false hj]
      exact hur j hj

variable [DecidableEq (Places K S₀)]

/-- **The norm identity at a switch of the presentation** (PROVED; tex 4157–4170, 4385–4451): for
the switch `C_T ⊂ C_{T ∪ {p}}` (`suppSwitchS`, whose inclusion is `suppInclS`), a global identity
`a_R = e a_P + d b_G` between a relaxed and a primitive class, lifts of both at the old places, of
`a_R` at the unramified places of `T ∪ {p}` and of `a_P` at the unramified places of `T` give
strict lifts with `z_R = e · i(z) + d b` (the hypothesis `hnorm` of `CMStepHyps`). -/
theorem hnorm_pres (T : Finset ι) (p : ι) (aR aP : (globalCx k (GKS K S) M).X 1) (e : k)
    (bG : (globalCx k (GKS K S) M).X 0)
    (hιold : ∀ v₀, Function.Injective ((Δ.i v₀).f 1 1 rfl))
    (hsold : ∀ v₀, Function.Surjective ((Δ.i v₀).f 0 0 rfl))
    (hsEU : ∀ j, Function.Surjective ((EU j).i.f 0 0 rfl))
    (hG : aR = e • aP + (globalCx k (GKS K S) M).d 0 1 rfl bG)
    (holdR : ∀ v₀, ∃ u, (Δ.i v₀).f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl aR (.inl v₀))
    (holdP : ∀ v₀, ∃ u, (Δ.i v₀).f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl aP (.inl v₀))
    (hurR : ∀ j, j.1 ∉ insert p T → ∃ u, (EU j).i.f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl aR (.inr j))
    (hurP : ∀ j, j.1 ∉ T → ∃ u, (EU j).i.f 1 1 rfl u =
      (resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 1 1 rfl aP (.inr j)) :
    ∃ (zR : (suppCxS K S₀ S k M Δ place X EU (insert p T)).X 1)
      (z : (suppCxS K S₀ S k M Δ place X EU T).X 1)
      (b : (suppCxS K S₀ S k M Δ place X EU (insert p T)).X 0),
      zR.1 = aR ∧ z.1 = aP ∧
      zR = e • (suppSwitchS K S₀ S k M Δ place X EU T p).i.f 1 1 rfl z +
        (suppCxS K S₀ S k M Δ place X EU (insert p T)).d 0 1 rfl b := by
  obtain ⟨uR, hR⟩ := exists_presLift₁ K S₀ S k M Δ place X EU (insert p T) aR holdR hurR
  obtain ⟨uP, hP⟩ := exists_presLift₁ K S₀ S k M Δ place X EU T aP holdP hurP
  obtain ⟨bU, hbU⟩ := exists_presLift₀ K S₀ S k M Δ place X EU (insert p T) hsold hsEU
    ((resS k (GKS K S) (presGv K S₀ S place) (presLoc K S₀ S place) M).f 0 0 rfl bG)
  exact ⟨((aR, uR, 0) : selT (suppDataS K S₀ S k M Δ place X EU (insert p T)) 1),
    ((aP, uP, 0) : selT (suppDataS K S₀ S k M Δ place X EU T) 1),
    ((bG, bU, 0) : selT (suppDataS K S₀ S k M Δ place X EU (insert p T)) 0), rfl, rfl,
    hnorm_changeIncl (presCondInclS K S₀ S k M Δ place X EU T p) aR aP uR uP e bG bU
      (presι_injective K S₀ S k M Δ place X EU (insert p T) hιold) hR hP hG hbU⟩

end Presentation

end ZInQ.Contrib.CloudB3E2.NormCochain
