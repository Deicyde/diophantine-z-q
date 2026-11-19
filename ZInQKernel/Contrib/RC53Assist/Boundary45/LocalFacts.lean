import ZInQKernel.Contrib.OneProof.RC.BaseZeroAssembly.Boundary45
import ZInQKernel.Contrib.OneProof.RC.CoefModules.CocycleCondition
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Selmer

/-!
# The local facts used in boundary (4.5)

At one finite coefficient stage, write `L_v = C_cont(G_v, M)` and
`i_v : U_v → L_v` for the local-condition map. The two hypotheses are:

* Every `c` in `L_v^0` with `d c = 0` is `i_v w` for some `w` in `U_v^0`
  with `d w = 0`.
* If `u` in `U_v^1` is closed and `i_v u = d c` in `L_v`, then `u = d w`
  for some `w` in `U_v^0`.

Thus the assertions concern surjectivity on zeroth cohomology and
injectivity on first cohomology, not surjectivity on all first cochains.
For the local complexes here, a stronger elementary criterion applies:
`i_v^0` is surjective on cochains and `i_v^1` is injective on cochains.

The cocycle condition is `[C^0 → Z + B^1]`, with `Z` a submodule of
continuous cocycles. This includes the existing finite Kummer condition
and its coefficient extension by taking `Z` to be the corresponding
Kummer span. The unramified condition is `[W --(Phi-1)-→ W]`, mapped to
local cochains by inflated cocycles. Its degree-zero map is surjective
when the coefficient comparison `W → M` is surjective, and its
first-degree map is injective when that comparison is injective and
Frobenius lifts. These properties hold for the identity comparison used
by `urAt` outside the coefficient support.

The manuscript uses these assertions in the proof of
`ex:arith-central-specialization`, lines 3917-3918. The finite Kummer
shape is described at lines 3413-3438; the unramified maps at lines
3471-3498. Nekovar's Selmer-complex formalism and support comparison are
cited there. No printed arithmetic assertion is introduced here.

The theorems also assemble the local facts over the product of places
and apply the retained-boundary lifting theorem. No assertion is made
for orthogonal zero local conditions with nonzero local invariants.
-/


noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules

universe u

section Abstract

variable {k : Type u} [CommRing k] {U L : GCx k}

/-- Exactly the `honto` hypothesis of the finite boundary theorem. -/
def H0Onto (i : GHom U L) : Prop :=
  ∀ c : L.X 0, L.d 0 1 rfl c = 0 →
    ∃ w : U.X 0, U.d 0 1 rfl w = 0 ∧ i.f 0 0 rfl w = c

/-- Exactly the `hinj` hypothesis of the finite boundary theorem. -/
def H1Injective (i : GHom U L) : Prop :=
  ∀ a : U.X 1, U.d 1 2 rfl a = 0 →
    (∃ c : L.X 0, i.f 1 1 rfl a = L.d 0 1 rfl c) →
    ∃ w : U.X 0, U.d 0 1 rfl w = a

/-- The pair of local hypotheses, with the cochain representatives retained. -/
def LocalFacts (i : GHom U L) : Prop := H0Onto i ∧ H1Injective i

/-- A degree-zero surjection and degree-one injection suffice for both local facts. -/
theorem localFacts_of_surjective_zero_injective_one (i : GHom U L)
    (h0 : Function.Surjective (i.f 0 0 rfl))
    (h1 : Function.Injective (i.f 1 1 rfl)) : LocalFacts i := by
  constructor
  · intro c hc
    obtain ⟨w, hw⟩ := h0 c
    refine ⟨w, ?_, hw⟩
    apply h1
    rw [i.comm 0 1 0 1 rfl rfl rfl rfl, hw, hc, map_zero]
  · intro a _ha ha
    obtain ⟨c, hc⟩ := ha
    obtain ⟨w, hw⟩ := h0 c
    refine ⟨w, ?_⟩
    apply h1
    rw [i.comm 0 1 0 1 rfl rfl rfl rfl, hw, hc]

/-- Local facts assemble componentwise. For finite places, this product is their direct sum. -/
theorem localFacts_pi {V : Type u} {Us Ls : V → GCx k}
    (i : ∀ v, GHom (Us v) (Ls v)) (hi : ∀ v, LocalFacts (i v)) :
    LocalFacts (piMap i) := by
  constructor
  · intro c hc
    have hv : ∀ v, (Ls v).d 0 1 rfl (c v) = 0 := fun v => congrFun hc v
    choose w hw hwi using fun v => (hi v).1 (c v) (hv v)
    exact ⟨w, funext hw, funext hwi⟩
  · intro a ha hca
    obtain ⟨c, hc⟩ := hca
    have hv : ∀ v, (Us v).d 1 2 rfl (a v) = 0 := fun v => congrFun ha v
    choose w hw using fun v => (hi v).2 (a v) (hv v) ⟨c v, congrFun hc v⟩
    exact ⟨w, funext hw⟩

/-- The full local condition satisfies both hypotheses. -/
theorem full_localFacts (L : GCx k) : LocalFacts (idGHom L) :=
  localFacts_of_surjective_zero_injective_one _ (fun c => ⟨c, rfl⟩) (fun _ _ h => h)

end Abstract

section CocycleCondition

variable {k : Type u} [CommRing k]
  {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul G M]

/-- Both local facts for every cocycle condition, including the finite Kummer spans. -/
theorem cocycleCondition_localFacts (Z : Submodule k (contCochain k G M 1))
    (hZ : ∀ z ∈ Z, contD k G M 1 z = 0) :
    LocalFacts (cocycleConditionι Z hZ) :=
  localFacts_of_surjective_zero_injective_one _
    (fun c => ⟨ofCondZero Z hZ c, rfl⟩) (cocycleConditionι_injective Z hZ 1)

end CocycleCondition

section Unramified

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (p : G →ₜ* H) (X : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M]
  [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : X.V →ₗ[k] M) (hf : ∀ (g : G) (x : X.V), f (p g • x) = g • f x)

/-- The actual unramified cochain map has both local facts when its coefficient map is bijective. -/
theorem unramified_localFacts (hfb : Function.Bijective f)
    (hp : ∃ g, p g = frobElt e) :
    LocalFacts (ofCCHom (urToLocal e p X f hf)) := by
  apply localFacts_of_surjective_zero_injective_one
  · change Function.Surjective ((urToLocal e p X f hf).f 0).hom
    rw [urToLocal_f₀]
    change Function.Surjective ((urLin₀ (G := G) X f) ∘
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (frob e X - 1)) rel01).hom.hom)
    apply Function.Surjective.comp _ ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    intro c
    obtain ⟨x, hx⟩ := hfb.2 (cfun c default)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext g
    change f x = cfun c g
    rw [hx]
    exact congrArg (cfun c) (Subsingleton.elim default g)
  · exact urToLocal_injective e p X f hf hfb.1 hp 1

end Unramified

section Places

variable {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  (M0 : Type) [AddCommGroup M0] [Module k M0] [DistribMulAction (GKS K S0) M0]
  [SMulCommClass (GKS K S0) k M0] [TopologicalSpace M0] [DiscreteTopology M0]
  [ContinuousSMul (GKS K S0) M0] [Finite M0]

/-- Both local hypotheses outside the coefficient support, for the existing `urAt` map. -/
theorem urAt_localFacts (v : Places K S) (hv : v.1 ∉ S0) :
    LocalFacts (urAt hS k M0 v hv).i := by
  have hlocal : SMulCommClass (Gloc K v.1) k (ResMod (locMap K S v.1) (InflMod hS M0)) :=
    ⟨fun g c x => by
      change (inflMap K hS (locMap K S v.1 g)) • (c • (show M0 from x)) =
        c • ((inflMap K hS (locMap K S v.1 g)) • (show M0 from x))
      exact smul_comm _ _ _⟩
  exact @unramified_localFacts k _ _ (Gloc K v.1) _ _ _ (GUr K v.1) _ _ _
    (eUr K v.1) (resUr K v.1) (urRep k M0 (newPlace v hv))
    (urRep_continuousSMul k M0 (newPlace v hv)) _ _
    (ResMod (locMap K S v.1) (InflMod hS M0)) _ _ _ hlocal _ _ _
    (urId hS k M0 (newPlace v hv)) (urId_compat hS k M0 v hv)
    ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩ (resUr_surjective K v.1 (frobElt (eUr K v.1)))

end Places

section ActualStages

open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
  (a : GKS K S0 →* (Acoef n)ˣ) [IsOpenKer a]

/-- The local hypotheses for the existing actual Selmer datum, reduced only to the old places. -/
theorem actual_localFacts
    (c : ∀ v : Places K S, v.1 ∈ S0 → CondAt K S (Acoef n) (MinS hS W n a) v)
    (hc : ∀ v h, LocalFacts (c v h).i) :
    LocalFacts (actualSelData hS W n a c).ι := by
  classical
  let _ := acoefTop n
  let _ := acoefTop_discrete n
  change LocalFacts (piMap (actualConditions hS W n a c).i)
  apply localFacts_pi
  intro v
  change LocalFacts (urOutside hS (Acoef n) (Mcoef K S0 W n a) c v).i
  by_cases hv : v.1 ∈ S0
  · have he : urOutside hS (Acoef n) (Mcoef K S0 W n a) c v = c v hv := by
      unfold urOutside
      exact dite_eq_left hv
    rw [he]
    exact hc v hv
  · have he : urOutside hS (Acoef n) (Mcoef K S0 W n a) c v =
        urAt hS (Acoef n) (Mcoef K S0 W n a) v hv := by
      unfold urOutside
      exact dite_eq_right hv
    rw [he]
    exact urAt_localFacts hS (Acoef n) (Mcoef K S0 W n a) v hv

/-- Actual finite coefficient data with cocycle conditions at the old places.
For Kummer data, the parameter `Z v` is its existing extended Kummer span. -/
def cocycleStageSelData
    (Z : ∀ v : Places K S, Submodule (Acoef n)
      (contCochain (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1))
    (hZ : ∀ v z, z ∈ Z v →
      contD (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1 z = 0) :
    SelData (Acoef n) :=
  actualSelData hS W n a (fun v _ => ⟨cocycleCondition (Z v) (hZ v),
    cocycleConditionι (Z v) (hZ v)⟩)

/-- Both exact boundary hypotheses for every actual cocycle-condition stage, with no local leaf. -/
theorem cocycleStage_localFacts
    (Z : ∀ v : Places K S, Submodule (Acoef n)
      (contCochain (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1))
    (hZ : ∀ v z, z ∈ Z v →
      contD (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1 z = 0) :
    LocalFacts (cocycleStageSelData hS W n a Z hZ).ι :=
  actual_localFacts hS W n a _ (fun v _ => cocycleCondition_localFacts (Z v) (hZ v))

open Classical in
/-- The old condition is full on the selected active and moving places, and a
cocycle condition on the remaining old places. -/
def mixedStageCond
    (F : Set (Places K S))
    (Z : ∀ v : Places K S, Submodule (Acoef n)
      (contCochain (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1))
    (hZ : ∀ v z, z ∈ Z v →
      contD (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1 z = 0)
    (v : Places K S) : CondAt K S (Acoef n) (MinS hS W n a) v :=
  if v ∈ F then fullAt K S (Acoef n) (MinS hS W n a) v
  else ⟨cocycleCondition (Z v) (hZ v), cocycleConditionι (Z v) (hZ v)⟩

/-- The finite Heegner local-condition pattern: old Kummer spans, full active and
moving places, and unramified conditions outside the coefficient support.
Here the Kummer spans are parameters; no choice of arithmetic class is changed. -/
def mixedStageSelData
    (F : Set (Places K S))
    (Z : ∀ v : Places K S, Submodule (Acoef n)
      (contCochain (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1))
    (hZ : ∀ v z, z ∈ Z v →
      contD (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1 z = 0) :
    SelData (Acoef n) :=
  actualSelData hS W n a (fun v _ => mixedStageCond hS W n a F Z hZ v)

/-- Both exact boundary hypotheses for the mixed finite-stage local conditions.
There is no assumption of either desired local fact. -/
theorem mixedStage_localFacts
    (F : Set (Places K S))
    (Z : ∀ v : Places K S, Submodule (Acoef n)
      (contCochain (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1))
    (hZ : ∀ v z, z ∈ Z v →
      contD (Acoef n) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W n a)) 1 z = 0) :
    LocalFacts (mixedStageSelData hS W n a F Z hZ).ι := by
  classical
  apply actual_localFacts hS W n a
  intro v _hv
  by_cases hvF : v ∈ F
  · have he : mixedStageCond hS W n a F Z hZ v =
        fullAt K S (Acoef n) (MinS hS W n a) v := by
      unfold mixedStageCond
      exact ite_eq_left hvF
    rw [he]
    exact full_localFacts _
  · have he : mixedStageCond hS W n a F Z hZ v =
        ⟨cocycleCondition (Z v) (hZ v), cocycleConditionι (Z v) (hZ v)⟩ := by
      unfold mixedStageCond
      exact ite_eq_right hvF
    rw [he]
    exact cocycleCondition_localFacts (Z v) (hZ v)

end ActualStages

section BoundaryLift

variable {k : Type u} [CommRing k]

/-- The manuscript's lifting step on the same Selmer datum, using the proved local facts. -/
theorem selmerCone_lift_of_localFacts (D : SelData k) (h : LocalFacts D.ι)
    {p p' : D.G.X 1} {a a' : D.U.X 1} {q q' : D.L.X 0}
    (ha : D.U.d 1 2 rfl a = 0) (ha' : D.U.d 1 2 rfl a' = 0)
    (hpq : D.res.f 1 1 rfl p - D.ι.f 1 1 rfl a = D.L.d 0 1 rfl q)
    (hpq' : D.res.f 1 1 rfl p' - D.ι.f 1 1 rfl a' = D.L.d 0 1 rfl q')
    {g : D.G.X 0} (hg : p - p' = D.G.d 0 1 rfl g) :
    ∃ w : D.U.X 0, D.U.d 0 1 rfl w = a - a' ∧
      D.res.f 0 0 rfl g - D.ι.f 0 0 rfl w = q - q' :=
  ZInQ.Manuscript.RC.BaseZeroAssembly.selmerCone_lift
    (D.G.d 0 1 rfl).toAddMonoidHom (D.U.d 0 1 rfl).toAddMonoidHom
    (D.U.d 1 2 rfl).toAddMonoidHom (D.L.d 0 1 rfl).toAddMonoidHom
    (D.res.f 0 0 rfl).toAddMonoidHom (D.res.f 1 1 rfl).toAddMonoidHom
    (D.ι.f 0 0 rfl).toAddMonoidHom (D.ι.f 1 1 rfl).toAddMonoidHom
    (D.res.comm 0 1 0 1 rfl rfl rfl rfl) (D.ι.comm 0 1 0 1 rfl rfl rfl rfl)
    h.1 h.2 ha ha' hpq hpq' hg

/-- The unchanged finite construction theorem with its two local inputs
supplied by `LocalFacts`. All global construction and cycle inputs are retained. -/
theorem boundary45_finite_of_construction_of_localFacts
    {PGroup : Type} [AddCommGroup PGroup] {P : PGroup} (T : SplitNormStage P)
    (D : SelData k) (hlocal : LocalFacts D.ι)
    {H1 A B C Q : Type*} [AddCommGroup H1] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup Q]
    (cls : D.G.X 1 →+ H1)
    (hexact : ∀ c : D.G.X 1, D.G.d 1 2 rfl c = 0 → cls c = 0 →
      ∃ g : D.G.X 0, D.G.d 0 1 rfl g = c)
    (δ : PGroup →+ H1) (e : ℕ) (Inp : HeegnerAlgebra.InfResInput A B C Q e)
    (κ : T.Pt →+ B) (δa : T.Pt →+ C) (hκ : ∀ x, Inp.seq.res (κ x) = δa x)
    (m0 Cπ Cbad : ℕ) (Tr : B →+ H1) (Wsum : T.Pt →+ PGroup)
    (hWsum : ∀ x, T.incl (Wsum x) = ∑ γ, T.act γ x)
    (hTr : ∀ x, Tr (κ x) = δ (Wsum x))
    {zG jG : D.G.X 1} {zU jU : D.U.X 1} {zL jL : D.L.X 0}
    (hzG : D.G.d 1 2 rfl zG = 0) (hjG : D.G.d 1 2 rfl jG = 0)
    (hzU : D.U.d 1 2 rfl zU = 0) (hjU : D.U.d 1 2 rfl jU = 0)
    (hz : D.res.f 1 1 rfl zG - D.ι.f 1 1 rfl zU = D.L.d 0 1 rfl zL)
    (hj : D.res.f 1 1 rfl jG - D.ι.f 1 1 rfl jU = D.L.d 0 1 rfl jL)
    (hzcls : cls zG =
      Tr (((m0 * Cbad : ℕ) : ℤ) • Inp.seq.descend e Inp.killD (δa ((Cπ : ℤ) • T.yr))))
    (hjcls : cls jG = δ P) :
    ∃ (v : D.G.X 0) (w : D.U.X 0),
      zG - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (T.a - 2)) • jG = D.G.d 0 1 rfl v ∧
      zU - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (T.a - 2)) • jU = D.U.d 0 1 rfl w ∧
      D.res.f 0 0 rfl v - D.ι.f 0 0 rfl w =
        zL - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (T.a - 2)) • jL :=
  ZInQ.Manuscript.RC.BaseZeroAssembly.boundary45_finite_of_construction T
    (D.G.d 0 1 rfl).toAddMonoidHom (D.G.d 1 2 rfl).toAddMonoidHom
    (D.U.d 0 1 rfl).toAddMonoidHom (D.U.d 1 2 rfl).toAddMonoidHom
    (D.L.d 0 1 rfl).toAddMonoidHom
    (D.res.f 0 0 rfl).toAddMonoidHom (D.res.f 1 1 rfl).toAddMonoidHom
    (D.ι.f 0 0 rfl).toAddMonoidHom (D.ι.f 1 1 rfl).toAddMonoidHom
    (D.res.comm 0 1 0 1 rfl rfl rfl rfl) (D.ι.comm 0 1 0 1 rfl rfl rfl rfl)
    hlocal.1 hlocal.2 cls hexact δ e Inp κ δa hκ m0 Cπ Cbad Tr Wsum hWsum hTr
    hzG hjG hzU hjU hz hj hzcls hjcls

end BoundaryLift

end ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local
