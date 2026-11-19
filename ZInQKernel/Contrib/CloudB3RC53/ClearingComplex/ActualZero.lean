import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.FullConditionNonVacuity

/-!
# Selmer complexes of the zero coefficient module with a model local condition

Tools for an actual instance of `Identification3` at `Q = ∅` (`ActualQEmpty.lean`):

* `bijGHom_quasiIso`: a relation-indexed chain map with bijective components is a
  quasi-isomorphism (an isomorphism of complexes);
* `selModelMap`, `selModelMap_bijective`: for Selmer data `G --res--> L <--ι-- U` whose global and
  local complexes vanish degreewise (subsingleton terms), a chain map `φ : A → U` with bijective
  components gives the bijective chain map `A → C(U)`, `x ↦ (0, φ x, 0)`;
* `atPlace v₀ v A`: the complex `A` at the place `v₀` and zero elsewhere (terms
  `PLift (v = v₀) → A^n`); `atPlaceMap`: `A → ∏_v atPlace v₀ v A`, bijective;
* `subsingleton_contCochains`, `subsingleton_natCx`: continuous cochains with values in a
  subsingleton module vanish.

All statements are PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex (natCx natX contCochains contSubCx piCx asFun contCochain)

universe u

variable {k : Type u} [CommRing k]

/-- **A chain map with bijective components is a quasi-isomorphism.** -/
theorem bijGHom_quasiIso {A B : GCx k} (φ : GHom A B) (h : ∀ n, Function.Bijective (φ.f n n rfl)) :
    QuasiIso (SelmerDuality.GHom.toCC φ) := by
  have : ∀ n, IsIso ((SelmerDuality.GHom.toCC φ).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (h n)
  have : IsIso (SelmerDuality.GHom.toCC φ) := HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-! ### Selmer data with vanishing global and local complexes -/

section SelModel

variable (D : SelData k) {A : GCx k} (φ : GHom A D.U)
  (hG : ∀ n, Subsingleton (D.G.X n)) (hL : ∀ n, Subsingleton (D.L.X n))

/-- The components `x ↦ (0, φ x, 0)`. -/
def selModelLin (n : ℤ) : A.X n →ₗ[k] selT D n :=
  LinearMap.prod 0 (LinearMap.prod (φ.f n n rfl) 0)

include hG hL in
/-- **The chain map `A → C(U)`, `x ↦ (0, φ x, 0)`.** -/
def selModelMap : GHom A (selCx D) where
  f i j h := by subst h; exact selModelLin D φ i
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    refine Prod.ext ((hG _).elim _ _) (Prod.ext ?_ ((hL _).elim _ _))
    exact φ.comm i (i + 1) i (i + 1) rfl rfl rfl rfl x

include hG hL in
theorem selModelMap_bijective (hφ : ∀ n, Function.Bijective (φ.f n n rfl)) (n : ℤ) :
    Function.Bijective ((selModelMap D φ hG hL).f n n rfl) := by
  constructor
  · intro x y hxy
    exact (hφ n).1 (congrArg (fun c : selT D n => c.2.1) hxy)
  · intro c
    obtain ⟨a, u, z⟩ := c
    obtain ⟨x, rfl⟩ := (hφ n).2 u
    exact ⟨x, Prod.ext ((hG n).elim _ _) (Prod.ext rfl ((hL _).elim _ _))⟩

end SelModel

/-! ### A complex at one place -/

section AtPlace

variable {ι : Type u} (v₀ : ι) (A : GCx k)

/-- **The complex `A` at the place `v₀`, zero elsewhere**: terms `PLift (v = v₀) → A^n`. -/
def atPlace (v : ι) : GCx k where
  X n := ModuleCat.of k (PLift (v = v₀) → A.X n)
  d i j h := LinearMap.compLeft (A.d i j h) (PLift (v = v₀))
  d_d i j l hij hjl x := funext fun e => A.d_d i j l hij hjl (x e)

/-- The map `A → ∏_v atPlace v₀ v A`. -/
def atPlaceMap : GHom A (piCx (atPlace v₀ A)) where
  f i j h := by
    subst h
    exact LinearMap.pi fun v => LinearMap.pi fun _ => LinearMap.id
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    rfl

theorem atPlaceMap_bijective (n : ℤ) : Function.Bijective ((atPlaceMap v₀ A).f n n rfl) := by
  constructor
  · intro x y hxy
    exact congrFun (congrFun hxy v₀) ⟨rfl⟩
  · intro F
    refine ⟨F v₀ ⟨rfl⟩, funext fun v => funext fun e => ?_⟩
    obtain ⟨rfl⟩ := e
    rfl

end AtPlace

/-! ### Cochains with values in a subsingleton module -/

section Zero

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type u} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]

theorem subsingleton_contCochains [Subsingleton M] (n : ℕ) :
    Subsingleton ((contCochains k G M).X n) :=
  ⟨fun x y => Subtype.ext (funext fun _ => @Subsingleton.elim M _ _ _)⟩

theorem subsingleton_natCx (K : CochainComplex (ModuleCat.{u} k) ℕ)
    (h : ∀ n, Subsingleton (K.X n)) (i : ℤ) : Subsingleton ((natCx K).X i) := by
  match i with
  | Int.ofNat n => exact h n
  | Int.negSucc n => exact (inferInstance : Subsingleton PUnit)

theorem subsingleton_natCx_contCochains [Subsingleton M] (i : ℤ) :
    Subsingleton ((natCx (contCochains k G M)).X i) :=
  subsingleton_natCx _ (subsingleton_contCochains (k := k) (G := G) (M := M)) i

theorem subsingleton_piCx {ι : Type u} (A : ι → GCx k) (h : ∀ v n, Subsingleton ((A v).X n))
    (n : ℤ) : Subsingleton ((piCx A).X n) :=
  ⟨fun x y => funext fun v => (h v n).elim _ _⟩

end Zero

end ZInQ.Contrib.CloudB3RC53.ClearingComplex
