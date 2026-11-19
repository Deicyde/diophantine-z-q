import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.TauCeti.RingTheory.Semisimple.DoubleCentralizer
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Trace

/-!
# Semisimple representations and their characters

The algebraic comparison is separated from Frobenius density. The proof uses
Schur's lemma, isotypic submodules, Jacobson density for finite semisimple
modules, and the fact that a nonzero idempotent has nonzero trace in
characteristic zero. These are proved library results, not literature inputs.

The application is the Brauer–Nesbitt step in the Galois comparison used with
Carayol 1986, Théorème (A), pp. 410–411 and §0.8, p. 411. The characteristic
zero hypothesis is essential for recovering multiplicities from traces.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0

section IsotypicHom

variable {R A B S : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S]

omit [IsSimpleModule R S] in
/-- **PROVED**, by generation of a semisimple module by its simple submodules.
Locators: Mathlib `IsSemisimpleModule.sSup_simples_eq_top`,
`IsIsotypicOfType`. If there is no map from the simple type to a module,
there is no map from a semisimple module of that isotypic type either. -/
theorem hom_from_isotypic_eq_zero [IsSemisimpleModule R A]
    (hA : IsIsotypicOfType R A S) (hno : ∀ f : S →ₗ[R] B, f = 0)
    (f : A →ₗ[R] B) : f = 0 := by
  apply LinearMap.ker_eq_top.mp
  rw [← top_le_iff, ← IsSemisimpleModule.sSup_simples_eq_top R A]
  apply sSup_le
  intro m hm
  have : IsSimpleModule R m := hm
  obtain ⟨e⟩ := hA m
  have hzero := hno ((f.comp m.subtype).comp e.symm.toLinearMap)
  intro x hx
  have h := LinearMap.congr_fun hzero (e ⟨x, hx⟩)
  simpa using h

/-- **PROVED**, by Schur's lemma and simple-submodule generation.
Locators: Mathlib `LinearMap.exists_ne_zero_of_sSup_eq_top`,
`LinearMap.injective_of_ne_zero`, `IsIsotypicOfType`.
A semisimple source admitting no map from the simple type admits no map
into a semisimple module of that isotypic type. -/
theorem hom_to_isotypic_eq_zero [IsSemisimpleModule R B]
    (hA : IsIsotypicOfType R A S) (hno : ∀ f : S →ₗ[R] B, f = 0)
    (f : B →ₗ[R] A) : f = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm, hfm⟩ := LinearMap.exists_ne_zero_of_sSup_eq_top hne _
    (IsSemisimpleModule.sSup_simples_eq_top R B)
  have : IsSimpleModule R m := hm
  let l : m →ₗ[R] A := f.comp m.subtype
  have hl : Function.Injective l := LinearMap.injective_of_ne_zero hfm
  let e : m ≃ₗ[R] LinearMap.range l := LinearEquiv.ofInjective l hl
  have : IsSimpleModule R (LinearMap.range l) := IsSimpleModule.congr e.symm
  obtain ⟨eS⟩ := hA (LinearMap.range l)
  let j : S →ₗ[R] B := m.subtype.comp (e.trans eS).symm.toLinearMap
  have hj : Function.Injective j := m.subtype_injective.comp (e.trans eS).symm.injective
  have hj0 := hno j
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  apply hs
  apply hj
  rw [hj0]
  simp

end IsotypicHom

section CentralProjection

variable {R A B : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- **DEFINITION**, the first projection on a direct sum, considered as an
endomorphism. Locator: Mathlib `LinearMap.inl`, `LinearMap.fst`. -/
def firstProjection : Module.End R (A × B) :=
  LinearMap.inl R A B ∘ₗ LinearMap.fst R A B

/-- **PROVED**, by the four blocks of a direct-sum endomorphism.
Locator: the definition of `firstProjection`. When both off-diagonal Hom
spaces vanish, the projection commutes with every equivariant endomorphism. -/
theorem firstProjection_commutes
    (hAB : ∀ f : A →ₗ[R] B, f = 0) (hBA : ∀ f : B →ₗ[R] A, f = 0)
    (f : Module.End R (A × B)) (v : A × B) :
    firstProjection (R := R) (A := A) (B := B) (f v) =
      f (firstProjection (R := R) (A := A) (B := B) v) := by
  rcases v with ⟨x, y⟩
  have h21 := hAB ((LinearMap.snd R A B).comp (f.comp (LinearMap.inl R A B)))
  have h12 := hBA ((LinearMap.fst R A B).comp (f.comp (LinearMap.inr R A B)))
  have h21' : (f (x, 0)).2 = 0 := LinearMap.congr_fun h21 x
  have h12' : (f (0, y)).1 = 0 := LinearMap.congr_fun h12 y
  have hsum : f (x, y) = f (x, 0) + f (0, y) := by
    rw [← map_add]
    congr 1
    simp
  apply Prod.ext
  · change (f (x, y)).1 = (f (x, 0)).1
    rw [hsum]
    simp [h12']
  · change 0 = (f (x, 0)).2
    exact h21'.symm

variable {K : Type*} [Field K] [Algebra K R]
    [Module K A] [IsScalarTower K R A] [SMulCommClass R K A]
    [Module K B] [IsScalarTower K R B] [SMulCommClass R K B]
    [FiniteDimensional K A] [FiniteDimensional K B]
    [IsSemisimpleModule R A] [IsSemisimpleModule R B]

include K in
omit [Algebra K R] [IsScalarTower K R A] [IsScalarTower K R B] in
/-- **PROVED**, by Jacobson density on the semisimple direct sum.
Locator: Mathlib `Module.Finite.toModuleEnd_moduleEnd_surjective`.
If the off-diagonal Hom spaces vanish, some element of the acting ring
acts by the identity on the first summand and by zero on the second. -/
theorem exists_scalar_first_projection
    (hAB : ∀ f : A →ₗ[R] B, f = 0) (hBA : ∀ f : B →ₗ[R] A, f = 0) :
    ∃ r : R, (∀ x : A, r • x = x) ∧ ∀ y : B, r • y = 0 := by
  let M := A × B
  let D := Module.End R M
  have : Module.Finite D M := Module.Finite.of_restrictScalars_finite K D M
  let P : Module.End D M :=
    { toFun := firstProjection (R := R) (A := A) (B := B)
      map_add' := (firstProjection (R := R) (A := A) (B := B)).map_add
      map_smul' := fun f v => by
        change firstProjection (R := R) (A := A) (B := B) (f v) =
          f (firstProjection (R := R) (A := A) (B := B) v)
        exact firstProjection_commutes hAB hBA f v }
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := M) P
  refine ⟨r, fun x => ?_, fun y => ?_⟩
  · exact congrArg Prod.fst (LinearMap.congr_fun hr (x, 0))
  · exact congrArg Prod.snd (LinearMap.congr_fun hr (0, y))

end CentralProjection

section ActionTraces

variable (K R V : Type*) [Field K] [Ring R] [Algebra K R]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower K R V] [SMulCommClass R K V]

/-- **DEFINITION**, the trace of the ring action on a vector space.
Locator: Mathlib `Module.toModuleEnd` and `LinearMap.trace`.
For a group representation this is the linear extension of its character
to the group algebra. -/
def actionTrace (r : R) : K :=
  LinearMap.trace K V (Module.toModuleEnd K V (S := R) r)

omit [Algebra K R] [IsScalarTower K R V] in
/-- **PROVED**, because the ring identity acts as the vector-space identity.
Locator: Mathlib `LinearMap.trace_one`. -/
theorem actionTrace_one [FiniteDimensional K V] :
    actionTrace K R V 1 = (Module.finrank K V : K) := by
  unfold actionTrace
  rw [map_one, LinearMap.trace_one]

variable {K R V} {W : Type*} [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower K R W] [SMulCommClass R K W]

/-- **PROVED**, by conjugating the acting endomorphism through an equivariant
linear isomorphism. Locator: Mathlib `LinearMap.trace_conj'`.
The action traces of isomorphic modules agree. -/
theorem actionTrace_congr (e : V ≃ₗ[R] W) (r : R) :
    actionTrace K R V r = actionTrace K R W r := by
  let eK := e.restrictScalars K
  have hc : eK.conj (Module.toModuleEnd K V (S := R) r) =
      Module.toModuleEnd K W (S := R) r := by
    ext w
    change e (r • e.symm w) = r • w
    rw [e.map_smul]
    simp
  exact (LinearMap.trace_conj' (Module.toModuleEnd K V (S := R) r) eK).symm.trans
    (congrArg (LinearMap.trace K W) hc)

omit [Algebra K R] [IsScalarTower K R V] [IsScalarTower K R W] in
/-- **PROVED**, by the block-diagonal trace formula; locator:
Mathlib `LinearMap.trace_prodMap'`. Action traces are additive under direct sums. -/
theorem actionTrace_prod [FiniteDimensional K V] [FiniteDimensional K W] (r : R) :
    actionTrace K R (V × W) r = actionTrace K R V r + actionTrace K R W r := by
  unfold actionTrace
  exact LinearMap.trace_prodMap' (Module.toModuleEnd K V (S := R) r)
    (Module.toModuleEnd K W (S := R) r)

end ActionTraces

section CommonConstituent

variable {K R V W : Type*} [Field K] [CharZero K] [Ring R] [Algebra K R]
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower K R V] [SMulCommClass R K V] [FiniteDimensional K V]
    [IsSemisimpleModule R V]
    [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower K R W] [SMulCommClass R K W] [FiniteDimensional K W]
    [IsSemisimpleModule R W]

omit [IsScalarTower K R W] in
/-- **PROVED**, by an isotypic-component projection and Jacobson density.
Locators: Mathlib `IsIsotypicOfType.isotypicComponent`,
`Submodule.le_isotypicComponent`, and `exists_scalar_first_projection`.
Equal action traces force every simple constituent of the first semisimple
module to occur in the second; the projection's positive dimension cannot
vanish in characteristic zero. -/
theorem exists_nonzero_hom_of_actionTrace_eq
    (htr : ∀ r : R, actionTrace K R V r = actionTrace K R W r)
    (S : Submodule R V) [IsSimpleModule R S] :
    ∃ f : S →ₗ[R] W, f ≠ 0 := by
  classical
  by_contra hno
  push Not at hno
  let A : Submodule R V := isotypicComponent R V S
  have hA : IsIsotypicOfType R A S := IsIsotypicOfType.isotypicComponent R V S
  have hA0 : A ≠ ⊥ := (bot_lt_isotypicComponent S).ne'
  have : Nontrivial A := Submodule.nontrivial_iff_ne_bot.mpr hA0
  obtain ⟨B, hAB⟩ := exists_isCompl A
  have : FiniteDimensional K A :=
    Module.Finite.of_injective (A.subtype.restrictScalars K) A.subtype_injective
  have : FiniteDimensional K B :=
    Module.Finite.of_injective (B.subtype.restrictScalars K) B.subtype_injective
  have hSB : ∀ f : S →ₗ[R] B, f = 0 := by
    intro f
    by_cases hf : f = 0
    · exact hf
    let l : S →ₗ[R] V := B.subtype.comp f
    have hl : Function.Injective l := B.subtype_injective.comp
      (LinearMap.injective_of_ne_zero hf)
    have hTA : LinearMap.range l ≤ A :=
      le_sSup ⟨(LinearEquiv.ofInjective l hl).symm⟩
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hAB.disjoint) (f s : V)
      (hTA ⟨s, rfl⟩) (f s).2
  have hSC : ∀ f : S →ₗ[R] (B × W), f = 0 := by
    intro f
    apply LinearMap.ext
    intro s
    apply Prod.ext
    · exact LinearMap.congr_fun (hSB ((LinearMap.fst R B W).comp f)) s
    · exact LinearMap.congr_fun (hno ((LinearMap.snd R B W).comp f)) s
  have hAC : ∀ f : A →ₗ[R] (B × W), f = 0 := hom_from_isotypic_eq_zero hA hSC
  have hCA : ∀ f : (B × W) →ₗ[R] A, f = 0 := hom_to_isotypic_eq_zero hA hSC
  obtain ⟨r, hrA, hrC⟩ := exists_scalar_first_projection (K := K) hAC hCA
  have hrB : ∀ b : B, r • b = 0 := fun b => congrArg Prod.fst (hrC (b, 0))
  have hrW : ∀ w : W, r • w = 0 := fun w => congrArg Prod.snd (hrC (0, w))
  have hAt : actionTrace K R A r = (Module.finrank K A : K) := by
    have hmap : Module.toModuleEnd K A (S := R) r = 1 := LinearMap.ext hrA
    rw [actionTrace, hmap, LinearMap.trace_one]
  have hBt : actionTrace K R B r = 0 := by
    have hmap : Module.toModuleEnd K B (S := R) r = 0 := LinearMap.ext hrB
    rw [actionTrace, hmap, map_zero]
  have hWt : actionTrace K R W r = 0 := by
    have hmap : Module.toModuleEnd K W (S := R) r = 0 := LinearMap.ext hrW
    rw [actionTrace, hmap, map_zero]
  have hVt : actionTrace K R V r = (Module.finrank K A : K) := by
    rw [actionTrace_congr (A.prodEquivOfIsCompl B hAB).symm r,
      actionTrace_prod, hAt, hBt, add_zero]
  have hz : (Module.finrank K A : K) = 0 := hVt.symm.trans ((htr r).trans hWt)
  have hz' : Module.finrank K A = 0 := by exact_mod_cast hz
  exact (not_subsingleton A) (Module.finrank_zero_iff.mp hz')

end CommonConstituent

/-- **PROVED**, by induction on dimension after extracting a common simple
constituent. Locators: `exists_nonzero_hom_of_actionTrace_eq`, Mathlib
`Submodule.prodEquivOfIsCompl`, and `LinearMap.trace_prodMap'`.
Finite-dimensional semisimple modules over a characteristic-zero algebra
with equal action traces are isomorphic. No algebraic-closure or finite-group
hypothesis is required. -/
theorem semisimple_actionTrace_comparison (K R : Type) [Field K] [CharZero K]
    [Ring R] [Algebra K R] (V W : Type)
    [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower K R V] [SMulCommClass R K V] [FiniteDimensional K V]
    [IsSemisimpleModule R V]
    [AddCommGroup W] [Module K W] [Module R W]
    [IsScalarTower K R W] [SMulCommClass R K W] [FiniteDimensional K W]
    [IsSemisimpleModule R W]
    (htr : ∀ r : R, actionTrace K R V r = actionTrace K R W r) :
    Nonempty (V ≃ₗ[R] W) := by
  classical
  have main : ∀ n : ℕ, ∀ (V W : Type)
      [AddCommGroup V] [Module K V] [Module R V]
      [IsScalarTower K R V] [SMulCommClass R K V] [FiniteDimensional K V]
      [IsSemisimpleModule R V]
      [AddCommGroup W] [Module K W] [Module R W]
      [IsScalarTower K R W] [SMulCommClass R K W] [FiniteDimensional K W]
      [IsSemisimpleModule R W],
      Module.finrank K V = n →
      (∀ r : R, actionTrace K R V r = actionTrace K R W r) →
        Nonempty (V ≃ₗ[R] W) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro V W iVA iVK iVR iVT iVC iVF iVS iWA iWK iWR iWT iWC iWF iWS hdim htrace
      rcases subsingleton_or_nontrivial V with hV | hV
      · have : Subsingleton V := hV
        have ht := htrace (1 : R)
        rw [actionTrace_one, actionTrace_one] at ht
        have hv' : Module.finrank K V = 0 := Module.finrank_zero_iff.mpr hV
        rw [hv', Nat.cast_zero] at ht
        have hw : (Module.finrank K W : K) = 0 := ht.symm
        have hw' : Module.finrank K W = 0 := by exact_mod_cast hw
        have : Subsingleton W := Module.finrank_zero_iff.mp hw'
        exact ⟨LinearEquiv.ofSubsingleton V W⟩
      · have : Nontrivial V := hV
        obtain ⟨S, _hS, hSsimple⟩ :=
          (IsSemisimpleModule.eq_bot_or_exists_simple_le (⊤ : Submodule R V)).resolve_left
            top_ne_bot
        have : IsSimpleModule R S := hSsimple
        have : Nontrivial S := IsSimpleModule.nontrivial R S
        have : FiniteDimensional K S :=
          Module.Finite.of_injective (S.subtype.restrictScalars K) S.subtype_injective
        obtain ⟨f, hf⟩ := exists_nonzero_hom_of_actionTrace_eq htrace S
        let T : Submodule R W := LinearMap.range f
        have : FiniteDimensional K T :=
          Module.Finite.of_injective (T.subtype.restrictScalars K) T.subtype_injective
        let eS : S ≃ₗ[R] T := LinearEquiv.ofInjective f (LinearMap.injective_of_ne_zero hf)
        have : IsSimpleModule R T := IsSimpleModule.congr eS.symm
        obtain ⟨SV, hSV⟩ := exists_isCompl S
        obtain ⟨TW, hTW⟩ := exists_isCompl T
        have : FiniteDimensional K SV :=
          Module.Finite.of_injective (SV.subtype.restrictScalars K) SV.subtype_injective
        have : FiniteDimensional K TW :=
          Module.Finite.of_injective (TW.subtype.restrictScalars K) TW.subtype_injective
        let eV : (S × SV) ≃ₗ[R] V := S.prodEquivOfIsCompl SV hSV
        let eW : (T × TW) ≃ₗ[R] W := T.prodEquivOfIsCompl TW hTW
        have hVtr : ∀ r : R, actionTrace K R V r =
            actionTrace K R S r + actionTrace K R SV r := fun r =>
          (actionTrace_congr eV.symm r).trans (actionTrace_prod r)
        have hWtr : ∀ r : R, actionTrace K R W r =
            actionTrace K R T r + actionTrace K R TW r := fun r =>
          (actionTrace_congr eW.symm r).trans (actionTrace_prod r)
        have hcomp : ∀ r : R, actionTrace K R SV r = actionTrace K R TW r := by
          intro r
          have h := htrace r
          rw [hVtr r, hWtr r, ← actionTrace_congr eS r] at h
          exact add_left_cancel h
        have hsum : Module.finrank K S + Module.finrank K SV = Module.finrank K V := by
          simpa only [Module.finrank_prod] using (eV.restrictScalars K).finrank_eq
        have hpos : 0 < Module.finrank K S := by
          apply Nat.pos_of_ne_zero
          intro hz
          exact (not_subsingleton S) (Module.finrank_zero_iff.mp hz)
        have hsmall : Module.finrank K SV < n := by omega
        obtain ⟨eComp⟩ := ih (Module.finrank K SV) hsmall SV TW rfl hcomp
        exact ⟨(eV.symm.trans (eS.prodCongr eComp)).trans eW⟩
  exact main (Module.finrank K V) V W rfl htr

section GroupCharacters

variable {K G V W : Type*} [Field K] [Monoid G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **PROVED**, by the canonical linear equivalence of the representation
with its group-algebra module. Locator: Mathlib `Representation.asModuleEquiv`.
The action trace is the trace of the integrated representation. -/
theorem actionTrace_asModule (ρ : Representation K G V) (a : MonoidAlgebra K G) :
    actionTrace K (MonoidAlgebra K G) ρ.asModule a =
      LinearMap.trace K V (ρ.asAlgebraHom a) := by
  have hc : ρ.asModuleEquiv.conj
      (Module.toModuleEnd K ρ.asModule (S := MonoidAlgebra K G) a) =
        ρ.asAlgebraHom a := by
    ext v
    rfl
  exact (LinearMap.trace_conj'
    (Module.toModuleEnd K ρ.asModule (S := MonoidAlgebra K G) a) ρ.asModuleEquiv).symm.trans
      (congrArg (LinearMap.trace K V) hc)

/-- **PROVED**, by linearity on the group-algebra basis; locator:
Mathlib `Representation.asAlgebraHom_single`.
Equality of characters extends to equality of traces on the entire group algebra. -/
theorem trace_on_groupAlgebra_eq (ρ : Representation K G V) (σ : Representation K G W)
    (htr : ∀ g : G, LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g))
    (a : MonoidAlgebra K G) :
    LinearMap.trace K V (ρ.asAlgebraHom a) =
      LinearMap.trace K W (σ.asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g c =>
    simp only [Representation.asAlgebraHom_single, map_smul, htr g]

end GroupCharacters

/-- **PROVED BRAUER–NESBITT**, characteristic-zero trace form, at precisely
the existing proposition `GlueC10.BrauerNesbittChar0`.
Locators: `semisimple_actionTrace_comparison`, `actionTrace_asModule`,
`trace_on_groupAlgebra_eq`. The statement is now proved, not assumed as a
literature input or as a substitute for the newform conclusion. -/
theorem brauerNesbittChar0 : GlueC10.BrauerNesbittChar0 := by
  intro K G V W iK iChar iG iV iKV iFinV iW iKW iFinW ρ σ hρ hσ htr
  have : IsSemisimpleModule (MonoidAlgebra K G) ρ.asModule := hρ
  have : IsSemisimpleModule (MonoidAlgebra K G) σ.asModule := hσ
  apply semisimple_actionTrace_comparison K (MonoidAlgebra K G) ρ.asModule σ.asModule
  intro a
  rw [actionTrace_asModule, actionTrace_asModule]
  exact trace_on_groupAlgebra_eq ρ σ htr a

/-- **PROVED**, by the closed Čebotarev density theorem and the proved
Brauer–Nesbitt theorem. Locators: `Contrib/Chebotarev/Exists.lean`,
`chebotarevExists_c10`, `brauerNesbittChar0`, and `GlueC10.iso_of_trace_eq_on_frob`.
Two actual continuous semisimple Galois representations with equal traces
at arithmetic Frobenius outside a finite set are isomorphic. -/
theorem galois_comparison_from_frobenius
    (K V W ι κ : Type) [Field K] [CharZero K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι K V) (bW : Module.Basis κ K W)
    (ρ : Representation K GlueC10.GQ V) (σ : Representation K GlueC10.GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra K GlueC10.GQ) σ.asModule)
    (S : Finset ℕ)
    (htr : ∀ g p, p.Prime → p ∉ S → GlueC10.IsFrobAt g p →
      LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra K GlueC10.GQ] σ.asModule) :=
  GlueC10.iso_of_trace_eq_on_frob brauerNesbittChar0 S
    (GlueC10.frobDense ZInQ.Contrib.chebotarevExists_c10 S)
    K V W ι κ bV bW ρ σ hρc hσc hρ hσ htr

end ZInQ.Contrib.RC53Assist.NewformGlueG0
