/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.PullbackStalk
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Pullback of sheaves of modules along a stalkwise flat morphism is left exact

Material for `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`; see `README.md`
on the mirror tree. It is the other half of
`Oka/Algebra/Category/ModuleCat/Sheaf/PullbackStalk.lean`:

```
SheafOfModules.preservesFiniteLimits_pullback
    (hflat : ∀ x, (PresheafOfModules.ringStalkMap f φ x).hom.Flat) :
  PreservesFiniteLimits (pullback (sheafRingHom φ))
```

Right exactness of `SheafOfModules.pullback` is free — it is a left adjoint — so this is the
whole of its exactness, and **it is where flatness is consumed**. The base-change formula of
`Oka/Algebra/Category/ModuleCat/Sheaf/PullbackStalk.lean` uses none — and the path is written out
because `Oka/Algebra/Category/ModuleCat/Presheaf/PullbackStalk.lean` states the same result one
level down, so the file name alone names two files.

## The route, and it is monomorphisms rather than short complexes

A right-exact additive functor between abelian categories is exact as soon as it preserves
monomorphisms (`CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels`, then
`CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology`). So the only thing to prove
is `PreservesMonomorphisms`, and monomorphisms of sheaves of modules are detected on stalks:

* `SheafOfModules.preservesMonomorphisms_stalkFunctor` — the module-valued stalk functor
  preserves monomorphisms, because the `AddCommGrpCat`-valued one does
  (`Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean`) and `forget₂` reflects them. **The two
  stalk functors agree by `rfl`**, which is what makes this one line rather than a transport;
* `SheafOfModules.mono_of_forall_mono_stalkFunctor_map` — the converse, from
  `SheafOfModules.exact_of_stalk_exact` applied to `0 ⟶ M ⟶ N` together with
  `CategoryTheory.ShortComplex.exact_iff_mono`.

Given those, the proof is: transport along `SheafOfModules.pullbackStalkIso`, and observe that
`ModuleCat.extendScalars` along a flat ring map preserves monomorphisms because it preserves
finite limits (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
`Mathlib/Algebra/Category/ModuleCat/Descent.lean`).

**The short-complex route is available and is longer.** Concluding from `S.Exact` that the stalks
are exact needs `SheafOfModules.toSheaf` to be *right* exact as well, which at `v4.32.0` — the
revision `lakefile.toml` pins, resolved by `lake-manifest.json` to
`81a5d257c8e410db227a6665ed08f64fea08e997` — Mathlib does not have; going through monomorphisms
needs only the direction that is there.

**That absence is measured in this repository already, and this sentence points at the run rather
than repeating the claim.** `Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean`'s passage on the
converse of `SheafOfModules.exact_of_stalk_exact` carries the instrument, the verdict and a
positive control: Mathlib has `CategoryTheory.Limits.PreservesFiniteLimits` for that functor
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`) and `inferInstance` fails on both
`CategoryTheory.Limits.PreservesFiniteColimits` and `CategoryTheory.Functor.PreservesHomology`.
**That passage is named here by what it is about and not by where it sits**, because a pointer
into another file's structure is falsified by any rearrangement of that file; at `6a792ba` it is
the first bullet of that file's `## What is not here`.
**That passage carried no version when this sentence was written, on 2026-09-21**; repairing it
is a change to a file this push only reads, and is filed as taxis #2152.

**The absence is Mathlib's and not this repository's, and when this sentence was written, on
2026-09-21, that passage did not say so.**
`Oka/Algebra/Category/ModuleCat/Sheaf/Colimits.lean` declares
`SheafOfModules.preservesFiniteColimits_toSheaf`, so `inferInstance` for
`CategoryTheory.Limits.PreservesFiniteColimits (SheafOfModules.toSheaf R)` **succeeds** under
`import Oka` and **fails** under `import Mathlib` alone at the revision above; both were run.
So what makes the short-complex route longer *here* is not that nobody has proved right
exactness — it is that **this file does not import that module**, while the monomorphism route
needs no import this file does not already have. **That passage then said *So the converse is a
theorem someone has to prove and not a transfer*, which a module of this repository two days
older than the file it sits in refutes**; repairing it is filed as taxis #2152, and that module
is out of scope here as well. At `6a792ba` that is the fourth of its five sentences and not its
last, and `git show 6a792ba:Oka/Algebra/Category/ModuleCat/Sheaf/Stalk.lean` carries it at
`:84–85`, wrapped after *has to*.

**That clause read *which Mathlib does not have (recorded in `Sheaf/Stalk.lean`)* until
2026-09-22**, with no version and with a pointer naming a file rather than the passage in it;
`git show c6bfc1f:Oka/Algebra/Category/ModuleCat/Sheaf/PullbackExact.lean` carries the retired
wording at `:52–53`, wrapped after *does not have*. **The claim is unchanged and only its warrant
is.**

## The check this file is built to pass

*A proof of left exactness that consumes no flatness is proving something false*: pullback along
an arbitrary morphism of ringed spaces is not left exact. **Measured**: deleting
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hflat x)` from
`preservesMonomorphisms_pullback` makes that proof, and nothing else in this file, fail with
`failed to synthesize (ModuleCat.extendScalars _).PreservesMonomorphisms`. So flatness enters at
exactly one place and it is the expected one.

## Main results

- `SheafOfModules.preservesMonomorphisms_stalkFunctor`,
  `SheafOfModules.mono_of_forall_mono_stalkFunctor_map`: monomorphisms of sheaves of modules on a
  space are exactly those that are monomorphisms on every stalk.
- `SheafOfModules.preservesMonomorphisms_pullback`.
- `SheafOfModules.preservesFiniteLimits_pullback`: **the theorem.**

## What is not here

* **Faithful flatness.** Only flatness is used. What faithful flatness would additionally give —
  that the pullback reflects isomorphisms — is
  `ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat` stalkwise, and nothing here
  needs it.
* **Coherence.** No finiteness hypothesis on the sheaves appears anywhere; the statement is for
  all sheaves of modules.
-/

open CategoryTheory Limits TopologicalSpace Opposite ZeroObject

universe u

noncomputable section

namespace SheafOfModules

section

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  {hR : TopCat.Presheaf.IsSheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- **The module-valued stalk functor preserves monomorphisms.**

The `AddCommGrpCat`-valued stalk functor does, because it preserves finite limits; the two agree
by `rfl` — `stalkFunctor x ⋙ forget₂ _ AddCommGrpCat` *is*
`SheafOfModules.stalkFunctorAddCommGrp x` — and `forget₂` is faithful, hence reflects
monomorphisms. -/
instance preservesMonomorphisms_stalkFunctor (x : X) :
    (stalkFunctor (hR := hR) x).PreservesMonomorphisms where
  preserves {M N} g hg := by
    have h1 : Mono ((stalkFunctorAddCommGrp (R := ofCommRingCat R hR) x).map g) :=
      inferInstance
    exact (forget₂ (ModuleCat.{u} (R.stalk x)) AddCommGrpCat.{u}).mono_of_mono_map h1

/-- **A morphism of sheaves of modules which is a monomorphism on every stalk is a
monomorphism.**

`SheafOfModules.exact_of_stalk_exact` applied to the short complex `0 ⟶ M ⟶ N`, whose exactness
is `Mono` at both ends by `CategoryTheory.ShortComplex.exact_iff_mono`. -/
theorem mono_of_forall_mono_stalkFunctor_map {M N : SheafOfModules.{u} (ofCommRingCat R hR)}
    (g : M ⟶ N) (hm : ∀ x : X, Mono ((stalkFunctor (hR := hR) x).map g)) : Mono g := by
  have hS : (ShortComplex.mk (0 : (0 : SheafOfModules.{u} (ofCommRingCat R hR)) ⟶ M) g
      (by simp)).Exact := by
    refine exact_of_stalk_exact _ fun x ↦ ?_
    refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
    · exact Functor.map_zero (stalkFunctorAddCommGrp (R := ofCommRingCat R hR) x) _ _
    · have := hm x
      exact inferInstanceAs (Mono ((forget₂ (ModuleCat.{u} (R.stalk x)) AddCommGrpCat.{u}).map
        ((stalkFunctor (hR := hR) x).map g)))
  exact (ShortComplex.exact_iff_mono _ (by simp)).1 hS

end

section


variable {X Y : TopCat.{u}} {f : X ⟶ Y} {S : Y.Presheaf CommRingCat.{u}}
  {R : X.Presheaf CommRingCat.{u}}
  {hS : TopCat.Presheaf.IsSheaf (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  {hR : TopCat.Presheaf.IsSheaf (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  (φ : S ⟶ (Opens.map f).op ⋙ R)

/-- **If every stalk map is flat, the pullback of sheaves of modules preserves
monomorphisms.** -/
theorem preservesMonomorphisms_pullback
    (hflat : ∀ x : X, ((PresheafOfModules.ringStalkMap f φ x).hom).Flat) :
    (pullback (sheafRingHom (hS := hS) (hR := hR) φ)).PreservesMonomorphisms where
  preserves {M N} g hg := by
    refine mono_of_forall_mono_stalkFunctor_map _ fun x ↦ ?_
    have hfl := ModuleCat.preservesFiniteLimits_extendScalars_of_flat.{u} (hflat x)
    have h1 : (stalkFunctor (hR := hS) (f x) ⋙
        ModuleCat.extendScalars (PresheafOfModules.ringStalkMap f φ x).hom
          ).PreservesMonomorphisms := by
      have : (ModuleCat.extendScalars.{u, u, u}
          (PresheafOfModules.ringStalkMap f φ x).hom).PreservesMonomorphisms :=
        inferInstance
      infer_instance
    have h2 := Functor.preservesMonomorphisms.of_iso
      (pullbackStalkIso (hS := hS) (hR := hR) φ x).symm
    exact h2.preserves g

/-- **If every stalk map is flat, the pullback of sheaves of modules is left exact.** -/
theorem preservesFiniteLimits_pullback
    (hflat : ∀ x : X, ((PresheafOfModules.ringStalkMap f φ x).hom).Flat) :
    PreservesFiniteLimits (pullback (sheafRingHom (hS := hS) (hR := hR) φ)) := by
  have h0 : (pullback (sheafRingHom (hS := hS) (hR := hR) φ)).PreservesMonomorphisms :=
    preservesMonomorphisms_pullback φ hflat
  have hp : (pushforward (sheafRingHom (hS := hS) (hR := hR) φ)).Additive := ⟨rfl⟩
  have h1 : (pullback (sheafRingHom (hS := hS) (hR := hR) φ)).Additive :=
    (pullbackPushforwardAdjunction (sheafRingHom (hS := hS) (hR := hR) φ)).left_adjoint_additive
  have h2 : (pullback (sheafRingHom (hS := hS) (hR := hR) φ)).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end

end SheafOfModules
