/- Modified for the Z-in-Q kernel (milne-compile, fix 2): `attribute [local instance] Kernel.kernelGroup` added,
since instance search could not find `MonObj` / `IsCommMonObj` on `(Kernel.kernelGrp f.hom).X` (as in `Kernel.lean`). -/
import ZInQKernel.Contrib.OneProof.H.TailQ
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Descent
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.GroupAnnihilator
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Flatness

/-!
# `AvSplit.MilneIsogenyQuasiInverse` (row H-54's published-form leaf)

For every field `K`, abelian varieties `A B : PkgI3.AbVar K` and a homomorphism `f : Hom A B`
whose underlying scheme morphism is finite and surjective, there are `d > 0` and `g : Hom B A`
with `f.hom ≫ g.hom = [d]_A` and `g.hom ≫ f.hom = [d]_B`, as equalities of actual morphisms in
`Over (Spec K)`. No characteristic, perfectness, algebraic closedness or further hypothesis is
added.

Proof (descent along `f`):

1. **Kernel.** `G := pullback f.hom η[B.X]` with the group structure of the represented kernel
   functor (`Kernel.kernelGrp`, ported from openai/math). It is commutative because `A.X` is
   (Mathlib, Stacks 0BFD, instance in `HDecomp/Objects`) and finite over `K` because `f.hom.left`
   is finite (base change).
2. **Annihilator.** `finiteGroup_exists_annihilator` (finite-Hopf rank annihilation, ported from
   openai/math, `GroupAnnihilator.lean`) gives `n > 0` killing every test-object point of `G`;
   `Kernel.pow_eq_one_of_kernelGrp` transfers this through the kernel point bijection to every
   `x : T ⟶ A.X` with `x ≫ f.hom = 1`, for all test schemes `T`, infinitesimal ones included.
3. **Flatness.** `finite_surjective_abVarHom_flat` (`Flatness.lean`) gives `Flat f.hom.left`.
4. **Descent.** `f.hom.left` is flat, surjective and quasi-compact (finite ⇒ affine ⇒
   quasi-compact), so Mathlib's fpqc `EffectiveEpi` instance applies;
   `Descent.FppfPowerComplement.Construction.exists_fppf_power_complement` (ported from
   openai/math) descends `(𝟙 A.X) ^ n` to a homomorphism `r : B.X ⟶ A.X` with
   `f.hom ≫ r = (𝟙 A.X) ^ n` and `r ≫ f.hom = (𝟙 B.X) ^ n` (epi cancellation and group laws).
5. **Packaging.** `g := Hom.mk' r`, `d := n`; `(𝟙 _) ^ n = [n]` by `AvSplit.comp_natCast_hom'`.

Status: compiled by milne-compile on 2026-11-16 at Lean 4.35.0 / Mathlib v4.35.0; one fix (the local
instance `Kernel.kernelGroup` below). `milneIsogenyQuasiInverse_proof` depends only on `propext`,
`Classical.choice` and `Quot.sound`. This file imports `TailQ` (the module declaring the
target), never `ZInQKernel.Contrib.OneProof.Main`.
-/

namespace ZInQ.Contrib.MilneQuasiInverse

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

-- The bundled kernel `Kernel.kernelGrp f.hom` carries the group structure `Kernel.kernelGroup`;
-- `kernelGrp` is reducible, so its `.X` is seen as `kernelObject f.hom` and instance search needs
-- `kernelGroup` as a local instance (as in `Kernel.lean`).
attribute [local instance] ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGroup

/-- **Kernel annihilation for an isogeny of abelian varieties.** Some `n > 0` satisfies
`x ^ n = 1` for every test object `T` over `Spec K` and every `x : T ⟶ A.X` with
`x ≫ f.hom = 1`. -/
theorem isogeny_kernel_annihilator {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : PkgI3.AbVar.Hom A B) (hf : PkgI3.AbVar.IsIsogenyMor f.hom) :
    ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ A.X),
      x ≫ f.hom = 1 → x ^ n = 1 := by
  obtain ⟨hfin, -⟩ := hf
  haveI : AlgebraicGeometry.IsFinite f.hom.left := hfin
  haveI : IsCommMonObj (ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGrp f.hom).X :=
    ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGrp_isCommMonObj f.hom
  haveI : AlgebraicGeometry.IsFinite
      (ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGrp f.hom).X.hom :=
    ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGrp_isFinite f.hom
  obtain ⟨n, hn, hG⟩ := ZInQ.Contrib.MilneQuasiInverse.finiteGroup_exists_annihilator K
    (ZInQ.Contrib.MilneQuasiInverse.Kernel.kernelGrp f.hom)
  exact ⟨n, hn, ZInQ.Contrib.MilneQuasiInverse.Kernel.pow_eq_one_of_kernelGrp f.hom n hG⟩

/-- **`AvSplit.MilneIsogenyQuasiInverse`**, with no added hypothesis: for an isogeny
`f : A → B` (finite and surjective) of abelian varieties over any field there are `d > 0` and a
homomorphism `g : B → A` with `f.hom ≫ g.hom = [d]_A` and `g.hom ≫ f.hom = [d]_B`. -/
theorem milneIsogenyQuasiInverse_proof : _root_.AvSplit.MilneIsogenyQuasiInverse := by
  intro K _ A B f hf
  obtain ⟨n, hn, hker⟩ := isogeny_kernel_annihilator f hf
  haveI : AlgebraicGeometry.Flat f.hom.left :=
    ZInQ.Contrib.MilneQuasiInverse.finite_surjective_abVarHom_flat (f := f) (hf := hf)
  obtain ⟨hfin, hsurj⟩ := hf
  haveI : AlgebraicGeometry.IsFinite f.hom.left := hfin
  haveI : AlgebraicGeometry.Surjective f.hom.left := hsurj
  haveI : AlgebraicGeometry.QuasiCompact f.hom.left := inferInstance
  obtain ⟨r, hr, hfr, hrf⟩ :=
    ZInQ.Contrib.MilneQuasiInverse.Descent.FppfPowerComplement.Construction.exists_fppf_power_complement
      f.hom n hker
  haveI : IsMonHom r := hr
  refine ⟨n, hn, PkgI3.AbVar.Hom.mk' r, ?_, ?_⟩
  · rw [PkgI3.AbVar.Hom.hom_mk']
    exact hfr.trans
      ((_root_.AvSplit.comp_natCast_hom' A (𝟙 A.X) n).symm.trans (Category.id_comp _))
  · rw [PkgI3.AbVar.Hom.hom_mk']
    exact hrf.trans
      ((_root_.AvSplit.comp_natCast_hom' B (𝟙 B.X) n).symm.trans (Category.id_comp _))

end ZInQ.Contrib.MilneQuasiInverse
