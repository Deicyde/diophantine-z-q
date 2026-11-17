/-
Adapted from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
file P2M/Sol/S_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.lean (see Vendor/AnthropicFLT/NOTICE, NOTICE.upstream, ATTRIBUTION.upstream.md and LICENSE).
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): the projective-embedding hypotheses are
removed, the projective algebraization step is replaced by `ProperAlgebraization` (proper schemes),
imports are relocated and the namespace is renamed; every other change is marked `-- [port]`; 160 names of constants that are not in this file's import closure are dropped from its `attribute [-instance]`/`[-simp]` lines (they come from the upstream combined environment).
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_AdicThickening
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3SC2Mumford.Pipeline.MulHom
import ZInQKernel.Contrib.CloudB3SC2Mumford.Pipeline.InvHom
import ZInQKernel.Contrib.CloudB3SC2Mumford.Pipeline.LiftMul
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_mul_eq_inv_eq_of_comp_eq

-- [port] the upstream lakefile options, as for the vendored files
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
namespace ZInQ.Contrib.CloudB3SC2Mumford.Pipeline.Complete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution (hA : ProperAlgebraization.{u}) -- [port]
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hp : IsProper f) -- [port] in place of a projective embedding
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hone : ∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫ adicThickeningι f I n = adicThickeningBase I n ≫ e.1)
    (hcompat : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
      (P Q : SchemeHomOver t (adicThickeningToBase f I n)),
      ((L n).mul t P Q).1 ≫ adicThickeningTransition f I n =
        ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
          ⟨P.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ adicThickeningTransition f I n, by
            rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) :
    ∃ L' : RelativeGroupLaw R f, (L'.one (𝟙 _)).1 = e.1 := by
  obtain ⟨m, hm, hmul⟩ :=
    ZInQ.Contrib.CloudB3SC2Mumford.Pipeline.MulHom.solution hA -- [port] proj-free copy
      I f hp L hcompat
  obtain ⟨i, hi, hinv⟩ :=
    ZInQ.Contrib.CloudB3SC2Mumford.Pipeline.InvHom.solution hA -- [port] proj-free copy
      I f hp L hcompat
  obtain ⟨h1, h2, h3, h4⟩ :=
    ZInQ.Contrib.CloudB3SC2Mumford.Pipeline.LiftMul.solution -- [port] proj-free copy
      I f hp e L hone m hm hmul i hi hinv
  obtain ⟨L', hL', -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_mul_eq_inv_eq_of_comp_eq f e m hm h1 h2 h3 i hi h4
  exact ⟨L', by rw [hL']⟩
