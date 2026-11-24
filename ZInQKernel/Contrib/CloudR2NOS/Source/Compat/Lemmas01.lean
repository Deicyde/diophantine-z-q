/-
Lean 4.35 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 compatibility lemmas (group 01) for
the H5 lane4 port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
whose source was written against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.

Each declaration restates, with the SAME name and statement, a Mathlib db584 lemma whose name
Mathlib 56a reused for a different statement or whose signature it changed, proved from the
Mathlib 56a API.  Isolated beneath the port prefix `ZInQ.Contrib.CloudW03NeronSurj.FLT`; no axiom.
Statements are from Mathlib (Apache License 2.0) at db584cd6:
  * `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`, Mathlib/RingTheory/Ideal/GoingUp.lean
    (Mathlib 56a: this name now takes a ring hom; the algebra form is `isMaximal_under_…`);
  * `Cardinal.nat_lt_aleph0`, Mathlib/SetTheory/Cardinal/Basic.lean
    (Mathlib 56a: renamed `natCast_lt_aleph0`, now with implicit `n`).
NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14: statements copied; proofs
replaced by one-line references to the Mathlib 56a lemmas.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

universe u

namespace Ideal

theorem isMaximal_comap_of_isIntegral_of_isMaximal {R : Type*} [CommRing R] {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] (I : _root_.Ideal S)
    [hI : I.IsMaximal] : _root_.Ideal.IsMaximal (I.comap (algebraMap R S)) :=
  _root_.Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) I

end Ideal

namespace Cardinal

theorem nat_lt_aleph0 (n : ℕ) : (n : _root_.Cardinal.{u}) < _root_.Cardinal.aleph0 :=
  _root_.Cardinal.natCast_lt_aleph0

end Cardinal

end ZInQ.Contrib.CloudW03NeronSurj.FLT
