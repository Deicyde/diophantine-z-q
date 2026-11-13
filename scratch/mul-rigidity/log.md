# mul-rigidity results log

## Setup
- 05:22 base 2dd83306; `git merge origin/wip/g0-fibresimple`: already up to date (its files present).
- Source of the Props: scratch/g0-fibresimple/FibreSimple.lean §4″ (`MulIsogeny`) and §4‴ (`RigidityHom`).
  Their `PkgI3` section (Split.lean l.2516-2612) is identical to ZInQKernel/HDecomp/Objects.lean l.154-250
  (VERIFIED by diff), so the scratch files import `ZInQKernel.HDecomp.Objects`.
- `lake build ZInQKernel.HDecomp.Objects`: up to date (OK).

## RigidityHom
- 05:27 COMPILED (exit 0, 7 s): `MulRigidity.rigidity_algClosed` (two-sided rigidity lemma over an algebraically
  closed field: G proper, G ×_K G integral, Z separated lft, c : G ⊗ G ⟶ Z with c(e,·) = z, c(·,e) = z ⇒ c = z).
  Proof = Mathlib's proof of Stacks 0BFD (isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed) with
  the commutator replaced by c and the target G ⊗ G of γ by G ⊗ Z.
- 05:28 COMPILED (exit 0, 8 s): `MulRigidity.isMonHom_of_algClosed` (c = (μ≫h)·((h⊗h)≫μ)⁻¹),
  `MulRigidity.isMonHom_of_geometricallyIntegral` (any field: base change along Spec K̄ → Spec K, `Over.pullback`
  faithful and monoidal, `Functor.grpObjObj`), and **`G0FibreSimple.rigidityHom : G0FibreSimple.RigidityHom`**
  (RigidityHom copied verbatim). `#print axioms`: propext, Classical.choice, Quot.sound. VERIFIED.
  So the textbook leaf RigidityHom is no longer a hypothesis: it is a theorem (only G proper + geometrically
  integral on the source, B separated + locally of finite type on the target are used).

## MulIsogeny (Mul.lean)
- 05:31 COMPILED (exit 0): `locallyQuasiFinite_of_formallyUnramified` (scheme-level, from Mathlib's algebra
  instance EssFiniteType + FormallyUnramified ⇒ Algebra.QuasiFinite), `isProper_left`,
  `isIsogenyMor_of_lqf_of_isOpenMap` (finite: Mathlib ZMT `IsFinite.of_isProper_of_locallyQuasiFinite`;
  surjective: clopen nonempty range in irreducible A), `mulIsogeny_of_mulEtale : MulEtale → MulIsogeny`,
  `mulUnramified_of_mulEtale`, `mulIsogeny_of_mulUnramified : MulUnramified → QuasiFiniteEndSurjective →
  MulIsogeny`. Axioms: propext, Classical.choice, Quot.sound. VERIFIED.
- 05:36 COMPILED (exit 0): `ne_of_specializes_of_lqf` (LQF maps strict specializations to distinct points; fibres
  discrete), `surjective_of_lqf_self` (LQF closed self-map of an irreducible Noetherian scheme is surjective:
  generic-point orbit ξ ⤳ fξ ⤳ f²ξ ⤳ … would be a strictly decreasing chain of closed sets), and
  **`quasiFiniteEndSurjective : QuasiFiniteEndSurjective`** (A.X.left Noetherian via
  `LocallyOfFiniteType.isLocallyNoetherian` + `QuasiCompact.compactSpace_of_compactSpace`; irreducible via
  `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`). Hence
  **`mulIsogeny_of_mulUnramified' : MulUnramified → MulIsogeny`**. Axioms: propext, Classical.choice, Quot.sound.
  So `QuasiFiniteEndSurjective` (stated as a dimension-theory leaf) is NOT a leaf: Mathlib proves it, no dimension
  theory needed. Remaining leaf for MulIsogeny: `MulUnramified` (char 0, n ≠ 0 ⇒ FormallyUnramified [n].left),
  implied by `MulEtale` (`mulUnramified_of_mulEtale`).
