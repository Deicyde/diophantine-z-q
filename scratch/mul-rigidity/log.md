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
