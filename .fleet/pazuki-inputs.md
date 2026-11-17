# pazuki-inputs (fleet note)

**Verdict.** The target (−1 GLUE: `pazukiCor13Upper` out, only printed-form leaves in) is **not met**. No statement
was changed, and none is false or vacuous for the instance used (a genus-2 Jacobian over a number field; report §2.3).

**Main result (compiled, standard axioms).** `ZInQKernel/Contrib/OneProof/PazukiInputs.lean` proves pazuki-dict's
arithmetic half `SymmPrincipalDescends` from a section-free core, with every step in Lean:
- `SymmPrincipalDefinedOver` (new, composite GLUE): every symmetric principal `L` on `A_ℂ` is `bcMap^* M` for a
  symmetric principal `M` on `A_{K'}`, `K'` a number field over `σ`;
- `symmPrincipalDescends_of_definedOver`: `bcMap` is a base change of `Spec ℂ → Spec K'` (hence surjective); a nonzero
  section of `M` pulls back to a nonzero section; `H⁰(L)` is one-dimensional over the field `Γ(A_ℂ, 𝒪)`, so the divisors
  agree;
- `pazukiCor13Upper_of_definedOver`: the field, from `GAGAMorphism`, `PazukiCor13UpperPP`, `RiemannPPAV` and the core.

**Checks (all passed).** Full build Main + Discharges + PazukiInputs (14230 jobs). `#discharges` shows the field
discharged, with the standard axioms. Autofold dry run (`scratch/pazuki-inputs/autofold.json`): the generated module
compiles; the fold needs `--allow-rise` (strictest 11/18 → 12/19, +1 GLUE, as for pazuki-alg; pazuki-dict's coarse
spec is neutral).

**What remains.**
- `RiemannPPAV`: the reading of Mumford, *Abelian varieties*, §3 (scheme form of the algebraization with its theta
  bundle) was not possible: no copy of the book on this host and no network. It stays composite.
- `SymmPrincipalDefinedOver`: proof sketch in report §4. The existing fields picRepresentableAbVar, PicZeroAbVar,
  kleimanPicZeroProper and mumfordTorsionAlgClosed cover part of it. Still missing: `[-1]^*` is inversion on `Pic⁰`,
  the finiteness of `π₀` (Néron–Severi), the `Aut(ℂ/K)`-orbit or closed-point argument, injectivity of `Pic` under
  field extension, and descent of ampleness.

Report: `docs/research/pazuki-inputs.md`. Log: `scratch/pazuki-inputs/log.md`.
