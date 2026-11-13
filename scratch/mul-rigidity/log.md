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
- 05:40 COMPILED (exit 0): `kerUnit`, `diffKer`, `diagonal_isPullback` (Δ_f is the base change of the unit section
  of ker f along (x,y) ↦ x⁻¹y, for any homomorphism f : A → A), `formallyUnramified_of_kerUnit`,
  leaf `KerUnitOpen`, `mulUnramified_of_kerUnitOpen`, **`mulIsogeny_of_kerUnitOpen : KerUnitOpen → MulIsogeny`**.
- 05:44 COMPILED (exit 0): `isOpenImmersion_of_section` (section of formally unramified lft is an open immersion),
  **`kerUnitOpen_of_mulEtale : MulEtale → KerUnitOpen`** (so the leaf KerUnitOpen is implied by the published
  "[n] étale for char ∤ n"). All axioms: propext, Classical.choice, Quot.sound.

## Assembled file and consumers
- `assemble.sh` builds `MulRigidity.lean` = `import Mathlib` + Objects + Rigidity.lean + Mul.lean + fs_tail.lean.part
  (FS2 `EndDivisionOfSchemeIso` and FS3 `EndDivisionOfEnd0Division` with their g0-fibresimple proofs, copied
  verbatim). With `import Mathlib`, the identifier `γ` clashes with a Mathlib notation: renamed to `gm` in
  Rigidity.lean.
- 05:41 COMPILED (exit 0, 12 s): MulRigidity.lean; **`G0FibreSimple.endDivisionOfSchemeIso :
  EndDivisionOfSchemeIso`** (FS2 closed, no hypotheses) and `end0Division_of_homFree_kerUnitOpen :
  HomFreeFinite → KerUnitOpen → EndDivisionOfEnd0Division`. All eight `#print axioms`: propext,
  Classical.choice, Quot.sound. Rigidity.lean alone recompiled after the rename (OK).
- Verbatim check (diff): `def RigidityHom` (with docstring) and `def MulIsogeny` identical to
  scratch/g0-fibresimple/FibreSimple.lean.

## KerUnitOpen reduced to two glue statements (cotangent space at the origin)
- 05:44 COMPILED (exit 0, Mul.lean 4 s; MulRigidity.lean 12 s): `origin`, `map_origin`, `O0` (= stalk at the
  origin), `stalkEndo` (f^♯ on 𝒪_{A,0}, via `stalkCongr` + `stalkMap`), `cotangentMap` (`Ideal.mapCotangent` of
  f^♯.toIntAlgHom on m₀/m₀²), glue Props **`KerUnitOpenOfCotangentSurj`** (cotangent map surjective ⇒ unit
  section of ker f open immersion; Nakayama + fibre local ring) and **`CotangentMulN`** (cotangent map of [n] is
  n • id, any characteristic), `charZero_residueField` (residue field at 0 has char 0: ring hom
  k → Γ(Spec k) → Γ(A) → 𝒪_{A,0} → κ), `kerUnitOpen_of_cotangent`, **`mulIsogeny_of_cotangent :
  KerUnitOpenOfCotangentSurj → CotangentMulN → MulIsogeny`**. Axioms: propext, Classical.choice, Quot.sound.
- Truth checks (argument, STANDARD): n = 0 gives cotangent map 0 (f^♯ factors through the residue map, which kills
  m₀), consistent with KerUnitOpenOfCotangentSurj (ker [0] = A, unit section open iff dim A = 0 iff m₀/m₀² = 0).
  Neither glue Prop is proved: Mathlib v4.35 lacks stalks of fibre products / tangent vectors as k[ε]-points.
