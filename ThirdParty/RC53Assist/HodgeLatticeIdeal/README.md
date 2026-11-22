# The invariant differential and its Hodge-lattice ideal

A–C are proved for the actual evaluated, transported invariant differential, without a
principality assumption. The original model, unit sections, generic-fibre identification,
`G.omega`, `G.detLattice`, and `secIndex` are unchanged.

The main export is
`ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal.invariantDifferential_ideal_dictionary`
in `Binding.lean:38`. Its hypotheses are exactly the original geometric and Weierstrass data:
`G`, `hdim : E.dim = 1`, `E'` with its ellipticity instance, `e`, `i`, `hfield`, and `hO`.
There is no extra lattice, rank, principality, norm, or evaluation hypothesis.

## Proved dictionary

Let `R := 𝓞 L`. The reviewed binding supplies `hreg` and the actual nonzero vector

```
η := hodgeEval G hdim ⟨transported invariant differential, hreg⟩
η = G.wedge ![originParameter G E' i hO]
```

Define `fη : L →ₗ[R] G.hodgeSpace 1` by `fη a = a • η`, and put

```
Iη := coefficientSubmodule (G.detLattice 1) η
Iη = (G.detLattice 1).comap fη
```

The main theorem produces the following conclusions for that vector:

* **A — reconstruction and uniqueness.**
  `G.detLattice 1 = Iη.map fη`; `fη` is injective; each lattice vector has exactly one
  coefficient in `Iη`.
* **B — the actual fractional ideal.**
  `Iη ≠ ⊥`, `Iη.FG`, and `Submodule.span L (Iη : Set L) = ⊤`.
  `coefficientFractionalIdeal G hdim η hη` is a nonzero
  `FractionalIdeal (nonZeroDivisors R) L` whose underlying submodule is exactly `Iη`.
* **The original integral cotangent lattice.**
  `oneHodgeMap G` is injective and
  `G.detLattice 1 = G.omega.map (oneHodgeMap G)`.
  `omegaCoefficientEquiv` identifies `G.omega` with `Iη`, and its value at `x` satisfies
  `(omegaCoefficientEquiv ... x : L) • η = oneHodgeMap G x`.
* **C — the original section-index orientation.**
  For every `a : L`, without a membership assumption,

  ```
  secIndex (G.detLattice 1) (a • η) = secIndex Iη a
    = (Submodule.span R {a}).toAddSubgroup.relIndex Iη.toAddSubgroup
  ```

  Thus the general relative index is `[Iη : Iη ∩ R a]`. If `a ∈ Iη`, it is the cardinality
  of `Iη / R a`, not the reverse quotient. For `a ∈ Iη` and `a ≠ 0`, writing `Jη` for the
  bundled fractional ideal,

  ```
  (secIndex (G.detLattice 1) (a • η) : ℚ) * FractionalIdeal.absNorm Jη =
    |Algebra.norm ℚ a|
  (secIndex (G.detLattice 1) (a • η) : ℚ) =
    |Algebra.norm ℚ a| / FractionalIdeal.absNorm Jη
  secIndex (G.detLattice 1) (a • η) ≠ 0
  ```

  Integral rescaling multiplies the index by the absolute integer norm, as in the unchanged
  `secIndex_smul` theorem.

Neither `η ∈ G.detLattice 1` nor global freeness of `G.omega` or `Iη` is asserted.
No nonprincipal ideal is replaced by a chosen principal generator.

## Rank input and first barrier

There is **no barrier for A–C**. The required pointwise statement is proved in
`ModelLattice.lean:124`:

```
Module.rank L (L ⊗[𝓞 L] G.cotangent) = 1
```

It follows from the reviewed cotangent-space finrank result, the existing Weierstrass
presentation theorem, and `HodgeLattice.rank_tensor_cotangent`.
`hodgeLattice_one`, at `ModelLattice.lean:140`, then proves the original dimension-one
Hodge-lattice conclusion using `omegaLocal`, its finiteness and spanning consequences, and
`hodgeLattice_of_lattice`.

The original `CotangentRank` and `HodgeLatticeTheorem` are globally quantified over all
abelian varieties and all dimensions. A rank-one result is not their global input.
Accordingly, the pointwise proof underlying `hodgeLatticeTheorem_of_cotangentRank` is used;
no all-dimensions proposition is fabricated or assumed, and no global discharge is claimed.

## Definitions and theorem locators

* **Definition:** `coordinateMap` — `Coordinates.lean:29`.
* **Definition:** `coefficientSubmodule` — `Coordinates.lean:38`.
* **Definition:** `oneHodgeMap` — `ModelLattice.lean:34`.
* **Theorem, proved:** `detLattice_one_eq_map_omega` — `ModelLattice.lean:79`.
* **Theorem, proved:** `rank_tensor_cotangent_of_dim_one` — `ModelLattice.lean:124`.
* **Theorem, proved:** `hodgeLattice_one` — `ModelLattice.lean:140`.
* **Definition:** `coefficientFractionalIdeal` — `Fractional.lean:74`.
* **Definition:** `omegaCoefficientEquiv` — `Fractional.lean:95`.
* **Theorem, proved:** `secIndex_detLattice_coordinate` — `Fractional.lean:116`.
* **Theorem, proved:** `secIndex_detLattice_eq_norm_div` — `Fractional.lean:148`.
* **Theorem, proved:** `invariantDifferential_ideal_dictionary` — `Binding.lean:38`.

The source contains the exact signatures and literature/library locators for every named
result. `AxiomsAndTypes.log` contains the complete elaborated types of all 60 named constants.

## Non-vacuity

`NonVacuity.lean` checks the dictionary on the rational number field:

* For the ordinary integral lattice and `η = 1/2`, the coefficient lattice is `2 𝓞_ℚ`.
  The vector `1/2` is proved not to belong to the ordinary integral lattice
  (`rational_half_not_integral`, line 87).
* For `η = 2`, the coefficient lattice is `(1/2) 𝓞_ℚ`; it contains a genuinely non-integral
  coefficient (`rational_two_fractional_not_integral`).
* The index of two in the ordinary integral lattice is two.
  In half coordinates the coefficient four has index two in `2 𝓞_ℚ`
  (`rational_half_index`, line 127).
  In two coordinates the coefficient one has index two in `(1/2) 𝓞_ℚ`
  (`rational_two_index`, line 137).
* The fractional-ideal norm-index identity is also instantiated for an arbitrary fractional
  ideal of an arbitrary number field, without any principality hypothesis.

These are algebraic examples, not a construction or replacement of a group model.

## Verification and custody

The aggregate module `All` built successfully with Lean 4.35.0 and the existing pinned
Mathlib dependencies. The permitted build used eight Lean threads and a heartbeat limit
of 800,000. Every new Lean source has lines at most 100 characters, except imports.

All 60 named constants were axiom-audited. Their only axioms are
`propext`, `Classical.choice`, and `Quot.sound`; the raw output retains universe annotations.
`AxiomsAndTypes.log` gives the complete output, and `Verification.json` records its hash,
the exact source hashes, and the successful audit.

All 20 recorded inputs, including the original lattice definitions, reviewed binding sources,
dependency pins, and the frozen target, were verified unchanged. The supplied base is
`9c12329f81c7ce54a015cecd2937815155b55730`. No source-control operation or dependency update
was performed. No pre-existing source file was edited.

The first module-build failures were saved before repair and remain byte-identical:

```
79a073d26c7992bb95436a07a916f889f2d9fc8a4022b11ab40e1c800e2d2a9b  Coordinates
5202c604628ccada0b0338d3c2a5bac7a82b088ff78bcfbe61fe4a1f9d0ef29b  ModelLattice
c9195e00d125da688ca977cef0a2aa735697c23c12082c6e4975846dede660fb  NonVacuity
```

`Fractional`, `Binding`, and `All` succeeded on their first direct builds.
The private verification archive preserves every numbered transcript, first-failure transcript,
build receipt, and audit receipt. The first audit transcript was also retained: its reader
initially rejected universe suffixes on the standard axiom names; only the reader was corrected.
No mathematical source was changed for that correction.

### Final source files: SHA-256 and byte size

```
2ac1a129705a5f1c5f148c3e7c5b9d1a2d7ea5398de926e3cdf670870699aeef  Coordinates.lean
2d1afcbd8e013e94006d37d3522f96839d77871a42d24f0a2cc5caeca867783e  ModelLattice.lean
fa6f037871ae3c44f2b66335c780fbf2956503e878d4be40b90c3487d3924784  Fractional.lean
b6306026a6ce04d6e68a87d5a76b46c87d99974a2bbdf533f1504fc733f687ec  Binding.lean
0c70778965dc172238363f64324b1f2285489fb486e15aff0dbc82fdb9d84dff  NonVacuity.lean
ebb1bfa61aa9b8df367d0a6ede075cae96e51b89ccd4f76d19c74887bf6ca1e3  All.lean
```

Byte sizes, in the same order: **7,579; 8,341; 10,542; 4,949; 9,052; 703**.
The frozen `TargetStatement.md` is **7,612 bytes**, with SHA-256
`6c75c79c3280aad540d9548dd207e45655a84001e055e70d0cd4400d6a8a9b0d`.
`FileManifest.tsv` lists the supplied files with byte sizes and hashes.

## Scope boundary

The contribution is algebraic only. No minimal-discriminant, delta, archimedean, period,
metric, or height claim is made. It has been built and axiom-audited, but has not been
committed, integrated, or independently reviewed.
