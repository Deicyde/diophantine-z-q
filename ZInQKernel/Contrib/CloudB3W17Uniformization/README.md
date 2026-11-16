# Exact H103 uniformization — verified

The unchanged original statement is proved:

```lean
theorem uniformizationLeafAll_proof : BPAnalytic.Uniformization.UniformizationLeafAll :=
  CloudB3W17Uniformization.uniformizationLeafAll
```

Entry point: `ZInQKernel/Contrib/OneProof/UniformizationLeafAll.lean`.
Proof-source commit: **151897bc9645a52002e8048f808b1e2bb12a1171**.
Base: **e22df37cdef936f5b0f29ec09501854bea6c7316**, freshly fetched before the
named build and again before the discharge check. The latter fetch found main
unchanged. Lean 4.35.0; Mathlib **56a005855ea17e0b0958f73ec801ae140b0a1679**.

## Exact prescribed verification

On a dedicated internal build host, in the private author checkout:

```sh
env LEAN_NUM_THREADS=1 lake build \
  +ZInQKernel.OneProof.Main \
  +ZInQKernel.OneProof.Discharges \
  +ZInQKernel.Contrib.OneProof.UniformizationLeafAll
lake env lean -M24000 -j4 scratch/ExactUniformizationDischarges.lean
lake env lean -M24000 -j4 scratch/H103AllAxioms.lean
```

The named build exits **0**, **13,776 Lake jobs**, **23:04.45** elapsed.
`LEAN_NUM_THREADS=1` serializes the Lake Lean workers; the single scratch-check
process has four Lean threads. Maximum process/child RSS reported by `time -v`:
**16,155,020 KB** for the named build. This is attributable process RSS, not a
measurement of the entire host or team.

The exact discharge check exits **0** in **8.39s**, RSS **9,295,756 KB**:

```text
DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by uniformizationLeafAll_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 59 open hypotheses, 2859 theorems checked, 8 discharge one
```

The other seven rows in the full output concern older contributions; they are
not attributed to this proof. The exact root constant is checked explicitly,
and its axiom report is also `[propext, Classical.choice, Quot.sound]`.

The separate public-owned axiom check exits **0** in **5.03s**, RSS
**7,147,240 KB**. All **34** checked declarations (including the exact closing
constant and pointwise supporting adapters) report only the three standard
axioms. The scratch file also elaborates an example of the exact original type.

Full raw stdout/stderr and `time -v` evidence, in the W17 scout directory:
`H103-NamedBuild.log`, `H103-Discharges.log`, `H103-AllAxioms.log`.
The named build retains upstream/donor deprecation, module-system and
class-definition-reducibility warnings; it is **not** described as warning-free.
The new closing module and the single exact discharge check are warning-free.
An earlier direct Bridge rebuild exceeded -M7500 and -M12000; the unmodified
Bridge succeeded with -M24000, peak RSS13,058,672 KB. No proof or target waiver
was used to solve that resource issue.

## What supplies the proof

- Native complex-point analytic manifolds, constant relative dimensions,
  regular sections and coordinates: the immutable Paul-Lez/HodgeConjecture
  port at **2ead713179628a3c738197d5996f51c8a9c886ac**, W17 donor core
  **e222d7ba1999d47ab0618cc0d812bb0b6f8b7229**.
- Native projective compactness and smooth integral connectedness: companion
  **9fbc627ae28ffa756cdf33f2c8995eddce06601a**.
- Actual kernel/native point carrier, membership, evaluation, topology and
  unchanged canonical atlas: Bridge through
  **04b32ceef8b3abb4d21805a35417963d6c37bdbd**; manifold transport
  **8644688119927b2d83c309714babddee9a176580**.
- Both analytic comparison directions for the exact choice-based atlas:
  minimal canonical donor **f4a2589d5281b37e9edc4d35c5155f7817fe630b**.
  No H105 wrappers or canonical-model/descent modules are imported for H103.
- Integral proper native complex-point compactness, via a continuous
  surjective projective Chow cover: proper-compact donor through
  **3a05b08d2a07702f67fc545e0d41ffebcebdb399**. Target projectivity or compactness
  is not assumed. The existing Anthropic FLT Chow source pin remains unchanged.
- Actual global analytic exponential, built from finitely many fixed real
  flows with a proved Cauchy–Riemann derivative; analytic IFT, surjectivity,
  full lattice and torus group diffeomorphism: W17 Realify/LocalExp/Lattice
  sources, including torus donor **0db926096a4f57f52c4579e08ad2b02241d95c0d**.

Actual abelian points are commutative by the existing Mathlib algebraic result
and `MonObj.Hom.commGroup`. No general compact complex Lie-group commutativity
or analytic dependence on velocity is assumed.

Owned pointwise adapters reuse host `unif-printed` Stage1/2a/2b/2c proof logic
with explicit attribution to **dbf043a4eb8d977b1d4bf0b03010f915b70bcfb8** in
source docstrings. No unmerged host module is copied or imported. Every
literature, topology, analytic-coordinate and torus input is now a proved
component, not an open premise or a purpose-built replacement field.

## Owned assembly files

Under `ZInQKernel/Contrib/CloudB3W17Uniformization/`:
`BPFromTorus.lean`, `FromAnalyticPoints.lean`, `PointProduct.lean`,
`AbelianPointLieGroup.lean`, `NativeAnalytic.lean`, `NativeAbelianGeometry.lean`,
`ClassicalNeighborhood.lean`, `TransportAnalytic.lean`, `CanonicalAnalytic.lean`,
`AbelianAnalyticAssembly.lean`, `Uniformization.lean`.
The new OneProof entry is separate. Earlier conditional adapters are helper
lemmas discharged by the final theorem; they are not remaining leaves.

## Integrity and scope

Comment/string-aware audit at the proof commit: **81 new delivered Lean files**,
**635,593 bytes**, largest file **55,419 bytes**, zero prohibited-code matches.
Original H103/H105 declaring files, `Objects.lean`, toolchain, Mathlib manifest
and Lake config are unchanged. No existing module was edited. License,
NOTICE and modification records of both port slices are retained.
No sorry, extra axiom, new parser/notation/macro/elaborator, native proof
shortcut or OneProof.Main import occurs in the new delivered code.

The branch has no upstream and `push.default=nothing`. Only inherited
`.setup-done` is untracked. No public GitHub write, push, merge or human outreach
was made. Publication and independent final-head review remain the lead's work.
This closes the mathematical H103 supplier; it does **not** claim H105 GAGA,
which is a separate algebraization task, or claim the repository has already
folded/merged this new proof.
