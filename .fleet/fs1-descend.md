# fs1-descend (fleet summary)

**Verdict: FS1b′ `FiniteDescends` is PROVED, from Mathlib v4.35 only, with no new leaf or glue Prop.**
The statement was copied verbatim from scratch/g0-fibresimple/. The proof is in scratch/fs1-descend/FiniteDescends.lean
(`FS1Descend.finiteDescends`), with the write-up in docs/research/fs1-descend.md.

Route: the proof avoids fpqc descent of affineness, which Mathlib lacks, by using Mathlib's ZMT characterization
`IsFinite ↔ IsProper ∧ LocallyQuasiFinite`. Separatedness descends because `IsSeparated = diagonal UniversallyClosed`
(proved). Properness descends through Mathlib's descent of UniversallyClosed and LocallyOfFiniteType. Local
quasi-finiteness descends along surjections by the fibre-cardinality criterion. The by-product is a general instance,
`DescendsAlong @IsFinite (Surjective ⊓ Flat ⊓ QuasiCompact)`, that could be upstreamed to Mathlib.

What compiles (VERIFIED):
- FiniteDescends.lean: exit 0 in 76 s, no warnings, standard three axioms.
- Integration check (check_integration.sh; g0-fibresimple's FibreSimple.lean verbatim plus this proof, 20784 lines):
  exit 0 in 193 s, no sorry. `fibreSimple_of_leaves_fs5 : TextbookLeaves → MulIsogeny → RigidityHom →
  FibreComTrivial → FibreSimple` has the standard axioms.

What remains: FibreSimple's glue now needs only FS5 `FibreComTrivial`, which is blocked by qm-pin and was not worked on.
For integration, swap `FibreSimplePieces.finiteDescends` for `FS1Descend.finiteDescends`.
