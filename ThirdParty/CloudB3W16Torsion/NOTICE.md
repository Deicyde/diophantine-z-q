# Worker16 torsion source port

**Verification status:** staged source port with separately checked prerequisites.
No H102 discharge is claimed until the genuine geometric provider, the leaf,
and the exact newest-Main/Discharges scratch compile.

## Immutable sources

- anthropics/fermats-last-theorem, `6e837e75355538c7f80bab5b956861e86c4eacc2`.
  Complete upstream LICENSE, NOTICE, and ATTRIBUTION.md are preserved in
  `Vendor/AnthropicFLT/{LICENSE,NOTICE.upstream,ATTRIBUTION.upstream.md}`.
- AxiomMath/Stacks, `c496df0d9beea9deaeabcea8492605f9a0a2313b`, was assessed as an
  alternative. Its complete `AbelianTorsion/FromCube` proof has a much larger
  dependency cone (over 10,000 additional modules). No Stacks geometric code is
  copied into this family.
- Existing FLT ports under CloudW02Connectedness and CloudB2X0Transitive are reused
  by import, not duplicated. The independent finite-group port is imported from
  CloudB3W16FiniteGroup, not copied or replaced here.

## Exact source route

`GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero`
counts the torsion of a proper smooth connected group scheme with relative dimension
g over an algebraically closed field. Its source proof includes the degree formula
`endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero`: multiplication by n has degree
n^(2g). That formula uses the theorem of the cube, a symmetric ample line bundle,
and an Euler-characteristic/degree calculation; it is not an additional hypothesis.

`RelativeBridges.lean` translates the exact PkgI2 field, structure map, law and Krull
dimension to those source definitions. `NativeBridges.lean` separately records
multiplication étale and finite, finiteness of torsion, and the comparison with the
additive torsion subgroup. Finiteness alone is explicitly not treated as the
cardinality formula.

## Port changes

- Local import paths moved below this contribution. Original declaration namespaces
  are generally retained, but colliding implementations and their dependent APIs
  are alpha-renamed as recorded below; this is not a namespace-preservation claim.
- Nonessential broad negative-instance/simp preambles and reactivation scaffolding removed.
- Standalone namespace/open/export scaffold has been translated to ordinary Lean
  commands where needed. Some multi-command inline `p2m_export` invocations remain
  and use the existing imported `P2M.Util` helpers; this port does not define new
  elaborators, macros, syntax or notation. Per-file conversion headers describe
  the porting method, not a claim that every existing helper invocation is gone.
- Source-local notation expanded as literal expressions at its lexical scope.
- Backward elaboration transparency restored for the fixed Lean4.35/Mathlib56a00585
  environment. Definitions and theorem conclusions are not weakened.
- The six large curve modules are assigned to the independent Worker16 curve lane,
  which splits them between whole proof declarations and preserves their original
  public solution APIs. They are not authored or duplicated in this lane.

`Vendor/AnthropicFLT/SOURCE_MANIFEST.json` records original source hashes, paths,
relocated names, direct reused imports and the six delegated original modules.
All authored Lean files are under 150KB after scaffold removal. A lexical audit is
not compilation evidence.

## Current-Main declaration isolation (2026-11-17)

The Main import closure already contains CloudW07JacobiansCurves and the
CloudB3W16Dimension StacksFrontier depth APIs. Relocating file imports alone does
not isolate Lean declaration names. The publication cone therefore gives its
colliding implementations fresh names and redirects their qualified references,
opened-namespace short references, and export lists. Existing Main, W07,
Dimension, pinned dependencies, and the final Mumford leaf are not edited.

Key mappings (namespace prefixes unchanged unless stated):

- `SheafOfModules.monoidalCategory` / `symmetricCategory` and
  `AlgebraicGeometry.Scheme.Modules.monoidalCategory` / `symmetricCategory`
  become `fltMonoidalCategory` / `fltSymmetricCategory` in their respective
  namespaces; `Scheme.Modules.dual` becomes `Scheme.Modules.fltDual`.
- `Scheme.IdealSheafData.IsInvertible` and its method namespace become
  `Scheme.IdealSheafData.IsCartierFLT`. The distinct line-bundle predicate
  `Scheme.Modules.IsInvertible` is preserved. Ideal-sheaf short references to
  `nonempty_mul_module_iso_tensor` and `isInvertible_module` follow the new
  `IsCartierFLT` namespace. `isInvertible_top` becomes `isInvertible_topFLT`;
  the Picard unit theorem `isInvertible_unit` becomes `isInvertible_unitFLT`.
- `tensorPow`, `tensorPow_zero`, `tensorPow_succ`, and `tensorPowOneIso`
  become their `FLT`-suffixed names. This implementation uses the successor
  order `pow n ⊗ L`, unlike W07's `L ⊗ pow n`; these are not blindly retargeted.
  `tensorPowSection` and its zero/successor APIs likewise gain `FLT` suffixes.
- The owned `pullbackSection` / `pullbackSection_def`, `pullback_hom_ext`,
  `pullbackTensorObjIso`, `preservesBinaryProducts_opensMap`, and
  `preservesTerminal_opensMap` gain `FLT` suffixes. The pushforward/restriction
  APIs `pushforwardRestrictIso`, `pushforwardRestrictIso_hom_app_app`, and
  `restrictPushforwardOpensIso` also gain `FLT` suffixes; their direction is
  retained, rather than replaced by W07's oppositely directed constructions.
- `GeometricallyIrreducible.geometricallyConnected`, ideal-sheaf `comap_mul`,
  and smooth `isRegularLocalRing_stalk` gain `FLT` suffixes because the
  nominally isolated dependencies make their declarations nonidentical to
  the existing Main statements.
- `Module.depth` becomes `Module.depthFLT`, including generated declarations
  and opened/exported short uses. Its local-ring weakly-regular-sequence
  supremum is not Main's ideal-indexed regular-sequence depth with a separate
  `I • ⊤ = ⊤` branch. The dependent theorem `Module.depth_le_ringKrullDim`
  becomes `Module.depthFLT_le_ringKrullDim`; its statement retains this port's
  depth, not Main's different definition.

No new geometric or cardinality hypothesis is introduced by these mappings.
Old source/check receipts are historical evidence, not certificates for the
renamed sources. A current candidate must recheck its affected consumers using
current source/dependency fingerprints, enumerate duplicate declarations from
all actual olean import headers (including public/module-system imports and
private parts), and compile Main + Discharges + the exact leaf together.
