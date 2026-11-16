# W28 source provenance and compatibility changes

This contribution vendors an import-directed arithmetic cone from
[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)
at **6e837e75355538c7f80bab5b956861e86c4eacc2**. The public source archive has
SHA-256 `c50bd3976cec66bdaccc694e522ae9cf8c9f2570ca62269335ff661f4c3c465e`.

The upstream code is Copyright 2026 Anthropic, PBC, under Apache License 2.0.
Its complete `LICENSE`, `NOTICE`, and file-by-file `ATTRIBUTION.md` are preserved
byte-for-byte as `Vendor/AnthropicFLT/LICENSE`, `NOTICE.upstream`, and
`ATTRIBUTION.upstream.md`. They retain the notices for the FLT project, Mathlib,
flt-regular, and the other upstream material. The original upstream headers
inside the Lean bodies are retained.

`Vendor/AnthropicFLT/SOURCE_MANIFEST.json` identifies each upstream module,
original SHA-256, resulting path and SHA-256, and any prefix cut. The arithmetic
cone has 25 modules; it is not the 8,788-module fine-moduli proof cone tested
separately in the development evidence.

## Changes

- Relocate imports to `ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT`.
  The upstream mathematical namespaces and theorem names remain unchanged.
- Make the upstream Lake options explicit in the new files: `maxHeartbeats`,
  `synthInstance.maxHeartbeats`, and the elaborator's
  `backward.isDefEq.respectTransparency.types`. These do not disable kernel
  checking; verification uses `-Ddebug.skipKernelTC=false`.
- Omit the upstream negative global instance/simp cleanup masks from theorem
  wrappers. No extra imports are added just to supply irrelevant cleanup names.
- Omit the unused `P2M.Util` imports, and replace its exact/revert wrapper tactic
  with Lean's built-in `apply` and `assumption`. The original proved solution
  remains the supplied proof. No new elaborator, macro, axiom, or native proof
  delegation is added.
- Close the outer `P2MW.*` namespaces explicitly at EOF.
- In `Def_QuaternionAlgebra_EichlerOrder`, drop the unused `Def_Submodule_LocalBox`
  import. The `IsOrder`, `IsMaximalOrder`, and related definition bodies are
  unchanged.
- In the general quaternion-to-matrix splitting wrapper, drop unused
  `Def_Submodule_FiniteAdeleBox` and `Def_Submodule_LocalBox` imports. This also
  removes the now-unneeded `Def_QuaternionAlgebra_Order_FiniteIdele` module from
  the cone. The general splitting statement and its actual proof body are
  unchanged.
- In `Def_CerednikDrinfeld_ShimuraCurve`, keep only the exact original
  `QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt` definition block. Its five
  unrelated geometry imports, the rest of the Shimura-curve-model declarations,
  and the now-unused `AlgebraicCurve` open are omitted. The predicate's arguments,
  types, and body are unchanged. This is an arithmetic prerequisite, not a new
  moduli model.

The new bridge source specializes the actual project order and coefficients.
It does not modify `LeafQM.B`, `LeafQM.O`, `LeafQM.ofInt`, `R1fpAb`, the existing
assemblies, Lake configuration, or dependency pins. `MaximalOrder.lean` reuses
`GlueRepo.A1`'s original coordinate vectors and trace-discriminant proof rather
than copying them. `Ramification.lean` adapts the genuine local-isotropy route
of the upstream definite-at-two template to `(2, -3)` and includes an actual
real tensor-product splitting.

The input project is frozen at `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`;
Lean is 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. No new Lake dependency is introduced.

These notices record source reuse and changes, not a compiler, axiom, discharge,
or integration verdict. The verification report supplies those separately.
