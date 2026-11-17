/-
NEW EDITION (H5 lane4 a940f2af, 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat.lean
  Source sha256  : 3896a3cd6d3580ac230c2a0a32cd10238fccb7e69cd0e01973c25f6f3e702a80
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
r2nos_namespace_dual

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace QFDescent
r2nos_namespace_dual

theorem Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.QuasiFinite T (T ⊗[R] S)] : Algebra.QuasiFinite R S := by
  refine ⟨fun P _ => ?_⟩

  obtain ⟨⟨Q, hQprime⟩, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := T) ⟨P, ‹_›⟩
  have hQP : Q.comap (algebraMap R T) = P := congrArg PrimeSpectrum.asIdeal hQ
  haveI : Q.LiesOver P := ⟨hQP.symm⟩

  letI : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.mapₐ P Q (Algebra.ofId R T) hQP.symm).toRingHom.toAlgebra
  haveI : IsScalarTower R P.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => ((Ideal.ResidueField.mapₐ P Q (Algebra.ofId R T) hQP.symm).commutes r).symm

  have hfin : Module.Finite Q.ResidueField (Q.Fiber (T ⊗[R] S)) := Algebra.QuasiFinite.finite_fiber Q
  let e₁ := Algebra.TensorProduct.cancelBaseChange R T Q.ResidueField Q.ResidueField S
  let e₂ := Algebra.TensorProduct.cancelBaseChange R P.ResidueField Q.ResidueField Q.ResidueField S
  haveI : Module.Finite Q.ResidueField (Q.ResidueField ⊗[P.ResidueField] (P.ResidueField ⊗[R] S)) :=
    Module.Finite.equiv (e₁.trans e₂.symm).toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (R := P.ResidueField) Q.ResidueField
    (M := P.ResidueField ⊗[R] S)

end QFDescent

namespace RingHom
r2nos_namespace_dual
w03_export "RingHom" "QuasiFinite.respectsIso Finite QuasiFinite CodescendsAlong faithfullyFlat_algebraMap_iff FaithfullyFlat mk quasiFinite_algebraMap toAlgebra"
w03_open "RingHom"

namespace QuasiFinite
r2nos_namespace_dual
w03_export "RingHom.QuasiFinite" "toAlgebra respectsIso"
end QuasiFinite
r2nos_open_scoped "RingHom.QuasiFinite" in
theorem QuasiFinite.codescendsAlong_faithfullyFlat' : CodescendsAlong QuasiFinite FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact QFDescent.Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat S

end RingHom

theorem solution :
    RingHom.CodescendsAlong (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
      (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) :=
  RingHom.QuasiFinite.codescendsAlong_faithfullyFlat'
end S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
