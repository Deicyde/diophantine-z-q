/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr`.
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Congr
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

public noncomputable section

open TauCeti
namespace RingEquiv

variable {K L : Type*} [Field K] [Field L]

/-- A field isomorphism induces a chosen ring equivalence of separable closures. -/
def separableClosureCongr (e : K ≃+* L) :
    SeparableClosure L ≃+* SeparableClosure K := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  let eA : K ≃ₐ[K] L := { e with commutes' := fun _ => rfl }
  let σ : L →ₐ[K] SeparableClosure K :=
    (Algebra.ofId K (SeparableClosure K)).comp eA.symm.toAlgHom
  exact separableClosureRingEquiv K L σ

end RingEquiv

open TauCeti
namespace IntermediateField

variable {K L : Type*} [Field K] [Field L]
    (E : IntermediateField K (SeparableClosure K)) (e : K ≃+* L)

/-- Transport a subextension through the chosen identification of separable closures. -/
def separableClosureCongr : IntermediateField L (SeparableClosure L) :=
  (E.toSubfield.comap e.separableClosureCongr.toRingHom).toIntermediateField (fun r => by
    -- Unpack comap membership to apply the separable-closure algebraMap formula.
    change e.separableClosureCongr (algebraMap L (SeparableClosure L) r) ∈ E
    simp)

end IntermediateField

end
