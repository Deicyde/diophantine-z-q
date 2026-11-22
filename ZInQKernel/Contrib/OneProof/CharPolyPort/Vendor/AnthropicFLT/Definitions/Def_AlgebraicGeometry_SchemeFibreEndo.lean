/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_SchemeFibreEndo. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib.AlgebraicGeometry.ResidueField

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

def schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (s : S) :
    Limits.pullback f (S.fromSpecResidueField s)
      ⟶ Limits.pullback f (S.fromSpecResidueField s) :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ h) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, hcomm, Limits.pullback.condition])

@[simp] theorem schemeFibreEndo_fst {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ h :=
  Limits.pullback.lift_fst _ _ _

@[simp] theorem schemeFibreEndo_snd {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ :=
  Limits.pullback.lift_snd _ _ _

end AlgebraicGeometry

end

