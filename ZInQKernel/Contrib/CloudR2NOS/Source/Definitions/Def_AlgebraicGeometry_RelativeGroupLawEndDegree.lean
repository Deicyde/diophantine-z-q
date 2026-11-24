/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_RelativeGroupLawEndDegree.lean
  Source sha256  : b5ee28e431d2522d8ee44a5b5b06fa518dc3e1dd32ed3074963e448c3558bb77
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra"

namespace NeronModelInfra
r2nos_namespace_dual

variable {B X : Scheme.{u}} {f : X ⟶ B}

def schemeHomOverNpow (β : SchemeHomOver f f) : ℕ → SchemeHomOver f f
  | 0 => schemeHomOverId f
  | i + 1 => schemeHomOverComp (schemeHomOverNpow β i) β

@[simp] theorem schemeHomOverNpow_zero (β : SchemeHomOver f f) :
    schemeHomOverNpow β 0 = schemeHomOverId f := rfl

@[simp] theorem schemeHomOverNpow_succ (β : SchemeHomOver f f) (i : ℕ) :
    schemeHomOverNpow β (i + 1) = schemeHomOverComp (schemeHomOverNpow β i) β := rfl

end NeronModelInfra

namespace GoodReductionJacobian
r2nos_namespace_dual
namespace RelativeGroupLaw
r2nos_namespace_dual

section General

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

@[reducible]
def pointCommGroup (G : RelativeGroupLaw R f) (hc : G.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : CommGroup (SchemeHomOver t f) :=
  { G.pointGroup t with mul_comm := fun x y => hc t x y }

def endAeval (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f)
    (p : Polynomial ℤ) : SchemeHomOver f f :=
  letI := G.pointCommGroup hc f
  ∏ i ∈ Finset.range (p.natDegree + 1), NeronModelInfra.schemeHomOverNpow β i ^ p.coeff i

theorem endAeval_X (G : RelativeGroupLaw R f) (hc : G.IsCommutative) (β : SchemeHomOver f f) :
    G.endAeval hc β Polynomial.X = β := by
  letI := G.pointCommGroup hc f
  rw [endAeval, Polynomial.natDegree_X, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, Polynomial.coeff_X_zero, Polynomial.coeff_X_one, zpow_zero, zpow_one,
    _root_.one_mul, _root_.one_mul, NeronModelInfra.schemeHomOverNpow_succ,
    NeronModelInfra.schemeHomOverNpow_zero, NeronModelInfra.schemeHomOverComp_id_left]

abbrev endKer (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : Scheme.{u} :=
  pullback β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev endKerStr (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKer β ⟶ Spec (CommRingCat.of R) :=
  pullback.snd β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev endKerι (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) : G.endKer β ⟶ A :=
  pullback.fst β.1 (G.one (𝟙 (Spec (CommRingCat.of R)))).1

theorem endKer_nsmul_idPoint (G : RelativeGroupLaw R f) (n : ℕ) :
    G.endKer (G.nsmul f n idPoint) = G.schemeKer n :=
  rfl

theorem endKerι_comp (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKerι β ≫ β.1 = G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  pullback.condition

theorem endKerι_comp_base (G : RelativeGroupLaw R f) (β : SchemeHomOver f f) :
    G.endKerι β ≫ f = G.endKerStr β := by
  calc G.endKerι β ≫ f = G.endKerι β ≫ (β.1 ≫ f) := by rw [β.2]
    _ = (G.endKerStr β ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
        rw [← Category.assoc, endKerι_comp]
    _ = G.endKerStr β := by rw [Category.assoc, (G.one _).2, Category.comp_id]

end General

section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

def endDegree (G : RelativeGroupLaw K f) (β : SchemeHomOver f f) : ℕ := by
  classical
  exact if IsFinite (G.endKerStr β) then (G.endKerStr β).finrank (IsLocalRing.closedPoint K) else 0

theorem endDegree_of_isFinite (G : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [h : IsFinite (G.endKerStr β)] :
    G.endDegree β = (G.endKerStr β).finrank (IsLocalRing.closedPoint K) := by
  rw [endDegree, if_pos h]

theorem endDegree_of_not_isFinite (G : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    (h : ¬ IsFinite (G.endKerStr β)) : G.endDegree β = 0 := by
  rw [endDegree, if_neg h]

instance isIso_endKerStr_schemeHomOverId (G : RelativeGroupLaw K f) :
    IsIso (G.endKerStr (schemeHomOverId f)) := by
  change IsIso (pullback.snd (𝟙 A) (G.one (𝟙 (Spec (CommRingCat.of K)))).1)
  infer_instance

theorem endDegree_schemeHomOverId (G : RelativeGroupLaw K f) :
    G.endDegree (schemeHomOverId f) = 1 := by
  haveI : IsFinite (G.endKerStr (schemeHomOverId f)) := inferInstance
  rw [endDegree_of_isFinite]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

end Field

end RelativeGroupLaw
end GoodReductionJacobian

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
