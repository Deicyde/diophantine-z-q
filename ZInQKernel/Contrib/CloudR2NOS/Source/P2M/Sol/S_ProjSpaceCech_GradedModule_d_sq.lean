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
  Source file    : P2M/Sol/S_ProjSpaceCech_GradedModule_d_sq.lean
  Source sha256  : d5f290b9bfdbec2ba9661d145c059772bb074928264fc358cdcb26f572bf3a82
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_ProjSpaceCech_GradedModule_d_sq
r2nos_namespace_dual

set_option autoImplicit false

universe u

noncomputable section

open Finset Function MvPolynomial
r2nos_open_dual "Finset Function MvPolynomial"

namespace ProjSpaceCech
r2nos_namespace_dual
w03_export "ProjSpaceCech" "Idx.succAbove_comp_succAbove Idx Idx.img Idx.face Idx.img_face_subset GradedModule GradedModule.secIncl GradedModule.secIncl_trans GradedModule.faceRes GradedModule.d GradedModule.d_apply GradedModule.H"
w03_open "ProjSpaceCech"

section GradAltdSq

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

namespace GradedModule
r2nos_namespace_dual
w03_export "ProjSpaceCech.GradedModule" "secIncl secIncl_trans faceRes d d_apply H"
end GradedModule
r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.d_sq' (i : ℕ) :
    GradedModule.d D (i + 1) ∘ₗ GradedModule.d D i = 0 := by
  refine LinearMap.ext fun f => funext fun s => ?_
  rw [LinearMap.comp_apply, GradedModule.d_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [GradedModule.d_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    ← pow_add]
  simp only [GradedModule.faceRes]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (i + 3) × Fin (i + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1
        (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ h1)
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (i + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface :
        Idx.face n (Idx.face n s a) b
          = Idx.face n (Idx.face n s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b)
        = s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, Idx.succAbove_comp_succAbove halt]
    have hsign : ((-1 : R) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : R) ^ (((b.succ : Fin (i + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b:ℕ) + 1 + (a:ℕ)) = ((a:ℕ) + (b:ℕ)) + 1 from by ring, pow_succ]
      ring
    simp only [Fin.val_succ, a', Fin.val_castLT] at hsign ⊢
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) rfl ?_)

    have key : ∀ {t t' : Idx n i} (heq : t = t')
        {K K'} (h1 : Idx.img n t ⊆ K) (h1' : K ⊆ Idx.img n s)
        (h2 : Idx.img n t' ⊆ K') (h2' : K' ⊆ Idx.img n s),
        (GradedModule.secIncl D h1') ((GradedModule.secIncl D h1) (f t))
          = (GradedModule.secIncl D h2') ((GradedModule.secIncl D h2) (f t')) := by
      rintro t _ rfl K K' h1 h1' h2 h2'
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        GradedModule.secIncl_trans, GradedModule.secIncl_trans]
    exact key hface (Idx.img_face_subset n _ b)
      (Idx.img_face_subset n s a)
      (Idx.img_face_subset n _ a')
      (Idx.img_face_subset n s b.succ)

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.range_d_le_ker (i : ℕ) :
    LinearMap.range (GradedModule.d D i)
      ≤ LinearMap.ker (GradedModule.d D (i + 1)) := by
  rintro _ ⟨f, rfl⟩
  exact LinearMap.congr_fun (GradedModule.d_sq' D i) f

end GradAltdSq

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n) (i : ℕ) :
    ProjSpaceCech.GradedModule.d D (i + 1) ∘ₗ ProjSpaceCech.GradedModule.d D i = 0 :=
  ProjSpaceCech.GradedModule.d_sq' D i

end
end S_ProjSpaceCech_GradedModule_d_sq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
