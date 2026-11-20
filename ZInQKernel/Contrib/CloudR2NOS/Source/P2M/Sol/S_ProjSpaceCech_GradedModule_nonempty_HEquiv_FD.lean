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
  Source file    : P2M/Sol/S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD.lean
  Source sha256  : f6d6c0ca9a50a9b3be2efc3a809564d1ca5814736c411ab74cff0b640a0419b1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 24 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R1×3; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_ProjSpaceCech_Twist_d_sq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
r2nos_namespace_dual

set_option autoImplicit false

universe u

noncomputable section

open Finset Function MvPolynomial
r2nos_open_dual "Finset Function MvPolynomial"

namespace ProjSpaceCech
r2nos_namespace_dual
w03_export "ProjSpaceCech" "Twist.mem_negSupp Twist.Mon Twist.Mon.incl Twist.Sec Idx Idx.img Idx.face Idx.img_face_subset Twist.faceRes Twist.cochain Twist.d Twist.d_apply Twist.H GradedModule GradedModule.monMul GradedModule.monMul_congr GradedModule.monMul_add_apply GradedModule.monMul_mem_grade GradedModule.Frac GradedModule.Frac.supp_add GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.secMkAt GradedModule.secIncl GradedModule.secIncl_mk GradedModule.cochain GradedModule.faceRes GradedModule.d GradedModule.d_apply GradedModule.H GradedModule.freeGrade GradedModule.freeGrade_of_nonneg GradedModule.free_monMul_apply GradedModule.free_monMul_injective GradedModule.FD GradedModule.prod_X_pow_mem_freeGrade Twist.d_sq"
w03_open "ProjSpaceCech"

section Bridge

variable {R : Type u} [CommRing R] {n : ℕ}
variable (d₀ : ℤ)

namespace GradedModule
r2nos_namespace_dual
w03_export "ProjSpaceCech.GradedModule" "monMul monMul_congr monMul_add_apply monMul_mem_grade Frac Frac.supp_add sec sec.mk sec_mk_eq secMkAt secIncl secIncl_mk cochain faceRes d d_apply H freeGrade freeGrade_of_nonneg free free_monMul_apply free_monMul_injective FD prod_X_pow_mem_freeGrade mk M xMul grade Frac.num"
end GradedModule
r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.toNat_sub_neg_toNat (b : ℤ) :
    ((b.toNat : ℤ) - ((-b).toNat : ℤ)) = b := by
  omega

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.Xprod (e : Fin (n + 1) → ℕ) : MvPolynomial (Fin (n + 1)) R :=
  ∏ j, X j ^ e j

r2nos_open_scoped "ProjSpaceCech.GradedModule" in
theorem GradedModule.Xprod_mem_freeGrade (e : Fin (n + 1) → ℕ) {d : ℤ}
    (hd : d = ∑ j, (e j : ℤ)) :
    (GradedModule.Xprod (R := R) e) ∈ GradedModule.freeGrade R n d := by
  rw [hd]; exact GradedModule.prod_X_pow_mem_freeGrade e

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.twistFrac {I : Finset (Fin (n + 1))}
    (b : Twist.Mon n d₀ I) : GradedModule.Frac (GradedModule.FD R n d₀) I where
  denExp j := (- b.1 j).toNat
  hden j hj := by
    have hbj : 0 ≤ b.1 j := by
      by_contra h; exact hj (b.2.2 ((Twist.mem_negSupp n).mpr (not_le.mp h)))
    omega
  num := GradedModule.Xprod (R := R) (fun j => (b.1 j).toNat)
  hnum := by
    refine GradedModule.Xprod_mem_freeGrade _ ?_

    have hb := b.2.1
    have hsum : ∑ j, (((b.1 j).toNat : ℤ) - (((- b.1 j).toNat : ℤ))) = d₀ := by
      simp_rw [GradedModule.toNat_sub_neg_toNat]; exact hb
    rw [Finset.sum_sub_distrib] at hsum
    linarith

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.twistToGradSec (I : Finset (Fin (n + 1))) :
    Twist.Sec R n d₀ I →ₗ[R] GradedModule.sec (GradedModule.FD R n d₀) I :=
  Finsupp.linearCombination R
    (fun b => GradedModule.sec.mk _ I (GradedModule.twistFrac d₀ b))

r2nos_open_scoped "ProjSpaceCech.GradedModule" in
theorem GradedModule.twistToGradSec_single (I : Finset (Fin (n + 1)))
    (b : Twist.Mon n d₀ I) (r : R) :
    GradedModule.twistToGradSec d₀ I (Finsupp.single b r)
      = r • GradedModule.sec.mk _ I (GradedModule.twistFrac d₀ b) := by
  simp [GradedModule.twistToGradSec, Finsupp.linearCombination_single]

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.twistToGradSec_incl {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    (GradedModule.secIncl (GradedModule.FD R n d₀) hIJ).comp
        (GradedModule.twistToGradSec d₀ I)
      = (GradedModule.twistToGradSec d₀ J).comp
          (Finsupp.lmapDomain R R (Twist.Mon.incl n d₀ hIJ)) := by
  refine Finsupp.lhom_ext fun b r => ?_
  simp only [LinearMap.comp_apply, GradedModule.twistToGradSec_single, map_smul,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  refine congrArg (r • ·) ?_
  rw [GradedModule.secIncl_mk]
  rfl

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.sec_mk_enlarge (I : Finset (Fin (n + 1)))
    (x : GradedModule.Frac (GradedModule.FD R n d₀) I) (c : Fin (n + 1) → ℕ)
    (hc : ∀ j ∉ I, c j = 0) :
    GradedModule.sec.mk _ I x
      = GradedModule.sec.mk _ I
          ⟨c + x.denExp, GradedModule.Frac.supp_add I hc x.hden,
            GradedModule.monMul _ c x.num, by
              have h := GradedModule.monMul_mem_grade (GradedModule.FD R n d₀) c _ x.num x.hnum
              convert h using 2
              simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring⟩ := by
  refine (GradedModule.sec_mk_eq _ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
  simp only [zero_add, ← GradedModule.monMul_add_apply]
  exact GradedModule.monMul_congr _ (fun j => by simp [add_comm]) _

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.FD_monMul_apply (c : Fin (n + 1) → ℕ)
    (p : MvPolynomial (Fin (n + 1)) R) :
    GradedModule.monMul (GradedModule.FD R n d₀) c p
      = (∏ j, X j ^ c j) * p := by
  exact GradedModule.free_monMul_apply c p

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.Xprod_mul (c e : Fin (n + 1) → ℕ) :
    (GradedModule.Xprod (R := R) c) * (GradedModule.Xprod e)
      = GradedModule.Xprod (c + e) := by
  unfold GradedModule.Xprod
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun j _ => (pow_add _ _ _).symm)

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.coeff_Xprod (e : Fin (n + 1) → ℕ) (s : Fin (n + 1) →₀ ℕ) :
    ((GradedModule.Xprod (R := R) e)).coeff s
      = if s = ∑ j, Finsupp.single j (e j) then 1 else 0 := by
  unfold GradedModule.Xprod
  rw [show (∏ j, (X j : MvPolynomial (Fin (n+1)) R) ^ e j)
      = MvPolynomial.monomial (∑ j, Finsupp.single j (e j)) 1 from by
    rw [MvPolynomial.monomial_sum_one]
    exact Finset.prod_congr rfl fun j _ => MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_monomial]
  simp only [eq_comm]

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.sec_mk_Xprod_eq_twistFrac (I : Finset (Fin (n + 1)))
    (a e : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0)
    (hdeg : (GradedModule.Xprod (R := R) e) ∈ (GradedModule.FD R n d₀).grade (∑ j, (a j : ℤ)))
    (b : Twist.Mon n d₀ I) (hb : ∀ j, b.1 j = (e j : ℤ) - (a j : ℤ)) :
    GradedModule.sec.mk (GradedModule.FD R n d₀) I ⟨a, ha, GradedModule.Xprod e, hdeg⟩
      = GradedModule.sec.mk _ I (GradedModule.twistFrac d₀ b) := by
  refine (GradedModule.sec_mk_eq _ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
  have key : (GradedModule.Xprod (R := R) (fun j => (- b.1 j).toNat)) * GradedModule.Xprod e
      = (GradedModule.Xprod (R := R) a) * GradedModule.Xprod (fun j => (b.1 j).toNat) := by
    rw [GradedModule.Xprod_mul, GradedModule.Xprod_mul]
    congr 1; ext j; simp only [Pi.add_apply, hb]; omega
  simp only [zero_add, GradedModule.FD_monMul_apply, GradedModule.twistFrac]
  exact key

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.secMkAt_FD_injective (I : Finset (Fin (n + 1)))
    (a : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    Function.Injective (GradedModule.secMkAt (GradedModule.FD R n d₀) I a ha) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨p, hp⟩ hker
  refine Subtype.ext ?_
  simp only [GradedModule.secMkAt, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at hker
  have hrel := (GradedModule.sec_mk_eq _ I).mp hker
  obtain ⟨c, _hc, heq⟩ := hrel
  simp only [map_zero] at heq

  have := GradedModule.free_monMul_injective (R := R) (n := n) (c + 0)
    (heq.trans (map_zero _).symm)
  exact this

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.twistToGradSec_injective (I : Finset (Fin (n + 1))) :
    Function.Injective (GradedModule.twistToGradSec (R := R) (n := n) d₀ I) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  classical

  set a₀ : Fin (n + 1) → ℕ := fun j => f.support.sup (fun b => (- b.1 j).toNat) with ha₀_def
  have ha₀I : ∀ j ∉ I, a₀ j = 0 := by
    intro j hj
    exact Nat.le_zero.mp (Finset.sup_le fun b _ =>
      Nat.le_zero.mpr ((GradedModule.twistFrac (R := R) d₀ b).hden j hj))
  have ha₀b_nn : ∀ b ∈ f.support, ∀ j, (0:ℤ) ≤ (a₀ j : ℤ) + b.1 j := by
    intro b hb j
    have hle : (- b.1 j).toNat ≤ a₀ j := Finset.le_sup (f := fun b => (- b.1 j).toNat) hb
    omega

  have habdeg : ∀ b ∈ f.support, (∑ j, (a₀ j : ℤ)) + d₀
      = ∑ j, (((a₀ j : ℤ) + b.1 j).toNat : ℤ) := by
    intro b hb
    have hsb := b.2.1
    calc (∑ j, (a₀ j : ℤ)) + d₀ = ∑ j, ((a₀ j : ℤ) + b.1 j) := by
          rw [Finset.sum_add_distrib, hsb]
      _ = ∑ j, (((a₀ j : ℤ) + b.1 j).toNat : ℤ) :=
          Finset.sum_congr rfl fun j _ => (Int.toNat_of_nonneg (ha₀b_nn b hb j)).symm
  have hXpm : ∀ b ∈ f.support,
      (GradedModule.Xprod (R := R) (fun j => ((a₀ j : ℤ) + b.1 j).toNat))
        ∈ (GradedModule.FD R n d₀).grade (∑ j, (a₀ j : ℤ)) :=
    fun b hb => GradedModule.Xprod_mem_freeGrade _ (habdeg b hb)
  have hrew : ∀ b (hb : b ∈ f.support),
      GradedModule.sec.mk _ I (GradedModule.twistFrac d₀ b)
        = GradedModule.secMkAt (GradedModule.FD R n d₀) I a₀ ha₀I
            ⟨GradedModule.Xprod (fun j => ((a₀ j : ℤ) + b.1 j).toNat), hXpm b hb⟩ := by
    intro b hb
    refine (GradedModule.sec_mk_Xprod_eq_twistFrac d₀ I a₀ _ ha₀I (hXpm b hb) b
      (fun j => ?_)).symm
    rw [Int.toNat_of_nonneg (ha₀b_nn b hb j)]; ring

  simp only [LinearMap.mem_ker, GradedModule.twistToGradSec,
    Finsupp.linearCombination_apply, Finsupp.sum] at hf
  rw [← Finset.sum_attach] at hf
  have hf' : GradedModule.secMkAt (GradedModule.FD R n d₀) I a₀ ha₀I
      (∑ e ∈ f.support.attach, f e.1 •
        ⟨GradedModule.Xprod (fun j => ((a₀ j : ℤ) + e.1.1 j).toNat), hXpm e.1 e.2⟩) = 0 := by
    rw [map_sum]; simp_rw [LinearMap.map_smul]
    rw [← hf]; exact Finset.sum_congr rfl fun e _ => congrArg (f e.1 • ·) (hrew e.1 e.2).symm

  have hpz := GradedModule.secMkAt_FD_injective d₀ I a₀ ha₀I
    (hf'.trans (map_zero _).symm)
  rw [Subtype.ext_iff] at hpz
  simp only [Submodule.coe_sum, SetLike.val_smul, Submodule.coe_zero] at hpz

  change (∑ x ∈ f.support.attach, f x.1 •
    GradedModule.Xprod (R := R) (fun j => ((a₀ j : ℤ) + x.1.1 j).toNat))
      = (0 : MvPolynomial (Fin (n + 1)) R) at hpz

  have hcoeffs : ∀ s : Fin (n + 1) →₀ ℕ,
      ∑ e ∈ f.support.attach,
        f e.1 * (if s = ∑ j, Finsupp.single j ((a₀ j : ℤ) + e.1.1 j).toNat then (1:R) else 0)
          = 0 := by
    intro s
    have hc := congrArg (AddMonoidAlgebra.coeff · s) hpz
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, MvPolynomial.coeff_sum] at hc
    refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) hc
    rw [MvPolynomial.coeff_smul, GradedModule.coeff_Xprod, smul_eq_mul]

  ext b₀
  by_cases hb₀ : b₀ ∈ f.support
  · have hkey := hcoeffs (∑ j, Finsupp.single j ((a₀ j : ℤ) + b₀.1 j).toNat)
    rw [Finset.sum_eq_single (⟨b₀, hb₀⟩ : {x // x ∈ f.support})] at hkey
    · simpa using hkey
    · rintro ⟨b, hb⟩ _ hne
      rw [if_neg, mul_zero]
      intro heq
      refine hne (Subtype.ext (Subtype.ext (funext fun j => ?_)))
      have hj := Finsupp.ext_iff.mp heq j
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at hj
      have hnn := ha₀b_nn b hb j; have hnn₀ := ha₀b_nn b₀ hb₀ j
      show b.1 j = b₀.1 j
      omega
    · intro hne; exact absurd (Finset.mem_attach _ _) hne
  · exact (Finsupp.notMem_support_iff.mp hb₀).trans rfl

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.twistToGradSec_surjective (I : Finset (Fin (n + 1))) :
    Function.Surjective (GradedModule.twistToGradSec (R := R) (n := n) d₀ I) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro z -
  obtain ⟨⟨a, ha, m, hm⟩⟩ := z
  change GradedModule.secMkAt (GradedModule.FD R n d₀) I a ha ⟨m, hm⟩
    ∈ LinearMap.range (GradedModule.twistToGradSec d₀ I)

  by_cases hsign : (0 : ℤ) ≤ (∑ j, (a j : ℤ)) + d₀
  ·
    have hmh : m.IsHomogeneous (((∑ j, (a j : ℤ)) + d₀).toNat) :=
      (mem_homogeneousSubmodule _ _).mp ((GradedModule.freeGrade_of_nonneg R n hsign) ▸ hm)
    have hedeg : ∀ e ∈ m.support, (∑ j, (a j : ℤ)) + d₀ = ∑ j, (e j : ℤ) := by
      intro e he
      have hk : e.degree = ((∑ j, (a j : ℤ)) + d₀).toNat := by
        by_contra hne; exact (MvPolynomial.mem_support_iff.mp he) (hmh.coeff_eq_zero hne)
      calc (∑ j, (a j : ℤ)) + d₀ = ((((∑ j, (a j : ℤ)) + d₀).toNat : ℤ)) :=
            (Int.toNat_of_nonneg hsign).symm
        _ = (e.degree : ℤ) := by rw [hk]
        _ = ∑ j ∈ e.support, (e j : ℤ) := by simp [Finsupp.degree]
        _ = ∑ j, (e j : ℤ) := Finset.sum_subset (Finset.subset_univ _)
              (fun j _ hj => by simp [Finsupp.notMem_support_iff.mp hj])
    have hXpm : ∀ e ∈ m.support,
        (GradedModule.Xprod (R := R) (fun j => e j))
          ∈ (GradedModule.FD R n d₀).grade (∑ j, (a j : ℤ)) :=
      fun e he => GradedModule.Xprod_mem_freeGrade _ (hedeg e he)

    have hmdecomp : (⟨m, hm⟩ : (GradedModule.FD R n d₀).grade (∑ j, (a j : ℤ)))
        = ∑ e ∈ m.support.attach,
            m.coeff e.1 • ⟨GradedModule.Xprod (fun j => e.1 j), hXpm e.1 e.2⟩ := by
      refine Subtype.ext ?_
      simp only [Submodule.coe_sum, SetLike.val_smul, GradedModule.Xprod]
      conv_lhs => rw [m.as_sum]
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        MvPolynomial.C_mul']
      rfl
    rw [hmdecomp, map_sum]
    refine Submodule.sum_mem _ fun e _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_

    set b : Twist.Mon n d₀ I :=
      ⟨fun j => (e.1 j : ℤ) - (a j : ℤ), by
        rw [Finset.sum_sub_distrib, ← hedeg e.1 e.2]; ring, fun j hj => by
        rw [Twist.mem_negSupp] at hj
        by_contra hjI; have := ha j hjI; omega⟩
    refine ⟨Finsupp.single b 1, ?_⟩
    rw [GradedModule.twistToGradSec_single, one_smul]
    exact (GradedModule.sec_mk_Xprod_eq_twistFrac d₀ I a _ ha (hXpm e.1 e.2) b
      (fun j => rfl)).symm
  ·
    have hm0 : m = 0 := by
      have : (GradedModule.FD R n d₀).grade (∑ j, (a j : ℤ)) = ⊥ := by
        show GradedModule.freeGrade R n _ = ⊥
        rw [GradedModule.freeGrade, if_neg hsign]
      rw [this] at hm; exact hm
    rw [show (⟨m, hm⟩ : (GradedModule.FD R n d₀).grade _) = 0 from Subtype.ext hm0, map_zero]
    exact Submodule.zero_mem _

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.secTwistEquiv (I : Finset (Fin (n + 1))) :
    Twist.Sec R n d₀ I ≃ₗ[R] GradedModule.sec (GradedModule.FD R n d₀) I :=
  LinearEquiv.ofBijective (GradedModule.twistToGradSec d₀ I)
    ⟨GradedModule.twistToGradSec_injective d₀ I,
      GradedModule.twistToGradSec_surjective d₀ I⟩

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.cochainTwistEquiv (i : ℕ) :
    Twist.cochain R n d₀ i
      ≃ₗ[R] GradedModule.cochain (GradedModule.FD R n d₀) i :=
  LinearEquiv.piCongrRight (fun s => GradedModule.secTwistEquiv d₀ (Idx.img n s))

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.cochainTwistEquiv_comm (i : ℕ) :
    (GradedModule.d (GradedModule.FD R n d₀) i).comp
        (GradedModule.cochainTwistEquiv (R := R) (n := n) d₀ i).toLinearMap
      = (GradedModule.cochainTwistEquiv (R := R) (n := n) d₀ (i + 1)).toLinearMap.comp
          (Twist.d R n d₀ i) := by
  refine LinearMap.ext fun f => funext fun s => ?_
  simp only [LinearMap.comp_apply, GradedModule.d_apply, Twist.d_apply,
    GradedModule.cochainTwistEquiv, LinearEquiv.coe_toLinearMap,
    LinearEquiv.piCongrRight_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ (j : ℕ)),
    show (((-1 : ℤ) ^ (j : ℕ) : ℤ) : R) = (-1 : R) ^ (j : ℕ) from by push_cast; ring]
  refine congrArg (((-1 : R) ^ (j : ℕ)) • ·) ?_
  simp only [GradedModule.faceRes, Twist.faceRes, GradedModule.secTwistEquiv,
    LinearEquiv.ofBijective_apply]
  exact LinearMap.congr_fun
    (GradedModule.twistToGradSec_incl d₀ (Idx.img_face_subset n s j))
    (f (Idx.face n s j))

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.cochainTwistEquiv_ker (k : ℕ) :
    (LinearMap.ker (Twist.d R n d₀ k)).map
        (GradedModule.cochainTwistEquiv (R := R) (n := n) d₀ k).toLinearMap
      = LinearMap.ker (GradedModule.d (GradedModule.FD R n d₀) k) := by
  have hcomm := GradedModule.cochainTwistEquiv_comm (R := R) (n := n) d₀ k
  have hcomap : (LinearMap.ker (GradedModule.d (GradedModule.FD R n d₀) k)).comap
      (GradedModule.cochainTwistEquiv (R := R) (n := n) d₀ k).toLinearMap
        = LinearMap.ker (Twist.d R n d₀ k) := by
    rw [← LinearMap.ker_comp, hcomm, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  rw [← hcomap, Submodule.map_comap_eq_of_surjective
    (GradedModule.cochainTwistEquiv d₀ k).surjective]

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.cochainTwistEquiv_range (k : ℕ) :
    (LinearMap.range (Twist.d R n d₀ k)).map
        (GradedModule.cochainTwistEquiv (R := R) (n := n) d₀ (k + 1)).toLinearMap
      = LinearMap.range (GradedModule.d (GradedModule.FD R n d₀) k) := by
  rw [LinearMap.range_eq_map, ← Submodule.map_comp,
    ← GradedModule.cochainTwistEquiv_comm, Submodule.map_comp, Submodule.map_top,
    LinearEquiv.range, Submodule.map_top]

r2nos_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.HTwistEquiv (i : ℕ) :
    Twist.H R n d₀ i ≃ₗ[R] GradedModule.H (GradedModule.FD R n d₀) i := by
  rcases i with _ | j
  ·
    exact ((GradedModule.cochainTwistEquiv d₀ 0).submoduleMap _).trans
      (LinearEquiv.ofEq _ _ (GradedModule.cochainTwistEquiv_ker d₀ 0))
  ·
    set E := GradedModule.cochainTwistEquiv (R := R) (n := n) d₀ (j + 1)
    set Eker : LinearMap.ker (Twist.d R n d₀ (j + 1))
        ≃ₗ[R] LinearMap.ker (GradedModule.d (GradedModule.FD R n d₀) (j + 1)) :=
      (E.submoduleMap _).trans
        (LinearEquiv.ofEq _ _ (GradedModule.cochainTwistEquiv_ker d₀ (j + 1))) with hEker
    refine Submodule.Quotient.equiv _ _ Eker ?_

    have hEker_apply : ∀ y hy,
        ((Eker ⟨y, hy⟩ : _) : GradedModule.cochain (GradedModule.FD R n d₀) (j + 1)) = E y := by
      intro y hy
      simp only [hEker, LinearEquiv.trans_apply, LinearEquiv.submoduleMap_apply,
        LinearEquiv.coe_ofEq_apply]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨⟨y, hy⟩, hyr, hyx⟩
      have hxy : E y = x := (hEker_apply y hy).symm.trans (congrArg Subtype.val hyx)
      rw [← hxy, ← GradedModule.cochainTwistEquiv_range d₀ j]
      exact Submodule.mem_map_of_mem hyr
    · intro hxr
      rw [← GradedModule.cochainTwistEquiv_range (R := R) (n := n) d₀ j] at hxr
      obtain ⟨y, hyr, hyx⟩ := hxr

      have hyk : y ∈ LinearMap.ker (Twist.d R n d₀ (j + 1)) := by
        obtain ⟨z, hz⟩ := hyr
        exact LinearMap.mem_ker.mpr
          (hz ▸ LinearMap.congr_fun (Twist.d_sq R n d₀ j) z)
      exact ⟨⟨y, hyk⟩, hyr, Subtype.ext ((hEker_apply y hyk).trans hyx)⟩

end Bridge

end ProjSpaceCech

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d₀ : ℤ) (i : ℕ) :
    Nonempty (ProjSpaceCech.Twist.H R n d₀ i ≃ₗ[R] ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) :=
  ⟨ProjSpaceCech.GradedModule.HTwistEquiv (R := R) (n := n) d₀ i⟩

end
end S_ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
