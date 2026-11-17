/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/Algebra/Group/Subgroup/FiniteFiltration.lean
Original SHA-256: fbd04d08ccdd3327dcbef503a17258f5e81619b096dec3c0101be780135edfdf
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/Algebra/Group/Subgroup/FiniteFiltration.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.SetLike.Fintype
import Mathlib.Order.OrderIsoNat
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section

namespace TauCeti.Subgroup

variable {G : Type*} [Group G]

/- An antitone sequence of subgroups with finite first term eventually equals its intersection. -/
theorem exists_forall_eq_iInf_of_antitone (f : ℕ → Subgroup G) (hf : Antitone f)
    [Finite (f 0)] : ∃ N, ∀ i, N ≤ i → f i = ⨅ j, f j := by
  classical
  let _ := Fintype.ofFinite (f 0)
  have hsubgroupOf : Antitone fun i ↦ (f i).subgroupOf (f 0) :=
    fun _ _ hij ↦ Subgroup.subgroupOf_mono _ (hf hij)
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hsubgroupOf
  have hstable : ∀ i, N ≤ i → f N = f i := by
    intro i hi
    apply le_antisymm
    · intro g hg
      have hg0 : g ∈ f 0 := hf (Nat.zero_le N) hg
      have hgN : (⟨g, hg0⟩ : f 0) ∈ (f N).subgroupOf (f 0) :=
        Subgroup.mem_subgroupOf.mpr hg
      exact Subgroup.mem_subgroupOf.mp (hN i hi ▸ hgN)
    · exact hf hi
  have hN_iInf : f N = ⨅ j, f j := by
    apply le_antisymm
    · refine le_iInf fun j ↦ ?_
      rcases le_total N j with hNj | hjN
      · exact (hstable j hNj).le
      · exact hf hjN
    · exact iInf_le f N
  exact ⟨N, fun i hi ↦ (hstable i hi).symm.trans hN_iInf⟩

/- An antitone sequence of subgroups with finite first term and trivial intersection is
eventually the trivial subgroup. -/
end TauCeti.Subgroup
