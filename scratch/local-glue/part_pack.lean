
noncomputable section

/-! ## §8 (local-glue). The packs: G8's data with the local glue replaced by Props on `A/K`

`G8LocalPack` is copied verbatim from scratch/local-data/tail_part.lean (the hypothesis of
local-data's tail `modularConstituent_tail_L`). `G7LocalPackK` asks instead for G7's data
(`G7Out`), G8's output, the clauses, `KerWild`, and the torsion-point Props `TorsFixWild`
(`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper` (`p = 2`) at the primes in `P`. -/

namespace G0ModNewform

open PkgI4 (Qbar GQ GaloisRep)
open PkgI3

-- BEGIN verbatim copy (scratch/local-data/tail_part.lean)
/-- **G8's data for a representation `r` at coefficient prime `ℓ`, with the G4/G7 clauses and
the local glue at the primes `p ∈ P`** (`G15Ram.G7Clauses`, `G15Ram.LocalGlue`). -/
def G8LocalPack (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (a β : GQ → PadicAlgCl ℓ)
    (ε : GQ → GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ Qbar),
    G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G15Ram.G7Clauses β ε L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p → @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β L

-- END verbatim copy

/-- **G7's data for `r` at coefficient prime `ℓ`, with the local glue at `p ∈ P` as Props on the
abelian surface `A/K` (GLUE).** -/
def G7LocalPackK (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → @G15Ram.TorsFixWild p ⟨hp⟩ K _ _ A ℓ _) ∧
      (p ≤ 5 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L) ∧
      (p = 2 → @G15Ram.BetaUpper p ⟨hp⟩ ℓ _ β (@G15Ram.Lv p ⟨hp⟩ L) U0)

/-- **`G8LocalPack` from `G7LocalPackK` (proved)**, by `G15Ram.localGlue_of_g7`. -/
theorem g8LocalPack_of_K {ℓ : ℕ} [Fact ℓ.Prime] {r : GaloisRep ℓ 2} {P : ℕ → Prop}
    (h : G7LocalPackK ℓ r P) : G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hE, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_g7 h7 hC hK (fun h => G15Ram.tateWildK_of_torsFixWild (hW h))
    (fun h => G15Ram.tateWildKE_of_torsFixWildE (hE h)) hB

/-- **G15's open Prop `G15RamG` from the packs (proved)**: g15-ram's `G15RamG D u` follows from
G7's data for `D.r5` (local glue at `p ≠ 5`) and for `D.r3` (at `p = 5`), and G11's outputs. -/
theorem g15RamG_of_packK {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) (h5 : G7LocalPackK 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackK 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ := g8LocalPack_of_K h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ := g8LocalPack_of_K h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` in leaf-and-bridge form (GLUE).**
At `p ≥ 7`: `RaynaudPlace A 3`, `RaynaudPlace A 7` (R6 at the place) and `PtFinite A`; at
`p ∈ {3, 5}`: `TorsFixWildOdd`; at `p = 2`: `TorsFixWildE` and `BetaTwist2` (which replaces
`BetaUpper`, `G15Ram.betaUpper_of_twist`). With the leaf I2-Tors
and `p ≠ ℓ` on `P`, it gives `G7LocalPackK` (`g7LocalPackK_of_R`). -/
def G7LocalPackR (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧ G15Ram.PtFinite A ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → @G15Ram.RaynaudPlace p ⟨hp⟩ K _ _ A 3 ∧ @G15Ram.RaynaudPlace p ⟨hp⟩ K _ _ A 7) ∧
      (3 ≤ p → p ≤ 5 → @G15Ram.TorsFixWildOdd p ⟨hp⟩ K _ _ A ℓ _ L) ∧
      (p = 2 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L ∧ @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G7LocalPackK` from `G7LocalPackR`, the leaf I2-Tors and `p ≠ ℓ` on `P` (proved).** -/
theorem g7LocalPackK_of_R (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackR ℓ r P) :
    G7LocalPackK ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hPt, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hR, hO, h2⟩ := hloc p hp hP
  refine ⟨fun h7p => ?_, fun h5 => ?_, fun h2' => G15Ram.betaUpper_of_twist hC (h2 h2').2⟩
  · obtain ⟨hR3, hR7⟩ := hR h7p
    exact G15Ram.torsFixWild_of_raynaud (Ne.symm (hPℓ p hP)) h7p
      (G15Ram.wildIter_of_ptFinite hPt) (G15Ram.torsGL_of_leaf hTors A h7.1 3 (by norm_num))
      (G15Ram.torsGL_of_leaf hTors A h7.1 7 (by norm_num)) hR3 hR7
  · by_cases hp2 : p = 2
    · exact (h2 hp2).1
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact G15Ram.torsFixWildE_of_odd hp2 hC (hO h3 h5)

/-- **`G15RamG` from the leaf-and-bridge packs and I2-Tors (proved).** -/
theorem g15RamG_of_packR (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackR 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackR 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u :=
  g15RamG_of_packK D u (g7LocalPackK_of_R hTors (fun _ h => h) h5)
    (g7LocalPackK_of_R hTors (fun p h => by rw [h]; norm_num) h3) h11₅ h11₃

end G0ModNewform

end

#print axioms G0ModNewform.g8LocalPack_of_K
#print axioms G0ModNewform.g15RamG_of_packK
#print axioms G0ModNewform.g7LocalPackK_of_R
#print axioms G0ModNewform.g15RamG_of_packR
