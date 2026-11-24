import ZInQKernel.Contrib.OneProof.GR56Lattice
import ZInQKernel.Contrib.OneProof.EichlerBound.Bound

/-!
# eichler-bound: `GR56.R5fpCountLe` without Eichler's formula

`GR56.R5fpCountLe` (the bound `#CM(R) ≤ 2^{b(k)} h(R)`, the only half of `gonzalezRotgerProp56X6` that the chain
reads, through `HDec.FS5NoCM.nocm_on_witness`) is proved here from the three textbook fields
`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed` alone, **with no new leaf**:

* `GR56.card_cmSet_le` (gr56-prove): `#CM(R) ≤ #(Emb(R, 𝒪)/𝒪^×)` from the three textbook fields;
* `EichlerBound.conjRel_card_le` (this task, `EichlerBound/*.lean`): `#(Emb(R, 𝒪)/𝒪^×) ≤ 2^{b(k)} · #Pic(R)` for
  the maximal order `𝒪` of `B = (2, −3 | ℚ)` and every order `R` of conductor prime to `6`, by an explicit
  injection `Emb(R, 𝒪)/𝒪^× ↪ Pic(R) × T` (`#T = 2^{b(k)}`, the types at `2` and `3`), proved from class number one
  of `𝒪` (its norm-Euclidean algorithm), the intertwiner lattice of two embeddings, a polynomial certificate at
  the primes `ℓ ∤ 6` and the uniformizers `i`, `j` at `2` and `3`. This replaces `GRCountX6.EichlerOptEmbCount6`.

No `sorry`; standard axioms only.
-/

namespace EichlerBound

/-- **The optimal-embedding bound for `𝒪 ⊂ (2, −3 | ℚ)`** (proved, no leaf): for an order `R` of conductor prime
to `6` in a quadratic field `k`, the `𝒪^×`-classes of optimal embeddings `R ↪ 𝒪` are finitely many and at most
`2^{b(k)} · #Pic(R)`. (Eichler's formula gives equality; only the bound is proved here.) -/
theorem eichlerOptEmbBound6 (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2)
    (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (LeafQM.AV.conductor R) 6) (hh : Nat.card (CommRing.Pic R) ≠ 0) :
    Finite (Quot (GRCountX6.ConjRel R)) ∧
      Nat.card (Quot (GRCountX6.ConjRel R)) ≤ 2 ^ LeafQM.AV.inertCount6 k * Nat.card (CommRing.Pic R) :=
  conjRel_card_le k hk R hR hc hh

/-- **`GR56.R5fpCountLe` from the three textbook fields alone** (replaces `GR56.r5fpCountLe_of_eichler`, which
also needed the leaf `GRCountX6.EichlerOptEmbCount6`). -/
theorem r5fpCountLe_proof (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : GR56.R5fpCountLe := by
  intro k _ _ _ hk R hR hc hh
  obtain ⟨hfin, hle⟩ := eichlerOptEmbBound6 k hk R hR hc hh
  obtain ⟨hf, hle'⟩ := GR56.card_cmSet_le hU hG hM k hk R hR hc hfin
  exact ⟨hf, hle'.trans hle⟩

end EichlerBound
