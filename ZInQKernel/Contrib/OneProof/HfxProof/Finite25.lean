import ZInQKernel.Contrib.OneProof.T21Proof.Finite

/-!
# hfx-proof: TYZ Lemma 2.5, the finite part (kernel `decide`)

Task hfx-proof. Every residue `r ∈ (O_B/4O_B)^×` (Hurwitz coordinates mod 4, odd norm) is
`± μ (1 + 2x_t)` for a Hurwitz unit `μ` and one of TYZ's 8 representatives `β_t = 1 + 2x_t`
(TYZ L645–661): the 8 classes exhaust `O_B^× \ (O_B/4)^× / {±1}`.
-/

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.T21Proof

/-- Scalar multiple in `H4 (ZMod 4)`. -/
def scal4 (s : ZMod 4) (v : H4 (ZMod 4)) : H4 (ZMod 4) := ⟨s * v.a0, s * v.a1, s * v.a2, s * v.a3⟩

/-- The index `t` read off from `1 + 2x_t (mod 4)`. -/
def tOf (v : H4 (ZMod 4)) : Fin 2 × Fin 2 × Fin 2 :=
  (⟨v.a1.val / 2 % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨v.a2.val / 2 % 2, Nat.mod_lt _ (by norm_num)⟩,
    ⟨v.a3.val / 2 % 2, Nat.mod_lt _ (by norm_num)⟩)

/-- **The 8 classes cover `(O_B/4)^×`.** -/
theorem lemma25_check : ∀ a0 a1 a2 a3 : ZMod 4, nrdH (⟨a0, a1, a2, a3⟩ : H4 (ZMod 4)) ≠ 0 →
    nrdH (⟨a0, a1, a2, a3⟩ : H4 (ZMod 4)) ≠ 2 →
    ∃ μ ∈ unitList, ∃ s : Fin 2, (⟨a0, a1, a2, a3⟩ : H4 (ZMod 4)) =
      mapH (Int.castRingHom (ZMod 4)) (smulH (sg s) (mulH μ (βZ (tOf (scal4 (sg s : ZMod 4)
        (mulH (starH (mapH (Int.castRingHom (ZMod 4)) μ)) ⟨a0, a1, a2, a3⟩)))))) := by
  decide +kernel

end ZInQ.Contrib.HfxProof
