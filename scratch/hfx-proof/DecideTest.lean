import ZInQKernel.Contrib.OneProof.T21Proof.Finite

open ZInQ.Contrib.T21Proof

def IsTRForm (v : H4 (ZMod 4)) : Prop :=
  v.a0 = 1 ∧ v.a1.val % 2 = 0 ∧ v.a2.val % 2 = 0 ∧ v.a3.val % 2 = 0

instance (v : H4 (ZMod 4)) : Decidable (IsTRForm v) := by unfold IsTRForm; infer_instance

def scal4 (s : ZMod 4) (v : H4 (ZMod 4)) : H4 (ZMod 4) := ⟨s * v.a0, s * v.a1, s * v.a2, s * v.a3⟩

set_option maxRecDepth 100000 in
theorem lemma25_check : ∀ a0 a1 a2 a3 : ZMod 4, nrdH (⟨a0, a1, a2, a3⟩ : H4 (ZMod 4)) ≠ 0 →
    nrdH (⟨a0, a1, a2, a3⟩ : H4 (ZMod 4)) ≠ 2 →
    ∃ μ ∈ unitList, ∃ s : Fin 2, IsTRForm (scal4 (sg s : ZMod 4)
      (mulH (starH (mapH (Int.castRingHom (ZMod 4)) μ)) ⟨a0, a1, a2, a3⟩)) := by
  decide +kernel
