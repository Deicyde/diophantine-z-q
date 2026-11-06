import ZInQKernel.Compiler.Circuits.Packed.Construction
import ZInQKernel.Compiler.Circuits.Scope
import ZInQKernel.Compiler.Circuits.PowerTemplate

/-!
# Well-scopedness of the compiled circuits

The packed-history construction and the power template preserve the scope invariant, so their
natural circuits are well scoped.
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM

variable {k : ℕ}

theorem pres_freshN (n : ℕ) : Pres k (freshN n) := by
  induction n with
  | zero => exact Pres.pure _
  | succ n ih => exact Pres.fresh.bind fun _ => ih.bind fun _ => Pres.pure _

theorem pres_appendM {m₁ m₂ : NM (List NForm)} (h₁ : Pres k m₁) (h₂ : Pres k m₂) :
    Pres k (appendM m₁ m₂) := h₁.bind fun _ => h₂.bind fun _ => Pres.pure _

theorem pres_seqConcat : ∀ (ms : List (NM (List NForm))), (∀ m ∈ ms, Pres k m) →
    Pres k (seqConcat ms)
  | [], _ => Pres.pure _
  | m :: ms, h => pres_appendM (h m List.mem_cons_self)
      (pres_seqConcat ms fun m' hm => h m' (List.mem_cons_of_mem _ hm))

theorem pres_subBranches (zero : Ex) (S N : List Ex) (i : ℕ) (p : Program) :
    Pres k (subBranches zero S N i p) := by
  induction p generalizing i with
  | nil => exact Pres.pure _
  | cons ins rest ih =>
    cases ins with
    | dec j x y =>
      exact Pres.fresh.bind fun V => Pres.fresh.bind fun W =>
        (Pres.seqM_cons (Pres.bitAnd _ _ _ _) (Pres.seqM_cons ((Pres.addL _).bind fun _ =>
          Pres.pure _) Pres.seqM_nil)).bind fun _ => (ih _).bind fun _ => Pres.pure _
    | inc j x => exact ih _
    | halt => exact ih _

theorem pres_construction (p : Program) (r : ℕ) : Pres k (construction p r k) := by
  unfold construction
  refine (Pres.constant _).bind fun zero => (Pres.constant _).bind fun one => ?_
  refine Pres.fresh.bind fun q => Pres.fresh.bind fun c => Pres.fresh.bind fun K => ?_
  refine Pres.fresh.bind fun B => Pres.fresh.bind fun T => Pres.fresh.bind fun F => ?_
  refine Pres.fresh.bind fun D => (pres_freshN _).bind fun R => (pres_freshN _).bind fun N => ?_
  refine (pres_freshN _).bind fun S => ?_
  refine Pres.bind ?_ fun _ => Pres.pure _
  unfold packedFormulas
  refine pres_appendM ?_ (pres_appendM ?_ (pres_appendM ?_ (pres_appendM ?_ ?_)))
  · unfold items1
    refine Pres.seqM_all _ fun m hm => ?_
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_nil_iff, or_false] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | ⟨ai, -, rfl⟩
    · exact Pres.lt _ _
    · exact (Pres.constant _).bind fun _ => Pres.power _ _ _ _
    · exact (Pres.scale _ _).bind fun _ => Pres.pure _
    · exact (Pres.constant _).bind fun _ => Pres.lt _ _
    · exact Pres.power _ _ _ _
    · exact Pres.lt _ _
  · unfold items2
    refine Pres.seqM_all _ fun m hm => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact (Pres.mulL _).bind fun _ => (Pres.addL _).bind fun _ => (Pres.mulL _).bind fun _ =>
        (Pres.addL _).bind fun _ => Pres.pure _
    · exact (Pres.addL _).bind fun _ => (Pres.mulL _).bind fun _ => Pres.pure _
    · exact (Pres.addL _).bind fun _ => Pres.pure _
    · exact Pres.pure _
  · unfold items3
    refine Pres.seqM_all _ fun m hm => ?_
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
    exact Pres.mask _ _ _
  · unfold items4
    refine pres_seqConcat _ fun m hm => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
    unfold registerMasks
    exact Pres.seqM_cons (Pres.mask _ _ _) (Pres.seqM_cons (Pres.lt _ _) (Pres.seqM_cons
      ((Pres.mulL _).bind fun _ => (Pres.addL _).bind fun _ => (Pres.mulL _).bind fun _ =>
        Pres.bitAnd _ _ _ _) Pres.seqM_nil))
  · refine (pres_subBranches _ _ _ _ _).bind fun sb => pres_appendM (Pres.pure _) ?_
    refine pres_appendM ?_ ?_
    · unfold items6
      refine Pres.seqM_all _ fun m hm => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
      unfold registerEq
      exact (Pres.addL _).bind fun _ => (Pres.mulL _).bind fun _ => (Pres.addL _).bind fun _ =>
        (Pres.mulL _).bind fun _ => (Pres.addL _).bind fun _ => (Pres.mulL _).bind fun _ =>
          (Pres.addL _).bind fun _ => Pres.pure _
    · unfold items7
      refine Pres.seqM_all _ fun m hm => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hm
      unfold stateEq
      exact (Pres.addL _).bind fun _ => (Pres.mulL _).bind fun _ => (Pres.addL _).bind fun _ =>
        Pres.pure _

/-- **The compiled circuit is well scoped.** -/
theorem compiled_wellScoped (p : Program) (r k : ℕ) : (compiled p r k).WellScoped :=
  toCircuit_wellScoped (pres_construction p r)

/-- **The power template circuit is well scoped.** -/
theorem powerTemplateCircuit_wellScoped : powerTemplateCircuit.WellScoped :=
  toCircuit_wellScoped (Pres.power .flat _ _ _)

end ZInQ.Compiler.Packed
