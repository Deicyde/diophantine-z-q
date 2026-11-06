import ZInQKernel.Compiler.Circuits.Packed.Semantics
import ZInQKernel.Compiler.Circuits.Packed.Valid
import ZInQKernel.Compiler.Circuits.Packed.Sound
import ZInQKernel.Compiler.Circuits.Packed.Complete

/-!
# The compiled circuit of a register machine

For a primitive program `p` valid for `r` registers and `1 ≤ k ≤ r`, the compiled circuit
`𝒞_{p,k}` of the packed-history construction has a natural zero with inputs `a` exactly when
`p` accepts `a` (`compiled_natRel_iff`).

(Blueprint: `compiler/natural/packed/register-machine-polynomial.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM Syntax MvPolynomial Finset

/-- The natural relation of a circuit through assignments agreeing with the inputs. -/
theorem natRel_iff_agree (C : NatCircuit) (T : ExPoly) (hk : C.inputCount ≤ C.varCount)
    (a : Fin C.inputCount → ℕ) :
    C.NatRel T a ↔ ∃ y, Agree (NatCircuit.natPoint C.inputCount (C.varCount - C.inputCount) a
      fun _ => 0) y C.inputCount C.varCount ∧ zv y (C.poly T) = 0 := by
  unfold NatCircuit.NatRel
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨_, fun i hi => ?_, hw⟩
    simp only [NatCircuit.natPoint]
    split_ifs with h1 h2 h3 <;> first | rfl | omega
  · rintro ⟨y, hy, h⟩
    refine ⟨fun j => y (C.inputCount + j), ?_⟩
    have hpt : NatCircuit.natPoint C.inputCount (C.varCount - C.inputCount) a
        (fun j => y (C.inputCount + j)) = y := by
      funext i
      simp only [NatCircuit.natPoint]
      split_ifs with h1 h2
      · rw [hy i (by omega)]; simp [NatCircuit.natPoint, h1]
      · congr 1; omega
      · rw [hy i (by omega)]; simp [NatCircuit.natPoint, h1, h2]
    show zv _ _ = 0
    rw [hpt]; exact h

/-- The run of the packed-history construction from the initial state. -/
theorem construction_run (p : Program) (r k : ℕ) : construction p r k (State.init k) =
    let r0 := constant 0 (State.init k)
    let r1 := constant 1 r0.2
    let rq := fresh r1.2
    let rc := fresh rq.2
    let rK := fresh rc.2
    let rB := fresh rK.2
    let rT := fresh rB.2
    let rF := fresh rT.2
    let rD := fresh rF.2
    let rR := freshN r rD.2
    let rN := freshN r rR.2
    let rS := freshN p.length rN.2
    let res := packedFormulas p r (inputs k) r0.1 r1.1 rq.1 rc.1 rK.1 rB.1 rT.1 rF.1 rD.1 rR.1 rN.1
      rS.1 rS.2
    (NForm.and res.1, res.2) := rfl

theorem getD_of_map_eq {L : List Ex} {n : ℕ} {f : ℕ → Poly}
    (h : L.map Ex.poly = (List.range n).map f) {i : ℕ} (hi : i < n) (d : Ex) :
    (L.getD i d).poly = f i := by
  have hl : L.length = n := by simpa using congrArg List.length h
  have := congrArg (fun l => l.getD i 0) h
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using hi),
    List.getD_eq_getElem _ _ (by simpa using hi)] at this
  simpa using this

theorem mem_of_map_eq {L : List Ex} {n : ℕ} {f : ℕ → ℕ}
    (h : L.map Ex.poly = (List.range n).map fun i => X (f i)) :
    ∀ e ∈ L, ∃ i < n, e.poly = X (f i) := by
  intro e he
  have : e.poly ∈ (List.range n).map fun i => X (f i) := h ▸ List.mem_map_of_mem he
  obtain ⟨i, hi, h'⟩ := List.mem_map.1 this
  exact ⟨i, List.mem_range.1 hi, h'.symm⟩

/-- The specification of the packed formulas at the initial state, abstract form. -/
theorem packed_spec (p : Program) (r k : ℕ) (zero one q c K B T F D : Ex) (R N S : List Ex)
    (s1 : State) (hz : zero.poly = C 0) (ho : one.poly = C 1) (hq : q.poly = X k)
    (hc : c.poly = X (k + 1)) (hK : K.poly = X (k + 2)) (hB : B.poly = X (k + 3))
    (hT : T.poly = X (k + 4)) (hF : F.poly = X (k + 5)) (hD : D.poly = X (k + 6))
    (hR : R.map Ex.poly = (List.range r).map fun j => X (k + 7 + j))
    (hN : N.map Ex.poly = (List.range r).map fun j => X (k + 7 + r + j))
    (hS : S.map Ex.poly = (List.range p.length).map fun i => X (k + 7 + 2 * r + i))
    (hs1 : s1.next = k + 7 + 2 * r + p.length) :
    Spec (.and ((packedFormulas p r (inputs k) zero one q c K B T F D R N S s1).1.map
        (NForm.toFormula powerTemplate))) {i | i < k} k
      (packedFormulas p r (inputs k) zero one q c K B T F D R N S s1).2.next fun x =>
      ∃ z, AgreeOut x z (· ∈ {i | k ≤ i ∧ i < k + (7 + 2 * r + p.length)} ∪
          vwSet (packedVW p r (inputs k) zero one q c K B T F D R N S s1)) ∧
        True ∧
        ((0 < z (k + 1) ∧ z (k + 2) = 2 ^ z (k + 1) ∧ z (k + 3) = 4 * z (k + 2) ∧
            p.length < z (k + 3) ∧ z (k + 4) = z (k + 3) ^ z k) ∧
          ∀ e ∈ inputs k, nv z e.poly < z (k + 2)) ∧
        (((z (k + 3) : ℤ) * z (k + 5) + 1 = z (k + 5) + z (k + 3) * z (k + 4)) ∧
          ((z (k + 6) : ℤ) + z (k + 5) = z (k + 2) * z (k + 5)) ∧
          (S.map fun e => zv z e.poly).sum = z (k + 5) ∧
          zv z (S.getLastD zero).poly = z (k + 4)) ∧
        (∀ e ∈ S, Nat.land (nv z e.poly) (z (k + 5)) = nv z e.poly) ∧
        (∀ j < r, Nat.land (z (k + 7 + j)) (z (k + 6)) = z (k + 7 + j) ∧
          z (k + 7 + j) < z (k + 4) ∧
          z (k + 2) * z (k + 7 + r + j) = Nat.land (z (k + 7 + j) + z (k + 6))
            (z (k + 2) * z (k + 5))) ∧
        subRel p zero S N (packedVW p r (inputs k) zero one q c K B T F D R N S s1) z ∧
        (∀ j ∈ List.range r,
          zv z (R.getD j zero).poly + zv z B.poly *
              ((decHandles p zero (packedVW p r (inputs k) zero one q c K B T F D R N S s1) j).map
                fun e => zv z e.poly).sum =
            zv z ((inputs k).getD j zero).poly + zv z B.poly * zv z (R.getD j zero).poly +
              zv z B.poly * ((incHandles p zero S j).map fun e => zv z e.poly).sum) ∧
        (∀ i ∈ List.range p.length,
          zv z (S.getD i zero).poly = zv z (if i = 0 then one else zero).poly +
            zv z B.poly * ((inHandles p zero S
              (packedVW p r (inputs k) zero one q c K B T F D R N S s1) i).map
                fun e => zv z e.poly).sum) := by
  set U : Set ℕ := {i | i < k} ∪ {i | k ≤ i ∧ i < k + (7 + 2 * r + p.length)}
  have hU : ∀ i ∈ U, i < s1.next := by
    intro i hi; rcases hi with hi | hi
    · simp only [Set.mem_setOf_eq] at hi; omega
    · simp only [Set.mem_setOf_eq] at hi; omega
  have hmem : ∀ i, i < k + 7 + 2 * r + p.length → i ∈ U := by
    intro i hi
    by_cases h : i < k
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
  have hP := packedFormulas_specE (τ := powerTemplate) powerSpec_hierarchical_powerTemplate p r
    (inputs k) zero one q c K B T F D R N S s1 (U := U) (pR := k + 7) (pN := k + 7 + r)
    hz ho hq hc hK hB hT hF hD
    (fun j hj => getD_of_map_eq hR hj zero) (fun j hj => getD_of_map_eq hN hj zero)
    (fun e he => by
      obtain ⟨j, hj, h⟩ := mem_of_map_eq hR e he; exact ⟨_, hmem _ (by omega), h⟩)
    (fun e he => by
      obtain ⟨j, hj, h⟩ := mem_of_map_eq hN e he; exact ⟨_, hmem _ (by omega), h⟩)
    (fun e he => by
      obtain ⟨j, hj, h⟩ := mem_of_map_eq hS e he; exact ⟨_, hmem _ (by omega), h⟩)
    (fun e he => by
      simp only [inputs, List.mem_map, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he; exact ⟨i, Or.inl hi, rfl⟩)
    ⟨hmem _ (by omega), hmem _ (by omega), hmem _ (by omega), hmem _ (by omega),
      hmem _ (by omega), hmem _ (by omega), hmem _ (by omega)⟩
    (fun j hj => hmem _ (by omega)) (fun j hj => hmem _ (by omega)) hU
  have hE := SpecE.expose {i | i < k} k (7 + 2 * r + p.length)
  rw [show k + (7 + 2 * r + p.length) = s1.next by omega] at hE
  have := (hE.append (hP.mono fun i hi => by
    rcases hi with hi | hi <;> simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢ <;> omega)
    (fun i hi => hi)).close
  have hS' : k + (7 + 2 * r + p.length) = s1.next := by omega
  simp only [List.nil_append] at this
  rw [hS']
  convert this using 3

end ZInQ.Compiler.Packed
