import ZInQKernel.Compiler.Universal.NodeCheck
import ZInQ.CantorDecoder

/-!
# The five-input specialization of a two-input circuit

For a natural circuit `ℋ` with inputs `X_0, X_1` and an integer `c₃`, `specialize ℋ c₃` is the
natural circuit with `5` inputs obtained as follows.

1. *Variables.* Inputs `X_0, …, X_4`, pairing variables `X_5, …, X_8` (`t_0, …, t_3`); every
   variable `X_i` of `ℋ` with `i ≥ 2` becomes `X_{i+7}`, every block start `w` becomes `w + 7`.
   The explicit variables are `0, …, 8` followed by the shifted explicit witnesses of `ℋ`, and
   the variable count is that of `ℋ` plus `7`.
2. *Nodes.* The node list of `ℋ`, in order, with the variable node of `X_0` replaced by the
   constant node `c₃`, that of `X_1` by the variable node of `X_5`, every other variable node
   and every call block start shifted by `7`; followed by the `52` nodes: the variable nodes of
   `X_0, …, X_4, X_6, X_7, X_8`, the constants `1, 2, -1`, for `i = 0, 1, 2, 3` (with
   `t_4 = X_4`) the eight nodes of `π_i = 2t_i + (-1)·((c_i + t_{i+1})(c_i + t_{i+1} + 1) +
   2t_{i+1})`, and the left-nested sum of squares `ρ² + π_0² + ⋯ + π_3²` as root.

Its polynomial is `θ([[ℋ]])² + Σ_i π_i²` for the substitution `θ : X_0 ↦ c₃, X_1 ↦ X_5,
X_i ↦ X_{i+7}` (`specialize_poly`), and for natural `c₃` its natural zeros at `c ∈ ℕ⁵` are the
natural zeros of `ℋ` at `(c₃, enc₅(c))` (`specialize_natRel_iff`).

(Blueprint: `compiler/natural/universal/precision-circuit.md` and
`precision-circuit-specialization.md`, for an arbitrary two-input circuit.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open Natural Syntax MvPolynomial

/-- The renaming of a node of `ℋ`. -/
def renameNode (code : ℤ) : NatNode → NatNode
  | .var 0 => .const code
  | .var 1 => .var 5
  | .var (i + 2) => .var (i + 9)
  | .const c => .const c
  | .add j k => .add j k
  | .mul j k => .mul j k
  | .call a b c w => .call a b c (w + 7)

/-- The eight nodes of a pairing equation `π = 2t + (-1)·((c + t')(c + t' + 1) + 2t')`, stored
from index `b`; `one, two, neg` are the nodes of the constants `1, 2, -1` and `c, t', t` those of
`c, t', t`. -/
def pairingBlock (b one two neg c t' t : ℕ) : List NatNode :=
  [.add c t', .add b one, .mul b (b + 1), .mul two t, .mul two t', .add (b + 2) (b + 4),
    .mul neg (b + 5), .add (b + 3) (b + 6)]

/-- The `52` appended nodes, for a node list of length `L` with root `ρ`. -/
def appendedNodes (L ρ : ℕ) : List NatNode :=
  [.var 0, .var 1, .var 2, .var 3, .var 4, .var 6, .var 7, .var 8,
    .const 1, .const 2, .const (-1)] ++
  pairingBlock (L + 11) (L + 8) (L + 9) (L + 10) L (L + 5) 1 ++
  pairingBlock (L + 19) (L + 8) (L + 9) (L + 10) (L + 1) (L + 6) (L + 5) ++
  pairingBlock (L + 27) (L + 8) (L + 9) (L + 10) (L + 2) (L + 7) (L + 6) ++
  pairingBlock (L + 35) (L + 8) (L + 9) (L + 10) (L + 3) (L + 4) (L + 7) ++
  [.mul ρ ρ, .mul (L + 18) (L + 18), .add (L + 43) (L + 44), .mul (L + 26) (L + 26),
    .add (L + 45) (L + 46), .mul (L + 34) (L + 34), .add (L + 47) (L + 48),
    .mul (L + 42) (L + 42), .add (L + 49) (L + 50)]

/-- **The five-input specialization** of a two-input circuit `H` at the program literal
`code`. -/
def specialize (H : NatCircuit) (code : ℤ) : NatCircuit where
  inputCount := 5
  explicitVars := (List.range 9).map (fun i => (i, if i < 5 then .input else .witness)) ++
    (H.explicitVars.drop 2).map fun v => (v.1 + 7, v.2)
  nodes := H.nodes.map (renameNode code) ++ appendedNodes H.nodes.length H.root
  root := H.nodes.length + 51
  varCount := H.varCount + 7

/-! ### The polynomial -/

/-- The substitution `θ : X_0 ↦ c₃, X_1 ↦ X_5, X_i ↦ X_{i+7}` (`i ≥ 2`). -/
def theta (code : ℤ) : ℕ → Poly
  | 0 => C code
  | 1 => X 5
  | i + 2 => X (i + 9)

/-- The pairing variables `t_0, …, t_3 = X_5, …, X_8` and `t_4 = X_4`. -/
def tVar (i : ℕ) : Poly := if i = 4 then X 4 else X (5 + i)

/-- The pairing polynomial `π_i = 2t_i - (X_i + t_{i+1})(X_i + t_{i+1} + 1) - 2t_{i+1}`. -/
def pairPoly (i : ℕ) : Poly :=
  2 * tVar i - (X i + tVar (i + 1)) * (X i + tVar (i + 1) + 1) - 2 * tVar (i + 1)

theorem getPoly_map_bind₁ (f : ℕ → Poly) (vals : List Poly) (j : ℕ) :
    getPoly (vals.map (bind₁ f)) j = bind₁ f (getPoly vals j) := by
  unfold getPoly
  have h := List.getD_map (l := vals) (n := j) (d := (0 : Poly)) (bind₁ f)
  rw [map_zero] at h
  exact h

theorem bind₁_callPoly (code : ℤ) (P : Poly) (p w : ℕ) (g : Fin p → Poly) (hw : 2 ≤ w) :
    bind₁ (theta code) (callPoly P p w g) = callPoly P p (w + 7) (fun i => bind₁ (theta code) (g i)) := by
  unfold callPoly
  rw [bind₁_bind₁]
  refine congrArg (fun f => bind₁ f P) (funext fun i => ?_)
  unfold callSubst
  split_ifs with h
  · rfl
  · rw [bind₁_X_right]
    obtain ⟨j, hj⟩ : ∃ j, w + (i - p) = j + 2 := ⟨w + (i - p) - 2, by omega⟩
    rw [hj, theta]
    congr 1
    omega

theorem renameNode_denote (code : ℤ) (T : ExPoly) (vals : List Poly) (n : NatNode)
    (hn : ∀ a b c w, n = .call a b c w → 2 ≤ w) :
    (renameNode code n).denote T (vals.map (bind₁ (theta code))) =
      bind₁ (theta code) (n.denote T vals) := by
  cases n with
  | const c => simp [renameNode, NatNode.denote]
  | var i =>
    rcases i with _ | _ | i
    · simp [renameNode, NatNode.denote, theta]
    · simp [renameNode, NatNode.denote, theta]
    · simp [renameNode, NatNode.denote, theta]
  | add j k => simp [renameNode, NatNode.denote, getPoly_map_bind₁]
  | mul j k => simp [renameNode, NatNode.denote, getPoly_map_bind₁]
  | call a b c w =>
    simp only [renameNode, NatNode.denote, getPoly_map_bind₁, ExPoly.call]
    rw [bind₁_callPoly code _ _ _ _ (hn a b c w rfl)]
    congr 1
    funext i
    simp only [callArgs, getPoly]
    rcases i with ⟨_ | _ | _ | i, hi⟩ <;> simp

theorem denoteNatNodes_map_renameNode (code : ℤ) (T : ExPoly) (l : List NatNode)
    (hl : ∀ a b c w, NatNode.call a b c w ∈ l → 2 ≤ w) :
    denoteNatNodes T (l.map (renameNode code)) = (denoteNatNodes T l).map (bind₁ (theta code)) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih =>
    rw [List.map_append, List.map_singleton, denoteNatNodes_append, denoteNatNodes_append,
      ih fun a b c w h => hl a b c w (List.mem_append_left _ h), List.map_append,
      List.map_singleton, renameNode_denote code T _ n fun a b c w h =>
        hl a b c w (List.mem_append_right _ (by simp [h]))]

/-- The pairing polynomial in the node form of `pairingBlock`. -/
def pairNodePoly (c t' t : Poly) : Poly :=
  C 2 * t + C (-1) * ((c + t') * ((c + t') + C 1) + C 2 * t')

theorem getPoly_append_length (vals l : List Poly) (j : ℕ) :
    getPoly (vals ++ l) (vals.length + j) = l.getD j 0 := by
  unfold getPoly
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem getPoly_append_length' (vals l : List Poly) :
    getPoly (vals ++ l) vals.length = l.getD 0 0 := by
  simpa using getPoly_append_length vals l 0

theorem getPoly_append_lt (vals l : List Poly) {j : ℕ} (hj : j < vals.length) :
    getPoly (vals ++ l) j = getPoly vals j := by
  unfold getPoly
  rw [List.getD_append _ _ _ _ hj]

/-- The denotation of the appended nodes. -/
theorem foldl_appendedNodes (T : ExPoly) (vals : List Poly) (ρ : ℕ) (h1 : 1 < vals.length)
    (hρ : ρ < vals.length) :
    getPoly ((appendedNodes vals.length ρ).foldl (fun vs n => vs ++ [n.denote T vs]) vals)
        (vals.length + 51) =
      getPoly vals ρ * getPoly vals ρ +
        pairNodePoly (X 0) (X 6) (getPoly vals 1) * pairNodePoly (X 0) (X 6) (getPoly vals 1) +
        pairNodePoly (X 1) (X 7) (X 6) * pairNodePoly (X 1) (X 7) (X 6) +
        pairNodePoly (X 2) (X 8) (X 7) * pairNodePoly (X 2) (X 8) (X 7) +
        pairNodePoly (X 3) (X 4) (X 8) * pairNodePoly (X 3) (X 4) (X 8) := by
  simp only [appendedNodes, pairingBlock, List.cons_append, List.nil_append, List.foldl_cons,
    List.foldl_nil, List.append_assoc, NatNode.denote, getPoly_append_length,
    getPoly_append_length', getPoly_append_lt _ _ h1, getPoly_append_lt _ _ hρ,
    List.getD_cons_succ, List.getD_cons_zero, Nat.add_assoc, pairNodePoly]

theorem denoteNatNodes_append_list (T : ExPoly) (l l' : List NatNode) :
    denoteNatNodes T (l ++ l') =
      l'.foldl (fun vals n => vals ++ [n.denote T vals]) (denoteNatNodes T l) :=
  List.foldl_append ..

/-- **The polynomial of the specialization**: `[[specialize ℋ c₃]] = θ([[ℋ]])² + Σ_{i<4} π_i²`,
for a circuit whose node list begins with the variable nodes of `X_0, X_1`, whose root is a
node, and whose call blocks start at `2` or later. -/
theorem specialize_poly (H : NatCircuit) (code : ℤ) (T : ExPoly)
    (hH : ∃ rest, H.nodes = .var 0 :: .var 1 :: rest) (hroot : H.root < H.nodes.length)
    (hcall : ∀ a b c w, NatNode.call a b c w ∈ H.nodes → 2 ≤ w) :
    (specialize H code).poly T =
      bind₁ (theta code) (H.poly T) ^ 2 + ∑ i : Fin 4, pairPoly i ^ 2 := by
  obtain ⟨rest, hr⟩ := hH
  have h1 : getPoly (denoteNatNodes T H.nodes) 1 = X 1 := by
    rw [hr, show (NatNode.var 0 :: .var 1 :: rest) = [.var 0, .var 1] ++ rest from rfl,
      getPoly_denoteNatNodes_append T (by simp)]
    simp [denoteNatNodes, NatNode.denote, getPoly]
  have hlen : (denoteNatNodes T (H.nodes.map (renameNode code))).length = H.nodes.length := by
    simp [length_denoteNatNodes]
  have hmap := denoteNatNodes_map_renameNode code T H.nodes hcall
  have hL : 1 < H.nodes.length := by simp [hr]
  simp only [NatCircuit.poly, specialize]
  rw [denoteNatNodes_append_list, ← hlen,
    foldl_appendedNodes T _ _ (by rw [hlen]; exact hL) (by rw [hlen]; exact hroot), hmap,
    getPoly_map_bind₁, getPoly_map_bind₁, h1, bind₁_X_right]
  simp only [theta, Fin.sum_univ_four, pairPoly, pairNodePoly, tVar]
  norm_num
  ring

/-! ### The natural relation -/

/-- The natural relation through assignments `ℕ → ℕ`: the inputs are fixed and the variables
from the variable count on are `0`. -/
theorem natRel_iff_point (C : NatCircuit) (T : ExPoly) (hk : C.inputCount ≤ C.varCount)
    (a : Fin C.inputCount → ℕ) :
    C.NatRel T a ↔ ∃ y : ℕ → ℕ, (∀ i (h : i < C.inputCount), y i = a ⟨i, h⟩) ∧
      (∀ i, C.varCount ≤ i → y i = 0) ∧ zv y (C.poly T) = 0 := by
  rw [Packed.natRel_iff_agree C T hk a]
  refine exists_congr fun y => ?_
  rw [← and_assoc]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by omega)]; simp [NatCircuit.natPoint, hi]
    · rw [h i (by omega)]; simp [NatCircuit.natPoint, show ¬ i < C.inputCount by omega]
  · rintro ⟨h1, h2⟩ i hi
    simp only [NatCircuit.natPoint]
    split_ifs with h
    · exact h1 i h
    · exact h2 i (by omega)
    · exact h2 i (by omega)

/-- The assignment of `ℋ` read off an assignment of its specialization. -/
def thetaPoint (code : ℕ) (y : ℕ → ℕ) : ℕ → ℕ
  | 0 => code
  | 1 => y 5
  | i + 2 => y (i + 9)

theorem zv_bind₁_theta (code : ℕ) (y : ℕ → ℕ) (P : Poly) :
    zv y (bind₁ (theta code) P) = zv (thetaPoint code y) P := by
  show eval₂Hom (RingHom.id ℤ) _ (bind₁ _ P) = eval₂Hom (RingHom.id ℤ) _ P
  rw [eval₂Hom_bind₁]
  refine congrArg (fun f => eval₂Hom (RingHom.id ℤ) f P) (funext fun i => ?_)
  rcases i with _ | _ | i <;> simp [theta, thetaPoint]

theorem sum_sq_eq_zero_iff (a b c d e : ℤ) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  constructor
  · intro h
    have ha := sq_nonneg a
    have hb := sq_nonneg b
    have hc := sq_nonneg c
    have hd := sq_nonneg d
    have he := sq_nonneg e
    refine ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith),
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith),
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith),
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith),
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    norm_num

theorem zv_pairPoly (y : ℕ → ℕ) (i : ℕ) (hi : i < 4) :
    zv y (pairPoly i) = 2 * (y (5 + i) : ℤ) -
      ((y i : ℤ) + (if i + 1 = 4 then y 4 else y (5 + (i + 1)) : ℕ)) *
        ((y i : ℤ) + (if i + 1 = 4 then y 4 else y (5 + (i + 1)) : ℕ) + 1) -
      2 * ((if i + 1 = 4 then y 4 else y (5 + (i + 1)) : ℕ) : ℤ) := by
  have h4 : i ≠ 4 := by omega
  simp only [pairPoly, tVar, ite_eq_right h4]
  split_ifs <;> simp

/-- **The natural relation of the specialization.** For natural `c₃`, the specialization has a
natural zero at `c ∈ ℕ⁵` iff `ℋ` has a natural zero with `X_0 = c₃` and `X_1 = enc₅(c)`. -/
theorem specialize_natRel_iff (H : NatCircuit) (code : ℕ) (T : ExPoly)
    (hH : ∃ rest, H.nodes = .var 0 :: .var 1 :: rest) (hroot : H.root < H.nodes.length)
    (hcall : ∀ a b c w, NatNode.call a b c w ∈ H.nodes → 2 ≤ w) (hV : 2 ≤ H.varCount)
    (c : Fin 5 → ℕ) :
    (specialize H code).NatRel T c ↔
      ∃ y : ℕ → ℕ, y 0 = code ∧ y 1 = CantorDecoder.encode5 (c 0) (c 1) (c 2) (c 3) (c 4) ∧
        (∀ i, H.varCount ≤ i → y i = 0) ∧ zv y (H.poly T) = 0 := by
  refine (natRel_iff_point (specialize H code) T (by simp only [specialize]; omega) c).trans ?_
  simp only [specialize_poly H code T hH hroot hcall, zv_add, zv_pow, zv_bind₁_theta,
    Fin.sum_univ_four]
  have hp : ∀ y : ℕ → ℕ, ∀ i < 4, (zv y (pairPoly i) = 0 ↔
      y (5 + i) = CantorDecoder.pair (y i) (if i + 1 = 4 then y 4 else y (5 + (i + 1)))) :=
    fun y i hi => by rw [zv_pairPoly y i hi]; exact CantorDecoder.pairing_equation_iff _ _ _
  constructor
  · rintro ⟨y, hin, hzero, h⟩
    rw [← add_assoc, ← add_assoc, ← add_assoc, sum_sq_eq_zero_iff] at h
    obtain ⟨hH0, h0, h1, h2, h3⟩ := h
    have e0 := (hp y 0 (by norm_num)).1 (by simpa using h0)
    have e1 := (hp y 1 (by norm_num)).1 (by simpa using h1)
    have e2 := (hp y 2 (by norm_num)).1 (by simpa using h2)
    have e3 := (hp y 3 (by norm_num)).1 (by simpa using h3)
    norm_num at e0 e1 e2 e3
    refine ⟨thetaPoint code y, rfl, ?_, fun i hi => ?_, hH0⟩
    · simp only [thetaPoint, e0, e1, e2, e3, CantorDecoder.encode5]
      have hk : (specialize H code).inputCount = 5 := rfl
      rw [hin 0 (by omega), hin 1 (by omega), hin 2 (by omega), hin 3 (by omega),
        hin 4 (by omega)]
      rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
      exact hzero _ (by simp [specialize]; omega)
  · rintro ⟨y', hy0, hy1, hzero, h⟩
    let t3 := CantorDecoder.pair (c 3) (c 4)
    let t2 := CantorDecoder.pair (c 2) t3
    let t1 := CantorDecoder.pair (c 1) t2
    let y : ℕ → ℕ := fun i =>
      if h : i < 5 then c ⟨i, h⟩ else if i = 5 then y' 1 else if i = 6 then t1 else
        if i = 7 then t2 else if i = 8 then t3 else y' (i - 7)
    have hθ : thetaPoint code y = y' := by
      funext i
      rcases i with _ | _ | i
      · exact hy0.symm
      · rfl
      · simp only [thetaPoint, y]
        rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        congr 1
    refine ⟨y, fun i hi => by simp only [y]; rw [dite_eq_left (show i < 5 from hi)]; rfl,
      fun i hi => ?_, ?_⟩
    · simp only [specialize] at hi
      simp only [y]
      rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      exact hzero _ (by omega)
    · rw [hθ, h, ← add_assoc, ← add_assoc, ← add_assoc, sum_sq_eq_zero_iff]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simpa using (hp y 0 (by norm_num)).2 (by simp [y, hy1, CantorDecoder.encode5, t1, t2, t3])
      · simpa using (hp y 1 (by norm_num)).2 (by simp [y, t1])
      · simpa using (hp y 2 (by norm_num)).2 (by simp [y, t2])
      · simpa using (hp y 3 (by norm_num)).2 (by simp [y, t3])

end ZInQ.Compiler.Universal
