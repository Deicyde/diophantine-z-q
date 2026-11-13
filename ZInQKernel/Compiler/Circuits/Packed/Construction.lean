import ZInQKernel.Compiler.Circuits.Circuit
import ZInQKernel.Compiler.Circuits.Packed.Branches

/-!
# The packed-history construction

For a primitive program `p = (p_0, …, p_{m-1})` valid for `r` registers and `1 ≤ k ≤ r`, the
packed-history construction is the natural construction in hierarchical mode with `k` inputs
`a_0, …, a_{k-1}` which takes the fresh variables `q, c, K, B, T, F, D`, `R_0, …, R_{r-1}`,
`N_0, …, N_{r-1}`, `S_0, …, S_{m-1}` in this order and returns the conjunction of

1. `lt(0, c)`, `power(K, 2, c)`, `B ≐ 4K`, `lt(m, B)`, `power(T, B, q)`, `lt(a_i, K)` (`i < k`);
2. `B F + 1 ≐ F + B T`, `D + F ≐ K F`, `S_0 + ⋯ + S_{m-1} ≐ F`, `S_{m-1} ≐ T`;
3. `mask(S_i, F)` for `i < m`;
4. for each `j < r`: `mask(R_j, D)`, `lt(R_j, T)`, `bitAnd(K N_j, R_j + D, K F)`;
5. for each sub instruction `p_i = dec(j, x, y)`, in increasing `i`: fresh `V_i, W_i`, then
   `bitAnd(V_i, S_i, N_j)` and `S_i ≐ V_i + W_i`;
6. for each `j < r`: `R_j + B C_j ≐ ι_j + B R_j + B A_j` (`ι_j = a_j` for `j < k`, else `0`;
   `A_j` the sum of the `S_i` with `p_i = inc(j, ·)`, `C_j` that of the `V_i` with
   `p_i = dec(j, ·, ·)`);
7. for each `i < m`: `S_i ≐ [i = 0] + B I_i` (`I_i` the sum, in program order, of `S_{i'}` for
   `p_{i'} = inc(·, i)`, `V_{i'}` for `p_{i'} = dec(·, i, ·)` and `W_{i'}` for
   `p_{i'} = dec(·, ·, i)`).

This is a transcription of `compileRegisterMachine` of
`construction/integer-diophantine-compiler.js`. The compiled circuit `𝒞_{p,k}` is its natural
circuit. Validity of `p` is a hypothesis of the semantic theorems, not of the definition.

(Blueprint: `compiler/natural/packed/packed-compiler.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM Syntax MvPolynomial

/-- `n` fresh variables, in order. -/
def freshN : ℕ → NM (List Ex)
  | 0 => pure []
  | n + 1 => do
    let h ← fresh
    let hs ← freshN n
    pure (h :: hs)

/-- Concatenate the formula lists of constructions run in order. -/
def seqConcat : List (NM (List NForm)) → NM (List NForm)
  | [] => pure []
  | m :: ms => do
    let a ← m
    let b ← seqConcat ms
    pure (a ++ b)

/-- Item 4 for one register: `mask(R_j, D)`, `lt(R_j, T)`, `bitAnd(K N_j, R_j + D, K F)`. -/
def registerMasks (K D T F Rj Nj : Ex) : NM (List NForm) :=
  seqM [
    mask .hierarchical Rj D,
    lt Rj T,
    do bitAnd .hierarchical (← mulL [K, Nj]) (← addL [Rj, D]) (← mulL [K, F])]

/-- Item 5: the sub instructions of `p_i, p_{i+1}, …`, in increasing order. Returns the
formulas and the branch histories `(i, V_i, W_i)`. -/
def subBranches (zero : Ex) (S N : List Ex) :
    ℕ → List Instr → NM (List NForm × List (ℕ × Ex × Ex))
  | _, [] => pure ([], [])
  | i, .dec j _ _ :: rest => do
    let V ← fresh
    let W ← fresh
    let fs ← seqM [
      bitAnd .hierarchical V (S.getD i zero) (N.getD j zero),
      do pure (.eq (S.getD i zero) (← addL [V, W]))]
    let rest' ← subBranches zero S N (i + 1) rest
    pure (fs ++ rest'.1, (i, V, W) :: rest'.2)
  | i, _ :: rest => subBranches zero S N (i + 1) rest

/-- The branch histories `(V_i, W_i)` of instruction `i`. -/
def lookupVW (zero : Ex) (vw : List (ℕ × Ex × Ex)) (i : ℕ) : Ex × Ex :=
  ((vw.find? fun e => e.1 == i).map (·.2)).getD (zero, zero)

/-- The summands of `A_j`: the `S_i` with `p_i = inc(j, ·)`, in program order. -/
def incHandles (p : Program) (zero : Ex) (S : List Ex) (j : ℕ) : List Ex :=
  ((List.range p.length).filter fun i => decide (incOn p j i)).map fun i => S.getD i zero

/-- The summands of `C_j`: the `V_i` with `p_i = dec(j, ·, ·)`, in program order. -/
def decHandles (p : Program) (zero : Ex) (vw : List (ℕ × Ex × Ex)) (j : ℕ) : List Ex :=
  ((List.range p.length).filter fun i => decide (decOn p j i)).map fun i =>
    (lookupVW zero vw i).1

/-- The summands of `I_i`, in program order: `S_{i'}` for `p_{i'} = inc(·, i)`, `V_{i'}` for
`p_{i'} = dec(·, i, ·)` and `W_{i'}` for `p_{i'} = dec(·, ·, i)`. -/
def inHandles (p : Program) (zero : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex)) (i : ℕ) :
    List Ex :=
  (List.range p.length).flatMap fun i' =>
    (if incTo p i' i then [S.getD i' zero] else []) ++
      (if nzTo p i' i then [(lookupVW zero vw i').1] else []) ++
      (if zTo p i' i then [(lookupVW zero vw i').2] else [])

/-- Item 6 for one register: `R_j + B C_j ≐ ι_j + B R_j + B A_j`. -/
def registerEq (B Rj ιj : Ex) (decs incs : List Ex) : NM NForm := do
  let l ← addL [Rj, ← mulL [B, ← addL decs]]
  let r ← addL [ιj, ← mulL [B, Rj], ← mulL [B, ← addL incs]]
  pure (.eq l r)

/-- Item 7 for one state: `S_i ≐ e + B I_i`. -/
def stateEq (B Si e : Ex) (ins : List Ex) : NM NForm := do
  let r ← addL [e, ← mulL [B, ← addL ins]]
  pure (.eq Si r)

/-- Run two formula-list constructions in order and concatenate their formulas. -/
def appendM (m₁ m₂ : NM (List NForm)) : NM (List NForm) := do
  let l₁ ← m₁
  let l₂ ← m₂
  pure (l₁ ++ l₂)

/-- Item 1. -/
def items1 (p : Program) (a : List Ex) (zero q c K B T : Ex) : NM (List NForm) :=
  seqM ([
    lt zero c,
    do power .hierarchical K (← constant 2) c,
    do pure (.eq B (← scale 4 K)),
    do lt (← constant p.length) B,
    power .hierarchical T B q] ++ a.map fun ai => lt ai K)

/-- Item 2. -/
def items2 (zero one K B T F D : Ex) (S : List Ex) : NM (List NForm) :=
  seqM [
    do pure (.eq (← addL [← mulL [B, F], one]) (← addL [F, ← mulL [B, T]])),
    do pure (.eq (← addL [D, F]) (← mulL [K, F])),
    do pure (.eq (← addL S) F),
    pure (.eq (S.getLastD zero) T)]

/-- Item 3. -/
def items3 (F : Ex) (S : List Ex) : NM (List NForm) := seqM (S.map fun x => mask .hierarchical x F)

/-- Item 4. -/
def items4 (r : ℕ) (zero K D T F : Ex) (R N : List Ex) : NM (List NForm) :=
  seqConcat ((List.range r).map fun j =>
    registerMasks K D T F (R.getD j zero) (N.getD j zero))

/-- Item 6. -/
def items6 (p : Program) (r : ℕ) (a : List Ex) (zero B : Ex) (R S : List Ex)
    (vw : List (ℕ × Ex × Ex)) : NM (List NForm) :=
  seqM ((List.range r).map fun j =>
    registerEq B (R.getD j zero) (a.getD j zero) (decHandles p zero vw j)
      (incHandles p zero S j))

/-- Item 7. -/
def items7 (p : Program) (zero one B : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex)) :
    NM (List NForm) :=
  seqM ((List.range p.length).map fun i =>
    stateEq B (S.getD i zero) (if i = 0 then one else zero) (inHandles p zero S vw i))

/-- Items 1–7, in order, after the fresh variables `q, …, D, R, N, S`. -/
def packedFormulas (p : Program) (r : ℕ) (a : List Ex) (zero one q c K B T F D : Ex)
    (R N S : List Ex) : NM (List NForm) :=
  appendM (items1 p a zero q c K B T) <|
  appendM (items2 zero one K B T F D S) <|
  appendM (items3 F S) <|
  appendM (items4 r zero K D T F R N) do
    let sb ← subBranches zero S N 0 p
    appendM (pure sb.1) <|
    appendM (items6 p r a zero B R S sb.2) (items7 p zero one B S sb.2)

/-- **The packed-history construction** of `p` with `r` registers and `k` inputs. -/
def construction (p : Program) (r k : ℕ) : NM NForm := do
  let a := inputs k
  let zero ← constant 0
  let one ← constant 1
  let q ← fresh
  let c ← fresh
  let K ← fresh
  let B ← fresh
  let T ← fresh
  let F ← fresh
  let D ← fresh
  let R ← freshN r
  let N ← freshN r
  let S ← freshN p.length
  let φs ← packedFormulas p r a zero one q c K B T F D R N S
  pure (.and φs)

/-- **The compiled circuit** `𝒞_{p,k}`: the natural circuit of the packed-history
construction. -/
def compiled (p : Program) (r k : ℕ) : NatCircuit := (construction p r k).toCircuit k

end ZInQ.Compiler.Packed
