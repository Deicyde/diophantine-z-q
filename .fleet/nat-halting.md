# Report: nat-halting

Chapter `compiler/natural/universal/` (interpreter literal, halting circuit, five-input
circuit, sizes) and `compiler/natural/natural-polynomial-semantics.md`. Directory
`ZInQKernel/Compiler/Universal/`, root `ZInQKernel/Compiler/Universal.lean`. Merged
`wip/nat-interpreter` (numbering, codes, interpreter correctness) and `wip/nat-programs` (the
wrapper). `lake build ZInQKernel` passes. No axioms and no `native_decide`. One `sorry` remains,
in `natural_polynomial_semantics`, and it waits for wrapper correctness.

## Leaves

All names are in namespace `ZInQ.Compiler.Universal` unless written otherwise.

| Article | Lean name | Status |
| --- | --- | --- |
| `universal/universal-interpreter.md` | `interpreter` (`Interpreter.lean`) | proved (definition; the literal list of 1,399 instructions) |
| `universal/interpreter-shape.md` | `interpreter_shape`, with `interpreter_valid`, `interpreter_length`, `interpreter_subCount`, `interpreter_addCount`, `interpreter_getElem?_cleanup`, `interpreter_getElem?_last`, `interpreter_entry_iff`, `interpreter_getElem?_entry` (`Shape.lean`) | proved (`decide +kernel`, about 6 s) |
| `universal/halting-polynomial.md` | `haltingCircuit := Packed.compiled interpreter 204 2`; `haltingCircuit_explicitVars_eq'`, `haltingCircuit_nodes_eq` (`Halting.lean`) | proved (definition) |
| `universal/halting-circuit-counts.md` | `haltingCircuit_counts`, `haltingCircuit_witnessCount`, `haltingCircuit_macroCounts` (`Halting.lean`) | proved |
| `universal/halting-polynomial-semantics.md` | `haltingCircuit_natRel_iff` (`WrapperCode.lean`); `haltingCircuit_natRel_iff_accepts` (`Halting.lean`) | proved (uses `interpreter_accepts_iff` from nat-interpreter) |
| `universal/halting-node-check.md` | item 2: `powerTemplate_nodeStats`, `powerTemplate_nodes_length`; item 1: `HaltingNodeCheck` (named finite check), `haltingCircuit_nodeStats` (`NodeCheck.lean`) | item 2 proved (kernel, about 35 s); item 1 proved from the check, except the call count and first two nodes, which are proved outright |
| `universal/precision-circuit.md` | `specialize` (`Specialize.lean`), `precisionCircuitOf` (`PrecisionCircuit.lean`), `precisionCircuit := precisionCircuitOf c3` (`WrapperCode.lean`) | proved (definition) |
| `universal/precision-circuit-specialization.md` | `precisionCircuit_poly`, `precisionCircuit_natRel_iff`, `precisionCircuit_wellScoped`; general forms `specialize_poly`, `specialize_natRel_iff`, `specialize_wellScoped` | proved |
| `universal/circuit-node-counts.md` | `precisionCircuit_counts` (items 1–2), `precisionCircuitOf_explicitVars`, `precisionCircuit_nodeStats` (item 3), `precisionCircuit_consts` (item 4) | items 1, 2, 4 proved; item 3 proved from `HaltingNodeCheck` |
| `universal/wrapper-size-check.md` | `wrapper_small`, plus `wrapper_valid`, `wrapper_length` (`WrapperSize.lean`) | proved (structural bounds; kernel evaluates the lengths and largest registers of the ideal programs, a few seconds) |
| `universal/wrapper-code-size.md` | `c3` (an `irreducible_def`), `c3_lt`, `c3_lt'`, `c3_gt`; generic `code_lt_of_small`, `code_gt_of_small` (`CodeSize.lean`) | proved |
| `natural-polynomial-semantics.md` | `ZInQ.Compiler.natural_polynomial_semantics`, `ZInQ.Compiler.natural_polynomial_semantics'` (`Fin 1305806` form); `ZInQ.Compiler.natural_polynomial_semantics_of` (`WrapperCode.lean`) | statement only: the `sorry` stands for the correctness of the wrapper. The `_of` form takes it as a hypothesis and is proved |

## Statement corrections and choices

- **halting-node-check, item 1.** The node statistics of ℋ (293,568 hash-consed nodes) are not
  evaluated in the kernel. They are the named finite check
  `HaltingNodeCheck : Prop := countKind .var = 54049 ∧ countKind .const = 6 ∧
  countKind .add = 125307 ∧ countKind .mul = 98361 ∧ constList = [0,1,2,4,1399,-1]` on
  `haltingCircuit.nodes`. It is closed and decidable, and has a `Decidable` instance.
  `haltingCircuit_nodeStats` and `precisionCircuit_nodeStats` take it as a hypothesis. **It is
  a finite-computation input of milestone 1.**
  - Proved without the check: the call count (15,845), the first two nodes (`var 0`, `var 1`),
    that the non-call nodes are pairwise distinct, and that every constant of ℋ is among
    `0, 1, 2, 4, -1, 1399` (`haltingCircuit_consts`).
  - Upper bounds from counting node calls are too weak. The constructor's node calls are
    129,408 additions and 98,727 multiplications. Hash-consing removes:
    - 4,101 additions: 2,452 orthogonality re-sums `z + a` inside bitAnd, 1,601 re-sums
      `N + 1` in the mask binomials, and 48 in items 6–7;
    - 366 multiplications: 204 `K·F` in the register masks, 151 in items 6–7, and 11 in the
      formula encoding.
  - The witness accounting charges 6 witnesses per addition and 35,134 per multiplication, and
    has no slack. Call-count bounds would overshoot by about 12.9 million witnesses.
  - Downstream needs only `countKind .add ≤ 125307` and `countKind .mul ≤ 98361`, plus
    membership of the constants, which is proved. Those two bounds are tight, so they are as
    hard to prove as the exact counts.
  - The 151 multiplications and 48 additions removed in items 6–7 depend on the program, which
    makes an exact symbolic count impractical.
  - Kernel evaluation of the builder is out of reach. The 474-node power template alone takes
    about 30 s.
- **circuit-node-counts, item 4.** Proved without the check, in the form consumers use: every
  constant is among `0, 1, -1, c₃, 2, 4, 1399`, and `c₃, 2, 4, 1399` are distinct (from
  `c₃ > 1399`). The order of first occurrence, `constList = [c₃,0,1,2,4,1399,-1,1,2,-1]`, is in
  item 3 and needs the check. The template library needs only membership in the fixed table
  `(4, 2, 3, c₃, 1399)`.
- **precision-circuit.** Defined for an arbitrary two-input circuit and literal
  (`specialize H code`), then instantiated. `c₃` is `code wrapper : ℕ`, cast to `ℤ` in the
  constant node. The 52 appended nodes match the saved file's nodes 293,568–293,619 index for
  index, and its root is node 293,619 (checked by a script against the JSON). The `specialize_*` lemmas assume three properties of
  ℋ, all proved for ℋ:
  - its node list starts `var 0 :: var 1 :: …`;
  - its root is a node;
  - its blocks start at 2 or later.
- **precision-circuit-specialization.** The relation is stated for natural `code`, matching the
  article. Natural zeros of ℋ at `![code, enc₅ c]` use `ZInQ.CantorDecoder.encode5` (upstream)
  for `enc₅`.
- **halting-polynomial-semantics.** Proved via `RM.Program.Accepts` and nat-interpreter's
  `interpreter_accepts_iff`.
- **wrapper-size-check.** Lean's wrapper has 133,383 instructions and largest field 133,382
  (width 18), within the article's bounds. The proof is structural:
  - every field of `IR.code J S s acc rej` is bounded by `max(J+6, regs S)` for registers and
    `max(s+|S|, acc, rej)` for targets (`code_le`);
  - the lowering and the relocated wrapper are bounded the same way (`prefixed_*`);
  - `wrapper_numbers` evaluates `IR.Stmt.len` and the largest register of the two ideal
    programs by `decide +kernel`.

  Also proved: `wrapper_valid : wrapper.Valid (2^18)`. `halts_code_iff` and `code_ge` need it.
- **wrapper-code-size.** Exactly as stated (`1399 < c₃ < 2^14400019 < 2^(2^24)`). `c₃` is
  never evaluated. The proofs use Mathlib's `pow_le_pow_right₀`, not core's
  `Nat.pow_le_pow_right`. The core lemma made the elaborator try to evaluate `2^14400019` (the
  exponentiation threshold warning).
- **natural-polynomial-semantics.** Stated through `NatCircuit.NatRel`, plus a corollary with an
  explicit `Fin 1305806` witness vector (`natural_polynomial_semantics'`). The missing input is
  `∀ c, IR.wrapper.HaltsOn ![encode5 (c 0) … (c 4)] ↔ Precision.accepts c`, the
  `wrapper_halts_encode` of the wrapper-correct note.
- **universal-interpreter.** Pinned literally (option 2 of the implementation note). It was
  recovered from the saved circuit:
  - the state equations `S_i ≐ [i=0] + B·I_i` give the targets;
  - the register equations give the register indices;
  - the branch equations `S_i ≐ V_i + W_i` mark the sub instructions.

  As a cross-check, a Python transcription of the Lean builder (`Construction.lean`,
  `Packed/Construction.lean`) run on this literal reproduces the saved universal circuit
  exactly: 293,568 nodes and all 15,845 blocks (shifted by 7), with the same root. That run
  gives the statistics in `HaltingNodeCheck`. The recovery and generator scripts are kept
  outside the repository. nat-interpreter has since proved that the literal is the compilation
  of their structured interpreter.

## Lemmas added beyond the leaves

- `Grows.lean`: the judgement `Grows μ m`. It says the construction only appends witness
  variables (`VarsExt`) and nodes, keeps the non-call nodes duplicate-free, and creates
  constants only in `ConstSet μ = {0,1,2,4,-1,μ}`.
  - Proved for every builder operation, the hierarchical macros, the encoding and the packed
    construction (`grows_construction`).
  - `toCircuit_prefix` and `compiled_prefix` give, for a compiled circuit: inputs first, then
    only witnesses; the node list starts with the input variable nodes; non-call nodes are
    duplicate-free; constants lie in `{0,1,2,4,-1,m}`.
  - This is a separate judgement because `Counts` lives in nat-circuits' directory and was not
    edited.
- `Shape.lean`: the Boolean validity checker `programValidB` with `programValidB_sound`, and
  `instrTargets`.
- `NodeCheck.lean`: `NodeKind`, `nodeKind`, `countKind`, `constList`, `length_eq_countKind`,
  `countKind_call`, `countKind_append`, `constList_append`.
- `Specialize.lean`, `SpecializeShape.lean`:
  - definitions: `renameNode`, `pairingBlock`, `appendedNodes`, `theta`, `tVar`, `pairPoly`;
  - polynomial identity: `denoteNatNodes_map_renameNode`, `bind₁_callPoly`, `foldl_appendedNodes`;
  - natural relation: `natRel_iff_point` (natural relation through `ℕ → ℕ` assignments),
    `zv_bind₁_theta`;
  - counts and blocks: `specialize_nodeStats`, `specialize_blocks`;
  - well-scopedness: `specialize_wellScoped`.
- `PrecisionCircuit.lean`: `haltingCircuit_root_lt`, `haltingCircuit_call_ge`,
  `haltingCircuit_nodes_eq'`, `precisionCircuitOf_consts`.
- `CodeSize.lean`: `SmallProgram`, `width_le_of_small`, `code_lt_of_small`, `code_gt_of_small`,
  `haltingCircuit_natRel_iff_of`.
- `WrapperSize.lean`: `opMaxReg`, `stmtMaxReg`, `InstrLe`, `BlockLe`, block lemmas for every
  lowering block, `code_le`, `lowerBody_le`, `prefixed_valid`, `prefixed_fields`.
- `WrapperCode.lean`: `haltingCircuit_c3_iff`, `natRel_iff_witnessCount`,
  `precisionCircuit_natRel_iff_witnesses`.

## Problems

- Nothing blocking.
- Elaboration pitfall: never let the elaborator unify `precisionCircuit` (or `haltingCircuit`)
  terms by unfolding: it tries to evaluate the construction (maximum recursion). Workarounds:
  - rewrite with `precisionCircuit_eq` first;
  - pass `c3` explicitly;
  - state lemmas for generic circuits and instantiate them.
- `Specialize.lean` imports upstream's `ZInQ.CantorDecoder`, which triggers the harmless
  module-system import warning.
- The block lemmas of `WrapperSize.lean` restate nat-programs' block layouts. When the latest
  nat-programs changed `incs` (targets from `s + 2`), only `incs_le` needed a one-line update.
  Any further change to the lowering blocks needs the matching lemma updated.
- The merged nat-programs branch contains `ZInQKernel/Compiler/Programs/Scratch.lean`
  (theirs, not imported by the root).

## Suggestions for the next agent

- The `sorry` in `natural_polynomial_semantics` goes away once nat-programs proves wrapper
  correctness in the form above. Then `natural_polynomial_semantics_of interpreter_accepts_iff
  wrapper_halts_encode`.
- `wrapper_numbers` re-evaluates the ideal programs. If nat-programs changes the precision
  program, the bounds 2^18 and 200,000 are re-checked automatically. If they fail, raise them
  together with `c3_lt`; `18(4m + 1) + 1 ≤ 2^24` allows `m ≤ 233,016`.
- `HaltingNodeCheck` needs a milestone-2 certificate. Two possibilities:
  - a verified fast builder, which would mean parametrizing the builder over its node-insertion
    primitive and running it with an indexed map;
  - an exact symbolic count of the dedup events, of which only the 199 in items 6–7 depend on
    the program.

  The var-node count (54,049) and the presence of the six constants can be proved by extending
  `Grows` (a var-node/explicit-variable bijection, and a "constant `c` is present" judgement).
  The check would then need only the add and mul counts and the constant order.
