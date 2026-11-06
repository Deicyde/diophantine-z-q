# nat-circuits: report

Blueprint chapter `compiler/natural/`, sections `formulas/` (8 leaves) and `packed/` (10 leaves),
plus `programs/register-machine.md`. Lean modules are under `ZInQKernel/Compiler/Circuits/`, root
module `ZInQKernel/Compiler/Circuits.lean` (imported from `ZInQKernel.lean`). All 19 leaves are
done with no `sorry`; `#print axioms` on the main theorems shows only `propext`,
`Classical.choice`, `Quot.sound`. Namespaces: `ZInQ.Compiler.RM` (machines),
`ZInQ.Compiler.Natural` (constructions, circuits, semantics), `ZInQ.Compiler.Packed`
(packed histories). Origin/wip/nat-exponential is merged (its `AlphaEqns`, `PowEqns`,
`alphaEqns_iff`, `powEqns_iff` are used).

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| `programs/register-machine.md` | `RM.Instr`, `RM.Machine`, `RM.Config`, `RM.step`, `RM.stepN`, `RM.Halts`, `RM.Program`, `RM.Instr.Valid`, `RM.Program.Valid`, `RM.Program.toMachine`, `RM.initFile`, `RM.Program.HaltsOn`, `RM.Program.Accepts`, `addCount`, `subCount` (`RegisterMachine.lean`) | proved (definition) |
| `formulas/natural-constructions.md` | `Natural.NatNode`, `Ex`, `NForm`, `NForm.toFormula`, `State`, `NM`, `node`, `constant`, `fresh`, `addL`, `mulL`, `square`, `scale`, `callPower`, `andM`, `orM`, `lt`, `divides`, `congruent`, `odd`, `alpha`, `powerFlat`, `PowerMode`, `power`, `binomial`, `orthogonal`, `mask`, `bitAnd`, `NForm.encode` (`Construction.lean`) | proved (definition) |
| `formulas/natural-atom-gadgets.md` | `lt_gadget_iff`, `dvd_gadget_iff`, `congr_gadget_iff`, `congr_gadget_zero_iff`, `odd_gadget_iff` (`Gadgets.lean`) | proved |
| `formulas/natural-compilation.md` | item 1 `compile_zv_eq_zero_iff`; item 2 `exists_agree_congr`, `SpecL.cons`, `SpecL.and`, `SpecO.cons`, `SpecO.or`, `Spec.fresh`, `MSpec.andM`, `MSpec.orM`; item 3 `callPower_spec` (`Compilation.lean`); shared fresh variables `SpecE` (`Exposed.lean`) | proved |
| `formulas/power-template.md` | `powerTemplateConstruction`, `powerTemplateCircuit`, `powerTemplatePoly`, `powerTemplate`, `powerTemplate_params`, `powerTemplate_witnesses`, `powerTemplateCircuit_varCount` (82), `powerTemplate_poly` (= κ(power)), `powerTemplate_wf` (`PowerTemplate.lean`); `powerTemplateCircuit_stats` (474 nodes, root 473, 82 variables; kernel `decide`) (`PowerTemplateNodes.lean`) | proved |
| `formulas/power-template-semantics.md` | `powerTemplate_natRel`, `powerTemplateSem`, `powerSpec_hierarchical_powerTemplate` (`PowerTemplate.lean`) | proved |
| `formulas/macro-semantics.md` | `lt_spec`, `divides_spec`, `congruent_spec`, `odd_spec`, `alpha_spec`/`alpha_sem`, `powerFlat_spec`/`powerSpec_flat'`, `powerSpec_hierarchical`, `binomial_spec`, `orthogonal_spec`, `mask_spec`, `bitAnd_spec` (`MacroSemantics.lean`) | proved |
| `formulas/natural-circuit-semantics.md` | `NatCircuit`, `NatNode.denote`, `denoteNatNodes`, `NatCircuit.poly`, `NatCircuit.natPoint`, `NatCircuit.NatRel`, `NatCircuit.blocks`, `NatCircuit.WellScoped`, `NM.toCircuit` (`Circuit.lean`) | proved (definition) |
| `formulas/hierarchical-calls.md` | item 1 `toCircuit_item1`; item 2 `toCircuit_natRel_iff` with `NLift`, `exists_nholds_iff`, `nlift_call_powerTemplate` (`Hierarchical.lean`); well-scopedness `toCircuit_wellScoped` (`Scope.lean`); `[[𝒞]] = κ(φ)` `toCircuit_poly` (`Builder.lean`); item 3 for the packed construction: `Packed.packed_spec`, `Packed.compiled_natRel_iff` | proved (see corrections) |
| `packed/packed-compiler.md` | `Packed.construction`, `Packed.compiled`, phases `items1`–`items4`, `items6`, `items7`, `registerMasks`, `subBranches`, `registerEq`, `stateEq`, `incHandles`, `decHandles`, `inHandles`, `packedFormulas` (`Packed/Construction.lean`) | proved (definition) |
| `packed/packed-masks.md` | `packed_masks`, `F_D_eq` (`Packed/Masks.lean`) | proved |
| `packed/packed-state-selection.md` | `one_active_state` (`Packed/StateSelection.lean`) | proved |
| `packed/packed-nonzero-indicator.md` | `nonzero_indicator` (`Packed/NonzeroIndicator.lean`) | proved |
| `packed/packed-branches.md` | item 1 `branch_split`, item 2 `indicator_digits` (`Packed/Branches.lean`) | proved |
| `packed/packed-transitions.md` | `packed_register_iff`, `packed_state_iff` (`Packed/Transitions.lean`) | proved |
| `packed/packed-sound.md` | `PackedConditions`, `packed_sound`, `packed_sound_accepts` (`Packed/Sound.lean`) | proved |
| `packed/packed-complete.md` | `packed_complete` (`Packed/Complete.lean`) | proved |
| `packed/register-machine-polynomial.md` | `compiled_natRel_iff` (`Packed/Polynomial.lean`) | proved |
| `packed/packed-counts.md` | `packed_counts` (`Packed/Counts.lean`) | proved |

## Cross-checks with the JavaScript compiler

- The Lean node list of the power template equals, node for node, template `0` of
  `construction/precision-natural-polynomial.json` (474 nodes, root 473, 82 variables). This was
  checked by kernel `decide` against the full list during development; the committed module keeps
  the cheaper statistics check.
- The Lean node list of `Packed.compiled [dec 0 1 1, halt] 1 1` equals the output of
  `compileRegisterMachine` run with a `BuilderClass` whose `variable` uses one global counter and
  whose `power` allocates a block of 79 at the counter and creates the node `call [P, Q, R, w]`
  (567 nodes, root 566, 103 explicit variables, 29 calls, all as `packed_counts` predicts). The
  hierarchical builder itself is not in the repository; this is my reading of the article. The
  JSON's call node also carries the template index `0`, which `NatNode.call` omits.

## Statement corrections and choices

- No article is wrong. Choices of form:
- `natural-constructions`: expressions are handled as `Ex` (node index and polynomial); macros
  take already emitted expressions, so node creation follows the JavaScript argument order. The
  state records a macro log (`State.log`, `note`), as the JavaScript `macroCounts`, so that the
  macro counts of `packed-counts` are statements about the construction.
- `natural-compilation`, item 2: stated through `Spec φ U c₀ c₁ R` (variables in `U ∪ [c₀,c₁)`
  plus the private-witness equivalence) and its list/disjunction/fresh-variable rules; `SpecE`
  handles fresh variables used by later conjuncts (the history variables). "Holds naturally" is
  `NHolds x φ := φ.Holds (fun i => (x i : ℚ))`, equivalent to integer evaluation (`ev_qa`).
- `macro-semantics`: relations are stated for argument polynomials with natural values
  (`IsNat`), through `nv x f = (zv x f).toNat`; `binomial`, `orthogonal`, `mask`, `bitAnd` are
  proved for either power mode from the hypothesis `PowerSpec τ mode` (power means `P = Q^R`),
  which holds in flat mode (`powerSpec_flat'`) and for calls of the power template
  (`powerSpec_hierarchical_powerTemplate`). This is also the flat/hierarchical remark of
  `hierarchical-calls`.
- `power-template`: `powerTemplate := ⟨3, 79, powerTemplatePoly⟩`; that 79 is the circuit's
  variable count minus 3 is `powerTemplate_witnesses_circuit`. `powerTemplatePoly` is
  `@[irreducible]` so that elaboration never evaluates the node list.
- `natural-circuit-semantics`: `NatCircuit.poly T C` takes the called template `T : ExPoly` as a
  parameter (instance: `powerTemplate`). `NatRel` evaluates in `ℤ`. Well-scopedness is item 3
  verbatim, with blocks read from the call nodes.
- `hierarchical-calls`: "every macro argument is a polynomial in variables allocated before the
  macro" is formalized by hypotheses: the node encoding is valid (`Triple … (Valid)`, proved for
  all macros and the packed construction), the construction preserves the scope invariant
  (`Pres`, idem), and for item 2 the final formula's call blocks are private
  (`Formula.Scoped`), above the inputs, with `κ(φ)` below the variable count. Item 3 in
  general would need a formal notion of "the macros of a construction"; it is proved for the
  packed construction (`packed_spec` lists the macro relations, `compiled_natRel_iff`).
- `packed-compiler`: list lookups default to the `zero` expression (the JavaScript would fail);
  for valid programs no default is used, so the node list is unchanged. The construction is
  written in phases (`appendM` of items 1–7); the node list was rechecked after this.
- `packed-branches`, item 2: stated for an active-state function `act` with
  `σ_i(t) = [act t = i]`, giving the digit formulas of `incSum`, `decSum`, `inSum`.
- `packed-sound`/`packed-complete`: the formula with macros read as relations is the structure
  `PackedConditions`; `A_j, C_j, I_i` are written as sums over `range m` with conditions
  (`incSum`, `decSum`, `inSum`), equal to the construction's program-order list sums.
- `packed-counts`: holds for every program (validity is not needed).
- `register-machine`: register files are `ℕ → ℕ` (finite support not enforced); inputs are
  `Fin k → ℕ`.

## Lemmas beyond the leaves

- Builder soundness: `Ex.Valid`, `NForm.Valid`, `Triple` with bind rule, validity triples of all
  builder operations and macros (`triple_tac`), `encode_correct`, `encode_indep`,
  `toCircuit_poly` (`Builder.lean`); `triple_construction`, `compiled_poly`
  (`Packed/Valid.lean`).
- Allocation counts `Counts` and the counts of every macro (`Counts.lean`).
- Scope invariant `ScopeInv`/`Pres`, `toCircuit_wellScoped` (`Scope.lean`),
  `compiled_wellScoped`, `powerTemplateCircuit_wellScoped` (`Packed/Scope.lean`).
- Base-`B` digits: `pack`, `pack_inj`, `eq_pack_digit`, `digit_pack`, `land_pack`, `land_split`
  (`Packed/Digits.lean`).
- `step_iff_digits` (one machine step in slot digits), `decode`, `RunData`
  (`Packed/Step.lean`, `Packed/Sound.lean`).
- Phase specifications of the packed construction, `subBranches_shape`, `packedFormulas_specE`,
  `packed_spec`, `PackedRel`, `packedRel_conditions`, `conditions_packedRel`
  (`Packed/Semantics.lean`, `Packed/Polynomial.lean`); `natRel_iff_agree`.
- Natural private witness blocks `NLift`, `exists_call_iff`, `exists_nholds_iff`
  (`Hierarchical.lean`).

## Problems

- None blocking. Build warnings remain (deprecated `if_pos`/`push_neg` names, unused simp
  arguments in `MacroSemantics.lean`, a linter note in `Builder.lean`).
- `PowerTemplateNodes.lean` costs about 30 s of kernel time (`decide +kernel` over the 474-node
  hash-consed list).

## Suggestions for the next agent

- The universal section can apply `compiled_natRel_iff`, `compiled_poly`,
  `compiled_wellScoped` and `packed_counts` to the interpreter. Node counts of large circuits
  cannot be evaluated in the kernel (the hash-consed list is quadratic to build); only the
  variable and call counts are proved symbolically here.
- The translation chapter should read circuits in this `NatCircuit` format (inputs first in
  `explicitVars`, `NatNode.call a b c w` without template index, `varCount` the final counter).
- For new macros: write them in the `NM` monad, then prove `MSpec` (semantics, `Spec.fresh_bind`,
  `MSpec.expr_bind`, `MSpec.andM`), `Counts` (`counts_of`), `Triple` (`triple_tac`) and `Pres`
  (`pres_tac`); the tactics in `Counts.lean`, `Builder.lean`, `Scope.lean` do the last three.
