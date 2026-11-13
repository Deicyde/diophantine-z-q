# fold notes: t-skolem-kw

Fragment: `scratch/leaf-adopt3/fold/t-skolem-kw.lean` (1394 lines, `section TSkolemKWSec ... end
TSkolemKWSec`, no imports, no `noncomputable section` needed). It is
`SkolemNoether.lean` + `BrauerNesbitt.lean` + `FrobeniusDense.lean` (minus its `TSkolemKW.C10`
part) + `KroneckerWeberUse.lean`, concatenated in AllCheck's order with the same accumulated
top-level opens (`TensorProduct`, `Module`, `NumberField`). Then the final theorem of
`C10Closed.lean` and the bridges. (AllCheck.lean is up to date with the four files: regenerated
and diffed, identical up to a trailing blank line.)

## Bundle fields / glue rows
- `t13 : SkolemNoether` is proved: `TSkolemKW.hsyn_t13`. Also `PkgI6.SkolemNoether` and
  `GlueDescent.LeafSkolemNoether` (Leaves 7835, used by `GlueDescent.B6_inner`) are proved. The
  hypothesis of `PkgI6.skolemNoether_aut` is discharged too.
- `t19 : BrauerNesbitt` is proved: `TSkolemKW.hsyn_t19`. Also `PkgI6.BrauerNesbittChar0` and
  `GlueC10.BrauerNesbittChar0` (hypothesis of `GlueC10.c10` and `iso_of_trace_eq_frob_finite`)
  are proved.
- `t18 : FrobeniusDense` can be replaced by a field `PkgI6.ChebotarevExists`, via
  `TSkolemKW.hsyn_t18_of_chebotarev`.
- `t17 : KroneckerWeber` can be replaced by `t17 : TSkolemKW.KW.KroneckerWeberCyclic` (see below).
- C10: `TSkolemKW.C10.c10_of_chebotarev` is `GlueC10.c10` without its BN hypothesis.

## Bridging theorems (exact types)
- `TSkolemKW.pkgI6_skolemNoether : PkgI6.SkolemNoether`
- `TSkolemKW.hsyn_t13 : HSyn.SkolemNoether`
- `TSkolemKW.glueDescent_leafSkolemNoether : GlueDescent.LeafSkolemNoether`
- `TSkolemKW.pkgI6_brauerNesbittChar0 : PkgI6.BrauerNesbittChar0`
- `TSkolemKW.C10.brauerNesbittChar0' : GlueC10.BrauerNesbittChar0` (the task's own name, from
  C10Closed)
- `TSkolemKW.hsyn_t19 : HSyn.BrauerNesbitt`
- `TSkolemKW.hsyn_t18_of_chebotarev (h : PkgI6.ChebotarevExists) : HSyn.FrobeniusDense`
- `TSkolemKW.kroneckerWeberCyclic_of_hsyn (h : HSyn.KroneckerWeber) : TSkolemKW.KW.KroneckerWeberCyclic`
- `TSkolemKW.hsyn_dirichletCharacter_of_kroneckerWeberCyclic (hKW : KW.KroneckerWeberCyclic)
  {E : Type*} [Field E] (ψ : HSyn.GQ →* Eˣ) (hψ : IsOpen (ψ.ker : Set HSyn.GQ)) :
  ∃ (m : ℕ+) (χ : DirichletCharacter E (m : ℕ)), ∀ σ : HSyn.GQ, (ψ σ : E) = χ ((KW.cycChar m σ :
  (ZMod m)ˣ) : ZMod m)`. This is C8's use form, restated over `HSyn.GQ`.
- `TSkolemKW.C10.c10_of_chebotarev (hC : GlueC10.ChebotarevExists) ...` has `GlueC10.c10`'s
  statement minus `hBN`, written with `GlueC10.GQ`/`GlueC10.IsFrobAt`.
Each bridge is a one-line term. It relies on delta-defeq between the task's local copy
(character-identical body, checked by python) and the Leaves.lean def. If elaboration balks,
use `by intro ...; exact ...` or `fun .. => ..`.

## ChebotarevExists: which one
The task used `GlueC10.ChebotarevExists` (Leaves 11336), through its verbatim copy
`TSkolemKW.C10.ChebotarevExists`. Its body is character-identical to `PkgI6.ChebotarevExists`
(Leaves 5004), and both sit under `open NumberField`. So they are the same statement. The T18
bridge is typed with `PkgI6.ChebotarevExists` and passes it to `HS.frobeniusDense_of_chebotarev`,
which expects `GlueC10.ChebotarevExists` (delta-defeq).

## T17 precisely
- New leaf (statement-identical to the task):
  `def TSkolemKW.KW.KroneckerWeberCyclic : Prop := ∀ (L : Type) [Field L] [NumberField L]
  [IsGalois ℚ L], IsCyclic (L ≃ₐ[ℚ] L) → ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)`.
  This is Kronecker–Weber for cyclic L/ℚ (Washington, Thm 14.1, special case).
- Proved: `HSyn.KroneckerWeber → KroneckerWeberCyclic` (`kroneckerWeberCyclic_of_hsyn`). From
  `KroneckerWeberCyclic` alone, the C8 glue (`dirichletCharacter_of_kroneckerWeberCyclic`,
  `ker_ge_of_kroneckerWeberCyclic`, `eq_of_agree_on_roots_cyclic`; `isOpen_ker_of_continuous` needs
  no leaf).
- NOT proved: `KroneckerWeberCyclic → HSyn.KroneckerWeber`. The math is standard: an abelian L is
  the compositum of cyclic subfields, and a compositum of subfields of `ℚ(ζ_{n_i})` lies in
  `ℚ(ζ_lcm)`. It is not in Lean.
- Who consumes `t17` in Leaves.lean: nobody. `HSyn.KroneckerWeber` occurs only at its def (21206)
  and the field `t17` (21508). `TextbookLeaves` values are consumed only by `glueOutputs_of_leaves
  (_r) (_t) := sorry`, which ignores them. No `.t17` projection exists. So replacing the field by
  `t17 : TSkolemKW.KW.KroneckerWeberCyclic` breaks no Lean term and gives a weaker hypothesis.
  Justification for the C8 use: the report says C8 needs only `ψ` with values in a field
  (`\bar ℚ₅^×`), which the cyclic case covers. (The fragment comes before the bundle, so the
  name is in scope.)

## Deleted / replaced
- `FrobeniusDense.lean` lines 21-290 (`namespace TSkolemKW.C10`): a verbatim, in-order subsequence
  of Leaves.lean 11325-11776 (`GlueC10`). `diff` shows only the namespace lines differ. Deleted.
  The HS section's `open TSkolemKW.C10 (ChebotarevExists FrobDense IsFrobAt Zbar toZbar toZbar_coe
  frobDense)` became `open GlueC10 (...)` with the same names. This was the only edit inside
  task proofs.
- C10Closed's GlueC10 copy: deleted (it equals Leaves 11325-11776). Only `brauerNesbittChar0'`
  and `c10_of_chebotarev` are kept, rewritten with `GlueC10.`-qualified names (`GQ`, `IsFrobAt`,
  `ChebotarevExists`, `BrauerNesbittChar0`, `c10`).
- Kept as local copies (distinct names, no clash; bodies character-identical to Leaves, checked):
  `TSkolemKW.SkolemNoether` (=PkgI6), `TSkolemKW.HSynSkolemNoether` (=HSyn),
  `TSkolemKW.LeafSkolemNoether` (=GlueDescent), `TSkolemKW.BrauerNesbittChar0` (=PkgI6=GlueC10),
  `TSkolemKW.HSynBrauerNesbitt` (=HSyn.BrauerNesbitt), `TSkolemKW.HS.{Qbar,GQ,LiesOver,IsArithFrob,
  FrobeniusDense}` (=HSyn), `TSkolemKW.KW.{Qbar,GQ,KroneckerWeber}` (=HSyn). They were not
  substituted, because the proofs `intro`/`unfold` them. The bridges restate everything over the
  Leaves names.
- Omitted: `ChebotarevCyclotomic.lean` (`TSkolemKW.ChebCyc.chebotarevAt_cyclotomic`, a sanity
  check that the body of `ChebotarevExists` holds for cyclotomic M; it bridges nothing).
- No kernel declarations are needed (Mathlib only). No statement differs from Leaves.lean.
- `#print axioms` dropped: `TSkolemKW.skolemNoether`, `TSkolemKW.leafSkolemNoether`,
  `TSkolemKW.brauerNesbitt_module`, `TSkolemKW.brauerNesbittChar0`, `TSkolemKW.hsynBrauerNesbitt`,
  `TSkolemKW.HS.frobeniusDense_of_chebotarev`, `TSkolemKW.KW.eq_of_agree_on_roots`,
  `TSkolemKW.KW.eq_of_agree_on_roots_cyclic`,
  `TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic`, `TSkolemKW.KW.isOpen_ker_of_continuous`,
  `TSkolemKW.C10.c10_of_chebotarev` (report: standard three axioms only).

## Name clashes (checked)
Namespace `TSkolemKW` does not occur in Leaves.lean. Leaves.lean has no top-level `open`. There
are no Leaves declarations under `TensorProduct.`/`Module.`/`NumberField.`. The anonymous
`instance : IsGalois ℚ Qbar` in `TSkolemKW.KW` gets a `TSkolemKW.KW.`-prefixed auto-name. Leaves
already has global `IsGalois ℚ (AlgebraicClosure ℚ)` instances (9116, 11538, 12024), so this one
is redundant but harmless (AllCheck already had two such).

## Final top-level declarations defined
`TSkolemKW.`: SkolemNoether, HSynSkolemNoether, LeafSkolemNoether, isSimpleRing_tensor,
nonempty_linearEquiv_of_finrank_eq, Twist (+ Twist.of, Twist.smul_of, Twist.isScalarTower, three
anonymous Twist instances), skolemNoether, hsynSkolemNoether, leafSkolemNoether,
BrauerNesbittChar0, isNilpotent_of_trace_pow_eq_zero, act, act_pow, trace_act_equiv,
trace_act_prod, fd_sub, exists_injective_of_trace_eq, brauerNesbitt_module, brauerNesbittChar0,
HSynBrauerNesbitt, repOfGL, repOfGL_apply, isSemisimpleModule_repOfGL, hsynBrauerNesbitt;
bridges pkgI6_skolemNoether, hsyn_t13, glueDescent_leafSkolemNoether, pkgI6_brauerNesbittChar0,
hsyn_t19, hsyn_t18_of_chebotarev, kroneckerWeberCyclic_of_hsyn,
hsyn_dirichletCharacter_of_kroneckerWeberCyclic.
`TSkolemKW.HS.`: Qbar, GQ, LiesOver, IsArithFrob, FrobeniusDense, LocMem, one_notMem, natCast_mem,
exists_frac_or_inv, locMem_or_inv, zbarLoc, mem_zbarLoc, gZ, gZ_coe, liesOver_and_isArithFrob,
frobeniusDense_of_frobDense, frobeniusDense_of_chebotarev.
`TSkolemKW.KW.`: Qbar, GQ, KroneckerWeber, (anonymous IsGalois instance), fixes_of_embeds,
ker_ge_of_kroneckerWeber, KroneckerWeberCyclic, kroneckerWeberCyclic_of_kroneckerWeber,
ker_ge_of_kroneckerWeberCyclic, eq_of_agree_on_roots, eq_of_agree_on_roots_cyclic,
exists_isPrimitiveRoot_qbar, card_rootsOfUnity_qbar, toRingAut, cycChar, cycChar_spec,
agree_of_cycChar_eq, cycChar_surjective, dirichletCharacter_of_kroneckerWeberCyclic,
isOpen_ker_of_continuous.
`TSkolemKW.C10.`: brauerNesbittChar0', c10_of_chebotarev.

## Expected trouble spots
- The HS section now runs against Leaves' `GlueC10` instead of its own copy. The text is
  identical, but the HS proofs have only been compiled against the copy.
- Delta-defeq bridges, especially `hsyn_t18_of_chebotarev`. Its instances (Krull topology on
  `HSyn.GQ` vs `HS.GQ`) should coincide: Leaves only adds `IsTopologicalGroup GQ` instances, and
  no `TopologicalSpace` instance on GQ.
- Global instances and 14 global `@[simp]` lemmas in Leaves.lean could affect `simp`/`simpa` in
  the task proofs. None is obviously related.
- `section Matrix` inside `namespace TSkolemKW` (the task's own) stays as is.
