# T30 local square-root glue: conditional on actual local Kronecker–Weber

Status: proposed focused proof contribution, based on main
`a5937595cde3e3db00975b81e5171cdef92c801a`. No target registration, headline change,
local-KW proof, independent acceptance, or assembled class-field-theory claim is made.

## Exact result and remaining mathematical premise

Module: `ZInQKernel/Contrib/LocalSquareRoot/Criterion.lean`.

```lean
theorem ZInQ.Contrib.LocalSquareRoot.localKroneckerWeber_implies_leafSqrtCrit :
    (∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p) →
      GlueDescent.B2Q.LeafSqrtCrit
```

This is a closed theorem of an implication, **not** an unconditional proof of T30.
Its conclusion is the actual baseline leaf: for every prime `p`, nonzero modulus
`N`, Dirichlet character `χ : DirichletCharacter ℂ N`, and unit `u : (ZMod N)ˣ`
whose two casts are `-1` at `p ^ N.factorization p` and `1` at
`N / p ^ N.factorization p`,

```lean
(∃ φ : GlueDescent.B2Q.GQp p →* ℂˣ,
    IsLocallyConstant φ ∧
    ∀ x, φ x ^ 2 = GlueDescent.B2Q.galChar χ (GlueDescent.B2Q.resp p x)) ↔
  χ.toUnitHom u = 1
```

The remaining premise is **exactly T16(a)**, the universal baseline
`PkgI6.LocalKroneckerWeber`. It asserts containment of each actual finite abelian
intermediate field of `PadicAlgCl p` in an actual cyclotomic adjoin. T16(b),
`LocalReciprocityUpper`, is not used. There is no assumed square-root criterion,
`Fact` containing the target, replacement absolute Galois group, or reciprocity
compatibility assumption. `dirichlet_squareRoot_at_level` proves sufficiency
without local KW; KW is used only for necessity for an arbitrary locally constant
square-root character.

## Frozen inputs and provenance

- Baseline `ZInQKernel/HDecomp/Descent/B2Glue.lean`, lines 239–300 and 333–386,
  at the base above, SHA-256
  `bd7e603f92928ff3f34121d053be9d945b82968200486fb77ea3a22a968cd545`.
- Baseline `ZInQKernel/HDecomp/Conductor/I6Base.lean`, lines 249–260,
  same base, SHA-256
  `3a2688e5271203cb1d28663fefe3c017426a43dd4c5f4a710f0dabe6de96ce2d`.
- Frozen reference `ZInQKernel/Targets/H/T30.lean` at PR41 head
  `2757349fbd8ca613340b679bbd149f78c2baba6b`, SHA-256
  `1fce557f1f3e7ec30d4a7570c220a5342b167014ecc39a6204b45bcb11a10833`.
  The supplied frozen bytes were compared with that exact Git blob. Its
  `T30_iff_baseline` is `Iff.rfl`; the draft is unregistered and not accepted.
  Neither the frozen target nor the research leaf collection is imported.
- Research supplier `533aa66cc3485e21f2d90303e3a34f79d081722d`,
  `scratch/glue-sqrt-disj/Disj.lean`, SHA-256
  `8454c6906fc902eacf07ec14a0aec16543af191546fb0d0be954c6e00df94e67`,
  together with `docs/research/glue-sqrt-disj.md` and the preserved uncompiled
  `scratch/glue-sqrt-disj/AbsoluteAttempt.lean.txt`.
- Lean 4.35.0 and pinned Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The production base is main, **not the research branch**. `FiniteLevel.lean`
mechanically ports the already-proved unramified, disjointness, level-change, and
finite square-root machinery. Retained arithmetic source spans are 3–267,
330–428, 444–462, 499–729, and 745–1015. Duplicate helpers and unused standalone
corollaries were omitted. `Fields.lean` ports the actual cyclotomic adjoin and its
normalization from source lines 1029–1087, importing the baseline local-KW
proposition instead of redeclaring it.

The finite arithmetic is not redone. The supplying finite criterion had target
`AddCircle (1 : ℚ)`; its arithmetic proof is retained with target
`Additive ℂˣ`. `ComplexCharacter.lean` supplies the coefficient bridge:
algebraic closedness proves divisibility of nonzero complex numbers, Baer's
criterion gives character extension, and the frozen doubling-kernel/quotient/range
argument proves the half-character criterion. Additive `2 •` and `0` become
multiplicative square and `1`. This changes coefficients, not the finite Galois
objects, restriction maps, or the dyadic calculation.

Historically, the finite criterion and its arithmetic plumbing were already
proved. The research note explicitly left absolute-Galois descent, inflation,
and matching to the baseline character unfinished. Those are the new connections
here. The earlier concrete `muAlgebra` transitivity attempt was uncompiled;
`restrictNormal_trans` now proves transitivity through abstract scalar-tower maps
by `AlgEquiv.ext` and injectivity of the actual algebra map, before specializing
it to intermediate-field inclusions. No earlier favorable verdict is treated as
acceptance of this new assembly.

## Source-to-consumer connections

### 1. The actual character and finite cyclotomic field

`finiteCyc p N` is the primitive-root eigenvalue on
`Gal(muField p N / ℚ_[p])`, with
`muField p N = IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ N = 1}`.
`finiteGalChar p χ` is `χ.toUnitHom.comp (finiteCyc p N)`.

`absoluteGalois_map_intertwines` unfolds the exact `IsAlgClosed.lift` chosen inside
`Field.absoluteGaloisGroup.map`. `autToPow_map` compares eigenvalues through that
embedding and normal restriction; independence of the chosen primitive root is
proved. Consequently:

```lean
finiteGalChar (p : ℕ) χ (g.restrictNormal (muField (p : ℕ) N)) =
  GlueDescent.B2Q.galChar χ (GlueDescent.B2Q.resp p g)
```

Thus the descended character is the one consumed by the baseline, not just an
isomorphic abstract character.

### 2. Actual tau matching and sufficient square-root construction

The canonical factorization is proved using `Nat.ordProj_mul_ordCompl_eq_self`,
`Nat.ordCompl_pos`, and `Nat.coprime_ordCompl`. It uses exactly the factorization
and quotient appearing in the target's casts.

At level `N = p^k m`, `exists_tau` supplies a finite automorphism with
`galToProd τ = (-1,1)`. `finiteCyc_components` identifies both residues of its
actual cyclotomic eigenvalue. `finiteCyc_tau_eq` then uses the actual Chinese
remainder equivalence to prove `finiteCyc τ = u`; hence
`finiteGalChar χ τ = χ.toUnitHom u`.

If this value is one, the frozen finite criterion supplies the square-root
character at
`p^(k+1) * (p^(2f) - 1)`, where `f = orderOf (ZMod.unitOfCoprime p hcop)`.
`enlarged_level_pos` discharges the nonzero side condition, including `m = 1`.
`level_dvd` and `muField_mono` give the actual inclusion. The algebra in the tower
is induced by `IntermediateField.inclusion`, with both base and ambient scalar
compatibilities proved. Restriction is transitive.

Inflation through `AlgEquiv.restrictNormalHom` is locally constant because its
kernel contains the open fixing subgroup of this actual finite field. The
pointwise square identity is transferred through transitivity and the exact
baseline-character equality above. No local-KW input is needed here.

### 3. Necessity uses local KW on the square root's own field

For an arbitrary locally constant `φ : GQp p →* ℂˣ`, its kernel is open and closed
in the actual Krull topology. Infinite Galois correspondence gives its fixed field
`M`, proves `FiniteDimensional ℚ_[p] M`, and identifies
`M.fixingSubgroup = φ.ker`. Normality gives a Galois extension. The actual normal
automorphism quotient embeds into `φ.range`, a subgroup of the commutative group
`ℂˣ`, proving `IsAbelianGalois ℚ_[p] M`.

The generic fixed-field lemma explicitly assumes `PerfectField F`: an algebraic
closure over an imperfect field need not be separable. Its applications here set
`F = ℚ_[p]` and discharge that requirement by characteristic zero.

Apply the actual local-KW premise to **this `M`**, then enlarge the resulting
cyclotomic level to include the original Dirichlet level. `normalized_level_dvd`
proves both lower-level maps: the primary exponent inequality and prime-to-`p`
divisibility. `descendCharacter` descends `φ` using the surjective actual normal
restriction and the proved fixing-subgroup/kernel inclusion;
`descendCharacter_apply` identifies its evaluation with the original `φ`.

Choose the finite tau at the common larger level. It squares to one, and
`tau_restrict_acts` plus injectivity identifies its lower restriction with the
original tau. Lift it through the surjective absolute-Galois restriction map.
**The lift is not assumed to be an involution.** Its square is killed by the
descended square-root character, because the finite tau squares to one. The
original pointwise square identity now proves the original character's value at
tau is one, and the CRT match identifies that value with `χ.toUnitHom u`.

## Nine application checks and coverage

1. **Source hypotheses:** actual finite abelian `M` supplied to actual local KW;
   characteristic-zero perfectness and normality are proved/inferred, not omitted.
2. **Constructed objects:** baseline `GQp`, `resp`, `galChar`, `ℂˣ`, actual
   `PadicAlgCl` intermediate fields, and genuine finite Galois groups throughout.
3. **Domain/index coverage:** every `Nat.Primes` prime and every nonzero modulus;
   canonical factorization, inclusion, and enlarged-level nonzeroness proved.
4. **Transition maps:** the chosen baseline closure embedding, actual intermediate
   inclusions, surjective normal restrictions, and scalar-tower transitivity.
5. **Consumed-object identity:** exact inflated-character equality and exact tau/CRT
   eigenvalue equality, not merely proportionality or an abstract factorization.
6. **Coefficients/normalization:** complex units; additive tagging only; square/one
   agrees exactly with the baseline convention. No reciprocity sign convention is
   assumed, since the finite eigenvalue is computed directly.
7. **Local conditions:** actual Krull topology and `IsLocallyConstant`; open kernel
   for descent and an open fixing subgroup for inflation. Merely complex-valued
   continuity is not substituted for local constancy.
8. **Exceptional cases:** `p = 2`, `k = 0`, `N = 1`, and `m = 1` are retained. The
   frozen `redU_sq_eq_one` loses one primary power at every prime, including two;
   the unramified order is doubled. Modulus-one CRT components are allowed.
9. **Downstream consumption:** the exact baseline `LeafSqrtCrit`; no root, registry,
   protected baseline, pin, manuscript, or acceptance record is changed. Frozen
   draft T30 remains unregistered, and no unconditional provider is introduced.

This inventory covers this scoped implication and its direct supplying modules.
It does not purport to inventory or accept the whole height decomposition or CFT.
Proof construction and mechanical source extraction used automated tooling;
verification and provenance are recorded here. No independent acceptance is
supplied by the contribution's authors.

## Validation and reproduction

On 2026-11-12 the final dependency-ordered rebuild of all **ten owned modules**
exited **0**. `Audit.lean` passed the exact expanded frozen T30 type check and all
three endpoint examples: arbitrary-prime `N = 1`, the prime-to-two level `p = 2,
k = 0, N = 3`, and the dyadic obstruction at `p = 2, k = 2, N = 4`.

The 79 named supplying declarations' `#print axioms` readback contains only
subsets of `{propext, Classical.choice, Quot.sound}`. The final implication's set
is exactly those three allowed axioms. The finite-level supplying theorem text
was also compared with the frozen source: after the stated coefficient-type
replacement, its theorem body is unchanged.

The build retains style/unused-section-variable warnings, including warnings in
the frozen port; no linter is disabled to conceal them. Final source checks found
no forbidden proof/runtime declarations and no trailing whitespace. Git readback
confirmed the prescribed branch and unchanged main base, no changed tracked file,
and only the ten new contribution modules plus this dedicated note.

The checked normal commands use direct Lean against already-built pinned
baseline/dependency outputs. Compilation is sequential, with `LEAN_NUM_THREADS=2`;
resource gating does not alter arguments, sources, or compiler results. No
package setup, update, pin change, shared-cache write, or broad root build is run.
Given an already supplied `LEAN_PATH` for that pinned build, the normal commands
are reproducible with repository-relative paths:

```sh
export LEAN_NUM_THREADS=2
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/LocalSquareRoot
for mod in ComplexCharacter FiniteLevel Fields GaloisQuotient Tower \
    FiniteComplex Necessity Cyclotomic Criterion Audit; do
  lean -o ".lake/build/lib/lean/ZInQKernel/Contrib/LocalSquareRoot/$mod.olean" \
    "ZInQKernel/Contrib/LocalSquareRoot/$mod.lean" || exit "$?"
done
```

`Audit.lean` checks the expanded frozen T30 type with only T16(a) prepended, the
endpoint examples, and `#print axioms` for the 79 named supplying declarations.
This is author-side source compilation and axiom readback. Parent integration,
full project kernel replay, final source binding, and eligible independent review
remain separate outstanding checks. This proof-only contribution promotes no
polynomial record, so complete-manuscript release duties do not apply to this
scope; existing manuscript and release artifacts remain untouched.

## Source hashes

All module paths are under `ZInQKernel/Contrib/LocalSquareRoot/`. SHA-256 is over
the final UTF-8/LF source bytes. These are uncommitted contribution sources, not a
new committed or independently accepted revision.

| Module | SHA-256 |
| --- | --- |
| `ComplexCharacter.lean` | `dcf328775623b6e56e7374554c743cd785e9a87e96e571a65eaf846195477c93` |
| `FiniteLevel.lean` | `e130499acca61c2722e6af2414708473980aa1625abda816dc123c617b4832d4` |
| `Fields.lean` | `b8bd0527cbdcee216b54f1d32dd3bec44e14e186329dbf74791cd4a1975edf8c` |
| `GaloisQuotient.lean` | `6d65c01da8d1b49c7350b6c1637a73ee6180116f4566d15d98d0fbc855522de8` |
| `Tower.lean` | `4a5d7e536046bf7c2d3abe31a340d4bd1608c388e2a2f71852580c488e4439fe` |
| `FiniteComplex.lean` | `825562686e17fe6c0963ce9e3f5fc00a6779670257a5f8db1ec2b24fccddabda` |
| `Necessity.lean` | `8a2265084ff14236b39688ee86eec47731ea085e28c51033290535327e17e646` |
| `Cyclotomic.lean` | `21d791a5203552fff952b5251b8fdb7d0858f10a3fc7cbe14ba678048a607df0` |
| `Criterion.lean` | `c751dbeebef3c62456caca8882005421ad44fc5349d6b2f930823a150fc2c63d` |
| `Audit.lean` | `9b85c1a8fb576c321afd004947364e342e1dd64fdd4e838872d1d5864775cfcd` |
