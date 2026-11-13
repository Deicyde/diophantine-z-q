# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Task frob-trace, 2026-11-13. Lean: `scratch/frob-trace/part_frob.lean`. `scratch/frob-trace/build.sh`
assembles it into `scratch/frob-trace/FrobTrace.lean` after two verbatim copies (checked with
`cmp`): `part_tate_src.lean` = `scratch/unram-tate/TateBridge.lean`, and `part_bridge_src.lean` =
`scratch/g14-trace/part_bridge.lean`. One import is added: `ZInQKernel.HDecomp.C10.Link`, for
`FrobCompare`. Log: `scratch/frob-trace/log.md`.

## 1. Result

**`G14Bridge.TateBridge35` is proved from the existing leaf I3.M0 (`PkgI3.TateModuleFree`) and
one new AV-side glue Prop, `FrobTrace.AlgFrobRed`. Its conjunct `FrobTraceLink` therefore holds
for the operators it constructs.** The file compiles with no `sorry`. Every `#print axioms` line
gives `[propext, Classical.choice, Quot.sound]` (VERIFIED: `lake env lean
scratch/frob-trace/FrobTrace.lean`, exit 0, about 60 s; 26 axiom prints, log run 6).

```
theorem FrobTrace.tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree) (hR : AlgFrobRed) :
    G14Bridge.TateBridge35
```

It is the composite of three proved implications, each a theorem in the file:

```
algFrobOne_of_red          : AlgFrobRed → AlgFrobOne
algFrobLink_of_one         : AlgFrobOne → AlgFrobLink
tateBridge35_of_algFrobLink : PkgI3.TateModuleFree → AlgFrobLink → G14Bridge.TateBridge35
```

So any one of `AlgFrobLink`, `AlgFrobOne` or `AlgFrobRed`, together with I3.M0, gives
`TateBridge35`. `AlgFrobRed` is the smallest of the three. G14's consumer is
`G14Trace.g12Spec_g14_of_linked` (g14-trace). It takes linked `G7Out` data at 5 and 3 plus
`FrobTraceLink`, which is exactly what `TateBridge35` outputs. So the remaining input on this
side of G14 is `AlgFrobRed`. Through g14-trace's `tateBridge_five_three_of_35` (its copy is
compiled here), `TateBridge35` also gives the `ℓ = 5, 3` instances of g0-mod-field's
`TateBridge`.

No statement was changed. `TateBridge35` and `FrobTraceLink` are copied verbatim. Neither is
false or vacuous (see §4).

## 2. Named Props: leaf or glue

| Prop | kind | content |
|---|---|---|
| `PkgI3.TateModuleFree` (I3.M0) | **leaf** (existing, kernel `Objects.lean`) | `T_ℓ(A)` is free of rank `2 dim A` (Mumford, *Abelian Varieties* §18-19; locator as in pkg-I3, UNVERIFIED here). Used only for continuity, through unram-tate's `tateCont_of_tateModuleFree` |
| `FrobTrace.AlgFrobRed` | **glue** (new, AV side; N5 L777-786) | Setting: `A/L` an abelian variety, `L ⊆ ℚ̄` finite Galois, `F : A → A` a finite surjective morphism of schemes. Claim: there is a finite `S` such that for `p ∉ S`, `τ` an arithmetic Frobenius at `v ∣ p`, `g ∈ G_ℚ` and `f(x) = F ∘ x ∘ Spec(gτg⁻¹)` on `A(ℚ̄)`, there exist an abelian variety `Ā/k` with `char k = p`, `α' ∈ End(Ā)`, `N ≠ 0` and a group homomorphism `red : A(ℚ̄) → Ā(k̄)`. They satisfy `red ∘ (N·f) = α'_* ∘ red`, and for every prime `ℓ ≠ p` and every `n`, `red` is injective on `A[ℓⁿ]` and every point of `Ā(k̄)[ℓⁿ]` is the image of a point of `A[ℓⁿ]` |
| `FrobTrace.AlgFrobOne` | glue (implied by `AlgFrobRed`, proved) | the same, with `red` replaced by, for each prime `ℓ ≠ p`, a `ℚ_ℓ`-isomorphism `ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carrying `N·V_ℓ(f)` to `V_ℓ(α')` |
| `FrobTrace.AlgFrobLink` | glue (implied by `AlgFrobOne`, proved) | the same, for all maps `m_σ` of a descent datum at once (G7Data's clauses: Galois action on `G_L`, `G_L`-coset compatibility, `m_σ = F_σ ∘ - ∘ Spec σ`), at `σ = gτg⁻¹` |

The leaves that `AlgFrobRed` rests on. These are mathematical inputs; no Lean implication is
proved from them.
- I2-Red (`PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1; kernel `Objects.lean` L1467)
  gives the torsion clauses.
- I2-NMP (`PkgI2.NeronMappingAbelianScheme`, L1454) extends `F` to the abelian scheme.
- Mumford §4 rigidity says a morphism fixing `0` is a homomorphism (locator UNVERIFIED).
- Good reduction outside a finite set (spreading out) is also used. It is not a kernel leaf.

**Why `AlgFrobRed` is true** (N5 L777-786; SPECULATIVE in its Lean details; `N = 1` works).
Notation: `σ' = gτg⁻¹` is an arithmetic Frobenius at `v' = g(v)`, and `w = v' ∩ L`.
1. If `f` exists, then `F` lies over `Spec(s)` with `s = σ'⁻¹|_L`. Here `σ'|_L` lies in the
   decomposition group of `w`. Note that `≫` is diagrammatic and `Spec` is contravariant.
2. Let `S` be the primes below which `A` has bad reduction. Let `𝒜/O_w` be the abelian scheme
   and `Ā/κ(w)` its special fibre.
3. `F` is an `L`-morphism `A → A^{(s)}`, so it extends to `𝒜 → 𝒜^{(s)}` by I2-NMP.
4. `red` is `A(ℚ̄) = 𝒜(O_{v'}) → Ā(κ(v')) ≅ Ā(k̄)`, using the valuative criterion of
   properness.
5. `σ'` preserves `O_{v'}` and acts on `κ(v')` as `x ↦ x^p`. So `f` reduces to
   `x̄ ↦ F̄ ∘ x̄ ∘ Spec(Frob) = F̄ ∘ Fr_Ā ∘ x̄`, where `Fr_Ā` is the absolute Frobenius.
6. `F̄ ∘ Fr_Ā` lies over `Spec(φ⁻¹) ∘ Spec(φ) = id_{κ(w)}` and fixes `0`, because `f` is
   additive. By rigidity it is an endomorphism `α'`.
7. The torsion clauses are I2-Red for `m = ℓⁿ`.

`S` depends only on `A` (step 2). This is allowed, since `AlgFrobRed` lets `S` depend on `F`.

## 3. Proof outline (all steps compiled)

1. **The scalars in `ℚ̄`** (`scalarsQbar`, no leaf). `DescentDatum` and `G7Data` supply
   `a > 0`, `c = n/d`, the sign cocycle `ε` with `a_σ a_τ c = ε a_{στ}` and `∂β = ε`, and
   `a = β = 1` on `G_{L'}`. From these, `gC = β/a` satisfies `gC_σ gC_τ = c·gC_{στ}`, with
   `gC_σ^r ∈ ℚ` and `β_σ^{2r} = 1` when `σ^r ∈ G_{L'}`. So `gC` and `β` are algebraic, and
   embedding the field they generate into `ℚ̄` gives `γQ`, `βQ : G_ℚ → ℚ̄` and `ιC : ℚ̄ → ℂ` with
   `∂γQ = c`, `γQ = 1` on `G_{L'}` and `ιC ∘ βQ = β`.
2. **`G7Out` at `ℓ = 5, 3`** (`key` inside `tateBridge35_of_algFrobLink`). This is unram-tate's
   construction with `γ = j_ℓ ∘ γQ` (`j_ℓ = IsAlgClosed.lift : ℚ̄ → ℚ̄_ℓ`). It uses
   `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, `c = ε' = n/d`, `a' = 1` and `β' = γ(h·h⁻¹)`. The result
   is then rescaled by `φ = j_ℓ(βQ)/γ(h·h⁻¹)` (`g7Out_rescale`, proved; `φ = 1` on `G_{L'}`;
   `ρ = β⁻¹aT` is unchanged). That turns the scalars into `j_ℓ ∘ aQ` and `j_ℓ ∘ βQ`, with
   `aQ = βQ / γQ(h·h⁻¹)`. These are the same `aQ`, `βQ` at both primes, as `TateBridge35`
   requires.
3. **`FrobTraceLink`.** Apply `AlgFrobLink` to `m` with `g = h`. For `p ∉ S ∪ {3, 5}`, it gives
   the comparison of `N·V_ℓ(m_{hτh⁻¹})` with `V_ℓ(α')` at `ℓ = 3` and at `ℓ = 5`.
   `frobCompare_opV_conjE` (proved) transports this through `T_ℓ(Θ)` (`tateMapEquiv`) and base
   change to `ℚ̄_ℓ` (`conj_baseChange`). The result is the kernel's `FrobCompare ℓ (Tm_ℓ τ) α' N`.
4. **`AlgFrobOne → AlgFrobLink`** (`algFrobLink_of_one`). Fix one representative `σ_s` for
   each `s ∈ Gal(L/ℚ)`. For `k ∈ G_L`, `m_{σ_s k}(x) = F_{σ_s} ∘ x ∘ Spec(σ_s k)`, by the
   coset clause together with `m_k = galAct k = Spec(k) ≫ -`. Then `S = ⋃_s S(F_{σ_s})`, a
   finite union because `Gal(L/ℚ)` is finite.
5. **`AlgFrobRed → AlgFrobOne`** (`algFrobOne_of_red`). `T_ℓ(red)` is bijective
   (`tateMap_bijective`, pure algebra: compatible preimages exist by uniqueness on torsion). Take
   `Ψ = ℚ_ℓ ⊗ T_ℓ(red)`. Then `Ψ ∘ N·V_ℓ(f) ∘ Ψ⁻¹ = V_ℓ(α')` comes from `red ∘ N f = α' ∘ red`,
   checked componentwise.

## 4. Checks on the statements

- `TateBridge35` is not vacuous: its hypotheses are G7's actual data. It is not inert either:
  `G7Out` forces `ρ = β⁻¹ a Tm` to be a continuous representation extending the Tate
  representation (unram-tate §1), and `FrobTraceLink` ties `Tm_3` to `Tm_5` (g14-trace F2). The
  construction does not use any degenerate choice. The operators are the Tate functor applied to
  G7's points-level descent datum `m` (including its algebraicity clause, which `AlgFrobLink`
  consumes).
- `AlgFrobRed` cannot be met by a degenerate `Ā`. The torsion clauses force
  `Ā(k̄)[ℓⁿ] ≅ A(ℚ̄)[ℓⁿ]`, which is `(ℤ/ℓⁿ)^{2 dim A}`, for all `ℓ ≠ p`. The intertwining holds on
  all points. Its hypothesis (`f` of the given shape) is met by G7's maps `m_σ`.
- `AlgFrobLink` allows any `N ≠ 0`. That makes it weaker than the `N = 1` statement, and it is
  what `FrobCompare` uses.
- Like `TateBridge`, `TateBridge35` does not tie `Tm_ℓ` to `m_σ` in its statement (its docstring
  says so). So its `FrobTraceLink` conjunct constrains the operators chosen jointly with `G7Out`,
  not "the" operator built from `m`. That is enough for G14, which uses only traces, and the
  construction here does use the operators built from `m`.
- Review: one model review (read-only; no human review) of `AlgFrobLink`, `AlgFrobOne`,
  `AlgFrobRed`, `TateBridge35` and `FrobTraceLink`. It found all three glue Props true as stated
  (with `N = 1`), not vacuous and not degenerate:
  - `S` is quantified before `p, v, τ, g, f`;
  - the reduction is taken at `g(v)`, where `gτg⁻¹` is a Frobenius;
  - `red` exists on all points, by the valuative criterion for the non-noetherian `O_{g(v)}`;
  - the torsion clauses follow from `𝒜[ℓⁿ]` being finite étale and `O_{g(v)}` Henselian.

  It found two slips in the `AlgFrobLink` docstring (`w = v ∩ L` for `g(v) ∩ L`, and `m_τ` for
  `m_{gτg⁻¹}`), both fixed. The finiteness and surjectivity hypotheses on `F` are not needed for
  truth; they are harmless.

## 5. What compiles, what remains

- `scratch/frob-trace/FrobTrace.lean`: exit 0, no `sorry`, all axiom prints standard
  (VERIFIED). New declarations (namespace `FrobTrace`): `tateMapEquiv`, `conj_baseChange`,
  `AlgFrobLink`, `AlgFrobOne`, `algFrobLink_of_one`, `tateMap_bijective`, `AlgFrobRed`,
  `algFrobOne_of_red`, `frobCompare_opV_conjE`, `g7Out_rescale`, `scalarsQbar`,
  `tateBridge35_of_algFrobLink`, `tateBridge35_of_algFrobOne`, `tateBridge35_of_algFrobRed`.
- Remains: the glue `AlgFrobRed`, i.e. reduction of abelian varieties on PkgI3 objects. Deriving
  it in Lean from I2-Red and I2-NMP needs several things:
  - the abelian-scheme model over `O_w` for almost all `w` (spreading out; no kernel leaf yet);
  - a translation between PkgI3's `AbVar L` with points over `ℚ̄` and PkgI2's
    `Grp (Over Spec K)` with points over `AlgebraicClosure K`;
  - the reduction map as a homomorphism (I2-Red gives a bijection of torsion sets through the
    relation `IsReductionOf`);
  - absolute Frobenius on points.

  None of this was attempted.
- Not composed here: `G14Trace.g12Spec_g14_of_linked` (g14-trace's `G14Trace.lean`) and this
  file are separate environments. As in g14-trace, `G14Bridge.FrobTraceLink` and
  `G14Trace.FrobTraceLink` match by identical text only.
