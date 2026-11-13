# g14-trace: `G14TraceCompat` (r₃ and r₅ in one compatible system)

Task g14-trace, 2026-11-13. Lean: `scratch/g14-trace/part_g14.lean` (namespace `G14Trace`),
assembled by `scratch/g14-trace/build.sh` into `scratch/g14-trace/G14Trace.lean` after verbatim
copies of g0-mod-newform's parts. The second file, `scratch/g14-trace/part_bridge.lean`, is
assembled by `build_bridge.sh` into `G14Bridge.lean` after a verbatim copy of g0-mod-field's
`ModField.lean`. Log: `scratch/g14-trace/log.md`.

## 1. Result

**`G14TraceCompat D` is reduced to the leaf T7 plus one AV-side glue Prop, for the data `D`
that G8 constructs. The reduction compiles with no `sorry` and only standard axioms (VERIFIED).**
The precondition is that the `ℓ = 3` and `ℓ = 5` descent data share their scalars. The
producers' interface does not yet supply that link (finding F1 below), so the reduction also
states the corrected interface.

The target, copied verbatim from `scratch/g0-mod-newform/part_new.lean` (L197). For the data
`D = ⟨i, ιC, ι₅, ι₃, r₅, r₃⟩` it says: there is a finite `S` such that at every arithmetic
Frobenius `τ` above a prime `p ∉ S`, `tr r₅(τ) = ι₅(c)` implies `tr r₃(τ) = ι₃(c)`.

**Main theorem** (`G14Trace.g14TraceCompat_of_link`; VERIFIED, standard axioms):

```
theorem g14TraceCompat_of_link (hM : CharPolyIndepOfEll) (D : ModData K A)
    (j5 : Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : Qbar →ₐ[ℚ] PadicAlgCl 3) (γ : Qbar →ₐ[ℚ] Qbar)
    (hι5 : D.ι5 = j5.comp γ) (hι3 : D.ι3 = j3.comp γ) (a β : GQ → Qbar)
    (Tm5 : GQ → Module.End (PadicAlgCl 5) (Vb A 5)) (Tm3 : GQ → Module.End (PadicAlgCl 3) (Vb A 3))
    (h5 : GalG8Out A 5 (GlueDescent.rho Tm5 (fun g => j5 (a g)) (fun g => j5 (β g))) D.r5)
    (h3 : GalG8Out A 3 (GlueDescent.rho Tm3 (fun g => j3 (a g)) (fun g => j3 (β g))) D.r3)
    (hF : FrobTraceLink A Tm5 Tm3) : G14TraceCompat D
```

The hypotheses:
- `GalG8Out` is G8's output (g0-mod-galois' `G8Out`, as copied by g0-mod-newform). Its `e`
  intertwines `ρ_ℓ` with `r_ℓ ⊕ r_ℓ` on all of `G_ℚ`.
- `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` is the descended operator (`GlueDescent.rho`), built from one pair
  `a, β : G_ℚ → ℚ̄` mapped by `j_ℓ`. This is the *scalar link* (N5 L719-722).
- `FrobTraceLink` is the new AV-side glue Prop (§2).
- `hM` is the leaf T7, Mumford §19 Thm 4 (kernel's `PkgI3.CharPolyIndepOfEll`).

**Composite with G12** (`G14Trace.g12Spec_g14_of_galois`; VERIFIED). Add g0-mod-newform's
`DirichletOfFinite`, T7, G8's outputs at 3 and 5 (on the linked `ρ_ℓ`), G12's output
`GalG12Out r₅` and `FrobTraceLink`. Then
`∃ D, D.r5 = r5 ∧ D.r3 = r3 ∧ G12Spec D ∧ G14TraceCompat D`. That gives the first two conjuncts
of the input of g0-mod-newform's `modularConstituent_tail_G`. The equalities keep G8's `r₅`,
`r₃`, so the third conjunct `G15RamG D u` can be proved for them.

`G14Trace.g12Spec_g14_of_linked` starts one step earlier, from linked `G7Out` data at 5 and 3,
`FrobTraceLink`, and G8-G12 as hypotheses (in the shapes of g0-mod-galois' `g8_g12` and
`g8_g11`). It returns G8's `r₅`, `r₃` with their `GalG8Out`, and data `D` that carry them with
`G12Spec ∧ G14TraceCompat`. The embedding `ι₅` is Pan's (from
`g12Spec_of_galois`), and `ι₃ := j₃ ∘ γ`, where `ι₅ = j₅ ∘ γ` (`exists_comp_eq`, proved: any two
`ℚ`-embeddings of `ℚ̄` into a field differ by an endomorphism of `ℚ̄`).

**The statement is not changed**, and it is true for G8's construction from linked data (N5
L776-795). If the `ℓ = 3` data are an arbitrary `G7Out`, it *can fail* (F1, F2). This is the
"twists" warning in its docstring, made precise.

## 2. Named Props: what is leaf and what is glue

| Prop | kind | content | where |
|---|---|---|---|
| `PkgI3.CharPolyIndepOfEll` (T7) | **leaf** (existing) | the char. polynomial of `V_ℓ(φ)`, for `φ ∈ End(A)` and `A` over any field, is one monic `P ∈ ℤ[X]` for all `ℓ ≠ char k` | kernel `Objects.lean`; Mumford, *Abelian Varieties*, §19 Thm 4 (h-decomposition T7) |
| `G14Trace.FrobTraceLink A Tm₅ Tm₃` | **glue** (new, AV side) | there is a finite `S`. At an arithmetic Frobenius `τ` above `p ∉ S` there are an abelian variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)` and `N ≠ 0` with `FrobCompare ℓ (Tm_ℓ τ) α' N` at `ℓ = 3` and `ℓ = 5`: some isomorphism `ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ ⊗ V_ℓ(Ā)` carries `N·Tm_ℓ(τ)` to `V_ℓ(α')` | `part_g14.lean` §3; N5 L777-786 |
| `G14Trace.FrobSquaresLink` | **glue** (new; implies `FrobTraceLink`, proved: `frobTraceLink_of_squares`) | the same with `FrobCompare` split into the kernel's three squares (`GlueC10Link.FrobSquares`): descent instantiation `N·Tm_ℓ(τ) = μ' ∘ τ_*`, Serre–Tate `red' ∘ τ_* = V_ℓ(F) ∘ red`, Néron `red ∘ V_ℓ(μ') = V_ℓ(μ̄') ∘ red'` | `part_g14.lean` §3 |
| `G14Bridge.TateBridge35` | **glue** (new; corrects g0-mod-field's `TateBridge` at `ℓ = 3, 5`) | from `G7Data`, one pair `a, β : G_ℚ → ℚ̄` and embeddings `j₅`, `j₃`, with `G7Out` at 5 and at 3 for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, `FrobTraceLink` for the two `Tm_ℓ`, and `ιC ∘ β = G7Data's β` for some `ιC`. Like `TateBridge`, it does not tie `a` to `DescentDatum`'s `a` or `Tm_ℓ` to `m_σ` | `part_bridge.lean` |
| `G0ModNewform.DirichletOfFinite` | glue (existing, g0-mod-newform) | only used by the composite with G12 | — |

`FrobCompare`, `FrobSquares`, `trace_T_of_frobCompare` and `frobCompare_of_frobSquares` are the
kernel's (`ZInQKernel/HDecomp/C10/Link.lean`, glue-c10-link), reused unchanged.

**Why `FrobTraceLink` is true** for Glazer's `A/L'` (N5 L777-786; SPECULATIVE only in its Lean
details). Take `S = T ∪ {3, 5}` together with the primes ramified in `L'`, where `T` is the set
of bad primes. For `p ∉ S` and an arithmetic Frobenius `τ` at `v`:
- `A` has good reduction at `v ∩ L'`, with reduction `Ā` over the residue field `k`.
- `τ` maps the reduction of `A` to that of `{}^τA`. That reduction is `Ā^{(p)}`, and on points
  `τ` acts as the relative `p`-Frobenius `F : Ā → Ā^{(p)}`.
- `μ_τ : {}^τA → A` is defined over `L ⊆ L'` (N5 L638-640), so it reduces to `μ̄_τ`.
- With the Serre–Tate reduction isomorphism `V_ℓ(A) ≅ V_ℓ(Ā)` (leaf I2-Red, Néron), `N·Tm_ℓ(τ)`
  becomes `V_ℓ(α')` with `α' = N μ̄_τ ∘ F`. The same `α'` serves every `ℓ ≠ p`, because `Tm_ℓ` is
  built from one points-level `m_τ = μ_τ ∘ τ`.

**Why the scalar link is true.** N5 takes `a_σ = deg(μ_σ)^{-1/4}` (N5 L647), a real algebraic
number. In g0-mod-field's `DescentDatum` (`a : G_ℚ → ℝ_{>0}` with
`a_σ a_τ (n/d) = ε(σ,τ) a_{στ}`), once `m` is fixed, two such `a` differ by a homomorphism
`Gal(L/ℚ) → ℝ_{>0}`, which is trivial. Iterating the relation shows `a_σ^m ∈ ℚ` when
`σ^m ∈ G_L`. `G7Data`'s `β` has `β² = χ` of finite order, so its values are roots of unity.
`c = n/d ∈ ℚ` is the same at every `ℓ`. N5 L719-722 maps the scalars to `ℚ̄_ℓ` by embeddings of
the coefficient field. `TateBridge`'s docstring says the same, but its statement does not.

## 3. Findings

- **F1 (VERIFIED by reading `scratch/g0-mod-field/ModField.lean` L1021).** g0-mod-field's
  `TateBridge` concludes `∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`. The `ℓ = 3` data are not tied to the
  `ℓ = 5` data, nor to `G7Data`'s `β`. So the chain G7 → G8 (g0-mod-galois, `g8` at each `ℓ`) →
  `g12Spec_of_galois` can hand g0-mod-newform a pair `r₅, r₃` that is not one compatible
  system.
- **F2 (Lean, VERIFIED: `g7Out_twist`, `trace_rho_twist`, `twist_obstruction`).**
  - `G7Out A ℓ Tm c ε a β u` is preserved by `a ↦ χ·a`, for any continuous character
    `χ : G_ℚ → ℚ̄_ℓ^×` trivial on `G_K`. This twist multiplies `tr ρ_ℓ` by `χ`.
  - Take two data `D`, `D'` with the same `r₅`, `ι₅`, `ι₃`, where `tr D'.r₃ = χ · tr D.r₃`. If
    `G14TraceCompat` holds for both, then `(χ(τ) − 1) tr r₃(τ) = 0` at almost every Frobenius at
    which `tr r₅(τ)` is algebraic.
  - Consequence: for a fixed `ι₃`, given a nontrivial character `χ` of `Gal(L'/ℚ)` and
    `r₃ ≇ r₃ ⊗ χ`, at most one of the two twists satisfies `G14TraceCompat`. `G7Out` at `ℓ = 3`
    alone does not determine which one. This is a statement about the interface, not a proved
    non-implication: it needs such a `χ` (so `Gal(L'/ℚ)` must not be perfect), and it does not
    treat other choices of `ι₃`. In Glazer's argument
    it is fixed by using the same `a_σ` at every `ℓ`.
  - Correction: `TateBridge35` (§2), proved to contain the `ℓ = 3, 5` conclusions of `TateBridge`
    (`tateBridge_five_three_of_35`).
- **F3 (VERIFIED by reading).** The kernel already proves the trace link for the descended
  representation, in its own packaging: `GlueC10Link.trace_link`, `trace_link_three_five` and
  `c10_of_squares`, with `rL` the restriction to `e₀₀V`. g0-mod-newform's `r_ℓ` is instead
  G8's matrix representation with an intertwiner `e`. `trace_of_intertwines` (new, proved)
  connects the two: `tr ρ_ℓ(g) = 2 tr r_ℓ(g)` from `e` alone.

## 4. Proof outline (all steps proved in Lean)

1. `trace_of_intertwines`: `e` conjugates `ρ_ℓ(g)` to `toLin' M ⊕ toLin' M`, so
   `tr ρ_ℓ(g) = 2 tr M` (`LinearMap.trace_conj'`, `trace_prodMap'`, `Matrix.trace_toLin'_eq`).
2. The kernel's `trace_rho`: `tr ρ_ℓ(τ) = j_ℓ(β τ)⁻¹ j_ℓ(a τ) tr Tm_ℓ(τ)`.
3. The kernel's `trace_T_of_frobCompare` (from T7): one integer `t` with
   `N · tr Tm_ℓ(τ) = t` at `ℓ = 3` and at `ℓ = 5`, since `3, 5 ≠ char k` because `p ∉ S ∪ {3, 5}`.
4. `trace_eq_image`: `tr r_ℓ(τ) = j_ℓ(x)` with `x = ½ β(τ)⁻¹ a(τ) t/N ∈ ℚ̄` (`common_trace`).
5. `g14TraceCompat_of_common`: if `tr r₅(τ) = ι₅(c) = j₅(γ c)`, then `x = γ c` because `j₅` is
   injective, so `tr r₃(τ) = j₃(γ c) = ι₃(c)`.

## 5. What compiles, what remains

- `scratch/g14-trace/G14Trace.lean` (copies plus `part_g14.lean`, ~80 s): exit 0, no `sorry`.
  The 31 `#print axioms` lines (19 copied from g0-mod-newform, 12 new) all give
  `[propext, Classical.choice, Quot.sound]` (VERIFIED; log run4, run5).
- `scratch/g14-trace/G14Bridge.lean` (copy of `ModField.lean` plus `part_bridge.lean`, ~50 s):
  exit 0, no `sorry`, all axiom prints standard, including
  `G14Bridge.tateBridge_five_three_of_35` (VERIFIED; log bridge run1, run5).
- New Lean declarations (namespace `G14Trace`): `G7Out` (verbatim copy), `g7Out_twist`,
  `trace_rho_twist`, `twist_obstruction`, `trace_of_intertwines`, `trace_eq_image`,
  `FrobTraceLink`, `FrobSquaresLink`, `frobTraceLink_of_squares`, `common_trace`,
  `exists_comp_eq`, `g14TraceCompat_of_common`, `g14TraceCompat_of_link`,
  `g12Spec_g14_of_galois` and `g12Spec_g14_of_linked`. The last one takes linked `G7Out` data at
  5 and 3, `FrobTraceLink`, and g0-mod-galois' G8-G12 in the shapes of their `g8_g12` and
  `g8_g11`. In namespace `G14Bridge`: `FrobTraceLink`, `TateBridge35` and
  `tateBridge_five_three_of_35`.
- Remains:
  - the glue Props `FrobTraceLink`, or its square form `FrobSquaresLink`, for the genuine `A/L'`
    (reduction of abelian varieties: needs good reduction and the Néron / Serre–Tate inputs of
    pkg-I2 on PkgI3 objects);
  - `TateBridge35`, the Tate functor applied to G7's points-level data, as for `TateBridge`.
- No new literature leaf. T7 is used exactly in its kernel form.
- Two files: `TateBridge35` (over `G7Data`, in `G14Bridge.lean`) and `g12Spec_g14_of_linked` (in
  `G14Trace.lean`) are not composed in one environment. `G14Bridge.FrobTraceLink` over
  `GaloisCopy.Vb` and `G14Trace.FrobTraceLink` over `Vb` match only by identical text, as do the
  two copies of `G7Out`. G8-G12 enter as the hypotheses `hG5` and `hG3`.
- Review (one model review, read-only, no human review): it found no substantive defect. Its
  minor points were applied: the equalities were kept in `g12Spec_g14_of_linked`; `TateBridge35`
  now ties `β` to `G7Data`'s `β`; the words "false" were changed to "can fail"; the field of
  definition of `μ_σ` is corrected to `L`; the `FrobSquaresLink` docstring was changed. All of
  this was recompiled (log run5).
- Integration: `g14TraceCompat_of_link` takes G8's output in g0-mod-newform's `GalG8Out` form.
  g0-mod-galois' `g8` produces it from `G7Out` on `ρ = GlueDescent.rho Tm a β`. With
  `TateBridge35`, the `a`, `β` at 3 and 5 are `j_ℓ ∘ a`, `j_ℓ ∘ β`, which is exactly the
  hypothesis shape here.
