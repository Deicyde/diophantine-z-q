# g0-mod-newform: glue steps G13-G16 of `ModularConstituent`

Task g0-mod-newform, 2026-11-13. Lean: `scratch/g0-mod-newform/NewForm.lean`, assembled by
`scratch/g0-mod-newform/build.sh` from kernel imports, verbatim copies of
`scratch/c9-rhof/C9.lean` and `scratch/e1-sub/E1Sub.lean`, and the new section
`scratch/g0-mod-newform/part_new.lean` (namespace `G0ModNewform`, 991 lines). Log:
`scratch/g0-mod-newform/log.md`. Compiler output: `scratch/g0-mod-newform/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**G13-G16 are proved in Lean.** The hypotheses are the output of G8-G12, ten literature leaves
already stated in the kernel, three glue Props already named in the kernel, and two new, smaller
named Props on the abelian-variety side. VERIFIED: `lake env lean scratch/g0-mod-newform/NewForm.lean`
exits 0, with no errors and no `sorry`. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for each of the 19 declarations printed: `equivariant_of_asModule`,
`condAt_eq_of_intertwine`, `newform_of_pan`, `commonConstituent_of_attached`, `g13`, `iso_R14`,
`g14`, `g15`, `g16`, `g13_g16`, `g16Out_with_J1`, `localBound_of_ram`, `g13_g16_ram`,
`modularConstituent_tail`, `isConstituentOf_of_GalG8Out`, `g12Spec_of_galois`,
`localUnram_of_unramifiedAt`, `g15Ram_of_G` and `modularConstituent_tail_G`. A run takes about
30 s.

The headline is `modularConstituent_tail_G`. Its hypothesis `G15RamG` is `G15Ram` with clause (iii)
in G11's global form, which g0-mod-galois proves:

```
theorem G0ModNewform.modularConstituent_tail_G (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L)
```

`modularConstituent_tail` has the same conclusion, with `G15Ram` (the local form of clause (iii))
as the hypothesis.

Its conclusion is the last four conjuncts of `ModularConstituent`
(`scratch/g0-split/part_split.lean`): `0 < N`, `IsJ1 N J`, `N ≤ QM²`, and E1's hypothesis
`CommonConstituent`. The other conjuncts (the field `L'`, the embedding, the model `A` with
`A_ℚ̄ ≅ P.A` and `[L':ℚ] ≤ QM`) belong to G2-G7, the range of g0-mod-field.

### The steps

| step | Lean | proved from | conclusion |
|---|---|---|---|
| G13 | `g13` | T24 `EigenformTwist`, T25 `NewformOfEigenform`, R16 `R16_EichlerShimuraJ1'`, R9a `FaltingsSemisimple`, R9b `FaltingsTate`, I3.M0 `TateModuleFree`, T18 `FrobeniusDense`, T19 `BrauerNesbittChar0`; input `G12Spec D` | `G13Spec D N χ f`: a newform `f` of weight 2 and level `N > 0`; `r₅`, `r₃` semisimple; `r₅` attached to `f` outside a finite set; for **every** `J₁(N)` `J`, `CommonConstituent A (J_{L'})` |
| G14 | `g14` | R14 `EigenformRepExists`, T18, T19; input `G13Spec`, **`G14TraceCompat D`** (open) | `G14Spec D N f`: `r₅` and `r₃` are each equivariantly isomorphic to R14's semisimple `ρ` attached to `f` (`AttachedTo`: unramified outside `Nℓ`, trace `a_p`) |
| G15 | `g15`, `g15LocalBounds_of_ram`, `g15Ram_of_G` | R17 `CarayolR17'`; glue `SwanIndependent`, `SwanIntegral` (L8), `AdaptedExists`; input `G13Spec`, `G14Spec`, **`G15RamG D u`** (open clauses (i)-(ii); clause (iii) is G11's output) | `G15Out N u`: `v_p(N) ≤ E₀` (`p ≤ D`), `≤ 2` (`p > D`), `p ∣ N ⇒ p ∈ S_mul ∨ p ∣ M` |
| G16 | `g16` | `GlueConductor.level_le` (kernel), `Mult.le_heightD_of_mem_S_mul`, `GlueAssembly.one_le_heightD_real` | `N ≤ Q_D · M_{S_mul}(u)²` |

### Proved glue (new here)

- `equivariant_of_asModule`: an isomorphism of `k[G]`-modules `ρ.asModule ≅ σ.asModule` is an
  equivariant `k`-linear equivalence. This is the adapter between Brauer–Nesbitt's output
  (`GlueC10.BrauerNesbittChar0`) and E1's equivariant form.
- §2 `invariants_eq_map`, `codimInv_eq`, `isAdapted_of_intertwine`, `condAt_eq_of_intertwine`,
  `restrictLocal_intertwine`: the conductor exponent at an adapted level, and adaptedness, are
  invariant under isomorphism of Galois representations. G15 needs this to pass from `r_ℓ`, where
  Glazer's local bounds live, to R14's `ρ`, where Carayol's theorem applies.
- `newform_of_pan`: the twist bookkeeping of `C9Rhof.c9_r5`, written for a hypothesis `PanOutput`.
- `jSide`, `commonConstituent_of_attached`: E1 on the actual `A`. **One** application of R16 gives
  `A_f` for both C9's Brauer–Nesbitt isomorphism `r₅ ≅ ρ_{f,5}` (`C9Rhof.c9_core`) and E1's
  embedding `ρ_{f,5}|G_{L'} ⊆ V₅(J_{L'}) ⊗ ℚ̄₅`. The copied `c9` and `E1Sub.rhoF_subrep_JL` each
  obtain their own `A_f`, so they cannot be composed directly; finding F4 of the log.
- `iso_R14`: Brauer–Nesbitt against R14, from attachment outside a finite set.
- `restrictLocal_continuous`: `r|G_{ℚ_p}` is continuous, because Mathlib's
  `Field.absoluteGaloisGroup.map` is a continuous homomorphism (`→ₜ*`). No new hypothesis.
- §10 `localUnram_of_unramifiedAt`: if `r` is unramified at `p` in PkgI4's global sense (the
  inertia groups of `G_ℚ` at places above `p`, through Mathlib's `ValuationSubring.inertiaSubgroup`),
  then `r|G_{ℚ_p}` is trivial on the local inertia set `LadicCond.inertiaSet`. The proof builds the
  place `vj = {x : ‖j x‖ ≤ 1}` from the embedding `j : ℚ̄ → ℚ̄_p` underlying `PkgI4.decomp p`
  (`decomp_spec`). It then shows that `decomp p σ` stabilizes `vj` (the spectral norm is
  Galois-invariant, `spectralNorm_eq_of_equiv`) and acts trivially on its residue field. This
  identifies decomposition groups with `G_{ℚ_p}`, which §2 had expected to remain open.
- `localBound_of_ram` and `two_one_add_U0_le`: Glazer's arithmetic `a ≤ 2(1 + U₀) ≤ E₀` with
  `U₀ = 4(DG₀)²` and `E₀ = 10(DG₀)²` (N5 L826-850), from `LadicCond.condAt_le_of_upper`. Also
  `a ≤ 2` when wild inertia is trivial, and `a = 0` when the representation is unramified.

## 2. The two open Props (smaller than the step they come from)

**Finding (VERIFIED as a logical point).** A constituent `U ⊆ V_ℓ(A) ⊗ ℚ̄_ℓ` determines `r_ℓ` only
on `G_{L'}`. Twisting `r_ℓ` by a character of `Gal(L'/ℚ)` gives another constituent with the same
restriction. So "the `r₃`, `r₅` of any two constituents are compatible" and "`r_ℓ` has Glazer's
local ramification" are false when stated over all constituents. Both are statements about the
`r_ℓ` that G8 **constructs** from G7's descent data (`T_σ = a_σ μ_σ ∘ σ`, `β`). The open Props are
therefore hypotheses on the same data `D : ModData L A` as `G12Spec D`, and must be proved together
with that construction.

1. **`G14TraceCompat D`** (G14's AV side, N5 L776-795). There is a finite `S` such that at every
   arithmetic Frobenius `τ` above `p ∉ S` and for every `c ∈ ℚ̄`: if `tr r₅(τ) = ι₅(c)`, then
   `tr r₃(τ) = ι₃(c)`. Glazer's proof: the relative Frobenius of `Ā_v` composed with `μ̄_σ` is an
   endomorphism whose characteristic polynomial on `V_ℓ` does not depend on `ℓ` (T7, with T3 and
   T4). Half its trace times `β(σ)⁻¹a_σ` is one element of `C` whose images are the traces of
   every `r_ℓ`. The implication form avoids needing Frobenius elements to exist at every `p`. It
   is equivalent to "the traces are the images of one algebraic number" whenever such a Frobenius
   exists, because `ι₅` is injective. Truth: SPECULATIVE but direct from N5. The embeddings
   `ι₅`, `ι₃` are part of `D`, so the producer chooses `ι₃` compatibly ("transporting it through
   an embedding at three", N5).
2. **`G15RamG D u`** / **`G15Ram D u`** (G15's local analysis, N5 L819-852). `LocalRam` holds for `r₅` at every `p ≠ 5`
   and for `r₃` at `p = 5`:
   - (i) if `p ≤ D`, every absolute upper ramification group `G_{ℚ_p}^t` with `t > U₀` acts
     trivially (`LadicCond.upperAbs`);
   - (ii) if `p > D`, wild inertia acts trivially;
   - (iii) if `p ∉ S_mul` and `p ∤ M_{S_mul}(u)`, inertia acts trivially (in `G15RamG`, `LocalRamG`:
     `r.UnramifiedAt p`, i.e. G11's output).

   This is exactly what N5 proves before it does the conductor arithmetic: "all absolute
   ramification groups above `U₀` act trivially", "the same argument kills the wild part of `β`",
   "outside `T` it is zero". The arithmetic itself is proved here. Clause (iii) of `G15RamG` is
   exactly G11's output (`G0Galois.G11Out T r`, `∀ p ∉ T, p ≠ ℓ → r.UnramifiedAt p`, proved by
   g0-mod-galois as `g11`) for `T ⊇ S_mul ∪ supp M`. The move from global to local inertia is
   proved (`localUnram_of_unramifiedAt`). So the only open content of `G15RamG` is (i)-(ii).
   Proved cores of (i)-(ii) that are not on the actual `A`: D1 `GlueConductor.D1_genuine`,
   D2 `PkgI2.D2_fixed_of_raynaud`, D3 `GlueConductor.fourth_pow_mem`.

The intermediate form `G15LocalBounds D u` (an adapted level with the conductor bounds) is also
stated. `g13_g16` takes it directly, and `g13_g16_ram` derives it from `G15Ram`.

**Kernel glue Props used (already named, unproved):** `LadicCond.SwanIndependent` (Serre–Tate §2,
Herbrand), `LadicCond.SwanIntegral` (L8: `Sw = ∫ codim V^{G^u}`), `LadicCond.AdaptedExists`
(`ρ(P_p)` finite for `ℓ ≠ p`). `X1ModelExists` (glue target, leaf-modcurves) is used only to
produce a `J₁(N)`.

**Leaves used** (all already stated in the kernel or in `Leaves.lean`; bundled as
`NewformLeaves`): T24, T25, R14, R16, R17 (`CarayolR17'`, faithful per the locator audit), R9a,
R9b, I3.M0, T18, T19; and T33 (`JacobianExists ℚ`) for the `J₁(N)`.

## 3. How this range is fed, and how it feeds `ModularConstituent`

### Input: the output of G8-G12 (task g0-mod-galois)

`G12Spec D` for `D : ModData L A` (the data `i : ℚ̄ → L̄'`, `ιC`, `ι₅`, `ι₃`, `r₅`, `r₃`) asks for:

- (a) `r₅.IsIrreducible`, `r₃.IsIrreducible`;
- (b) `IsConstituentOf 5 A i r₅` and `IsConstituentOf 3 A i r₃`: a nonzero
  `U ⊆ V_ℓ(A) ⊗ ℚ̄_ℓ` with `U ≃ ℚ̄_ℓ²` carrying `τ ∈ G_{L'}` to `r(σ)` whenever `i ∘ σ = τ ∘ i`;
- (c) `PanOutput ιC ι₅ r₅`: `r₅.AttachedUpToTwist ψ ιC ι₅ g S` for a normalized weight-2 eigenform
  `g` of level `M`, with `ψ` equal at Frobenius to a Dirichlet character `ψD mod m`.

g0-mod-galois's draft (origin/wip/g0-mod-galois at ad7f14c2, `scratch/g0-mod-galois/part_galois.lean`)
supplies these. Its definitions `resQ`, `Vb`, `tate`, `Intertwines`, `G8Out` and `G12Out` are
copied verbatim into §9 of `part_new.lean`, over the kernel's objects, renamed `GalG8Out` and
`GalG12Out` there. The bridge is **proved** (VERIFIED, standard axioms):

- `g12Spec_of_galois (hDF : DirichletOfFinite) A ρ5 ρ3 r5 r3 (h5 : GalG8Out A 5 ρ5 r5)
  (h3 : GalG8Out A 3 ρ3 r3) (h12 : GalG12Out r5) ι3 : ∃ D, D.r5 = r5 ∧ D.r3 = r3 ∧ D.ι3 = ι3 ∧
  G12Spec D`.
- (a) Irreducibility: the span of `r(G_{L'})` is contained in the span of `r(G_ℚ)`.
- (b) `isConstituentOf_of_GalG8Out`: `U = ker(pr₂ ∘ e)`, where `e` is their
  `ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ² × ℚ̄_ℓ²`. `resQ_spec` shows that the embedding `IsAlgClosed.lift` underlying
  Mathlib's `Field.absoluteGaloisGroup.map` satisfies `i ∘ resQ K τ = τ ∘ i`
  (`AlgEquiv.restrictNormal_commutes`), so every `σ` with `i ∘ σ = τ ∘ i` is `resQ K τ`.
- (c) `panOutput_of_G12Out`: their `ψ` has finite image. One small glue Prop is named,
  **`DirichletOfFinite`**: a finite-image continuous `ψ : G_ℚ → ℚ̄_ℓ^×` agrees, at arithmetic
  Frobenius outside a finite set, with a Dirichlet character `ψD mod m` read through `ιC`, `ιL`.
  It is true: by Kronecker–Weber (T17) `ψ` factors through `Gal(ℚ(ζ_m)/ℚ) ≅ (ℤ/m)^×`, and its
  values are roots of unity, which lie in `ιL(ℚ̄)`. c9-rhof §3(b) noted the same gap.
- The draft may still change. If it does, the bridge has to be re-checked.
- `G14TraceCompat D` and clauses (i)-(ii) of `G15RamG D u` are to be proved with their construction of `r_ℓ` in
  `g8` (from `G7Out`'s `Tm`, `a`, `β`), as §2 explains.

### Output: into `ModularConstituent`

`ModularConstituent`'s conclusion is `∃ L emb A N J, (A_ℚ̄ ≅ P.A) ∧ 0 < N ∧ IsJ1 N J ∧ N ≤ QM² ∧
[L:ℚ] ≤ QM ∧ CommonConstituent (abVarEquiv A) (abVarEquiv ((abVarEquiv.symm J).baseChange L))`.
The proof of `ModularConstituent` composes:

1. G2-G7 (g0-mod-field) give `L`, `emb`, `A` (a `DefFaltings.AbVar L`), the isomorphism and
   `[L:ℚ] ≤ QM`.
2. G8-G12 (g0-mod-galois), applied to `A' := abVarEquiv L A` (a `PkgI3.AbVar L`), give `D` with
   `G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u` (clause (iii) from their `g11`).
3. `modularConstituent_tail_G lv hJac hX hSw hL8 hAd A' u ⟨D, …⟩` gives `N`, `J`, `0 < N`,
   `IsJ1 N J`, `N ≤ QM²` and `CommonConstituent A' (J.baseChange L)`.
4. Transport the last conjunct: `abVarEquiv L ((abVarEquiv ℚ).symm J |>.baseChange L) =
   J.baseChange L`. This needs `LeafAdopt.abVarEquiv` to commute with `baseChange`. It is a
   definitional check for the integrator: `abVarEquiv` is in `Leaves.lean`, not in the kernel, and
   was not checked here.

**Object layers.** My file is over the kernel (`ZInQKernel/HDecomp`: `PkgI3`, `PkgI4`,
`LeafModCurves`, `LadicCond`, `GlueC10`). `Split.lean` and g0-mod-galois are over the copies
inside `Leaves.lean`. The definitions have the same text (c9-rhof VERIFIED the leaves it copied
as substrings of `Leaves.lean`), but the two environments cannot be mixed in one file. The
integrator either moves `part_new.lean` onto `Leaves.lean`'s copies (the names are the same; the
C9 and E1Sub copies would come along) or moves `Split.lean` onto the kernel.

## 4. What compiles, what remains

- Compiles (VERIFIED): `NewForm.lean`, 2505 lines (copies plus `part_new.lean`), exit 0, no
  `sorry`, standard axioms.
- Remains:
  - the two AV-side Props `G14TraceCompat` and clauses (i)-(ii) of `G15RamG`, on G8's construction;
  - `DirichletOfFinite` (from T17);
  - the kernel glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`, `X1ModelExists`;
  - the object-layer transport of §3.

  None of these is a new literature leaf.
- No new leaf was introduced, and no leaf is used in a form stronger than its kernel statement.
