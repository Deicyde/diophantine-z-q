# e1-sub: E1 for R16, `ρ_{f,ι}` as a subrepresentation of `V_ℓ(J₁(N)_{L'}) ⊗ ℚ̄_ℓ`

Task e1-sub, 2026-11-12. Lean file: `scratch/e1-sub/E1Sub.lean` (about 890 lines). It imports only kernel
modules: `ZInQKernel.HDecomp.ModCurves.Glue`, `ZInQKernel.HDecomp.I3Linalg.C2` and
`ZInQKernel.HDecomp.I3Linalg.TateBC`. Results log: `scratch/e1-sub/log.md`.

Markers: **VERIFIED** = compiled, computed or read here. **STANDARD** = published, with a
reference. **SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (this
host has no network).

---

## §0. Main result

**The E1 glue for R16 is proved in Lean** (VERIFIED: `lake env lean scratch/e1-sub/E1Sub.lean`
exits 0 with no errors and no `sorry`). For each of the 10 main declarations listed below,
`#print axioms` gives `[propext, Classical.choice, Quot.sound]`. The only hypotheses are R16 and
the I3 leaves that are already in the kernel. No new leaf and no new glue target is introduced.

1. **`VSurjOfSurjective` is proved.** This was the glue target of leaf-modcurves.
   - `E1Sub.vSurjOfSurjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree) :
     LeafModCurves.VSurjOfSurjective`.
   - It is the `K = ℚ` case of `homVK_surjective`, which holds over any number field `K`.
   - The proof does not use Poincaré reducibility (§1).
2. **`ρ_{f,ι}` is a sub, not only a quotient, of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ`.**
   - `E1Sub.rhoF_subrep_J` works from R16 + `FaltingsSemisimple` + `FaltingsTate` +
     `TateModuleFree`.
   - It gives a subrepresentation `U ⊆ V_ℓ(J) ⊗ ℚ̄_ℓ` of `G_ℚ` and an equivariant isomorphism
     `U ≃ (eigenFun)^∨` onto R16's `rhoF ℓ A_f θ ι`. That representation is 2-dimensional, with
     Frobenius traces `ι(a_p(f))`.
   - This removes `g13_constituent`'s hypothesis `VSurjOfSurjective` and turns its quotient into a
     sub.
   - It also proves that `rhoF` is semisimple (`rhoF_semisimple_of_surj`): it is an equivariant
     quotient of the semisimple `V_ℓ(J) ⊗ ℚ̄_ℓ`. leaf-modcurves §5 listed this as one of C9's open
     inputs.
3. **`V_ℓ` under base change.**
   - Take an abelian variety `J/K`, a field `L ⊇ K` and a `K`-embedding `i : K̄ → L̄`.
   - `bcV ℓ J i : V_ℓ(J) → V_ℓ(J_L)` is injective (`bcV_injective`). After `⊗ E` it stays
     injective for every field `E ⊇ ℚ_ℓ` (`bcVE_injective`).
   - It intertwines `σ ∈ G_K` with `τ ∈ G_L` whenever `i ∘ σ = τ ∘ i` (`bcV_galRep`,
     `bcVE_equivariant`).
   - Every `τ` has exactly one such `σ`. This defines `res i : G_L →* G_K` (`exists_res`, `res`,
     `res_spec`).
   - Bijectivity (`bcT_bijective`) follows from `TateModuleFree` and the extra hypothesis
     `dim J_L = dim J`. E1 does not need it.
4. **E1 for R16** (`E1Sub.rhoF_subrep_JL`, `E1Sub.rhoFL_subrep_JL`). For a newform `f` of level
   `N`, any `J` with `IsJ1 N J`, any field `L` of characteristic 0 and any `i : ℚ̄ → L̄`, there
   are Shimura's `A_f`, `π : J ↠ A_f` and `θ : K_f → End⁰(A_f)` with the following property.
   For every prime `ℓ` and every `ι : K_f → ℚ̄_ℓ`, `ρ_{f,ι}|_{G_L} := rhoF ∘ res i`
   (`rhoFL`) is `G_L`-equivariantly isomorphic to a subrepresentation `U'` of
   `V_ℓ(J_L) ⊗ ℚ̄_ℓ`. This is the `J`-side input `U'` of the kernel's
   `PkgI3.E1_exists_hom_ne_zero'`.
5. **E1 assembled** (`E1Sub.E1_R16`, adding the leaf `PoincareReducibility`). Let `L` be a number
   field, `A'/L` an abelian variety, and `U` a nonzero subrepresentation of `V_ℓ(A') ⊗ ℚ̄_ℓ` with
   a `G_L`-equivariant isomorphism `U ≃ ρ_{f,ι}|_{G_L}`. Then:
   - there is a nonzero `φ : A' → J_L` over `L`;
   - if `End⁰(A')` is a division algebra (`EndDivision A'`), there are `Z/L` and `g : Z → J_L`
     with `(φ, g) : A' × Z → J_L` an isogeny (`IsIsogenyMor`). This is N5 L861-867.

**What E1 still needs from outside this task** (§4):
- the isomorphism `U ≃ ρ_{f,ι}|_{G_L}` on the `A'` side, which is C9's output;
- `EndDivision A'` (absolute simplicity of the QM surface; h-decomposition G17).

---

## §1. `VSurjOfSurjective` (proved; §1 of the file)

```lean
theorem homVK_surjective (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    [NumberField K] (J A : AbVar K) (π : Hom J A) (hπ : Surjective π.hom.left) :
    Function.Surjective (homVK ℓ π)
```

Proof (VERIFIED, compiled):
1. `R := im V_ℓ(π)` is `G_K`-stable. Faltings' semisimplicity (`hS`) gives an invariant complement
   `R'`. The projection `p` onto `R'` along `R` is equivariant (`GlueI3.projection_comm`) and
   satisfies `p ∘ V_ℓ(π) = 0`.
2. Clear denominators exactly as the kernel's `exists_hom_ne_zero_of_equivariant` does: `T_ℓ(A)`
   is finitely presented and free (`hT`), so `s · p` is induced by an equivariant
   `h : T_ℓ A → T_ℓ A` with `s ≠ 0`.
3. Faltings (`hF`, surjectivity part) gives `h = tateHomZl z` with `z ∈ ℤ_ℓ ⊗ End(A)`. Then
   `h ∘ T_ℓ(π) = tateHomZl_{J,A}((precomp π ⊗ ℤ_ℓ) z)` (`tateHomZl_precomp`), and this is `0`.
4. Faltings (injectivity part) on `Hom(J, A)` gives `(precomp π ⊗ ℤ_ℓ) z = 0`.
5. `precomp π : Hom(A, A) → Hom(J, A)` is injective (`precomp_injective`, VERIFIED):
   - `A.X.left` is reduced, by Mathlib's
     `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` (an abelian variety is
     geometrically integral and smooth, hence flat, over `Spec K`).
   - `A` is separated over `Spec K` (it is proper).
   - `π` surjective implies `π` dominant.
   - Mathlib's `ext_of_isDominant_of_isSeparated` then applies.
6. `ℤ_ℓ` is flat over `ℤ` (Mathlib instance: torsion-free over a Dedekind domain), so
   `precomp π ⊗ ℤ_ℓ` is injective. Hence `z = 0`, `h = 0`, `p = 0`, `R' = 0` and `R = V_ℓ(A)`.

The leaf-modcurves docstring for this target suggested "T8 plus isogenies are isomorphisms on
`V_ℓ`". That route would need the isogeny theory of `AbVar`, which the kernel does not have.
The route above uses only leaves already in the kernel.

## §2. Sub instead of quotient (§2-§3 of the file)

- `exists_subrep_equiv_of_surjective`: a surjective equivariant `q : V → W` out of a semisimple
  representation restricts to an equivariant isomorphism from an invariant complement of `ker q`
  onto `W`.
- `evalEigE : V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ → (eigenFun)^∨` sends `e ⊗ v ↦ (φ ↦ e·φ(v))`.
  - It is surjective (`evalEigE_surjective`, needs only `dim eigenFun < ∞`): a functional on
    `(eigenFun)^∨` that vanishes on the image is evaluation at some `φ ∈ eigenFun` that kills
    every `v`, so `φ = 0`.
  - It intertwines `repBaseChange (A.galRep)` with `rhoF` (`evalEigE_equivariant`).
- `rhoF_subrep_J` applies this to `q = evalEigE ∘ (V_ℓ(π) ⊗ ℚ̄_ℓ)`.
  - Surjectivity comes from §1 and `baseChange_surjective`.
  - Semisimplicity of `V_ℓ(J) ⊗ ℚ̄_ℓ` comes from `hS` and `GlueI3.semisimpleBaseChange` (proved
    in the kernel).
- **Convention.** `rhoF` acts on `(eigenFun)^∨`, the `ι`-component of `V_ℓ(A_f) ⊗ ℚ̄_ℓ` itself
  (leaf-modcurves §3), not on its dual. So `U ≅ ρ_{f,ι}` is a genuine constituent of the covariant
  `V_ℓ(J) ⊗ ℚ̄_ℓ`, with arithmetic Frobenius having trace `ι(a_p)`. `rhoF_subrep_J` records the
  trace clause together with the subrepresentation.

## §3. `V_ℓ` under base change (§4 of the file)

The map of points `bcPhi J i : J(K̄) →* J_L(L̄)` is the composite of two maps.
- `precompPt J i : J(K̄) → J(L̄)`, `P ↦ Spec(i) ≫ P`.
  - It is injective (`precompPt_injective`): `Spec K̄` is reduced, `Spec(i)` is dominant
    (one-point spaces), and Mathlib's `ext_of_isDominant_of_isSeparated` applies.
- `bcPt : J(L̄) (as K-points) → J_L(L̄)`, `Q ↦ u ≫ (Over.pullback f).map Q`. Here
  `u : Spec L̄ → Spec L̄ ×_K Spec L` is the graph of the structure maps (`ptUnit`).
  - It is a monoid homomorphism because `J_L`'s group law is the one transported by the monoidal
    functor `Over.pullback` (`Functor.grpObjObj`), and Mathlib's `Functor.map_mul` applies.
  - It is injective because `pullback.fst` recovers `Q` (`bcPt_fst`).

Equivariance (`bcPhi_galAct`) for `i ∘ σ = τ ∘ i` follows from two identities:
- `Spec(i) ≫ Spec(σ) = Spec(τ) ≫ Spec(i)`;
- `Spec(τ) ≫ u = u ≫ (Over.pullback f).map(Spec τ)`, checked on both pullback projections (`τ` is
  `L`-linear).

The `T_ℓ`, `V_ℓ` and `⊗ E` levels:
- `T_ℓ`: `PkgI3.Tate.map` of an injective homomorphism (`Tate.map_injective`, kernel TateBC).
- `V_ℓ`: `ℚ_ℓ` is flat over `ℤ_ℓ` (`IsLocalization.flat`).
- `⊗ E`: any module over the field `ℚ_ℓ` is flat.

**No dimension input is needed for E1.** The image of a subrepresentation under an injective
equivariant map is a subrepresentation. Bijectivity (`bcT_bijective`, via the kernel's
`Tate.map_bijective`) needs in addition `dim J_L = dim J`. That is STANDARD (the dimension of a
scheme locally of finite type over a field is invariant under extension of the base field; Stacks
Tag 00P4 for algebras, UNVERIFIED tag). It is taken as an explicit hypothesis there.

## §4. What remains for E1

| Input | Status |
| --- | --- |
| `J₁(N)` exists | leaf-modcurves `exists_J1` (from `X1ModelExists`, `JacobianExists`; unchanged) |
| `ρ_{f,ι} ⊂ V_ℓ(J₁(N)_{L'}) ⊗ ℚ̄_ℓ` | **done** (`rhoFL_subrep_JL`) |
| `VSurjOfSurjective` | **done** (`vSurjOfSurjective`) |
| `V_ℓ` under base change | **done** (injective form; bijective form modulo `dim J_L = dim J`) |
| Faltings Hom ⇒ nonzero `A' → J_{L'}`; Poincaré ⇒ isogeny `A' × Z → J_{L'}` | **done** (`E1_R16`, through the kernel's `E1_exists_hom_ne_zero'` and the leaf `PoincareReducibility`) |
| `A'`-side constituent `U ≅ ρ_{f,ι}\|_{G_{L'}}` | **open: C9.** It needs Brauer–Nesbitt between `r_ℓ` (from `V_ℓ(A') ⊗ E ≅ r ⊕ r`, kernel C2) and `rhoFL`. That in turn needs semisimplicity of `rhoF`, which is now **proved** (`rhoF_semisimple_of_surj`, recorded in `rhoF_subrep_J` and `rhoF_subrep_JL`), and equality of characteristic polynomials on a dense set of Frobenius elements (Chebotarev and continuity, open) |
| `EndDivision A'` | open (G17: absolute simplicity of the QM surface, from A9/B6) |
| `2 ≤ g = dim J₁(N)` (E1's last sentence) | open: needs `dim (A' × Z) = dim J` for an isogeny, i.e. a dimension theory of `AbVar` isogenies (not in the kernel) |

**Integration.** `scratch/e1-sub/E1Sub.lean` is self-contained over the kernel and could become
`ZInQKernel/HDecomp/ModCurves/E1.lean`. Its namespace is `E1Sub`. It defines a new `res`, `bcV`
and `rhoFL`. After integration, `LeafModCurves.g13_constituent`'s hypothesis `hV` can be
discharged by `E1Sub.vSurjOfSurjective hS hF hT`.

## §5. Risks and checks

1. All results are conditional on the kernel leaves `FaltingsSemisimple`, `FaltingsTate`,
   `TateModuleFree` (and `PoincareReducibility` for `E1_R16`) and on R16. These are the same
   hypotheses as the kernel's `E1_exists_hom_ne_zero'`.
2. `Surjective π.hom.left` in `VSurjOfSurjective` is Mathlib's `AlgebraicGeometry.Surjective`
   (surjective on underlying spaces). That is what R16 provides.
3. One proof-engineering finding (VERIFIED): `set Ψ := … with …` in the final proof hit a `whnf`
   timeout at 200000 heartbeats; `let` works. No `maxHeartbeats` override is used anywhere in the
   file.
4. An independent read-only model review of the statements is in §6.

## §6. Independent review (2026-11-12, one read-only model review, no human review)

Verdict: **minor issues; the statements are sound and not vacuous; the only hypotheses are the
published leaves** (R16, `FaltingsSemisimple`, `FaltingsTate`, `TateModuleFree`, and
`PoincareReducibility` in `E1_R16`); no hypothesis is a disguised form of the conclusion. The
review confirmed:
- `homVK_surjective` and `vSurjOfSurjective` match `LeafModCurves.VSurjOfSurjective` exactly.
- The `G_L` action through compatible `σ` is correct and well defined: `σ` is unique because `i` is
  injective.
- There is no contragredient issue: `(eigenFun)^∨` with `rhoF` is the covariant `ι`-component
  (Diamond–Shurman 9.5.4 convention).
- The docstring claims about reducedness, dominance and flatness are correct.

Findings and how they were handled:
1. **Interface gap (applied).** `E1_R16` named `A_f, θ` existentially but did not export the
   dimension, semisimplicity and trace clauses. C9 could therefore not build `eA` by
   Brauer–Nesbitt for those same `A_f, θ`. Fix: `E1_R16` now exports `finrank = 2`,
   `IsSemisimpleRepresentation` and the trace clause before the `∀ A' U …` part. Recompiled,
   VERIFIED.
2. **Wording (applied).** The `rhoF_subrep_JL` docstring now says that `σ` is unique because `i` is
   injective.
3. **Outside this task (not editable here).** The `VSurjOfSurjective` docstring in
   `ZInQKernel/HDecomp/ModCurves/Glue.lean` still says "by Poincaré reducibility". It is now proved
   by the Faltings route (§1), so the text should be updated at integration.
4. **Noted.** C9 will have to transport its `G_ℚ`-action on `V_ℓ(A)` to `A' : AbVar L'` along the
   same `i`. That is a fair obligation on C9; it is not a gap in E1.
5. **Noted.** R16's determinant clause is not re-exported. Brauer–Nesbitt in characteristic 0
   needs only traces.
