# c9-rhof: glue C9 for R16's representation `ρ_{f,ι}`

Task c9-rhof, 2026-11-12. Lean file: `scratch/c9-rhof/C9.lean` (≈600 lines). It imports the kernel
modules `ZInQKernel.HDecomp.ModCurves.Glue`, `ZInQKernel.HDecomp.I3Linalg.C2` and
`ZInQKernel.HDecomp.I3Linalg.RhoCont`. Results log: `scratch/c9-rhof/log.md`. Compiler output:
`scratch/c9-rhof/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

---

## §0. Main result

**Glue C9 is proved in Lean from leaves.** This covers the items of
`docs/research/leaf-modcurves.md` §5, row C9: semisimplicity and continuity of
`LeafModCurves.rhoF`, then Brauer–Nesbitt against R14 and against C8's `r₅`. VERIFIED:
`lake env lean scratch/c9-rhof/C9.lean` exits 0 with no errors, no warnings and no `sorry`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `rhoF_semisimple`,
`rhoF_continuous`, `c9`, `c9_R14`, `c9_r5` and `c10_via_c9`.

The theorems (namespace `C9Rhof`):

1. **`rhoF_semisimple`**: `ρ_{f,ι}` is semisimple (`IsSemisimpleRepresentation`). It uses
   **Faltings Satz 3** (`PkgI3.FaltingsSemisimple`) and **I3.M0** (`PkgI3.TateModuleFree`), which
   gives finite dimension of `V_ℓ`. Proof:
   - `ρ_{f,ι}` is an equivariant quotient of `V_ℓ(A) ⊗_{ℚ_ℓ} ℚ̄_ℓ`.
   - The quotient map `quotMap` is `e ⊗ v ↦ e·(φ ↦ φ(v))`, onto the dual of the
     `ι`-eigenfunctionals. It is equivariant (`quotMap_equivariant`) and surjective
     (`quotMap_surjective`).
   - The kernel's proved `GlueI3.isSemisimpleRepresentation_baseChange` (glue-ssbc) handles
     `V_ℓ ⊗ ℚ̄_ℓ`, and `GlueI3.isSemisimple_of_surjective` passes semisimplicity to the quotient.
2. **`rhoF_continuous`**: in every finite basis, `σ ↦ [ρ_{f,ι}(σ)]` is continuous. The topologies
   are Krull on `G_ℚ` and spectral norm on `ℚ̄_ℓ`. It uses only I3.M0. Proof:
   - Every matrix coefficient has the form `σ ↦ c(ρ_{f,ι}(σ)(quotMap x))`.
   - On pure tensors this is `e · L(ρ_ℓ(σ)v)`, with `L` a `ℚ_ℓ`-linear map out of
     finite-dimensional `V_ℓ`, so `L` is continuous for the module topology.
   - The kernel's `continuous_galRep_of_tateModuleFree` (glue-rho-cont) supplies continuity of
     `σ ↦ ρ_ℓ(σ)v`.
3. **`c9`** (the core statement). Hypotheses:
   - the leaves R16′, Faltings Satz 3, I3.M0, **T18** (`FrobeniusDense`) and **T19**
     (`GlueC10.BrauerNesbittChar0`);
   - a newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ`, a `J` with `IsJ1 N J`, and embeddings `ιC`, `ιL`;
   - a continuous, semisimple, finite-dimensional `r : G_ℚ → GL(W)` over `ℚ̄_ℓ` whose
     arithmetic-Frobenius traces outside a finite `S` are `ιL(α)`, `ιC(α) = a_p(f)`.

   Conclusions, for R16's `A_f`, `π`, `θ` and `ι = embOf ιC ιL = ιL ∘ ιC⁻¹`:
   - `ρ_{f,ι}` is 2-dimensional, semisimple and continuous;
   - **`r ≅ ρ_{f,ι}`** as `ℚ̄_ℓ[G_ℚ]`-modules;
   - `tr r(g) = tr ρ_{f,ι}(g)` for **every** `g ∈ G_ℚ`;
   - `tr ρ_{f,ι}(g) = ι(a_p(f))` at every `GlueC10.IsFrobAt g p` with `p ∤ Nℓ`.
4. **`c9_R14`**: R14's `ρ` (`EigenformRepExists`) for `f` is isomorphic to `ρ_{f,ι}`, with equal
   traces on all of `G_ℚ`. This is the Brauer–Nesbitt comparison "against R14".
5. **`c9_r5`**: C8's `r₅`, with C8's output in the form that is actually available. Hypotheses:
   - `r` is a semisimple `GaloisRep ℓ 2` with `r.AttachedUpToTwist ψ ιC ιL g S`. This is Pan's
     trace form, for a normalized weight-2 eigenform `g` of level `M`.
   - The twisting character `ψ` is the Dirichlet character `ψD mod m` at arithmetic Frobenius
     outside `S` (C8 step 4).

   It uses **T24** (`EigenformTwist`) and **T25** (`NewformOfEigenform`). Conclusion: a newform `f`
   of weight 2 and level `N ∣ Mm²` such that for every `J₁(N)`:
   - **`r₅ ≅ ρ_{f,ι}`**;
   - equal traces everywhere (`h₅`);
   - the Frobenius clause (`hρ₅`).
6. **`c10_via_c9`**: `GlueC10.c10` instantiated with `ρ₅ := rhoF`. C9's trace identity is
   `c10`'s `h₅`, and its Frobenius clause is `hρ₅` for every `S ⊇` primes of `Nℓ`. This shows that
   the shapes match: C9's output plugs into the kernel's C10 with no adapter.

Also proved: the `GaloisRep` → `Representation` bridge (leaf-modcurves §5 C9(c)). It consists of
`toRep`, `toRep_continuous`, `trace_toRep` and `toRep_semisimple` (from `GaloisRep.IsSemisimple`,
via `semisimple_of_complements`). Also proved: **`isSemisimple_of_isIrreducible`**, which says a
`GaloisRep` irreducible in Burnside's form (`GaloisRep.IsIrreducible`, one of the hypotheses of
Pan's theorem on `r₅`) is semisimple. So the semisimplicity hypothesis of `c9_r5` follows from the
irreducibility of `r₅`.

## §1. Leaves used (all as hypotheses)

| Leaf | Lean | Where from |
| --- | --- | --- |
| R16 (Eichler–Shimura in `J₁(N)`) | `LeafModCurves.R16_EichlerShimuraJ1'` | kernel |
| Faltings 1983 Satz 3 | `PkgI3.FaltingsSemisimple` | kernel |
| I3.M0 (Mumford §18-19, `T_ℓ` free of rank `2g`) | `PkgI3.TateModuleFree` | kernel |
| T18 Chebotarev density | `C9Rhof.FrobeniusDense` | verbatim copy of `HSyn.FrobeniusDense` (Leaves.lean) |
| T19 Brauer–Nesbitt | `GlueC10.BrauerNesbittChar0` | kernel (= `PkgI6.BrauerNesbittChar0`) |
| R14 (Galois representations of eigenforms) | `PkgI4.EigenformRepExists` | verbatim copy (Leaves.lean §3) |
| T24 twisting | `PkgI4.EigenformTwist` | verbatim copy |
| T25 newform of an eigensystem (Li) | `PkgI4.NewformOfEigenform` | verbatim copy |
| C10 only: Chebotarev (finite form) | `GlueC10.ChebotarevExists` | kernel |

VERIFIED: each copied block is a substring of `scratch/h-decomposition/Leaves.lean`, and so is
the definition `GaloisRep.AttachedUpToTwist`.

## §2. Findings

1. **`c10` uses only the trace identity (`h₅`), never the isomorphism `r₅ ≅ ρ_{f,5}`.** `h₅`
   needs only T18 and the continuity of `r₅` and `ρ_{f,ι}`. T19 and the two semisimplicity
   inputs (Faltings for `ρ_{f,ι}`, and `r₅` semisimple) are needed only for the isomorphism
   itself. That is h-trust's C9 statement, but the kernel's assembly does not consume it.
   VERIFIED: `trace_eq_of_arithFrob` has no T19 or semisimplicity hypothesis, and `c9` derives the
   trace identity from it.
2. **The density leaf has to be T18 in `IsArithFrob` form.**
   - R14's `AttachedTo`, Pan's `AttachedUpToTwist` and C8's data all give traces at
     `PkgI4.IsArithFrob` (valuation subrings).
   - The kernel's `FrobDense` (proved from `ChebotarevExists`) is about `GlueC10.IsFrobAt` (primes
     of `ℤ̄`).
   - The kernel proves `IsArithFrob ⇒ IsFrobAt` (`isFrobAt_of_isArithFrob`), but not the converse,
     which needs `ℤ̄_𝔓` to be a valuation ring.

   So `c9` uses T18, which is already in the leaf list. An alternative is to prove
   `IsFrobAt ⇒ ∃ v, IsArithFrob` (Prüfer property of `ℤ̄`; medium glue). Then T18 could be dropped
   in favour of `ChebotarevExists`.
3. **Normalizations agree** (VERIFIED in the code):
   - `rhoF` is the double dual of the `ι`-eigenfunctionals with `σ ↦ (φ ↦ φ ∘ ρ_ℓ(σ))ᵀ`, so it is
     the `ι`-component of the covariant `V_ℓ(A_f) ⊗ ℚ̄_ℓ` (arithmetic Frobenius, Tate
     normalization).
   - R14's `AttachedTo` is in the same normalization, with `tr = a_p` at arithmetic Frobenius.
   - The matching is through `embOf_spec` (`ι(a) = ιL(α)` when `ιC(α) = a`).
4. **Lean pitfall** (VERIFIED). `set`/`generalize` on `embOf ℓ ιC ιL (coeffField f)` inside the
   proof of `c9` hits a `whnf` heartbeat timeout. The proof therefore goes through `c9_core`, which
   is stated for an arbitrary `emb : F →+* ℚ̄_ℓ` and an arbitrary `a : ℕ → F`.

## §3. What remains (not done here)

- **C8's two outputs, assumed by `c9_r5`.**
  - (a) `r₅` as a `GaloisRep 5 2` with `IsIrreducible`; `isSemisimple_of_isIrreducible` then
    gives the hypothesis `hr` of `c9_r5`. C2 gives `r₅` absolutely irreducible
    (`PkgI3.C2_absolutelyIrreducible'`, for the abelian variety's representation). Still to do:
    pass from C2's `r₅`, a subrepresentation of `V₅(A) ⊗ E`, to a `GaloisRep 5 2` (choose a
    basis; Burnside's theorem gives the `IsIrreducible` form). Small to medium glue.
  - (b) `hψ`: the twisting character is a Dirichlet character at Frobenius. C8 steps 3-4 are needed:
    the finiteness of `ψ` (`GlueAssembly.twist_finite`, proved) and Kronecker–Weber (T17)
    converting a finite-image `ψ` into a Dirichlet character, with `ψ(Frob_p) = ψD(p)`. That
    conversion (class field theory of `ℚ` at Frobenius) is open glue, medium.
- **The abelian-variety side of C10** (`hr₅`, `hr₃`: Mumford §19 Thm 4 / Néron–Serre–Tate) is
  untouched. It is G14's open part.
- **Non-vacuity of the `J` quantifier** needs `X1ModelExists` and `JacobianExists`
  (leaf-modcurves). `c9_r5` quantifies over every `J` with `IsJ1 N J`.
- **Integration** (after the announcement):
  - Copy §1-§6 and §8-§9 of `C9.lean` into a kernel module importing `ModCurves.Glue`,
    `I3Linalg.C2` and `I3Linalg.RhoCont`.
  - Use `HSyn.FrobeniusDense` and the `PkgI4` leaves of `Leaves.lean` instead of the copies in §4
    and §7.
  - The headline is `C9Rhof.c9_r5` followed by `c10_via_c9`.
