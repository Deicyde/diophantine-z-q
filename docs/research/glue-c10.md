# glue-c10: the glue of step C10 (one compatible system at 3 and 5)

Status: research note (task glue-c10, 2026-11-11). Lean files: `scratch/glue-c10/C10.lean`
(Galois side) and `scratch/glue-c10/Trace.lean` (pkg-I3's definitions and ℓ-independence of
traces). Results log: `scratch/glue-c10/log.md`. No file under `ZInQKernel/`, `blueprint/`, or
another task's notes or scratch directory was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Theorem numbers given from memory are UNVERIFIED.

## Verdict

**All of C10's glue is proved in Lean, from the two leaves Chebotarev (pkg-I6's
`ChebotarevExists`) and Brauer–Nesbitt (pkg-I6's `BrauerNesbittChar0`).**

- The main theorem is `GlueC10.c10` (`scratch/glue-c10/C10.lean`): N5's identification of `r₃`
  with the modular representation `ρ_{f,ι₃}` from the 5-adic identification and the trace data.
- The lift of a finite-level Frobenius to `G_ℚ` is proved from Mathlib, so the density of
  Frobenius elements in `G_ℚ` is proved too (`frobDense`). glue-I6-rest left this lift open.
- The comparison of characteristic polynomials is proved from Mumford §19 Thm 4 (pkg-I3's
  `CharPolyIndepOfEll`): `PkgI3.trace_indep_of_ell` in `scratch/glue-c10/Trace.lean`.

No proof has a `sorry`. Each `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`. VERIFIED: `lake env lean` on `C10.lean`, `Lift.lean` and `Trace.lean`,
23:35-23:47 PST, no errors.

**What C10 still takes as hypotheses.** These are not glue. They are the trace identities
`hr₃, hr₅, hρ₃, hρ₅` of `c10` (with `h₅`, C9's `r₅ ≅ ρ_{f,ι₅}`), and the semisimplicity of `r₃`
and `ρ_{f,ι₃}`. They come from other steps and leaves:
- the Néron mapping property;
- Serre–Tate specialization;
- Eichler–Shimura;
- C2's absolute irreducibility, or Faltings Satz 3 with `semisimple_of_le`.

None of these is statable over Mathlib today (glue-assembly §2.2; §3 below).

**Faithful form (decision).** C10 is stated in `G_ℚ`, for continuous representations over any
Hausdorff topological field of characteristic 0. That is how N5 uses it (N5 L776-795):
- the hypotheses are about every arithmetic Frobenius element at every prime `p ∉ S`;
- the conclusion is an isomorphism of `k[G_ℚ]`-modules.

The finite-quotient form recommended by glue-I6-rest is proved too
(`iso_of_trace_eq_frob_finite`). It is not the statement of C10, for three reasons:
- `r₃` and `ρ_{f,ι₃}` do not factor through a finite quotient;
- passing to the reductions mod `ℓ^k` would need stable lattices;
- with the lift proved, the `G_ℚ` form costs nothing more.

## 1. Statements and status

All objects are Mathlib's:
- `GQ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`, which is definitionally
  `Field.absoluteGaloisGroup ℚ` (checked by `rfl`), with the Krull topology;
- `Zbar := integralClosure ℤ (AlgebraicClosure ℚ)`;
- `Representation`, `LinearMap.trace`, `IsArithFrobAt`, `Algebra.IsUnramifiedAt`.

**Definition `IsFrobAt g p`.** There is a prime `𝔓` of `\bar ℤ` with `𝔓 ∩ ℤ = (p)` and
`g x − x^p ∈ 𝔓` for all `x ∈ \bar ℤ`. This is N5's "lift σ of `x ↦ x^p` in the decomposition
group of `v`" (N5 L779-781).

| Lean name (file) | Statement | Hypotheses | Status |
| --- | --- | --- | --- |
| `PkgI3.trace_indep_of_ell` (Trace) | For `φ ∈ End(A)`, `A` an abelian variety over any field `k`: one `t ∈ ℤ` with `tr V_ℓ(φ) = t` for every prime `ℓ ≠ char k` (in any finite basis) | `CharPolyIndepOfEll` (Mumford §19 Thm 4) | **proved** (VERIFIED) |
| `PkgI3.trace_eq_trace_of_ell` (Trace) | the same, for two primes `ℓ₁, ℓ₂` at once | same | **proved** |
| `GlueC10.trace_half` (C10) | `tr ρ = 2·tr r` and `tr ρ = ι(s)` give `tr r = ι(s/2)` | — | **proved** |
| `GlueC10.iso_of_trace_eq_frob_finite` (C10) | `M/ℚ` finite Galois. Two semisimple finite-dimensional representations of `Gal(M/ℚ)` over a field of characteristic 0, with equal traces at every unramified Frobenius outside a finite `S`, are isomorphic | `ChebotarevExists`, `BrauerNesbittChar0` | **proved** |
| `GlueC10.eq_of_eq_on_frob` (C10) | Two continuous maps `G_ℚ → X` (`X` Hausdorff) that agree on `{g : IsFrobAt g p, p ∉ S}` are equal | `FrobDense S` | **proved** |
| `GlueC10.frobDense_of_chebotarev` (C10) | `FrobDense S`: for every finite `E ⊂ \bar ℚ` and every `g ∈ G_ℚ` there are a prime `p ∉ S` and an `h` with `IsFrobAt h p` and `h = g` on `E` | `ChebotarevExists`, `FrobLift` | **proved** |
| `GlueC10.iso_of_trace_eq_on_frob` (C10) | Two continuous semisimple finite-dimensional representations of `G_ℚ` over a Hausdorff topological field of characteristic 0, with equal traces at all Frobenius elements outside `S`, are isomorphic | `BrauerNesbittChar0`, `FrobDense S` | **proved** |
| `GlueC10.iso_three_of_five` (C10) | **C10 as N5 uses it.** Coefficient field `C`, embeddings `ι₅ : C → k₅`, `ι₃ : C → k₃`. Assume: `tr r_ℓ(g) = ι_ℓ(c_p)` and `tr ρ_ℓ(g) = ι_ℓ(a_p)` at every Frobenius `g` at `p ∉ S` (`ℓ = 3, 5`); `r₅` and `ρ₅` have equal traces there (C9). Then `r₃ ≅ ρ₃` (`r₃, ρ₃` continuous and semisimple) | `BrauerNesbittChar0`, `FrobDense S` | **proved** |
| `GlueC10.semisimple_of_le` (C10) | A `k[G]`-submodule of a semisimple representation is semisimple | — | **proved** (Mathlib instance) |
| `GlueC10.frobLift : FrobLift` (C10, Lift) | `E ⊂ \bar ℚ` finite Galois, `p` prime, `τ ∈ Gal(E/ℚ)` the arithmetic Frobenius at a prime `Q` of `𝓞_E` over `p`, unramified. Then some `h ∈ G_ℚ` with `IsFrobAt h p` restricts to `τ` (`AlgEquiv.restrictNormal h E = τ`) | none (Mathlib only) | **proved** |
| `GlueC10.restrictNormal_eq_of_frob` | a Frobenius `h` of `G_ℚ` at `𝔓 ∣ Q` restricts to the Frobenius at `Q` (`Q` unramified) | — | **proved** |
| `GlueC10.frobExistsFinite` | for `F` finite Galois, some `h ∈ G_ℚ` is Frobenius at `𝔓` on `\bar ℤ ∩ F` | — | **proved** |
| `GlueC10.frobExistsAt_of_finite` | every prime `𝔓` of `\bar ℤ` over `p` has an arithmetic Frobenius in `G_ℚ` | `FrobExistsFinite` | **proved** (compactness) |
| `GlueC10.frobDense` | `FrobDense S` for every finite `S` | `ChebotarevExists` | **proved** |
| **`GlueC10.c10`** | `iso_three_of_five` with `FrobDense` discharged | `ChebotarevExists`, `BrauerNesbittChar0` | **proved** |

Continuity of a representation is stated as continuity of its matrix coefficients in a
basis. It gives continuity of `g ↦ tr ρ(g)` (`continuous_trace`). The field `k` may be `ℚ_ℓ`, a
finite extension of `ℚ_ℓ`, or `\bar ℚ_ℓ` (`PadicAlgCl`): only `[TopologicalSpace k]`,
`[IsTopologicalRing k]` and `[T2Space k]` are used.

## 2. How the proofs go

1. **Characteristic polynomials.** `CharPolyIndepOfEll` gives a monic `P ∈ ℤ[X]` with
   `charpoly(V_ℓ φ) = P` in every basis. Then `tr = −nextCoeff(charpoly)` by
   `Matrix.trace_eq_neg_charpoly_nextCoeff`, and `nextCoeff` commutes with the injective map
   `ℤ → ℚ_ℓ` (`Polynomial.nextCoeff_map`). So `t = −nextCoeff P`. (VERIFIED)
2. **Frobenius classes to `G_ℚ`.** The set where two continuous functions differ is open. If it
   contains `g`, its translate by `g⁻¹` is a neighbourhood of `1`. So it contains `Gal(\bar ℚ/E)`
   for a finite `E` (`krullTopology_mem_nhds_one_iff`). `FrobDense` gives a Frobenius `h` with
   `g⁻¹h ∈ Gal(\bar ℚ/E)`, and `h` lies in the set, a contradiction. (VERIFIED)
3. **Density from Chebotarev.** Replace `E` by its normal closure `N`: finite and Galois, with
   instances `NumberField N` and `IsGalois ℚ N` built in place. Apply `ChebotarevExists` to `N` and
   `g|_N`. `FrobLift` (proved, §3) lifts the Frobenius obtained, and `restrictNormal_commutes` transfers
   `h|_N = g|_N` to `E`. (VERIFIED)
4. **Transport 5 → 3.** At a Frobenius `g` at `p ∉ S`, the hypotheses give
   `ι₅(c_p) = tr r₅(g) = tr ρ₅(g) = ι₅(a_p)`. A ring map out of a field is injective, so
   `c_p = a_p`. Then `tr r₃(g) = ι₃(c_p) = ι₃(a_p) = tr ρ₃(g)`. Items 2 and 1 of §1, with
   Brauer–Nesbitt, give `r₃ ≅ ρ₃`. The trace hypotheses are about every Frobenius element, so
   one `g` serves both primes and no comparison between different lifts is needed. (VERIFIED)
5. **Non-vacuity.** `IsFrobAt g p` is satisfiable for every prime `p`: lying-over gives `𝔓`, and
   `frobExistsAt_of_finite frobExistsFinite` gives `g`. `FrobDense S` is proved. So the trace
   hypotheses of `c10` constrain a dense set of genuine elements of `G_ℚ`. (VERIFIED)

## 3. The proof of `FrobLift`, and what remains

1. **`FrobLift` is proved.** It was open in glue-I6-rest. The proof (`C10.lean`; also standalone
   in `Lift.lean`) has three steps:
   - (a) Lying-over for `𝓞_E → \bar ℤ`: `Ideal.exists_ideal_over_prime_of_isIntegral`, with the
     algebra structure from `toZbar`.
   - (b) An arithmetic Frobenius exists in `G_ℚ` at every `𝔓`, by compactness. Mathlib's
     instance `CompactSpace Gal(K/k)` covers `IsGalois ℚ \bar ℚ`. The sets
     `FrobOn p 𝔓 F = {h : h x ≡ x^p mod 𝔓 for x ∈ \bar ℤ ∩ F}` are:
     - closed: each is a union of cosets of `Gal(\bar ℚ/F)`, which is open by
       `fixingSubgroup_isOpen`;
     - directed, via `F₁ ⊔ F₂`;
     - nonempty: use the normal closure of `F`, `IsArithFrobAt.exists_of_isInvariant` for
       `Gal(N/ℚ)` acting on `𝓞_N` through `galRestrict` (with
       `Algebra.isInvariant_of_isGalois`), and `liftNormal`.

     Every `x ∈ \bar ℤ` lies in `ℚ(x)`.
   - (c) Uniqueness at an unramified prime (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`)
     identifies `h|_E` with `τ` on `𝓞_E`, hence on `E` (`IsFractionRing.div_surjective`).

2. **Not glue of this task; these are leaves or other steps**:
   - the Néron mapping property (reduction of `μ_σ`);
   - Serre–Tate specialization `V_ℓ(A) ≅ V_ℓ(Ā_v)`;
   - Eichler–Shimura for `ρ_{f,ι}`.

   These supply the trace hypotheses `hr₃, hr₅, hρ₃, hρ₅` of `c10` / `iso_three_of_five`
   (glue-assembly §2.2, steps 1-2, and its leaf table). None is statable in Mathlib today:
   Mathlib has no Néron models and no modular forms with Galois representations (glue-assembly,
   prereq-survey).
3. **Linking `trace_indep_of_ell` to `c_p`.** `c_p = ½·β(σ)⁻¹a_σ·tr α_σ` with
   `α_σ ∈ End⁰(Ā_v)`. That needs the specialization of item 2 and `End⁰` scalars. Only the pure
   ℓ-independence is proved here.
4. **Integration.**
   - Over `PadicAlgCl ℓ`, the isomorphism `r₃ ≅ ρ₃` is a `k[G_ℚ]`-module isomorphism of
     `asModule`s. This is the output form of `BrauerNesbittChar0`.
   - `C10.lean` and `Trace.lean` are independent. Only `Trace.lean` needs pkg-I3's definitions.
   - pkg-I3's `galRep` is typed over `Field.absoluteGaloisGroup ℚ`, which is `GQ` by `rfl`.

## 4. Files

| File | Imports | Content | `sorry` |
| --- | --- | --- | --- |
| `scratch/glue-c10/C10.lean` | Mathlib | `ChebotarevExists`, `BrauerNesbittChar0` (copied); `IsUnramFrob`, `GQ`, `Zbar`, `IsFrobAt`, `FrobDense`, `FrobLift` (proved, `Lift.lean` merged in), `c10`; the theorems of §1 | none |
| `scratch/glue-c10/Lift.lean` | Mathlib | the proof of `FrobLift` alone (same content as in `C10.lean`) | none |
| `scratch/glue-c10/Trace.lean` | pkg-I3's imports | pkg-I3 §§1-2 verbatim (Tate module, `AbVar`, `homT`, `galRep`); `CharPolyIndepOfEll` (copied); `trace_indep_of_ell`, `trace_eq_trace_of_ell` | none |
