# glue-c10: the glue of step C10 (one compatible system at 3 and 5)

Status: research note (task glue-c10, 2026-11-11). Lean files: `scratch/glue-c10/C10.lean`
(Galois side) and `scratch/glue-c10/Trace.lean` (pkg-I3's definitions and ℓ-independence of
traces). Results log: `scratch/glue-c10/log.md`. No file under `ZInQKernel/`, `blueprint/`, or
another task's notes or scratch directory was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Theorem numbers given from memory are UNVERIFIED.

## Verdict

**C10's glue is proved in Lean, except one lemma: lifting a finite-level Frobenius to
`G_ℚ` (`FrobLift`, below).** The steps proved are:
- the comparison of characteristic polynomials (ℓ-independence of traces, from Mumford §19 Thm 4);
- the halving `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`;
- N5's transport from 5 to 3;
- the passage from Frobenius classes to the whole group `G_ℚ`;
- Brauer–Nesbitt;
- the semisimplification step.

Each proof has no `sorry`. `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` (VERIFIED: `lake env lean` on both files, 23:35-23:37 PST, no errors). The leaves
are copied verbatim from pkg-I6 (`ChebotarevExists`, `BrauerNesbittChar0`) and pkg-I3
(`CharPolyIndepOfEll`, with pkg-I3's definitions of `AbVar`, `T_ℓ`, `V_ℓ` and `homT`).

**Faithful form (decision).** C10 is stated in `G_ℚ`, for continuous representations, exactly as
N5 uses it (`iso_of_trace_eq_on_frob`, `iso_three_of_five`). The finite-quotient form recommended
by glue-I6-rest is also proved (`iso_of_trace_eq_frob_finite`). It is not used as the statement of
C10, for three reasons:
- the ℓ-adic representations `r₃` and `ρ_{f,ι₃}` do not factor through a finite quotient;
- passing to the reductions mod `ℓ^k` needs stable lattices;
- N5's hypothesis is about Frobenius elements of `G_ℚ`.

The `G_ℚ`-level theorem reduces to the finite level through one glue lemma, `FrobLift`. It is
stated precisely below and not yet proved.

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
| `GlueC10.FrobLift` (C10) | `E ⊂ \bar ℚ` finite Galois, `τ ∈ Gal(E/ℚ)` the arithmetic Frobenius at a prime `Q` of `𝓞_E` over `p`, unramified. Then some `h ∈ G_ℚ` with `IsFrobAt h p` restricts to `τ` (`AlgEquiv.restrictNormal h E = τ`) | — | **open** (stated, `def … : Prop`) |

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
   `g|_N`. `FrobLift` lifts the Frobenius obtained, and `restrictNormal_commutes` transfers
   `h|_N = g|_N` to `E`. (VERIFIED)
4. **Transport 5 → 3.** At a Frobenius `g` at `p ∉ S`, the hypotheses give
   `ι₅(c_p) = tr r₅(g) = tr ρ₅(g) = ι₅(a_p)`. A ring map out of a field is injective, so
   `c_p = a_p`. Then `tr r₃(g) = ι₃(c_p) = ι₃(a_p) = tr ρ₃(g)`. Items 2 and 1 of §1, with
   Brauer–Nesbitt, give `r₃ ≅ ρ₃`. Note: there is no need to compare at the same `g` across primes. The hypotheses
   are about every Frobenius element, so one `g` serves both primes. (VERIFIED)

## 3. What remains

1. **`FrobLift`** (SPECULATIVE: 150-300 lines). The plan:
   - (a) Choose a prime `𝔓` of `\bar ℤ` over `Q`. This is lying-over for the integral
     extension `𝓞_E → \bar ℤ`; one needs the algebra structure `𝓞_E → \bar ℤ`, which is
     boilerplate.
   - (b) An arithmetic Frobenius at `𝔓` exists in `G_ℚ`. Proof by compactness: for each finite
     Galois `F ⊂ \bar ℚ`, the set `C_F = {h : h x ≡ x^p mod 𝔓 for x ∈ 𝓞_F}` is closed, being a
     union of cosets of `Gal(\bar ℚ/F)`. It is nonempty by Mathlib's `exists_isArithFrobAt`
     (finite group acting) and `AlgEquiv.restrictNormalHom_surjective`. The family is directed:
     `C_{FF'} ⊆ C_F ∩ C_{F'}`. `G_ℚ` is compact (profinite). Every `x ∈ \bar ℤ` lies in some
     `𝓞_F`.
   - (c) `h|_E` is a Frobenius at `Q = 𝔓 ∩ 𝓞_E`. At an unramified prime the Frobenius is unique
     (`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`), so `h|_E` and `τ` agree as maps of `𝓞_E`.
     They then agree on `E = Frac 𝓞_E`.
2. **Not glue of this task; these are leaves or other steps**:
   - the Néron mapping property (reduction of `μ_σ`);
   - Serre–Tate specialization `V_ℓ(A) ≅ V_ℓ(Ā_v)`;
   - Eichler–Shimura for `ρ_{f,ι}`.

   These supply the trace hypotheses `hr₃, hr₅, hρ₃, hρ₅` of `iso_three_of_five`
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
| `scratch/glue-c10/C10.lean` | Mathlib | `ChebotarevExists`, `BrauerNesbittChar0` (copied); `IsUnramFrob`, `GQ`, `Zbar`, `IsFrobAt`, `FrobDense`, `FrobLift`; the theorems of §1 | none |
| `scratch/glue-c10/Trace.lean` | pkg-I3's imports | pkg-I3 §§1-2 verbatim (Tate module, `AbVar`, `homT`, `galRep`); `CharPolyIndepOfEll` (copied); `trace_indep_of_ell`, `trace_eq_trace_of_ell` | none |
