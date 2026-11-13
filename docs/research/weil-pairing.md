# weil-pairing: polarizations and the Weil pairing over `PkgI3.AbVar`

Task weil-pairing (2026-11-12). Lean file `scratch/weil-pairing/WeilPairing.lean` (about 1200
lines; imports `ZInQKernel.HDecomp.Objects`, `ZInQKernel.HDecomp.Assembly.C8`,
`ZInQKernel.HDecomp.QM.Structures`). Results log `scratch/weil-pairing/log.md`. No file under
`ZInQKernel/`, `blueprint/` or another task's directory was edited.

Marks. **VERIFIED**: compiled, or read in a named source. **STANDARD**: published, with
reference. **SPECULATIVE**: an assessment. There is no network on this host, so every theorem
number from memory is **UNVERIFIED**. Mumford = *Abelian varieties* (1970).

## 0. Verdict

**The "polarizations and Weil pairing" row of h-decomposition §4 is done, with one caveat (the
dual), and the T9-part of G12 is proved from leaves.** Everything below compiles with
`lake env lean scratch/weil-pairing/WeilPairing.lean`. There is no `sorry` and no `axiom`. The
axioms are `propext`, `Classical.choice` and `Quot.sound` (VERIFIED, `#print axioms` on the 12
main theorems at the end of the file).

1. **Definitions** over `PkgI3.AbVar`:
   - the torsion `A[n] ⊆ A(K̄)`, `μ_n(K̄)` and the Galois actions on both;
   - pairings `A[n] × B[n] → μ_n` (bilinear and `μ_n`-valued by construction), with the
     predicates perfect, alternating and Galois-equivariant;
   - **the dual as seen by its Weil pairings** (`WeilDual`), dual morphisms (`IsDualHom`);
   - **the Weil pairing** `e^λ_n(x, y) = e_n(x, λy)` (`weil`);
   - symmetric isogenies (`SymmIsogeny`);
   - **polarizations** (`Polarization`: symmetric isogeny plus Rosati positivity);
   - **principal** polarizations (`SymmIsogeny.IsPrincipal`: `λ` an isomorphism);
   - **the `ℓ`-adic Weil pairing** `E^λ : T_ℓ A × T_ℓ A → T_ℓ(μ)` (`tatePairing`);
   - Rosati type `μ` for QM surfaces (`RosatiTypeMu`).
2. **Basic API, proved**:
   - bilinearity, `e(x, y)ⁿ = 1`, `e(mx, y) = e(x, y)^m`;
   - alternating implies skew;
   - pull-back along homomorphisms (compatibility with isogenies): `weil_pullback`,
     `isSymmetric_pullback`, `IsDualHom.comp`, `IsDualHom.unique`;
   - Galois equivariance of `e^λ` (`weil_galois`);
   - nondegeneracy of `e^λ` up to the exponent of a quasi-inverse (`weil_nondeg`), and
     perfectness for principal `λ` (`weil_perfect_of_principal`);
   - **cyclotomic multiplier**, at finite level (`weil_cyclotomic`, through Mathlib's
     `modularCyclotomicCharacter'`) and `ℓ`-adically (`tatePairing_cyclotomic`, through
     Mathlib's `cyclotomicCharacter`): `E^λ(σx, σy) = χ_ℓ(σ)·E^λ(x, y)`;
   - `E^λ` alternating (`tatePairing_self`) and with trivial left kernel
     (`tatePairing_left_ker`);
   - `T_ℓ(μ) ↪ ℤ_ℓ` (`tmuCoordLin`, `tmuCoordLin_injective`, by discrete logarithms to a
     compatible system of roots of unity, `exists_tmu_gen`).
3. **T9 restated** over the definitions: `T09_SymmIsogenyExists` (every abelian variety over a
   field has a symmetric isogeny to a Weil dual). Together with `IsogenyQuasiInverse` it
   **implies the old leaf** `LeafPush.T09_WeilPairing` of `scratch/h-decomposition/Leaves.lean`.
   This is `oldT9_of_symmIsogeny` (VERIFIED, compiled against a verbatim copy, universe 0). So
   the `HSyn` bundle field `t9` can be replaced by the two new leaves.
4. **The G12 input, proved from four leaves:**
   `g12_detInput_of_leaves : T09_SymmIsogenyExists → IsogenyQuasiInverse →
   PkgI3.TateModuleFree → DivisiblePoints → G12_DetInput`.
   `G12_DetInput` is the statement `det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A}` on Objects' `V_ℓ(A)`, for
   every `A/K`, every prime `ℓ` invertible in `K` and every `σ ∈ G_K`. This is C8 item 1 (h-trust)
   in `det²` form. `twist_finite_four` is C8's determinant argument run from `(det r)⁴ = χ⁴`
   instead of `(det r)² = χ²`. With it, G12's determinant step needs no Pfaffian.
5. **Non-vacuity.**
   - Every definition is satisfiable: T9 and T9⁺ hold at `A = 0` (`symmIsogeny_zero`,
     `polarization_zero`).
   - Perfectness has content: the zero pairing is perfect only on trivial torsion
     (`isPerfect_zero_iff`). A `WeilDual` with trivial torsion forces `A[n] = 0`
     (`IsPerfect.left_trivial`). A symmetric isogeny with `e^λ_n = 0` forces `d·A[n] = 0`
     (`weil_ne_zero_of`).
   - The old leaf follows from the new one (item 3), so the new T9 is at least as strong as
     what the build uses.
   - Non-vacuity on a nonzero abelian variety cannot be checked in Lean: Mathlib v4.35 cannot
     construct one (Objects' `AbVar.zero` docstring).

**Caveat (the dual).** The genuine dual `Â = Pic⁰_{A/K}` **cannot be defined** over Mathlib
v4.35.0 (VERIFIED by search: there are no line bundles or Picard group of a scheme, only
`CommRing.Pic`). `WeilDual A` is a characterization: an abelian variety with a compatible system
of perfect Galois-equivariant pairings `A[n] × Â[n] → μ_n`. The genuine dual with Mumford's
`e_n` is one (STANDARD). But a `WeilDual` is **not unique**: over an algebraically closed `K` any
`Â` with `Â[n] ≅ A[n]` carries one (SPECULATIVE but elementary). Consequences:

- Leaves over `WeilDual` must be **existential** in the dual (`∃ D : WeilDual A, …`, witnessed
  by `Pic⁰`). All four stated here are.
- A universal leaf such as "every `f : A → B` has a dual `g : B̂ → Â` for all `WeilDual`s" or
  the uniqueness half of Lemma P would **not** be a consequence of the literature. They are not
  stated.
- Over a number field, a `WeilDual`'s `Â` is isogenous to `Pic⁰` (SPECULATIVE: Faltings'
  isogeny theorem applied to `V_ℓ Â ≅ V_ℓ(A)^∨(1)`). This is not needed and not used.

## 1. Definitions (VERIFIED: compiled)

| Lean | Meaning | Reference |
| --- | --- | --- |
| `tors A n` | `A(K̄)[n]`, an `AddSubgroup` of `Additive (A.Pt K̄)` | — |
| `Mu K n` | `μ_n(K̄)` (Mathlib `rootsOfUnity`), additively | — |
| `galTors`, `galMu`, `torsMap` | `G_K` on `A[n]`, on `μ_n`; `f : A → B` on `A[n]` | Objects' `galAct`, `ptMap` |
| `Pairing A B n` | `A[n] →+ B[n] →+ μ_n` | — |
| `IsPerfect`, `IsAlternating`, `IsGalEquivariant`, `pull` | as named; pull-back along `A(K̄) → A'(K̄)` | — |
| `WeilDual A` | `Â`, `e_n`, perfect, equivariant, `e_{mn}(x, y) = e_n(mx, y)` (`n` invertible in `K`), every `f ∈ End A` has a dual | Mumford §20 (UNVERIFIED §) |
| `IsDualHom DA DB f g` | `e_n(x, g y) = e_n(f x, y)` | Mumford §20 (5) (UNVERIFIED) |
| `weil D λ n` | `e^λ_n(x, y) = e_n(x, λ y)` | Mumford §§20, 23 |
| `IsSymmetric D λ` | every `e^λ_n` alternating | Mumford §23 (UNVERIFIED) |
| `SymmIsogeny A` | `D`, `λ : A → Â`, `IsIsogenyMor λ` (Objects: finite and surjective), symmetric | — |
| `IsQuasiInverse f g d` | `f g = [d]`, `g f = [d]` on `K̄`-points | — |
| `RosatiPositive S` | for `φ ≠ 0` in `End A` with dual `φ^∨` and quasi-inverse `ψ` of exponent `d`: `tr_{T_ℓ}(φ ∘ ψ φ^∨ λ)` is a positive integer | Mumford §21 Thm 1 (UNVERIFIED) |
| `Polarization A` | `SymmIsogeny` with `RosatiPositive` (up to sign: `−φ_L` qualifies) | Mumford §23 |
| `SymmIsogeny.IsPrincipal` | `λ` an isomorphism | — |
| `wv`, `tatePairing D λ hℓ` | `e^λ` on all of `A(K̄)` (junk `1` off `A[n]`); `E^λ` on `T_ℓ A` with components `e^λ_{ℓᵏ}(x_k, y_k)`, `ℤ_ℓ`-bilinear | — |
| `TMu K ℓ`, `galTMu`, `tmuCoordLin` | `T_ℓ(μ)` (Objects' `Tate.T` of `K̄ˣ`), `G_K` on it, coordinate `T_ℓ(μ) ↪ ℤ_ℓ` | — |
| `muO`, `oElt`, `RosatiTypeMu q S g` | `μ = 2j + k ∈ 𝒪`; `ι(μ) ∘ ι(b)† = ι(b̄) ∘ ι(μ)`, `b̄ = trd b − b` | rv-qm-polar §0 |

The "Pairing" type is bundled, so "the Weil pairing is bilinear with values in `μ_n`" holds by
construction. The proved content is in the multiplier, nondegeneracy and limit statements.

## 2. Leaves (`def … : Prop`)

None is used by a theorem of the build yet. Each is existential in the dual (see §0).

| Lean | Statement | Published source | E/C |
| --- | --- | --- | --- |
| `T09_SymmIsogenyExists` | every `A/K` has a `SymmIsogeny` | Mumford §6 App. 1 (projective, `L` ample over `K`), §8 (`Â`), §20 (`e_n`), §23 (`e^L` alternating) (UNVERIFIED §§) | C (`λ = φ_L`) |
| `T09plus_PolarizationExists` | every `A/K` has a `Polarization` | as T9, plus Mumford §21 Thm 1 | C |
| `IsogenyQuasiInverse` | isogeny `f` has `g`, `d ≥ 1` with `fg = [d]`, `gf = [d]` on points | Mumford §7 Rem. / §8 (UNVERIFIED); Milne 1986 §7-8 (UNVERIFIED) | C |
| `DivisiblePoints` | `A(K̄)` is divisible | `[n]` is an isogeny, Mumford §4 App. 2 (UNVERIFIED) | C |
| `LemmaP_Exists` (candidate) | a QM surface over a field of char 0 has a principal polarization of Rosati type `μ` | rv-qm-polar Lemma P (existence half; its sources UNVERIFIED there) | C |

Not stated, because it would be false or unsafe over `WeilDual` (§0): dual morphisms exist for
every `WeilDual`, and the uniqueness half of Lemma P.

## 3. Restated T9 and the G12 input

- **T9.** The old `LeafPush.T09_WeilPairing` hides the polarization: "there are `d` and a family
  `e` with six properties". The new leaf names the dual and `λ`. `oldT9_of_symmIsogeny` derives
  all six properties (VERIFIED):
  - `e^n = 1` from `μ_n`-values;
  - bimultiplicativity from bilinearity;
  - alternating from `IsSymmetric`;
  - nondegeneracy up to `d` from perfectness and `λψ = [d]`;
  - Galois equivariance from `weil_galois`;
  - compatibility from Mumford's `e_{mn}(x, y) = e_n(mx, y)` with bilinearity.
- **G12 (h-decomposition G12, h-trust C8 item 1).** C8 needs: `G_F` acts on `V₅(A)` through
  `GSp₄` with multiplier `χ`, so the determinant is a power of `χ`. Proved here:
  - `tatePairing_cyclotomic`: the multiplier of `E^λ` is `χ_ℓ`;
  - `det_galRep_sq`: `det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank}`. The proof uses the Gram matrix of
    `ι ∘ E^λ` (`det_sq_of_similitude_domain`), its nondegeneracy (`tatePairing_left_ker`, from
    `weil_nondeg` and the surjectivity `T_ℓ A → A[ℓᵏ]`, `tate_surj`) and
    `LinearMap.det_baseChange` to pass to `V_ℓ`;
  - `g12_detInput_of_leaves`, which assembles these.

  For `g = 2`: `det V₅(A) = (det r₅)²` (from C1's `V ⊗ E ≅ r ⊕ r`, not done here) gives
  `(det r₅)⁴ = χ⁴` on `G_F`. Then `twist_finite_four` gives the finiteness of the twist. The
  exact `det = χ^g` (Pfaffian) is not proved and not needed.

## 4. What remains

- **The genuine dual** `Pic⁰`: it needs line bundles on schemes and the Picard functor (very
  large, upstream Mathlib). Until then, `WeilDual` with existential leaves is the safe interface.
- **Fold-in**: replace `t9 : LeafPush.T09_WeilPairing` in the `HSyn` bundle by
  `T09_SymmIsogenyExists` and `IsogenyQuasiInverse` (via `oldT9_of_symmIsogeny`). Put the file
  in `ZInQKernel/HDecomp/` (it imports only HDecomp modules and Mathlib).
- **G12 assembly on the actual `A`**: `V ⊗ E ≅ r ⊕ r ⇒ det V = (det r)²` (C1's matrix units),
  and then `twist_finite_four`.
- **Positivity uses**: `RosatiPositive` is stated but not used. Lemma P's uniqueness half needs
  the genuine dual.
- `LemmaP_Exists` must be split before it can count as a leaf (§5 item 1).

## 5. Review

One adversarial model review (fresh agent, reading only; no human review) checked every leaf
against the genuine objects (`D = (Pic⁰, e_n)`, `λ = φ_L`). It found **no statement false,
stronger than the literature, or vacuous**. It confirmed:
- `compat` (Mumford's `e_{mn}(x, y) = e_n(mx, y)`), the perfect and Galois clauses in every
  characteristic for `n` invertible, and the direction of `IsDualHom`;
- `IsSymmetric` (`e^L_n(x, x) = 1`), the composition order in `RosatiPositive`, and
  `IsogenyQuasiInverse` and `DivisiblePoints` in every characteristic;
- `trd(ofInt n) = 2n₀ + n₂`, `μ² = −6`, and the equivalence of `RosatiTypeMu` with
  `ι(b)† = ι(μ⁻¹b̄μ)`;
- that `OldT9.T09_WeilPairing` is verbatim.

Its remarks, and what was done about each (the file recompiles, VERIFIED):
1. `LemmaP_Exists` combines several results (Rotger over `ℂ`, Lefschetz, descent) and is not one
   published theorem. It is now labelled a leaf **candidate**, not a leaf. To become a leaf it
   must be split into a published `ℂ`-statement and a descent step.
2. `RosatiPositive` and `RosatiTypeMu` constrain only those `φ` that have a dual. Fixed: the
   field `WeilDual.dualEnd` now requires every endomorphism to have a dual (true for `Pic⁰`;
   lemma `WeilDual.exists_dualEnd`), so both conditions apply to every `φ`. T9 is now slightly
   stronger and still a consequence of Mumford. `weilDualZero` and `oldT9_of_symmIsogeny` still
   compile.
3. `Polarization` is a polarization *up to sign*: `−φ_L` also qualifies. The docstring now says
   so. It is safe only in existential leaves, which is how it is used.
4. The docstring on the non-uniqueness of `WeilDual` is corrected: it needs compatible
   isomorphisms of the torsion, and even `Â = A` works over `K̄`.
