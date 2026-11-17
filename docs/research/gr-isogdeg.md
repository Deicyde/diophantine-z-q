# gr-isogdeg: `# ker φ(K̄) ≤ deg φ` proved; Gaudron–Rémond's row is a direct instance

Task gr-isogdeg, 2026-11-17. Base 73ac1620 (wip/r3-residual), merged with origin/main (ff558bedd). This is model
work only; no human has reviewed it. There was no network, so theorem numbers recalled from memory are marked
UNVERIFIED.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference), **SPECULATIVE**,
**UNVERIFIED**.

## 1. Result

**For every isogeny `φ : A → B` of abelian varieties over any field `K`, the number of geometric points of
the kernel is at most the degree of `φ` as a finite morphism. The degree here is Mathlib's rank
`Scheme.Hom.finrank` of `φ` at the generic point of `B`, which is `[K(A) : K(B)]`.** This is a Lean theorem
with the standard axioms (VERIFIED, §5):

```lean
noncomputable def ZInQ.GRIsogDeg.finDeg {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) : ℕ :=
  haveI := isIntegral_left B
  φ.left.finrank (genericPoint B.X.left)

theorem ZInQ.GRIsogDeg.isogDeg_le_finDeg {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) (hφ : IsIsogeny φ) :
    isogDeg φ ≤ finDeg φ
```

This was the one step left on Gaudron–Rémond's row after r3-residual:
- r3-residual's leaf `GaudronRemondThm14An` bounds `isogDeg φ = # ker φ(K̄)`;
- Gaudron and Rémond bound the degree of the isogeny.

The new leaf `GaudronRemondThm14AnDeg` is `GaudronRemondThm14An` verbatim, except that it bounds `finDeg`,
the printed degree. `gaudronRemondThm14An_of_deg` derives r3-residual's leaf from it, so
`GaudronRemondThm14An` is now a direct instance of the print.

```
DISCHARGES_PLACEHOLDER
```

**Count: −1 GLUE.** r3-residual's report (§3) left `gaudronRemondThm14An` GLUE on this step alone. With the
step proved, the row is a direct instance of the print, so r3-residual's full −3 stands.

The inequality holds in every characteristic, because `# ker(K̄)` is the separable degree. So the proof
needs neither characteristic 0 nor separability nor flatness.

The task also asked for the equality `deg = # ker(K̄)` in characteristic 0. It is **not proved** (§6). The
consumer uses only `≤`.

## 2. The proof

**§1, the ring level** (`card_ringHom_le_rankAtStalk`). Setting:
- `R` a domain, `S` a finite `R`-algebra;
- `ψ₀ : R → Ω` injective into a field.

Claim: the ring maps `S → Ω` over `ψ₀` are finitely many, and there are at most `rankAtStalk S ⊥` of them.

Proof:
- `ψ₀` extends to `R_(0) = Frac R → Ω`.
- The maps correspond bijectively to `Frac R`-algebra maps `Frac R ⊗_R S → Ω` (Mathlib `AlgHom.liftEquiv`).
- Mathlib's `card_algHom_le_finrank` (Stacks 09HS) bounds their number by
  `finrank (Frac R ⊗ S) = rankAtStalk S ⊥` (`rankAtStalk_eq_finrank_tensorProduct`).

**§2, the scheme level** (`card_points_le_finrank`). Setting:
- `f : X → Y` finite, with `Y` integral;
- `y₀ : Spec Ω → Y` onto the generic point.

Claim: the `Ω`-points of `X` over `y₀` are finitely many, and there are at most `f.finrank (genericPoint Y)`
of them.

Proof:
- `Scheme.Hom.finrank` is computed on Mathlib's chosen affine open `U = Spec R ∋ η` (its definition unfolds
  by `rfl`).
- `y₀` factors through `U`.
- Points over `y₀` inject into `Spec Ω`-points of the affine scheme `f⁻¹U` over `U`.
- Those inject into ring maps `Γ(f⁻¹U) → Ω` over `Γ(U) → Ω` (`ext_of_isAffine`).
- The point of `Spec Γ(U)` under the generic point is the zero prime, and it is the kernel of
  `Γ(U) → Ω`. So §1 applies.

**§3, abelian varieties** (`isogDeg_le_finDeg`).
1. Choose a geometric generic point `ξ : Spec Ω → A`, where `Ω` is an algebraic closure of `κ(η_A)`. Make it a
   `K`-point through the `K`-algebra structure that `ξ` induces.
2. Choose an embedding `K̄ → Ω` over `K` (`IsAlgClosed.lift`). It gives a map
   `ptObj K Ω ⟶ ptObj K K̄`, which is an epimorphism of schemes (flat and surjective).
3. Send each kernel point `P` to the translate `ξ · P_Ω`. Since `φ` is a homomorphism,
   `(ξ · P_Ω) ≫ φ = (ξ ≫ φ) · 1 = ξ ≫ φ`.
4. The map is injective: cancel in the group `Hom(Spec Ω, A)`, then cancel the epimorphism.
5. `φ` is surjective, so `ξ ≫ φ` lies over the generic point of `B`. §2 then gives
   `# ker φ(K̄) ≤ φ.finrank(η_B)`.

## 3. The new leaf and its rating

| new leaf | replaces | rating | reason |
| --- | --- | --- | --- |
| `ZInQ.GRIsogDeg.GaudronRemondThm14AnDeg` | `gaudronRemondThm14An` (r3-residual) / `gaudronRemondThm14Printed` (main) | **printed form** | GR Thm 1.4 verbatim over r3-residual's `IsAnStableHeight`, with the printed degree. The degree of an isogeny is the degree of the finite morphism, `[K(A):K(B)]` (Mumford, *Abelian varieties*, §4/§7, UNVERIFIED section numbers). `finDeg` is that degree as Mathlib's `Scheme.Hom.finrank` at the generic point of `B`, where the stalk is the field `K(B)` and the rank is the dimension of `K(A)` (STANDARD). |

Notes on the rating:
- **Never stronger.** The leaf is GR's statement with GR's degree.
  - The converse `GaudronRemondThm14An → GaudronRemondThm14AnDeg` would need `deg ≤ # ker(K̄)` in
    characteristic 0, which is not proved.
  - So "never stronger" rests on reading `deg` as `[K(A):K(B)]`, the definition of the degree. It is not a
    Lean implication from the old leaf.
- **No flatness in the statement.** `finDeg` is read at the generic point, where Mathlib's rank is the
  genuine fibre dimension without any flatness hypothesis. At other points, `Scheme.Hom.finrank` agrees with
  the degree only for flat `φ`. Isogenies are flat (STANDARD), but that is not proved here.
- **The old caveats of r3-residual's leaf remain unchanged:** readings R1, R2, R3′ and R4 of the height.

## 4. Files

- `ZInQKernel/Contrib/OneProof/GaudronRemondIsogDeg.lean` (new). It imports
  `ZInQKernel.Contrib.OneProof.AnalyticStableHeight` and four Mathlib modules. It has no `sorry`, no `axiom`,
  and no code that runs at build time.
- `scratch/gr-isogdeg/`:
  - `Ring.lean`, `Sch.lean`, `IsogDeg.lean` (development copies; `IsogDeg.lean` imports only
    `ZInQKernel.HDecomp.Faltings.Leaves` and Mathlib);
  - `log.md`;
  - `Discharges.lean`, `discharges.txt`;
  - `autofold.json` (against main: field `gaudronRemondThm14Printed`);
  - `autofold-after-r3.json` (if r3-residual is folded first: field `gaudronRemondThm14An`);
  - build logs.

## 5. Checks

CHECKS_PLACEHOLDER

## 6. What remains

- **The equality in characteristic 0** (`finDeg φ ≤ isogDeg φ`) is not proved. It needs:
  - that the kernel is étale (Cartier, STANDARD);
  - that the fibre algebra over the origin has dimension `[K(A):K(B)]`. This needs flatness of `φ`
    (miracle flatness, or homogeneity together with generic flatness), which Mathlib 4.35 lacks as far as
    checked.

  The consumer does not need the equality.
- Not attempted: a Lean proof that `finDeg φ = Module.finrank K(B) K(A)` through Mathlib's function fields.
  It would make the reading "rank at the generic point = `[K(A):K(B)]`" a theorem.
