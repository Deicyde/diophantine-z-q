# gr-isogdeg: `# ker φ(K̄) = deg φ` proved in characteristic 0; Gaudron–Rémond's row is a direct instance

Task gr-isogdeg, 2026-11-17. Base 73ac1620 (wip/r3-residual), merged with origin/main (ff558bedd). This is model
work only; no human has reviewed it. There was no network, so theorem numbers recalled from memory are marked
UNVERIFIED.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference), **SPECULATIVE**,
**UNVERIFIED**.

## 1. Result

**Main result.** For an isogeny `φ : A → B` of abelian varieties, the number of geometric points of the
kernel and the degree of `φ` as a finite morphism are now compared in Lean (VERIFIED, standard axioms, §5).
- Over **any** field: `# ker φ(K̄) ≤ deg φ`.
- Over a field of **characteristic 0**: `# ker φ(K̄) = deg φ`.

Here the degree is Mathlib's rank `Scheme.Hom.finrank` of `φ` at the generic point of `B`, which is
`[K(A) : K(B)]`.

```lean
noncomputable def ZInQ.GRIsogDeg.finDeg {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) : ℕ :=
  haveI := isIntegral_left B
  φ.left.finrank (genericPoint B.X.left)

theorem isogDeg_le_finDeg {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) (hφ : IsIsogeny φ) :
    isogDeg φ ≤ finDeg φ                                  -- any field
theorem isogDeg_eq_finDeg [CharZero K] {A B : PkgI3.AbVar K} (φ : A.X ⟶ B.X) (hφ : IsIsogeny φ) :
    isogDeg φ = finDeg φ                                  -- characteristic 0
```

**What this closes.** It was the last step on Gaudron–Rémond's row after r3-residual:
- r3-residual's leaf `GaudronRemondThm14An` bounds `isogDeg φ = # ker φ(K̄)`;
- Gaudron and Rémond bound the degree of the isogeny.

**The new leaf.** `GaudronRemondThm14AnDeg` is `GaudronRemondThm14An` verbatim, except that it bounds
`finDeg`, the printed degree.
- `gaudronRemondThm14An_of_deg` derives r3-residual's leaf from it, using `≤`.
- `gaudronRemondThm14AnDeg_iff_an` proves the two leaves equivalent, using the equality over number fields.
  So the new leaf is provably never stronger than the old one.

```
DISCHARGES [OpenResearchLeaves40.gaudronRemondThm14Printed] by ZInQ.GRIsogDeg.gaudronRemondThm14Printed_of_anDeg_final
  still assumes: [ZInQ.GRIsogDeg.GaudronRemondThm14AnDeg]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves40.gaudronRemondThm14Printed] by ZInQ.GRIsogDeg.gaudronRemondThm14Printed_of_anDeg
  still assumes: [ZInQ.GRIsogDeg.GaudronRemondThm14AnDeg, AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
```

**Count: −1 GLUE.**
- r3-residual's report (§3) left `gaudronRemondThm14An` GLUE on this step alone. With the step proved, the
  row is a direct instance of the print, and r3-residual's full −3 stands.
- The fold script (`autofold.py --dry-run`) shows no change: `16/15 → 16/15`. This base's `kinds.tsv`
  already rates the replaced row LEAF, so swapping it for a new LEAF leaves the counts as they were.
- The bundle field needs only the new leaf:
  - `mumfordTorsionAlgClosed` is filled by its proof,
    `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`;
  - T35 is filled by `uniformizationLeafAll_proof`.

## 2. The proof

### §1, ring level

**`card_ringHom_le_rankAtStalk`.** Setting:
- `R` a domain, `S` a finite `R`-algebra;
- `ψ₀ : R → Ω` injective into a field.

Claim: the ring maps `S → Ω` over `ψ₀` are finitely many, and there are at most `rankAtStalk S ⊥` of them.

Proof:
- `ψ₀` extends to `Frac R → Ω`.
- The maps correspond bijectively to `Frac R`-algebra maps `Frac R ⊗_R S → Ω` (Mathlib `AlgHom.liftEquiv`).
- Mathlib's `card_algHom_le_finrank` (Stacks 09HS) bounds their number by
  `finrank (Frac R ⊗ S) = rankAtStalk S ⊥` (`rankAtStalk_eq_finrank_tensorProduct`).

**`card_ringHom_eq_rankAtStalk`, the equality.** Extra hypotheses:
- `S` is a domain;
- `R → S` is injective;
- `Ω` is algebraically closed of characteristic 0.

Proof:
- `Frac R ⊗ S` is a localization of `S` (`IsLocalization.tensorRight`), hence a domain.
- It is finite over a field, hence a field.
- It is separable, since the characteristic is 0.
- Mathlib's `AlgHom.card` then gives exactly `finrank` maps.

**`card_ringHom_le_of_isAlgClosed`, descent.** Let `S` be integral over `R`, and let `k ⊆ Ω` be
algebraically closed. Every ring map `S → Ω` over `R → k ⊆ Ω` lands in `k`, because its values are integral
over `k` (`IsAlgClosed.algebraMap_bijective_of_isIntegral`).

### §2, scheme level

**`points_equiv_ringHom`.** Let `f` be finite and `u : Spec R → Y`. Then:
- the points `Spec L → X` over `Spec L → Spec R → Y` are in bijection with
- the ring maps `Γ(X ×_Y Spec R) → L` over `Γ(Spec R) → L`.

Proof: the pullback's universal property, plus `ext_of_isAffine` and `isoSpec` for the affine pullback.

**`card_points_le_finrank`.** Setting: `Y` integral, and `y₀` a point onto the generic point. Then
`#{x over y₀} ≤ f.finrank η`.

Proof:
- `Scheme.Hom.finrank` is computed on Mathlib's chosen affine open `U ∋ η`; its definition unfolds by `rfl`.
- The point of `Spec Γ(U)` under `η` is the zero prime, and it is the kernel of `Γ(U) → Ω`.

**`finrank_le_card_points`, the generic equality.** Extra hypotheses:
- `X` is integral;
- the fibre is nonempty;
- `Ω` is algebraically closed of characteristic 0.

The ring equality applies because `Γ(f⁻¹U)` is a domain, as an open subscheme of the integral `X`.

**`card_points_le_of_isAlgClosed`, descent.** For `f` finite and `k ⊆ Ω` algebraically closed:
- the `Ω`-points over a `k`-point are at most the `k`-points over it;
- both sets are finite.

### §3, abelian varieties

**`isogDeg_le_finDeg`.** Steps:
1. Take a geometric generic point `ξ : Spec Ω → A`, where `Ω` is an algebraic closure of `κ(η_A)`. It is a
   `K`-point through the `K`-algebra structure that `ξ` induces.
2. Take an embedding `K̄ → Ω` over `K`. It gives an epimorphism `Spec Ω → Spec K̄` (flat and surjective).
3. Translate: the points `ξ · P_Ω`, for `P` in the kernel, are distinct and lie over `ξ ≫ φ`.
4. `ξ ≫ φ` lies over the generic point of `B`, so §2 bounds their number.

**`finDeg_le_isogDeg` (characteristic 0)**, a chain of inequalities:

```
finDeg φ ≤ # fibre_Ω(ξ ≫ φ)    -- generic equality
         ≤ # ker_Ω              -- x ↦ ξ⁻¹ · x
         ≤ # ker_K̄ (points)     -- descent
         ≤ # ker(K̄)             -- these are Over-morphisms
         = isogDeg φ
```

**`finDeg_eq_finrank_of_flat`** (a remark, not used). If `φ` is flat and locally of finite presentation, the
rank is the same at every point.

## 3. The new leaf and its rating

| new leaf | replaces | rating | reason |
| --- | --- | --- | --- |
| `ZInQ.GRIsogDeg.GaudronRemondThm14AnDeg` | `gaudronRemondThm14An` (r3-residual) / `gaudronRemondThm14Printed` (main) | **printed form** | GR Thm 1.4 verbatim over r3-residual's `IsAnStableHeight`, with the printed degree. The degree of an isogeny is the degree of the finite morphism, `[K(A):K(B)]` (Mumford, *Abelian varieties*, §4/§7, UNVERIFIED section numbers). `finDeg` is that degree as Mathlib's `Scheme.Hom.finrank` at the generic point of `B`, where the stalk is the field `K(B)` (STANDARD). |

Notes on the rating:
- **Never stronger, proved.** `gaudronRemondThm14AnDeg_iff_an` shows the new leaf is equivalent to
  r3-residual's `GaudronRemondThm14An`, via `isogDeg_eq_finDeg` over number fields.
  - So swapping the leaves changes the reading, not the strength.
  - The rating "printed form" rests on GR's degree being `[K(A):K(B)]`, the definition of the degree of an
    isogeny.
- **No flatness in the statement.** `finDeg` is read at the generic point, where Mathlib's rank is the
  genuine fibre dimension without any flatness hypothesis. At other points, `Scheme.Hom.finrank` agrees with
  the degree for flat `φ` (`finDeg_eq_finrank_of_flat`). Isogenies are flat (STANDARD), but that is not proved
  here.
- **Locator.** The leaf is the same theorem as row R19 of `docs/research/locators.md` (Thm 1.4, p. 2060), so
  it needs no new row.
- **The old caveats of r3-residual's leaf remain unchanged:** readings R1, R2, R3′ and R4 of the height.

## 4. Files

- `ZInQKernel/Contrib/OneProof/GaudronRemondIsogDeg.lean` (new, 41 KB). It imports
  `ZInQKernel.Contrib.OneProof.AnalyticStableHeight`, `ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed` and
  four Mathlib modules. It has no `sorry`, no `axiom`, and no code that runs at build time.
- `scratch/gr-isogdeg/`:
  - development copies, which import only `ZInQKernel.HDecomp.Faltings.Leaves` and Mathlib: `Ring.lean`,
    `Sch.lean`, `IsogDeg.lean` (the inequality), `EqRing.lean`, `EqSch.lean`, `EqAll.lean` (the equality);
  - `log.md`;
  - `Discharges.lean`, `discharges.txt`;
  - `Axioms.lean`, `axioms.txt`;
  - `autofold.json` (against main: field `gaudronRemondThm14Printed`);
  - `autofold-after-r3.json` (if r3-residual is folded first: field `gaudronRemondThm14An`, proof
    `gaudronRemondThm14An_of_deg`);
  - `autofold-dryrun.txt`, `FoldDryRun.lean`, `FoldDryRun-compile.txt`;
  - build logs `build0.txt` to `build3.txt`.

## 5. Checks

All of the following are VERIFIED.

- **Build.** `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GaudronRemondIsogDeg`
  succeeded with 16049 jobs (`build3.txt`). `frozenTarget` has the standard axioms.
- **Axioms** (`axioms.txt`). `[propext, Classical.choice, Quot.sound]` for each of:
  - `isogDeg_le_finDeg`;
  - `isogDeg_eq_finDeg`;
  - `gaudronRemondThm14AnDeg_iff_an`;
  - `gaudronRemondThm14Printed_of_anDeg_final`;
  - `finDeg_eq_finrank_of_flat`.
- **`#discharges`** (`discharges.txt`): the two discharges in §1. r3-residual's own discharges are still listed
  as well.
- **Autofold.** Spec `autofold.json`: one new leaf, `gaudronRemondThm14AnDeg`, with kind published and flag
  "unread …; locator UNVERIFIED".
  - `--dry-run`: `strict count: 16/15 on 31 -> 16/15 on 31; strictest 16/15 -> 16/15`.
  - The generated module (first line stripped) compiles, and `HDec.HSyn.sixContactMin_of_open59` has the
    standard axioms (`FoldDryRun-compile.txt`).
  - A first draft of the spec used `{t}.mumfordTorsionAlgClosed`. That is no longer a bundle field on main:
    it was proved at TailZ64. The `_final` theorem fixes this.
- **The other spec.** `autofold-after-r3.json` applies only after r3-residual's fold, so it was not dry-run.

## 6. What remains

- Not needed by the consumer:
  - flatness of isogenies in Lean, which would make `finDeg` equal the rank at every point unconditionally;
  - `finDeg φ = Module.finrank K(B) K(A)` through Mathlib's function fields.
- Fold order. If r3-residual's `autofold.json` is folded first, use `autofold-after-r3.json`. Otherwise
  `autofold.json` discharges `gaudronRemondThm14Printed` directly, and r3-residual's discharge of the same
  field is then superseded.
