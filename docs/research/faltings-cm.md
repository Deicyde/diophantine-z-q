# faltings-cm: `r9a` (Faltings Satz 3) and `r9b` (Faltings Satz 4, Kor. 1) against their uses

Task faltings-cm, 2026-11-15. Base `43513d87` (leaf-fold25). Lean: `ZInQKernel/Contrib/OneProof/FaltingsTateSurj.lean`
(new). Scratch: `scratch/faltings-cm/` (`log.md`, `Closure.lean` with `closure_out.txt`, `Check.lean` with
`check_out.txt`, `Discharges.lean` with `discharges.txt`, `autofold.json`, `autofold-dryrun.txt`, `AutofoldDry.lean`
with `autofold-dry-compile.txt`). Marks: **VERIFIED** (read in a source, computed or compiled), **STANDARD**
(published, reference given), **SPECULATIVE**. There was no network access, so every theorem number recalled from
memory is marked **UNVERIFIED**.

## 1. Result

1. **Neither field follows from CM theory. Every consumer applies them to general, non-CM abelian varieties**
   (VERIFIED, §2). The live instances are:
   - `J = J₁(N)` over `ℚ`;
   - R16's Shimura quotient `A_f` of `J₁(N)` over `ℚ`;
   - `J₁(M)` base-changed to a number field `L'`;
   - the QM model `A` over `L'` of the fibre `P` of `Y₃` over `J(u)`, for any `u ∈ ℚ \ contactSet`
     (`contactSet = {0, −15, −20, −24, −30, −60}`, `Hypotheses/Height.lean` L84). This is a general QM abelian
     surface: nothing on the route makes it CM;
   - its conjugate variety `conjVar A s`.

   `hCM : T5Glue.ShimuraMainCM` is used only on the Tian–Yuan–Zhang branch (`Main.lean` L64-70), never on the H
   branch where `r9a`/`r9b` are consumed. So CM theory removes neither field.
2. **`r9b` is discharged from a strictly weaker new leaf and a field already in the bundles (VERIFIED, compiled,
   standard axioms).** On the route, the injectivity half of `r9b` is Mumford §19 Thm 3. That theorem is already the
   field `OpenTextbookLeaves11.homFreeFiniteAlgClosed`, which the kernel's `AVB1.homFreeFinite_of_algClosed` carries
   to any field. The inclusion `image ⊆ equivariant` is proved outright (`PkgI3.range_tateHomZl_subset`). So the
   only content of Faltings' theorem the route uses is `equivariant ⊆ image`, the new leaf `FaltingsTateSurj`.
   - Autofold folds it directly: the field is proved from the leaf, no consumer is rerouted.
   - The strict count is unchanged (46/10 on 56 → 46/10 on 56; strictest 45/11 → 45/11): one published LEAF is
     replaced by a weaker published LEAF.
3. **`r9a` stays as it is: a LEAF in printed form.**
   - Its instances are `J₁(N)` and `A_f` over `ℚ` (C9, E1Sub) and the QM model over `L'` (C2 for G8, E1).
   - Semisimplicity is not a formal consequence of the Tate property. A non-split extension of two distinct
     characters has scalar commutant, which is semisimple, yet the representation is not semisimple. So
     `FaltingsSemisimple` cannot be derived from `r9b`, nor from any other field in the bundles.
   - The used form is the full statement over number fields: all abelian varieties, `ℓ` arbitrary.
   - With rerouting it could be cut to `ℓ ∈ {3, 5}` (§2.3). That would not change the leaf's rating or its proof in
     the literature, so this is not proposed.

### 1.1 Theorems (`ZInQKernel/Contrib/OneProof/FaltingsTateSurj.lean`, namespace `ZInQ.Contrib.FaltingsCM`)

```lean
/-- **Faltings 1983, Satz 4 and Korollar 1, surjectivity half (printed form, consequence).** ... -/
def FaltingsTateSurj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    {φ | IsGalEquivariant φ} ⊆ Set.range (tateHomZl ℓ A B)

theorem faltingsTateSurj_of_faltingsTate (h : PkgI3.FaltingsTate) : FaltingsTateSurj

theorem faltingsTate_of_surj (hS : FaltingsTateSurj)
    (hH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : PkgI3.FaltingsTate
```

`#print axioms` (`scratch/faltings-cm/check_out.txt`, VERIFIED):

```
'ZInQ.Contrib.FaltingsCM.faltingsTate_of_surj' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.FaltingsCM.faltingsTateSurj_of_faltingsTate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Proof of `faltingsTate_of_surj`:
- injectivity is `(homFreeFinite_of_algClosed hH K A B).2.2.2 ℓ hℓK`, where `ℓ ≠ 0` in the number field `K`;
- the range clause is `Set.Subset.antisymm (range_tateHomZl_subset A B ℓ) (hS K A B ℓ)`.

### 1.2 `#discharges` (`scratch/faltings-cm/discharges.txt`, VERIFIED)

```
DISCHARGES [OpenResearchLeaves22.r9b] by ZInQ.Contrib.FaltingsCM.faltingsTate_of_surj
  still assumes: [ZInQ.Contrib.FaltingsCM.FaltingsTateSurj, ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
```

- `HomFreeFiniteAlgClosed` is the existing field `OpenTextbookLeaves11.homFreeFiniteAlgClosed`.
- The other seven DISCHARGES lines in the file belong to contributions already in the tree (GRCountX6, GapSHPair,
  ...).
- The summary line reads `#discharges: 63 open hypotheses, 1808 theorems checked, 8 discharge one`.

### 1.3 Autofold spec (`scratch/faltings-cm/autofold.json`)

```json
{"name": "faltings-cm",
 "imports": ["ZInQKernel.Contrib.OneProof.FaltingsTateSurj"],
 "discharges": [
   {"field": "r9b",
    "proof": "_root_.ZInQ.Contrib.FaltingsCM.faltingsTate_of_surj {n}.faltingsTateSurj {t}.homFreeFiniteAlgClosed",
    "leaves": [{"name": "faltingsTateSurj", "type": "_root_.ZInQ.Contrib.FaltingsCM.FaltingsTateSurj",
                "doc": "Faltings 1983 (Invent. Math. 73), Satz 4 and Korollar 1, surjectivity half: ...",
                "kind": "published", "flag": "",
                "source": "Faltings 1983 Satz 4, Kor. 1 (surjectivity half; locator UNVERIFIED)"}]}]}
```

`python3 scripts/one_proof/autofold.py scratch/faltings-cm/autofold.json --dry-run` printed `strict count: 46/10 on 56
-> 46/10 on 56; strictest 45/11 -> 45/11`. With its first line stripped, the generated module (`AutofoldDry.lean`:
`OpenResearchLeaves23`, `openResearchLeaves22_of_OpenResearchLeaves23`, `sixContactMin_of_open30`) compiles, and
`HDec.HSyn.sixContactMin_of_open30` depends on axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED). The fold
itself is left to the integration lead.

### 1.4 Leaf ratings

- **`faltingsTateSurj`: printed form (consequence), LEAF.**
  - It is the second conjunct of the old field with `=` weakened to `⊇` and the injectivity conjunct dropped, so it
    is implied by the published statement and never stronger (proved: `faltingsTateSurj_of_faltingsTate`).
  - It is stated over the kernel's genuine definitions:
    - `AbVar K` is a proper, smooth, geometrically integral group object over `Spec K`;
    - `T_ℓ` is the inverse limit of `A(K̄)[ℓⁿ]`;
    - `tateHomZl` is `ℤ_ℓ ⊗ Hom_K(A, B) → Hom(T_ℓ A, T_ℓ B)`;
    - `IsGalEquivariant` refers to `G_K = Gal(K̄/K)`.

    These are `HDecomp/Objects.lean` L56-360 (VERIFIED, read).
  - Source: G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983)
    349-366, Satz 4 / Korollar 1 (section and numbers UNVERIFIED; it is the same source as the old field). Proposed
    flag: "unread: new printed leaf, no reading recorded" (autofold's default).
- **`r9a` (unchanged): printed form, LEAF.** Faltings 1983 Satz 3 (UNVERIFIED number): `V_ℓ(A)` is a semisimple
  `G_K`-module for `A` over a number field. The Lean statement `(A.galRep ℓ).IsSemisimpleRepresentation` is exactly
  this, over the same genuine definitions.
- **`homFreeFiniteAlgClosed` (existing field):** Mumford §19 Thm 3 (UNVERIFIED locator). It now also carries the
  injectivity half of `r9b`, which is a classical theorem (Weil; Mumford) and needs no Faltings.

## 2. The consumers (VERIFIED)

### 2.1 Method

`scratch/faltings-cm/Closure.lean` (imports `ZInQKernel.OneProof.Main`) runs a BFS over `getUsedConstants` of types
and values from `ZInQ.OneProof.frozenTarget`. It lists every closure constant whose type mentions a constant named
`*.FaltingsSemisimple` or `*.FaltingsTate` (any namespace), and every closure definition whose body mentions one.
Output `closure_out.txt`:
- only the root `PkgI3.FaltingsSemisimple` and `PkgI3.FaltingsTate` are in the closure;
- apart from the bundle plumbing (`OpenResearchLeaves2..22`, `ResearchLeaves3`, `G0ModNewform.NewformLeaves`,
  `HSyn.faltings*_ofK5`), the consumers are the theorems and definitions below.

### 2.2 Instances

Line numbers are at the base.

| consumer | file:line | field use | instance |
|---|---|---|---|
| `C9Rhof.rhoF_semisimple` (via `c9_core`, from `G0ModNewform.commonConstituent_of_attached`) | `HDecomp/ModCurves/C9.lean:118` | `hS ℚ A ℓ` | `A = A_f`, R16's quotient of `J₁(N)` over `ℚ`; `ℓ = 5` |
| `E1Sub.rhoF_subrep_of_surj` (via `G0ModNewform.jSide`) | `HDecomp/ModCurves/E1Sub.lean:350` | `hS ℚ J ℓ` | `J = J₁(N)` over `ℚ` |
| `E1Sub.homVK_surjective` (via `vSurjOfSurjective`, in `jSide`) | `E1Sub.lean:134, 188, 190` | `hS ℚ Af ℓ`; `(hF ℚ Af Af ℓ).2`; `(hF ℚ J Af ℓ).1` | `A_f`, `J₁(N)` over `ℚ` |
| `PkgI3.C2_absolutelyIrreducible` (from `G0Galois.g8`, `g8_g11`, `g8_g12`) | `HDecomp/I3Linalg/C2.lean:751` | `hS K A ℓ` | QM model `A` over `K`, `ℓ = 5` (TailA L2272) and `ℓ = 3` (TailD L173) |
| `PkgI3.finrank_equivEnd` (in C2) | `HDecomp/Objects.lean:681, 683` | `(hF K A A ℓ).1`, `.2` | the same QM model |
| `PkgI3.E1_exists_hom_ne_zero` (from `HSyn.G0Split.hom_of_common3`, TailD L192; LPrefix L12319) | `C2.lean:784` | `hS K A ℓ` | `A_{L'}`, QM model; `ℓ` from `CommonConstituent` (built at `ℓ = 5`) |
| `PkgI3.exists_hom_ne_zero_of_equivariant` (in E1) | `Objects.lean:610` | `(hF K A B ℓ).2` | `(A_{L'}, J₁(M)_{L'})` |
| `G0Galois.faltingsV`, used by `conjTwistNontrivial_of_*` (the proof of `ConjTwistNontrivial`, which with `G10Glue` takes `hF` as a premise) | `OneProof/H/TailB.lean:2057` (uses at L2234, L2996) | `(hF K A B ℓ).2` | `(A, conjVar A s)` and ConjBettiData's `B`, QM model |

Where the abelian varieties come from:
- `AfterG7` (`TailA.lean:2977`) quantifies over the `G7Data` of a fibre context `FibreCtx Y Φ π u P` with
  `u ∉ contactSet`. There `P : QML3 ℚ̄` is the QM surface at a point over `J(u)`, and `A` is a model of it over `L`.
- R16 (`R16_EichlerShimuraJ1'`, `HDecomp/ModCurves/Leaves.lean:179`) supplies `A_f` and `π : J₁(N) ↠ A_f`.

None of these is CM in general.

### 2.3 What each field is really used for

- `r9b`:
  - `.1` (injectivity) is used twice, and both uses are covered by Mumford §19 Thm 3 (`homFreeFiniteAlgClosed`).
  - `.2` is used only as `equivariant ⊆ image`. Hence `FaltingsTateSurj`.
- `r9a`: every use is either a complement for a subrepresentation (`exists_isCompl`) or semisimplicity after base
  change to `ℚ̄_ℓ` (`GlueI3.semisimpleBaseChange`). Both need the full statement.
- `ℓ`: the explicit uses are at `ℓ = 5` (G8-G12, G13, C9/E1Sub) and `ℓ = 3` (G8-G11). The two E1 uses take `ℓ` from
  the existential in `CommonConstituent`, which is built at `ℓ = 5`. Restricting either field to `ℓ ∈ {3, 5}` would
  need `CommonConstituent` (and so `AfterG7`) to carry `ℓ = 5`: a rerouting through TailA, TailC, TailD, TailH and
  LPrefix. It is not proposed, because it changes neither the rating nor the literature behind the leaf.

## 3. Why CM theory cannot remove the fields

- **Tate property, `r9b`.** E1 needs `Hom_K(A_{L'}, J₁(M)_{L'}) ≠ 0` from a common constituent of the two `ℓ`-adic
  representations. Even if `A` were CM, this is Faltings' isogeny theorem for the general abelian variety
  `J₁(M)_{L'}` (STANDARD; no CM-only proof is known). The same holds for `(A_f, A_f)` in `homVK_surjective`.
- **Semisimplicity, `r9a`.** The instances `V_ℓ(J₁(N))` and `V_ℓ(A_f)` over `ℚ` are not CM.
  - Semisimplicity of `ρ_f` alone follows from Ribet's irreducibility theorem (Ribet 1977, LNM 601, Thm 2.3,
    UNVERIFIED). Neither that theorem nor the decomposition `J₁(N) ~ ∏ A_f^{m_f}` is in the bundles.
  - Ribet's theorem would also be a different leaf, not one fewer.
- **The QM instances are non-CM.** `u` ranges over all of `ℚ \ contactSet`.

## 4. What remains

- `r9a`: open LEAF, printed form, no reduction (§3).
- `faltingsTateSurj`: new LEAF, replacing `r9b` after the fold; it needs a statement check against Faltings 1983.
- Fold `scratch/faltings-cm/autofold.json` (integration lead).
