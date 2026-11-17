# y3-route-a: the Y₃ fine-moduli leaf as the manuscript's own conclusion (route (a))

Task y3-route-a, 2026-11-17. Branch wip/y3-route-a, based on wip/leaf-fold33b (bf691da22) with origin/wip/y3-audit
(8dc5f87d6) merged (clean). Lean: `ZInQKernel/Contrib/OneProof/Y3FullThreeZ30.lean`, namespace `Y3RouteA`.
Scratch: `scratch/y3-route-a/` (log, autofold spec, dry run and its compile, `#discharges`, kinds row).

Marks: **VERIFIED** = compiled, or read in the source; **STANDARD** = published argument with a reference;
**UNVERIFIED** = locator recalled, no network; **ON THE SPOT** = in neither the manuscript nor a print read here.

## 0. Source issues for the lead (to report to Jack)

1. **The kernel's old citation is wrong, not the manuscript's.** `Y3Fix.Y3FineModuliAbP` (kinds row
   `y3FineModuliAbP`) cited Buzzard 1997 §1 and Boutot–Carayol ch. III directly for full `𝒪`-linear level 3 at
   discriminant 6. Buzzard needs the level prime to the discriminant, and `3 ∣ 6` (y3-audit). The manuscript never
   cites a print at level 3: it applies Buzzard at `V₁(5)` and builds level 3 itself (L443-477, VERIFIED by
   reading). This task replaces the citation with the manuscript's own claim.
2. **The polarization is a possible mismatch inside the manuscript's route (UNVERIFIED).** The manuscript's freeness
   argument uses "a polarized automorphism" (L467), and the descent carries "its canonical principal polarization"
   (L474-475). As recalled (UNVERIFIED, not read here), Buzzard's moduli problem of false elliptic curves has no
   polarization. If so, the canonical principal polarization has to be supplied by the relative Lemma P (the
   type-`μ` principal polarization exists and is unique), which the manuscript does not state at this point. The
   argument only needs `Aut(A, ι)` to be finite, and Lemma P gives that. It is a gap of exposition, not of truth.
3. **"Its generic fiber is `Y₃`" (L476) silently uses the canonical-model identification** of the moduli scheme
   over ℚ with the Shimura curve `Sh_{K₃}` defined earlier in Section 4. In the kernel that identification is the
   separate leaf `deligneCanonicalModelY3EveryH` / `deligneCanonicalModelY3EveryPrint` (Deligne, Bourbaki 389).
   Nothing is missing; the two leaves together give the manuscript's sentence.

## 1. Result

**The leaf `Y3RouteA.Y3FullThreeRepZ30` states the manuscript's L473-477 conclusion over `ℤ[1/30]`.** It proves
`Y3Fix.Y3FineModuliAbP` in Lean, with standard axioms only (VERIFIED, `#print axioms`):

```lean
def Y3FullThreeRepZ30 : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of Z30))) (𝒜 : QMAbSchemeP 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of Z30))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbSchemeP S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily
```

Here `Z30 = Localization.Away (30 : ℤ)`. An object `QMAbSchemeP S` is:
* an abelian scheme of relative dimension 2;
* `ι : 𝒪 → End_S(A)` for the maximal order of `B = (2, −3 | ℚ)`;
* an `𝒪`-linear `η : 𝒪 → A(S)` killing `3𝒪` that is a bijection `𝒪/3𝒪 ≅ A_s[3]` at every geometric point.

Such an `η` is the same as a section of the manuscript's `Isom_𝒪(𝒪/3𝒪, A[3])`: `η` is determined by `η(1)`, and
`A[3]` is finite étale over `ℤ[1/30]`. The `ι` and `η` used here are the y3-fix / sgr-split objects, unchanged.

Theorems (all COMPILED, axioms `propext, Classical.choice, Quot.sound`):

| theorem | statement |
|---|---|
| `y3RepresentableQ_of_z30` | `Y3FullThreeRepZ30 → Y3Audit.Y3RepresentableQ` (the generic fibre `𝒴 ×_{ℤ[1/30]} ℚ` represents the problem on locally noetherian ℚ-schemes) |
| `y3FineModuliAbP_of_z30` | `Y3FullThreeRepZ30 → Y3Fix.Y3FineModuliAbP` (with y3-audit's `y3FineModuliAbP_of_rep'`) |
| `shimuraMainThmIDeligneY3AbU_of_z30` | `Y3FullThreeRepZ30 → DeligneCanonicalModelY3EveryH → ShimuraMainThmIDeligneY3AbU` |

The generic-fibre step uses `abBC`, the base change of a `QMAbScheme` along any morphism (Mathlib's monoidal
`Over.pullback`), and `qmFamFibre_abBC_of` / `qmFamFibre_trans`. These are copied from y3-audit's unfinished
`scratch/y3-audit/GenFib.lean`, which is route-independent there. That file did not compile, and three fixes were
needed:
* `Category.id_comp` had to be applied with `exact`, not `rw`;
* `one_eq` had to be unfolded to `ε ≫ map η`;
* the projection `j` had to be typed by the generic-fibre object.

The Kottwitz part of GenFib was not continued, as instructed.

**Rating of the new leaf: not printed form.** It is the manuscript's own claim (kind consequence, tag ELLIOT). The
manuscript derives it from one print plus glue:
* the print: Buzzard, Duke Math. J. 87 (1997), Thm 2.1 and Cor. 2.3 at `V₁(5)` (UNVERIFIED locator);
* the glue: the Isom sheaf, the free quotient and descent.

No print states it at level 3. It counts GLUE (strict and strictest), as did the row it replaces, so the GLUE
counts do not change (dry run: 4/27 on 31 → 4/27 on 31).

## 2. The leaf against the manuscript (VERIFIED by reading diophantine_zq.tex L443-477)

The manuscript's derivation, recorded in the docstring with line numbers:
1. Buzzard Thm 2.1 and Cor. 2.3 at `V₁(5)` over `ℤ[1/30]`: full determinant image, maximal at the division primes,
   and `5 ≥ 4` prime to 6 (L443-446).
2. A full five-marking, which gives a finite étale cover (L447-449).
3. The finite étale sheaf `Isom_𝒪(𝒪/3𝒪, A[3])` (L449-453). It is nonempty on geometric fibres because the Tate
   lattice is free of rank one over `𝒪₃` (L453-462). This gives `X₃₅`, smooth and projective (L464-465).
4. `G₅ = (𝒪/5𝒪)^×` acts freely, since `1 + 3M₄(ℤ₃)` is torsion-free (L465-472).
5. The quotient `X₃₅/G₅`, with descent of the universal abelian scheme, its polarization, its `𝒪`-action and its
   three-marking. The quotient represents the full-three problem, and its generic fibre is `Y₃` (L472-477).

How the Lean statement differs from L475-477. Each difference makes the Lean statement weaker or equivalent:
* **proper** in place of projective. This is weaker.
* The universal property is asked only on **locally noetherian bases in universe 0**. This is weaker.
* **No polarization.** The manuscript's functor carries the canonical principal polarization; `QMAbSchemeP` does
  not. The two functors are isomorphic through the canonical polarization, because every `(A, ι)` carries exactly
  one principal polarization of the canonical type, compatible with isomorphisms (relative Lemma P).
  **ON THE SPOT**: this equivalence is not in the manuscript in this form, and no print was read for it. It is not
  proved in the tree, where Lemma P exists only over fields and on lattices (`RvQMPolar`, `lemmaP_H1`). Nothing is
  built on it. It affects only the reading of the leaf as "the manuscript's statement".
* The marking is `η : 𝒪 → A(S)` with the geometric-fibre bijection, in place of a section of `Isom_𝒪`. The two are
  equivalent: `η(a) = ι(a)η(1)`, and a map of finite étale group schemes is an isomorphism if it is one on geometric
  fibres (STANDARD).
* "Its generic fibre is `Y₃`" is a theorem here (`y3RepresentableQ_of_z30`), with `Y₃` read as the kernel's witness
  of `Y3FineModuliAbP`. The identification with `Sh_{K₃}` is the separate canonical-model leaf (§0 item 3).

The rigidity argument of y3-audit (Serre's lemma) is an alternative to the manuscript's L469-471. It is not used and
not needed here.

## 3. Fold

The spec `scratch/y3-route-a/autofold.json` discharges `y3FineModuliAbP` by
`_root_.Y3RouteA.y3FineModuliAbP_of_z30 {n}.y3FullThreeRepZ30`, with one new leaf `y3FullThreeRepZ30` (kind
consequence, flag starting "ELLIOT:").

* Dry run (`autofold.py --dry-run`, VERIFIED): it generates `sixContactMin_of_open68` over `OpenResearchLeaves49`.
  Output: `scratch/y3-route-a/dryrun.txt`. The strict counts are unchanged: 4/27 on 31.
* Compile of the dry run, with line 1 stripped: `scratch/y3-route-a/DryRunFold.lean`, result in
  `dryrun-compile.txt` (see §5).
* `#discharges`: `scratch/y3-route-a/Discharges.lean`, result in `discharges.txt` (see §5).
* Consumers. `y3FineModuliAbP` enters the chain only through the bundle conversions (TailZ66, TailZ71, TailZ74:
  `shimuraMainThmIDeligneY3AbU_of_print ... n.y3FineModuliAbP ...`, and `elkiesX6StarEvery_of_ideal'`). The NoCM and
  Lemma NV consumers read it through the old generation. The fold fills that field with the proof above, so every
  consumer is unchanged; the compile of the dry run checks this.

The exact kinds row, generated with autofold's own row logic (`scratch/y3-route-a/kinds-row.tsv`):

```
research	y3FullThreeRepZ30	consequence	ELLIOT: the manuscript's own claim (diophantine_zq.tex L473-477), derived there from Buzzard 1997 Thm 2.1 / Cor. 2.3 at V1(5) plus the Isom sheaf, the free G5 = (O/5O)^x quotient and descent (L443-477); not a print at level 3 (Buzzard excludes level at 3 | disc 6); polarization-free form equivalent to the manuscript's polarized problem through the canonical principal polarization (relative Lemma P), ON THE SPOT, not proved in the tree; Buzzard locator UNVERIFIED	GLUE	GLUE	diophantine_zq.tex L443-477 (Glazer, 11/5 manuscript): Buzzard, Integral models of certain Shimura curves, Duke Math. J. 87 (1997) Thm 2.1 and Cor. 2.3 at V1(5) over Z[1/30], full five-marking, Isom_O(O/3O, A[3]), free quotient by (O/5O)^x, etale descent; locators UNVERIFIED	y3-route-a; pending review				unverified-locator	elliotglazer/diophantine-z-q#86
```

The flag contains "UNVERIFIED", so `render_open.must_be_glue` holds, and the row counts GLUE in both columns
regardless of kind.

## 4. What remains

* Formalizing the manuscript's derivation (steps 2-5) in Lean. Mathlib 4.35 lacks all of the following
  (y3-audit §4.2):
  * Isom schemes of finite étale group schemes;
  * `A[3]` as a group scheme over a base;
  * quotients by free finite group actions;
  * effective étale descent of abelian schemes;
  * polarizations over a base.
* A statement of Buzzard Thm 2.1 / Cor. 2.3 at `V₁(5)` as a printed leaf, which would make the new leaf a consequence
  of one print plus GLUE. This needs a level-5 variant of `QMAbSchemeP`, a mechanical copy. It was not done: it
  would only add glue, and it needs a reading of Buzzard for the polarization question (§0 item 2).
* The relative Lemma P (ON THE SPOT item above), if the lead wants the polarized statement.

## 5. Compile record (VERIFIED)

* `lake build +ZInQKernel.Contrib.OneProof.Y3FullThreeZ30`: OK. `#print axioms` on the three theorems:
  `[propext, Classical.choice, Quot.sound]`.
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: OK (14 min 34 s, no errors).
* `DryRunFold.lean` (the fold the spec generates): compiles with 0 errors. `HDec.HSyn.sixContactMin_of_open68`
  depends on `[propext, Classical.choice, Quot.sound]`.
* `#discharges` (`scratch/y3-route-a/discharges.txt`):

```
DISCHARGES [OpenResearchLeaves48.y3FineModuliAbP] by Y3RouteA.y3FineModuliAbP_of_z30
  still assumes: [Y3RouteA.Y3FullThreeRepZ30]
  axioms: [propext, Classical.choice, Quot.sound]
```
