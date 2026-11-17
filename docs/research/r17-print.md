# r17-print: `r17` from Carayol's Théorème (A), printed form, over printed newforms

Task r17-print, branch `wip/r17-print`, base 5e235a40 (wip/integrate-w82: TailZ45, strict 16 LEAF / 21 GLUE on
37), with e9683dac (newform-dict) and origin/wip/r17-bypass 3e6e5017 merged. 2026-11-16.
Marks: **VERIFIED** (compiled, or read in the named file), **STANDARD** (published, reference given),
**SPECULATIVE**. Theorem numbers from memory are **UNVERIFIED** (no network).

## 0. Result

**`r17 : LadicCond.CarayolR17'` is proved in Lean from one new leaf, `CarayolPrinted.CarayolThmA`, plus the
existing bundle field `eigenformCoeffFieldFinite`.** The leaf is Carayol's theorem stated for the representation
`ρ_{f,λ}` over `K_{f,λ}`, for a printed newform (Tau Ceti's `Newform N 2`). No new glue Prop. VERIFIED:

* `ZInQKernel/Contrib/OneProof/CarayolPrinted.lean` (23 KB) builds, with no warnings in the file;
* `#print axioms CarayolPrinted.carayolR17'_of_printed` gives `[propext, Classical.choice, Quot.sound]`;
* `#discharges`: `DISCHARGES [OpenResearchLeaves28.r17] by CarayolPrinted.carayolR17'_of_printed`, still
  assuming `[CarayolPrinted.CarayolThmA, DSCoeffExt.EigenformCoeffFieldFinite]`, with the standard axioms
  (`scratch/r17-print/discharges.txt`);
* autofold dry run: `strict count: 16/21 on 37 -> 17/20 on 37; strictest 16/21 -> 17/20`. The generated module
  compiles, and `sixContactMin_of_open39` has the standard axioms.

**Count effect: −1 GLUE (strict and strictest), provided the leaf keeps the flag `unread`.** That is the
contributor kit's rule for a new printed leaf. The reading risk is stated in §3 and in the flag: Carayol's own
wording is local–global compatibility. If a statement check finds the conductor packaging unprinted, re-flag the
leaf `pending reading`. The effect is then 0 (count-neutral), and the transport steps stay proved.

## 1. The field and why it is GLUE (VERIFIED, read)

`LadicCond.CarayolR17'` (`ZInQKernel/HDecomp/Conductor/LadicCond.lean:456`; verbatim copy in
`scratch/r17-print/R17Statement.lean.txt`) says: for every `ℓ`, `ιC`, `ιL`, every `f : CF N 2` with the kernel's
`IsNewform f χ`, every **semisimple** `ρ : GaloisRep ℓ 2` attached to `f` (trace form), and every prime `p ≠ ℓ`,
`condExp (ρ.restrictLocal p) = v_p(N)`. It differs from the print in three ways. All three are now proved in Lean:

| gap | print | proved by |
| --- | --- | --- |
| newform notion | Atkin–Lehner–Li newform (Petersson complement of the old space) | `NewformDict.exists_newform_of_isNewform` (strong multiplicity one; newform-dict) |
| coefficients | `ρ_{f,λ}` over `K_{f,λ}` | the place `λ_τ` cut out by `τ = ιL ∘ ιC⁻¹` and the continuous extension `τ̂ : K_{f,λ_τ} → ℚ̄_ℓ` (`DSCoeffExt`, coeff-ext); **new:** `condExp_map` (§2) |
| which `ρ` | the constructed `ρ_{f,λ}` | **new:** absolute irreducibility gives semisimplicity after scalar extension (§2); Brauer–Nesbitt + Chebotarev (`CarayolLevel.iso_of_attached`) and `condExp` invariant under isomorphism (`CarayolLevel.condExp_eq_of_intertwine`, r17-bypass) |

## 2. Lean (file `ZInQKernel/Contrib/OneProof/CarayolPrinted.lean`, namespace `CarayolPrinted`)

```lean
def CarayolThmA : Prop :=
  ∀ (N : ℕ) [NeZero N] (f : Newform N 2)
    [NumberField (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (f.toCuspForm : CF N 2))),
      Continuous ρ ∧
      Algebra.adjoin (lam.adicCompletion _) (Set.range fun σ => (ρ σ : Matrix (Fin 2) (Fin 2) _)) = ⊤ ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) _).trace =
            algebraMap (DSCoeffExt.coeffField _) (lam.adicCompletion _)
              ⟨coeff (f.toCuspForm : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        condExp (ρ.comp (decomp p)) = (N.factorization p : ℚ)

theorem carayolR17'_of_printed (h : CarayolThmA) (hK : DSCoeffExt.EigenformCoeffFieldFinite) :
    LadicCond.CarayolR17'
```

(Abbreviated with `_`. The file spells out every type.) Every object is a genuine definition:
* Tau Ceti's `Newform`;
* Mathlib's `adicCompletion`, `HeightOneSpectrum` and `Algebra.adjoin`;
* the kernel's `GQ`, `LiesOver`, `IsArithFrob`, `decomp` and `condExp` (the Serre–Tate conductor `codim V^{I_p} +
  Swan`, from `LadicCond`);
* `DSCoeffExt.coeffField` (`K_f = ℚ(a_n)`).

No structure was invented for the leaf.

New glue, all proved:
* **§1 `condExp_map`.** For a field homomorphism `φ : k → k'` and `ρ : G_{ℚ_p} → GL_n(k)`,
  `condExp (mapGL φ ∘ ρ) = condExp ρ`. It is assembled from three lemmas:
  * Invariants are the common zero set of the rows of `ρ(σ) − 1`. Their dimension is `n − rank`, computed
    through a finite linearly independent set of rows (`exists_linearIndependent`). The rank does not change
    under `φ`, by Mathlib's `linearIndependent_algebraMap_comp_iff`. These steps are `finrank_ann_map` and
    `codimInv_map`.
  * `mapGL φ` is injective, so the adapted levels agree (`isAdapted_map_iff`).
  * Hence `swan` picks the same level.
* **§2.** Burnside's absolute irreducibility (the image spans `M_n`) survives `φ` (`adjoin_map_eq_top`, through
  matrix units). It forces every invariant subspace to be `0` or everything (`eq_bot_or_top_of_adjoin`), hence
  the kernel's `IsSemisimple` (`isSemisimple_of_adjoin`).
* **§3 the discharge.** First `IsNewform f χ` gives `g : Newform N 2` with `g.toCuspForm = f`. The field
  `eigenformCoeffFieldFinite` makes `K_f` a number field. Take `λ = place τ` and get `ρ'` from the leaf, then
  `ρL = mapRep τ̂ ρ'`:
  * `ρL` is semisimple (§2);
  * `ρL` is attached to `f`: the trace is `τ̂(a_p) = ιL(ιC⁻¹ a_p)`;
  * `ρ ≅ ρL` (Brauer–Nesbitt and T18);
  * `condExp ρ|_p = condExp ρL|_p = condExp ρ'|_p = v_p(N)`.

## 3. Rating of the new leaf

| leaf | printed form? | reason |
| --- | --- | --- |
| `CarayolThmA` (kind published, flag `unread`, with the reading risk in the flag) | **Yes, in the packaged form** (UNVERIFIED wording) | It speaks about one representation `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` for a printed newform, as the sources do. It asserts only part of what they print: existence, continuity, absolute irreducibility, the Frobenius trace (not the full characteristic polynomial), and the conductor `v_p(N)` at `p ≠ ℓ`. It is not stronger than the print. **Reading risk:** Carayol 1986 Théorème (A) itself (pp. 409–411; coverage read by the locator audit, row R17: every `v ∤ ℓ`, every `ℓ` including 2, `p ∣ N` included) is local–global compatibility with `π_p` through the local Langlands correspondence. The conductor clause then follows with Casselman 1973 (`a(π_p) = v_p(N)` for newforms) and conductor preservation in the local correspondence. The irreducibility clause is Ribet 1977 Thm 2.3. The packaged statement ("`ρ_{f,λ}` is irreducible, with traces `a_p` and conductor `N` away from `ℓ`") is how the result is quoted, e.g. Darmon–Diamond–Taylor 1997 Thm 3.1 or Carayol §0.8. I cannot read either here: UNVERIFIED. |

The leaf cannot be Carayol's literal wording. The local Langlands correspondence, `π_p` and Weil–Deligne
representations are not definable in Mathlib v4.35. The conductor packaging is the strongest form that can be
stated in Lean, and it is exactly what r17 needs.

**Why the leaf must contain irreducibility** (mathematical, not a Lean artifact): r17 quantifies over every
semisimple attached `ρ`. Such a `ρ` is isomorphic to the semisimplification of the leaf's representation, and the
conductor is not invariant under semisimplification (Steinberg: `a = 1`, but its semisimplification is
unramified). So the leaf's representation must be known to be semisimple. Absolute irreducibility in Burnside's
form is the printed property (Ribet) that gives this after extending scalars to `ℚ̄_ℓ`.

**Statement check, what to read:**
1. Carayol 1986, §0.8 p. 411: is the conductor equality stated for `ρ_λ`?
2. DDT 1997 Thm 3.1 and the remarks after it: are "irreducible" (absolutely?) and `N(ρ_{f,λ}) = N` (prime to
   `ℓ`) stated?
3. Ribet 1977 Thm 2.3: irreducibility, and absolute irreducibility, for weight 2 on `Γ₁(N)` with nebentypus.

If any clause is not printed, the leaf becomes `pending reading`, count-neutral.

**Proposed `locators.md` row** (not added; the file belongs to other tasks):
`R17 (packaged, r17-print) | Carayol 1986 Théorème (A), §0.8; Casselman 1973; Ribet 1977 Thm 2.3; DDT 1997 Thm 3.1 |
— | UNVERIFIED | ρ_{f,λ} over K_{f,λ}: absolutely irreducible, traces a_p, conductor exponent v_p(N) at p ≠ ℓ;
check that the conductor packaging is printed for ρ_{f,λ}`.

## 4. Relation to the earlier tasks

* **r17-bypass** (`CarayolLevel.NewformRepConductor`, flagged pending reading): an existence form over `ℚ̄_ℓ`
  through `ιC`, `ιL`, over the kernel's `IsNewform`, asserting "semisimple". This leaf replaces it by:
  * the printed newform;
  * the printed coefficient field `K_{f,λ}` (one representation per `λ`, not one per pair of embeddings);
  * the printed property "absolutely irreducible" instead of "semisimple".

  The three dictionary steps are proved here. This file reuses r17-bypass's transport lemmas, and its
  `CarayolLevel.lean` must be folded with it, through the import.
* **newform-dict**: its `exists_newform_of_isNewform` is used directly. Its count-neutral restatement
  `CarayolR17Newform` is superseded.
* **The other hypothesis, `eigenformCoeffFieldFinite`** (existing field, composite, GLUE): the discharge uses it
  only at `k = 2`, where it is Diamond–Shurman Thm 6.5.1 (UNVERIFIED number), a single print. Note for the
  integrator: a `k = 2` restriction of that field could be rated a leaf separately. That is not part of this task.

## 5. Files

* `ZInQKernel/Contrib/OneProof/CarayolPrinted.lean`: the contribution. It imports `NewformDict`,
  `CarayolLevel` and `DSCoeffExt`, never `Main`.
* `scratch/r17-print/`:
  * `CarayolPrinted.lean`: scratch copy;
  * `Axioms.lean` and `axioms.txt`;
  * `Discharges.lean` and `discharges.txt`;
  * `autofold.json`, `autofold-dryrun.txt`, `AutofoldDryRun.lean` and `autofold-dryrun-compile.txt`;
  * `R17Statement.lean.txt`;
  * `log.md`.

## 6. What remains

* A statement check of `CarayolThmA` against the print (§3). This decides between −1 and 0.
* The fold (integrator). Folding `scratch/r17-print/autofold.json` brings in `CarayolLevel` and `NewformDict`
  through the import. Hashes were not compared in this task (dry run only).
