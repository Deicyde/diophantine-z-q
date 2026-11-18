# r16-thm1b: Shimura 1973 Theorem 1 as one row (`ShimuraThm1Af`), B-Sh split against the print

Task r16-thm1b (round 3 of r16-shimura73, 2026-11-17). Lean: `ZInQKernel/Contrib/OneProof/R16Thm1b.lean`
(namespace `R16Thm1b`; imports round 2's `R16Thm1`). Scratch: `scratch/r16-thm1b/` (log `log.md`). Round 2:
`docs/research/r16-thm1.md`; round 1: `docs/research/r16-shimura73.md`.

Input: an AI page read of the print of Shimura 1973 (cited as such). Per that read, p. 525 has "C = Ker(ν)", p. 526
builds `C` from the ideal (annihilating `f`) intersected with `End(J)` and states uniqueness "up to isomorphisms over
ℚ", and p. 527 gets `m = 1` from `q`-expansions. Round 2's premise, that multiplicity one is outside the print, was
wrong. Round 2's citation of DS 6.6.4 / Shimura 1971 Thm 7.14 for it is dropped.

## Main result

**GLUE count: base 5 LEAF / 24 GLUE on 29 rows, and 5 / 24 on 29 after the fold. The fold is count-neutral**
(autofold dry run: `strict count: 5/24 on 29 -> 5/24 on 29; strictest 5/24 -> 5/24`; no `--allow-rise` needed).
Round 2's two-row version was +1 GLUE. Out: `afShimura` (GLUE) and `heckeJ1DS` (GLUE). In: `shimuraThm1Af` (GLUE)
and `bShStandardModel` (GLUE).

* **One row replaces two** (the lead's ruling (a)). `R16Thm1b.ShimuraThm1Af` is the following statement. There is
  a triple `(A, ν, θ)` with Shimura's clauses (i)–(iii) (`R16Thm1.ShimuraClauses`) and `IsAfQuotient`
  (`ker ν = I_f J`). It is unique up to a `ν`-compatible isomorphism over `ℚ` among triples with (i)–(iii), and
  `K_f` is finite. The row is rated kind **consequence, GLUE**, with its steps flagged. It replaces round 2's
  `shimuraThm1Printed` + `shimuraQuotientIsAf`.
* `afShimura_of_thm1Af : ShimuraThm1Af → AfTateLam.AfShimura` is proved (VERIFIED, compiled, standard axioms).
  `IsAfQuotient` comes straight from the row. `IsAfAction` comes from clause (ii) by round 2's
  `R16Thm1.isAfAction_of`.
* `heckeJ1DS` is unchanged from round 2: `R16Thm1.heckeJ1DS_of_bSh` with the leaf `bShStandardModel`. Its flag is
  updated by the B-Sh analysis (§3). "The Hecke ring is rational" (p. 526) covers the rationality part of B-Sh only.
  The model identification and the double-coset dictionary are left ON THE SPOT. So the Shimura 1971 departure
  shrinks, and the curve's definition still goes back to Shimura 1971 through the print's own citation.
* `ShimuraTotalToComponents` (tex L770–773) is not in this fold (ruling (e)). `afCharpolyDS965` (DS 9.6.5,
  flagged) and `igusaGL2DSGalSome` are untouched.

## Known issues (exact locations)

1. **Misprint in Shimura 1973, p. 526, in the sentence on `f_σ` before clause (iv)** (AI page read; corrected per
   the lead's ruling (c), since round 2 had put it in the Euler clause): "`f_σ | T_n = a_n^σ f`" should read
   "`f_σ | T_n = a_n^σ f_σ`". The meaning is clear, so it is harmless, and the Lean rows do not state that sentence.
   Fixed in `R16Thm1.lean` (docstring of `ShimuraThm1Printed`), in round 2's report reference here, and in the flag
   of `shimuraThm1Af`.
2. **Round 2's Known issue 2 is withdrawn.** It said that the read's (i)–(iii) do not pin `A = J/I_f J` and that
   multiplicity one is not in the print. Per the new read, the print pins `C = Ker ν` (p. 525), builds `C` from the
   ideal ∩ `End(J)` (p. 526), and proves `m = 1` (p. 527). What remains are the on-the-spot steps of §2.
3. **The curve is Shimura's "standard model", defined by citation of Shimura 1971** (kept from round 2, now
   narrowed). Rationality of the Hecke ring is printed on p. 526, with no citation on the page. The identification
   with the kernel's `IsX1Gen` model and the double-coset dictionary are not printed (§3).
4. **Kept from rounds 1–2:** the gap at diophantine_zq.tex L770–773 (total Euler identity to per-embedding
   constituent). It is not repaired and not folded: it waits on Jack's ruling, and the lead recommends DS 9.6.5.
5. **Kept from rounds 1–2:** `ConjNewform` (Li applied to every `f_σ`) is uncited at the step.

## 1. The row (Lean: `R16Thm1b.lean`)

| name | statement | kind | printed form? |
| --- | --- | --- | --- |
| `ShimuraThm1Af` | for a newform `f ∈ S₂(Γ₁(N))` (`N ≥ 2`, nebentypus `χ`), any model `X` with `IsX1Gen`, Jacobian `J`, `T_p`, `⟨d⟩` with `IsHeckeT`/`IsDiamond`: `K_f` finite; `∃ A ν θ` with `ShimuraClauses` ((i) `ν` surjective, `ker ν` connected; (ii) `HeckeCompat` at `n = p` and at `n = p²` with `ξ_{p²} = T_p² − p⟨p⟩`; (iii) `dim A = [K_f : ℚ]`), `IsAfQuotient χ f tp δ A ν`, and `∀ A' ν' θ', ShimuraClauses … → ∃ ψ : A → A', IsIso ψ ∧ ν ≫ ψ = ν'` | consequence (GLUE, steps flagged) | **Not literally the printed form, but a consequence of the print plus three flagged ON THE SPOT steps.** The print (AI page read) gives the constructed triple `A = J/C`, `C = Ker ν` (p. 525), `C` from the ideal ∩ `End(J)` (p. 526), (i)–(iii) with `m = 1` (p. 527), and uniqueness "up to isomorphisms over ℚ" (p. 526). The steps are listed in §2. Dropped (weakenings): (iv), and the Euler clause (no consumer here; it stays in `R16Thm1.ShimuraThm1Printed` for `euler_of_shimura73_li`). |
| `BShStandardModel` | unchanged from round 2 (= the statement of `HeckeJ1DS`) | consequence (GLUE) | **No**: partly printed (rationality, p. 526) and partly ON THE SPOT (§3). |

Uniqueness is asked among competitors that satisfy (ii) only at `n = p, p²`. That is a larger class than the
print's (ii) for all `n`, so the clause is stronger than the printed one. Step 2 below (the Hecke relations) closes
the difference, which is why the row is rated consequence/GLUE and not a printed form.

## 2. The ON THE SPOT steps of `ShimuraThm1Af` (sketches; not formalized)

1. **`C = I_f J`.** Shimura's ideal is the kernel of `ρ : 𝕋 ⊗ ℚ → K_f`, `ξ_n ↦ a_n`. Its intersection with
   `End(J)` is the saturation `I_f^sat` of `I_f = {h ∈ 𝕋_ℤ : h f = 0}`. If `m x ∈ I_f` with `m > 0`, then
   `x(J) = (m x)(J)`, since `[m]` is surjective on `J`. So `I_f^sat J = I_f J`, as abelian subvarieties generated by
   images. The kernel's `KillsIf` uses the free algebra on `T_p`, `⟨d⟩` with `evF` (`T_p ↦ a_p`, `⟨d⟩ ↦ χ(d)`).
   Shimura's ring is generated by the `ξ_n` (and `ξ_{(p,p)}`). The two generate the same subring of `End(J)`, by
   the Hecke relations in both directions:
   * `ξ_{mn} = ξ_m ξ_n` for `(m, n) = 1`;
   * `ξ_{p^{k+1}} = ξ_p ξ_{p^k} − p ⟨p⟩ ξ_{p^{k−1}}` for `p ∤ N`;
   * `ξ_{p^k} = ξ_p^k` for `p ∣ N`;
   * conversely `p⟨p⟩ = ξ_p² − ξ_{p²}`, and `⟨d⟩ = ⟨p⟩` for a prime `p ≡ d (mod N)` (Dirichlet).

   The relation `ξ_{p²} = T_p² − p⟨p⟩` is a theorem step, not a definition (ruling (b)). It is the Hecke relation
   `T(p)² = T(p²) + p T(p,p)`. The ring maps agree on these generators (`a_n` satisfies the same recursions;
   `coeff_sq_relation` in Lean). So `ker ρ ∩ End(J) J = I_f J`. Then `ker ν = I_f J` gives `IsAfQuotient`:
   `J → J/B` is universal among homomorphisms killing `B`.
2. **(ii) for all `n` from `p` and `p²`.** The row's clause (ii) is at `n = p, p²` with `ξ_{p²} = xiSq`. The
   recursions in step 1, together with the multiplicativity and prime-power recursion of `a_n` for a normalized
   eigenform, give (ii) for every `n`. So a competitor in the row's uniqueness clause is a competitor in the
   print's.
3. **`ν`-compatible isomorphisms.** The print says "unique up to isomorphisms over ℚ". The row reads this as an
   isomorphism `ψ : A ≅ A'` with `ν ≫ ψ = ν'`. This holds because `ker ν' ⊇ I_f J` by the argument of step 1
   (`Hom` is torsion-free). By (i), `ker ν'` is connected, hence an abelian subvariety in characteristic 0. It has
   the dimension of `I_f J` by (iii) and `m = 1`, so `ker ν' = ker ν`.

## 3. B-Sh against the print (ruling (d))

What `heckeJ1DS_of_bSh` needs: for every `N ≥ 2`, every integral curve `X/ℚ` with `IsX1Gen N X jX tX` (function
field generated by `jX`, `tX` with the relations of `(j(τ), f₁(τ))`, points `x_τ` via `AtTau`), a rational point
`P₀` and Jacobian `(J, aj)`, there are `T_p ∈ End(J)` for every prime `p` and `⟨d⟩ ∈ End(J)` for every `d`, all
morphisms over `ℚ` (`AbVar ℚ`). They must act on the classes `[x_τ − x_τ']` by `IsHeckeT` (`p ∤ N`:
`Σ_i x_{(τ+i)/p} + x_{γ·pτ}` with `γ`'s lower-right entry `≡ p`; `p ∣ N`: `Σ_i x_{(τ+i)/p}`) and by `IsDiamond`
(`x_{γτ}`, `γ ∈ Γ₀(N)` with lower-right `≡ d`). This splits into four parts:

* **(B1) model.** The kernel's `X` is Shimura's standard model of `X₁(N)` over `ℚ`, with matching points `x_τ`.
  **Not printed in 1973**: the print defines its curve by citing Shimura 1971. This is ON THE SPOT. A proof would
  go through the `q`-expansion principle: both function fields are the functions with rational `q`-expansion at `∞`
  (Shimura 1971 §6.7 for the standard model, DS §7.5–7.7 for `ℚ(j, f₁)`; numbers UNVERIFIED).
* **(B2) rationality.** The Hecke correspondences `ξ_p` and `⟨d⟩` on the standard model are defined over `ℚ`.
  **Printed**: p. 526, "the Hecke ring is rational" (AI page read; no citation on the page).
* **(B3) on `J`.** A `ℚ`-rational correspondence induces an endomorphism of `J` over `ℚ` (Picard/Albanese
  functoriality). STANDARD. The print treats `ξ_n` as elements of `End(J)`, so this is implicit in it.
* **(B4) dictionary.** Shimura's `ξ_p = Γ diag(1, p) Γ` and his diamond operators act on points by DS's coset
  formulas (left action, the representatives `(1 i; 0 p)` and `γ diag(p, 1)`, and `⟨d⟩` with lower-right entry
  `≡ d`). **Not printed**: a convention dictionary, ON THE SPOT. The risk is a transposed convention for `Γ₁(N)`,
  which would conjugate by `w_N` and replace `⟨d⟩` by `⟨d⟩⁻¹`.

**Verdict on (d):** "the Hecke ring is rational" covers (B2), and with the standard (B3) it covers the rationality
of the operators on `J`. (B1) and (B4) remain, and they are definitional dictionaries rather than theorems of the
print. So B-Sh does not come entirely from the 1973 print. The Shimura 1971 departure shrinks to the definition of
the standard model, which the print itself cites, plus a convention check. The row `bShStandardModel` keeps
its Lean statement; its flag now records this split.

## 4. Merge check and proofs

* **Merge check (VERIFIED):** after the merge of fork main f3402e89 (e7ac05a33),
  `lake build ZInQKernel.Contrib.OneProof.R16Thm1` succeeds (11362 jobs; it rebuilds `R16ShimuraLi`, `R16CoreYDS965`
  and `R16Thm1`, with linter warnings only). The merge broke nothing, and no fix was needed.
* `R16Thm1.lean`: only docstrings were edited (misprint location per ruling (c); `xiSq` is a theorem step per (b);
  multiplicity one is cited to the print, p. 527, in place of DS 6.6.4 / Shimura 1971 Thm 7.14). It rebuilds.
* `R16Thm1b.lean` builds with no warnings. `afShimura_of_thm1Af` and `r16CoreY_of_thm1Af : BShStandardModel →
  ShimuraThm1Af → AfCharpolyDS965 → IgusaGL2DS → MumfordTorsionAlgClosed → R16CoreY` depend on `[propext,
  Classical.choice, Quot.sound]` (`scratch/r16-thm1b/Axioms-output.txt`; the round-1/2 theorems are re-checked
  there too).

## 5. Fold (`scratch/r16-thm1b/autofold.json`)

* Discharges `heckeJ1DS := R16Thm1.heckeJ1DS_of_bSh n.bShStandardModel` and
  `afShimura := R16Thm1b.afShimura_of_thm1Af n.shimuraThm1Af`. **No generation step**: both are fields of the top
  bundle `OpenResearchLeaves57` (TailZ83). The round-2 row `shimuraQuotientIsAf` is gone.
* **Dry run** (in the worktree; `--dry-run` writes nothing): `strict count: 5/24 on 29 -> 5/24 on 29; strictest 5/24
  -> 5/24`. Count-neutral, no `--allow-rise`. It writes TailZ84 with `OpenResearchLeaves58` and the new top
  `sixContactMin_of_open77`. Output: `scratch/r16-thm1b/FoldDryRun.lean.txt`.
* `scratch/r16-thm1b/FoldCheck.lean` (the dry-run module with line 1 stripped) compiles after
  `lake build ZInQKernel.OneProof.Main` on the merged tree (`frozenTarget` standard there). `HDec.HSyn.sixContactMin_of_open77`
  depends on `[propext, Classical.choice, Quot.sound]` (`FoldCheck-output.txt`).
* **`#discharges`** (`scratch/r16-thm1b/DischargesCheck-output.txt`): "30 open hypotheses, 11497 theorems checked,
  18 discharge one". Among them:
  * `DISCHARGES [OpenResearchLeaves57.afShimura] by R16Thm1b.afShimura_of_thm1Af`, still assumes
    `[R16Thm1b.ShimuraThm1Af]`, axioms `[propext, Classical.choice, Quot.sound]`;
  * `DISCHARGES [OpenResearchLeaves57.heckeJ1DS] by R16Thm1.heckeJ1DS_of_bSh`, still assumes
    `[R16Thm1.BShStandardModel]`, standard axioms;
  * round 2's `R16Thm1.afShimura_of_shimura73`, still assuming `[ShimuraThm1Printed, ShimuraQuotientIsAf]`, also
    appears; it is no longer used by the spec.
* **Exact kinds rows.** The fold was applied for real on a `git archive HEAD` copy in `/tmp`, not in the worktree.
  `scratch/r16-thm1b/kinds-diff.txt` has the full rows. Columns: bundle, field, kind, strict, strictest, rated_by,
  flag_class, area_issue.
  * Removed: `research afShimura consequence GLUE GLUE` and `research heckeJ1DS consequence GLUE GLUE` (queue11
    verdicts).
  * Added: `research shimuraThm1Af consequence GLUE GLUE "r16-thm1b; pending review" pending-review
    elliotglazer/diophantine-z-q#37`. Flag: "pending review: Shimura 1973 Thm 1 as printed (AI page read: Ker nu
    p. 525, uniqueness up to isomorphisms over Q p. 526, tangent space and m = 1 from q-expansions p. 527, C from the
    ideal intersected with End(J) p. 526); on-the-spot steps: C = I_f J (the ideal is ker rho, saturation, Hecke
    relations in both directions), (ii) for all n from p and p^2 via xi_{p^2} = T_p^2 - p<p> (theorem step),
    nu-compatible isomorphisms; misprint in the f_sigma sentence before (iv) on p. 526 ('f_sigma | T_n = a_n^sigma f'
    for 'a_n^sigma f_sigma') recorded in docs/research/r16-thm1b.md". Source: Shimura, J. Math. Soc. Japan 25
    (1973), 523–544, Theorem 1 and its construction (pp. 525–527; AI page read).
  * Added: `research bShStandardModel consequence GLUE GLUE "r16-thm1b; pending review" pending-review
    elliotglazer/diophantine-z-q#37`. Flag: "pending review: bridge B-Sh; rationality of the Hecke ring over Q
    printed in Shimura 1973 p. 526 (AI page read, no citation on the page); ON THE SPOT: the kernel's IsX1Gen model
    is Shimura's standard model (defined by citation of Shimura 1971) and xi_p, <d> act by DS's double-coset
    formulas (convention dictionary)".
  * In that copy, `render_open.py --check` complains only that OpenStatements is not regenerated (afShimura and
    heckeJ1DS are still listed as open). Regenerating it needs the Lean build, which is the maintainers' step.

## Manuscript check

The r16 route is the paragraph diophantine_zq.tex L755–794 ("Modularity and a uniform conductor bound"). The rows
for L768–771 are updated from round 2. The other rows are kept.

| tex lines | step | verdict | reason |
| --- | --- | --- | --- |
| L767–768 | absorb the finite character, take the primitive newform `f` | OK | standard newform theory (Atkin–Lehner–Li). The Lean `R16CoreY` starts from a newform. |
| L768–770 | Li's Fricke formula (Li 1975, p. 296, before Lemma 6) makes the span of the coefficient conjugates Fricke-stable | gap filled | Li's formula is for newforms. Applying it to every `f_σ` needs the conjugates to be newforms (`ConjNewform`, uncited, GLUE). With that, Lean proves `FrickeStable` (`R16ShimuraLi.frickeStable_of_li`). Li's page is not read (locator UNVERIFIED). The proviso is used only for the Euler clause, which the fold's row does not carry (it stays in `R16Thm1.ShimuraThm1Printed`, `euler_of_shimura73_li`). |
| L770–771 | Shimura's quotient construction (Shimura 1973 Thm 1) | OK (updated) | per the new AI page read: `A = J/C` with `C = Ker ν` (p. 525), `C` built from the ideal annihilating `f` ∩ `End(J)` (p. 526), the `K_f`-action compatible with `ξ_n`, `dim A = [K_f : ℚ]` and the tangent space from `m = 1` via `q`-expansions (p. 527), uniqueness up to isomorphism over `ℚ` (p. 526). This is all printed, without proviso. So the quotient the manuscript cites is DS's `J/I_f J` up to the three ON THE SPOT steps of §2 (`C = I_f J` via the Hecke relations, (ii) for all `n`, `ν`-compatible uniqueness). Round 2's claim that multiplicity one is not in the print is withdrawn. The curve is the standard model, defined by citation of Shimura 1971. Rationality of the Hecke ring is printed (p. 526); the model and dictionary are not (§3). |
| L771 | Shimura's Euler-factor identity under the proviso | OK (updated) | the print's proviso (`Γ = Γ₀(N)` or `span{f_σ}` Fricke-stable) is what L768–770 supplies. The clause is total, over all embeddings (`euler_of_shimura73_li`, proved from the leaves). The misprint is in the `f_σ` sentence before (iv) on p. 526 ("`f_σ | T_n = a_n^σ f`" for "`a_n^σ f_σ`"), not in the Euler clause (Known issues 1, corrected from round 2). |
| L771–773 | "therefore" `r_5` is a constituent of the Tate module of `A_f` | unverified (gap, not filled) | the total Euler identity does not see `θ`. The conclusion needs Faltings semisimplicity, then Chebotarev or Brauer–Nesbitt, then per-embedding traces, and none of these is written (round 1, Known issue 1). The Lean route uses DS 9.6.5 (`afCharpolyDS965`, flagged). `ShimuraTotalToComponents` is kept out of this fold pending Jack's ruling. |
| L773–774 | dual: `r_5^∨` is a cohomological constituent; duality preserves the conductor | OK | the conductor of the contragredient equals the conductor (the inertia invariants of `V` and `V^∨` have the same dimension, and the Swan conductors agree). Not on the Lean route, which uses the Tate-module normalization. |
| L776–794 | `r_3` identified with the modular Tate representation (ℓ-independence on the reduction, Chebotarev, semisimplicity) | unverified | uses the modular traces at three per embedding, so it needs the same per-embedding input as L771–773. The Lean route does not use `r16` at three (round 1, §4). |

## What remains

* A reviewer should rate `shimuraThm1Af` (consequence, GLUE with flagged steps) and check the three ON THE SPOT
  steps of §2 against pp. 525–527.
* B-Sh: (B1) the model identification (`q`-expansion principle, Shimura 1971 / DS §7) and (B4) the convention
  dictionary are not in the 1973 print.
* Jack's ruling on `ShimuraTotalToComponents` (tex L770–773) versus DS 9.6.5.
