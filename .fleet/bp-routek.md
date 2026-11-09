# bp-routek: Route K in the blueprint

No Lean file was edited. `lake build ZInQKernel` succeeds. `autoform check blueprint --lean-root .`
gives OK (418 articles, 1315 dependencies, 1154 declaration names resolved, no warnings), and
`autoform audit blueprint` gives OK with no warnings. Before this task the counts were 398 articles
and 1275 dependencies, also with no warnings.

`autoform audit blueprint --lean-root .` was not required. It reports only the two
`lean-target-kind-mismatch` errors that were already there (`ir-integer-routines.md`,
`natural-circuit-well-formed.md`) and `node-too-large` warnings on articles this task did not touch.
None of the new articles triggers a warning.

The branch merges `origin/wip/tyz-5b`, which adds only docs, scratch files and its report. The merge
makes `docs/research/tyz-5b.md`, cited by the `CertifiedRank` docstring and by the new locators,
present in this branch.

## Articles added

Every new article is `origin: bridged`. All are `statement: formalized`. Theorems and lemmas also
carry `proof: formalized`. The first `lean:` name takes the progress credit.

| Article | Lean names (first takes credit) | Status |
| --- | --- | --- |
| `route-k/README.md` (chapter) | — | container |
| `route-k/configuration.md` (structure) | `ZInQ.RouteK.Config`, `oddClasses`, `lam8`, `mu8`, `Config.lam`, `Config.mu`, `Config.prodClass`, `Config.bit_symm_of_cls_one` | statement formalized |
| `route-k/selmer-system.md` (def Σ(𝒞)) | `ZInQ.RouteK.Config.IsSol`, `Config.sols`, `Unknowns`, `Unknowns.first`, `Config.monsky`, `Config.E1`, `Config.E2`, `twoAdicRows`, `Config.D`, `dot` | statement formalized |
| `route-k/partner-lemma.md` (Lemma 1, single and family form) | `ZInQ.RouteK.Config.Partner.bijOn`, `Config.Partner`, `Config.erase`, `Partner.isSol_iff`, `Partner.solsEquiv`, `Partner.solsEquiv_symm_apply`, `Partner.card_sols`, `Config.Partners`, `Config.restrictLeft`, `Partners.isSol_iff`, `Partners.bijOn`, `Partners.card_sols` | proved |
| `route-k/gluing-lemma.md` (Lemma 2) | `ZInQ.RouteK.Config.Gluing.bijOn`, `Config.Gluing`, `Config.glue`, `Config.glueMap`, `Config.glueLift`, `Gluing.solsEquiv`, `Gluing.solsEquiv_symm_apply`, `Gluing.card_sols`, `Config.glue_prodClass` | proved |
| `route-k/base-configuration.md` (Lemma 3) | `ZInQ.RouteK.Config.base_card_sols'`, `base_mem_sols'`, `base_exists_first'`, `base_isSol_iff`, `base_card_sols`, `baseSol₀_mem`, `base_exists_first` | proved |
| `route-k/residue-bits.md` (def) | `ZInQ.RouteK.legBit`, `lamBit`, `muBit`, `signBit`, `primesOf` | statement formalized |
| `route-k/reciprocity-bits.md` (`origin: background`) | `ZInQ.RouteK.legBit_reciprocity`, `lamBit_eq`, `muBit_eq`, `legBit_mul`, `legBit_prod`, `legBit_eq_zero_iff`, `legBit_symm_of_one_mod_four`, `legBit_symm_of_three_mod_four` | proved |
| `route-k/prime-configuration.md` (def: 𝒞_d, class of a, Selmer certificate) | `ZInQ.RouteK.natConfig`, `primeCfg`, `natClass`, `SelmerCertified` | statement formalized |
| `route-k/squarefree-part.md` (def: admissible B, sqf, β, θ) | `ZInQ.RouteK.sqf`, `betaOf`, `thetaOf`, `Admissible`, `sqfInt`, `sqfNat`, `sqf_spec`, `sqf_eq_of_eq_mul_sq`, `poleCompleteness_iff_admissible` | statement formalized |
| `route-k/multiplier-lemma.md` (L1) | `ZInQ.RouteK.exists_multiplier_pos`, `exists_multiplier` | proved |
| `route-k/theta-properties.md` ((θ1)–(θ4)) | `ZInQ.RouteK.theta_props`, `theta1`, `theta2`, `theta2_isCoprime`, `theta3`, `theta4` | proved |
| `route-k/slot-lemma.md` (Dirichlet + CRT) | `ZInQ.RouteK.exists_prime_slot`, `exists_prime_slot_bits` | proved |
| `route-k/slot-conditions.md` (structure: the slot data) | `ZInQ.RouteK.Slots`, `Slots.sum_q₀_sym`, `Slots.card_primes`, `Slots.rev_q₀`, `Slots.rev_rP`, `Slots.rev_rT` | statement formalized |
| `route-k/slots.md` (L3: the slots exist) | `ZInQ.RouteK.exists_slots`, `exists_slots_of_admissible`, `exists_multiplier_and_slots` | proved |
| `route-k/realization.md` (L5: both curves reduce to the base) | `ZInQ.RouteK.Slots.selmerCertified_d₁`, `Slots.selmerCertified_d₂`, `Inputs`, `Slots.d₁`, `Slots.d₂`, `Slots.d₁_eq'`, `Slots.d₂_eq`, `Slots.squarefree_d₁`, `Slots.squarefree_d₂`, `Slots.d₁_mod`, `Slots.β_dvd_d₁`, `selmerCertified_of_primeCfg` | proved |
| `route-k/descent-lemma.md` (DL) | `ZInQ.RouteK.descent_lemma`, `inputs_of_admissible` | proved |
| `route-k/points-pole-solubility.md` (L6) | `ZInQ.RouteK.poleSoluble_of_points`, `exists_multiplier_bits` | proved |
| `route-k/pole-completeness-from-cr3.md` | `ZInQ.poleCompleteness_of_certifiedRank` | proved |
| `main/certified-rank.md` (CR₃, def; hypothesis, not proved here) | `ZInQ.CertifiedRank` | statement formalized (hypothesis) |

New source file: `sources/route-k-locators.md`. It holds locators for `docs/research/slot-k.md`
§§1.1–2.5 and §§4.1–4.2, `descent-alt.md` §4.1 (Proposition 0), `rv-route-k.md` §§4.1–4.3 and
`tyz-5b.md` §§1–5, and citations for Kriz, Tian–Yuan–Zhang, Gross–Zagier–Kolyvagin (manuscript
Lemma 5.5) and Poonen–Stoll (manuscript Lemma `lem:corank`). The research notes are labelled as
project-authored specifications.

Article ids were generated with `autoform migrate article-ids blueprint --json` and inserted by hand
into the new files only. `--write` was not used. No implementation notes were written: every new
article is proved or is a stated definition.

## Articles changed

| Article | Lean names | Change |
| --- | --- | --- |
| `main/pole-completeness.md` | `ZInQ.PoleCompleteness`, `ZInQ.polePoly`, `ZInQ.PoleSoluble`, `ZInQ.poleS0` | The polynomial is the Route K one: `T₁ = A(A−e)(A+e)`, `T₂ = A(Az²−eH)(Az²+eH)`, and the curves are named. One sentence says the manuscript uses `A+3e`, `Az²+3eH` and derives PC from RC by a simultaneous descent. It says that PC is no longer a hypothesis and links the CR₃ ⇒ PC article in prose. Still `declaration: def` (see the first correction below). |
| `main/main-theorem.md` | as before, plus `..._of_poleCompleteness` | The hypotheses are H_min, CR₃, 22P. It depends on target, H_min, CR₃, 22P. The proof depends on assembly, PC from CR₃, 22P ⇒ SR, catalogue instance. One sentence covers the PC variant. |
| `main/README.md` | — | The PC paragraph now places CR₃ and links the Route K chapter. The closing sentence lists H_min, CR₃ (or PC), 22P (or 22P₂). |
| `multiplication/abscissa-parity.md` | `ZInQ.Mult.abscissa_val_even` | Curve `y² = x(x−ℓ)(x+ℓ)`. `p ≠ 3` is gone, matching the Lean statement. The sketch uses the ultrametric equality at every prime and notes that the manuscript's curve needs `p ≠ 3`. |
| `multiplication/pole-obstruction.md` | unchanged | Curves `C_e`, `C_{eH}` with `x + ℓ`. "(p ≠ 3 because p ∉ S₀)" is removed. One sentence says that this is Lemma 5.1 for the Route K polynomial, with the same statement and the same `S₀`. |
| `multiplication/README.md` | — | Curves `x + ℓ`. PC is now proved from CR₃ in the Route K chapter. The link title of abscissa parity is updated. |
| `syntax/templates/template-pole.md` | unchanged | `T₁`, `T₂` are the Route K ones. One sentence notes the manuscript's factors. |
| `roadmap/README.md` | — | The preface names CR₃ instead of PC among the hypotheses. The chapter list adds Route K, last, next to the progressions chapter, which likewise proves a former hypothesis. |
| `coverage/README.md` | — | Section 5 and Section 5.1 rows: Theorem 5.2 is PC for the Route K polynomial, proved from CR₃. The restricted converse is replaced by Route K, with links to DL and CR₃. Dispositions are unchanged. |
| `sources/multiplication-locators.md` | — | The pole predicate and PC locators note that the blueprint uses the `x + ℓ` polynomial and that PC is proved from CR₃. |

## Statement corrections and decisions

1. **`main/pole-completeness.md` stays a definition.** The task asked for `proof: formalized` with
   `lean: ZInQ.PoleCompleteness, ZInQ.poleCompleteness_of_certifiedRank`. That would create a cycle:
   - the article defines `Q_pole` and `Φ`;
   - L6 needs Φ to be stated, so it depends on this article;
   - a proof of PC depends on L6.

   So the article follows the precedent of `catalogue-bound.md`/`catalogue-instance.md` and
   `mordell-weil.md`/`mordell-weil-from-descent.md`:
   - it is the `def` of the statement PC, with `lean:` naming the definitions it states;
   - the theorem is `route-k/pole-completeness-from-cr3.md`;
   - the article says in prose that PC is proved from CR₃ and links that theorem.

   Two alternatives would avoid the cycle:
   - split `Q_pole` and Φ into their own article, and make `main/pole-completeness.md` the theorem
     "assume CR₃; then PC";
   - but then that theorem and `pole-completeness-from-cr3` would state the same thing.

   If the lead prefers the split, the work is: move the polynomial to a new `def` article, repoint
   `pole-obstruction`, `template-pole`, `pole-semantics`, L6 and `squarefree-part` to it, and fold
   `pole-completeness-from-cr3` into `main/pole-completeness.md`.
2. **CR₃ is in `main/`** (`main/certified-rank.md`), next to the other hypotheses of the main
   theorem, like `prime-pattern.md`. The Route K README links it in prose. It is stated exactly as
   the Lean `CertifiedRank` reads:
   - `d > 0` squarefree, `d ≡ 5 (mod 8)`;
   - `a` a squarefree divisor of `d` with `|a| ≡ 7 (mod 8)`;
   - 8 solutions, and a solution with first coordinate `(s(a), 0, [p ∣ a])`;
   - conclusion: a point with `x ≠ 0` and `x/a` a square.

   The article says what CR₃ rests on:
   - Proposition 0;
   - rank one, either from TYZ Theorem 3.5(2) (in the form its proof gives) together with the row-5b
     computation of tyz-5b and GZK, or from Kriz's 2-converse (an unrefereed preprint) with the
     corank lemma;
   - surjectivity of the Kummer map, and the fact that the class `a` is not a torsion class.
3. **DL (`descent-lemma.md`) states the Lean form.** The note's DL says "a squarefree `n` with
   `β ∣ n` such that `C_n`, `C_{nθ}` carry a certificate", where a certificate may be torsion or
   Selmer. The article states what the Lean statement says:
   - Selmer certificates for `(|n|, β)` and `(|nθ|, β)`;
   - `n` and `nθ` squarefree;
   - `|n| ≡ |nθ| ≡ 5`, `|β| ≡ 7 (mod 8)`.
4. **The multiplier lemma is stated in the Lean strong form.** It holds for every `B ≠ 0`, with
   `m > 0` (`exists_multiplier_pos`); the admissible case is the "in particular". The proof sketch
   is the Lean proof: `m = 2^f m₀`.
5. **(θ1)–(θ4)** are stated as in the note; the article adds that (θ4) holds at `p = 2` too. The
   sketch is the Lean integer form, `ma = βs²`, `θc² = M² − ma`, with the local lemma used at
   `j = 3` and `j = 1`. It is not the note's `p`-adic argument.
6. **The slots are split in two.** `slot-conditions.md` (the structure `Slots`) and `slots.md`
   (existence) are separate articles. As one node, the Lean span was 217 lines and drew a
   `node-too-large` warning under `audit --lean-root`. The conditions are written in the
   symmetric form that Lean records, and the article notes that `[q₀/ℓ] = 0` is never used.
7. **Realization.** The hypotheses of `Inputs` are stated in residue bits: `[β/ℓ] = 0` and
   `[θ/p] = 0`. The article states `d₁ ≡ 5 (mod 8)`, which has its own lemma (`d₁_mod`), and
   notes `d₂ ≡ 5` in parentheses (it is derived inside DL). Step 5 of the sketch follows Lean and
   uses no Jacobi symbols.
8. **The selmer-system article mentions Proposition 0 only as context.** It is not formalized, and
   it enters only through CR₃.

## Articles added beyond the task's list

- `residue-bits.md` and `reciprocity-bits.md`: the bits `[a/p]` are used by four articles, and the
  configuration of a number needs reciprocity to be well defined (Proof depends on).
- `prime-configuration.md`: the definitions `natConfig`, `natClass` and `SelmerCertified`. CR₃, the
  realization and DL state their results through them.
- `slot-lemma.md`: the Dirichlet and CRT step, which `slots.md` uses for each slot.
- `slot-conditions.md`: see correction 6.

## Problems

- None blocking.
- `audit --lean-root` keeps its two old errors, in files outside this task.

## Suggestions for the next agent / the lead

- Decide on correction 1: keep the precedent, or split out the polynomial.
- `main-theorem.md` still does not list `..._of_nodeCheck`. It is not credited anywhere; it could
  join the `lean:` list.
- `construction/` and upstream `lean/ZInQ/PolePolynomial.lean` still encode `x + 3ℓ`; pole-switch
  reported this already.
- `sources/manuscript.md` describes Theorem 5.2 as the hypothesis from which Section 5.1 derives
  PC. That is accurate for the manuscript, so it was left alone.
- If Proposition 0 is ever formalized, a `route-k/proposition-0.md` article can sit between
  `selmer-system.md` and `main/certified-rank.md`. CR₃ would then be restated with genuine Selmer
  groups.
