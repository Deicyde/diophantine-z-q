# flt-cqj: porting FLT's cyclic-quotient bijection, and what was done instead

## Verdict

1. **The port could not be done on this host. The source is missing.** The cloud worker (cdd05f1c) committed
   only 250 of the 661 modules in the proof cone of Anthropic FLT's
   `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`. Of the other 411, the
   worker reports that 224 built and 187 did not. None of the 411 is on this host or in any git ref (§3), and this
   task may not run network commands. `cyclicQuotientJBijOn_proof : CyclicQuotientJBijOn` is therefore **not
   proved**, and `ZInQKernel/Contrib/OneProof/CyclicQuotientJ.lean` was not created. Which of the 15 failing
   modules fail, and why, cannot be checked: their sources are not here and the worker did not record their names.
2. **The task's premise about the fold is wrong.** No X0Transitive → IgusaGL2 route exists in the tree, and
   none can exist: Igusa's full `GL₂(ℤ/N)` image is strictly stronger than transitivity on cyclic subgroups. The
   tree has only the converse route, `CurveSplit.x0Transitive_of_igusaGL2` (`OneProof/H/TailR.lean:1592`). It is
   used once, in `textbookLeaves6_of_open7` (`TailX.lean:239`), to fill the field `x0Transitive` of
   `OpenTextbookLeaves6`. So even a proof of `CyclicQuotientJBijOn` could not discharge `igusaGL2` through
   `autofold.py`, which fills a field with a term of that field's type. A **bypass fold** is needed instead, and
   it has been built and checked (point 4).
3. **New result (compiled, standard axioms only): `X0Transitive` from a strictly smaller statement.**
   `ZInQKernel/Contrib/CloudB2X0Transitive/ModularEquation.lean` proves
   `FltCqj.x0Transitive_of_modularEquationGeneric : FltCqj.ModularEquationGeneric → ZInQ.RLeaf.X0Transitive`.
   `ModularEquationGeneric` is the classical modular equation for the generic curve: for every cyclic subgroup
   `C` of order `N` of `E_j` over `\overline{ℚ(j)}`, `Φ_N(j(E_j/C), j) = 0`. Here `j(E_j/C)` is FLT's
   iterated-Vélu `cyclicQuotientJ`, and `Φ_N` is FLT's `ModularPolynomialData`. This is only the `MapsTo` half
   of `CyclicQuotientJBijOn` at `K = ℚ`, `L = \overline{ℚ(j)}`, `E = E_j`
   (`modularEquationGeneric_of_bijOn`). The rest of the bijection, surjectivity and injectivity, is proved here
   (§2).
4. **Bypass fold, checked.** `scratch/flt-cqj/FoldBypassModEq.lean` is written by
   `scratch/flt-cqj/gen_bypass.py`. It compiles, and its `frozenTarget_cqj : ZInQ.FrozenTarget` has exactly the
   hypotheses of `ZInQ.OneProof.frozenTarget` except that `igusaGL2 : ZInQ.RLeaf.IgusaGL2` becomes
   `modularEquationGeneric : FltCqj.ModularEquationGeneric`. `FoldBypass.lean` is the same fold with
   `cyclicQuotientJBijOn` as the new field. Both print only `[propext, Classical.choice, Quot.sound]`. So Igusa's
   theorem can leave the single proof in favour of the modular equation, which FLT's proof covers as its
   `MapsTo` half.

## 1. Statements

| name | where | status |
|---|---|---|
| `ZInQ.RLeaf.IgusaGL2` (field `igusaGL2`, `OpenTextbookLeaves11`) | `Contrib/RLeaf/IgusaSL2.lean:120` | open LEAF (Igusa 1959); used only to get `X0Transitive` |
| `ZInQ.RLeaf.X0Transitive` | `Contrib/RLeaf/IgusaX0.lean:69` | proved from `ModularEquationGeneric` (this task) and from `CyclicQuotientJBijOn` (cloud worker) |
| `CyclicQuotientJBijOn` | `Contrib/CloudB2X0Transitive/Bridge.lean:61` | FLT's statement at universe 0; proved in Lean upstream (anthropics/fermats-last-theorem@6e837e75, Lean 4.33.1), **not ported** |
| `FltCqj.ModularEquationGeneric` (new) | `Contrib/CloudB2X0Transitive/ModularEquation.lean` | leaf candidate, implied by `CyclicQuotientJBijOn` |

Verbatim copies of `CyclicQuotientJBijOn` and `X0Transitive` are checked against the constants by `Iff.rfl` in
`scratch/flt-cqj/Statement.lean` (compiles).

**Kind of the new leaf.** Over `ℂ`, `Φ_N(X, j(τ)) = ∏ (X − j(γτ))`, the product running over the `ψ(N)`
primitive matrices of determinant `N` modulo `SL₂(ℤ)` (Cox, *Primes of the form x² + ny²*, Thm 11.18; Lang,
*Elliptic functions*, Ch. 5 §2, Thm 3; numbers UNVERIFIED). The curves `ℂ/Λ'`, with `Λ' ⊃ Λ_τ` of cyclic index
`N`, are the quotients `E_τ/C`, and Vélu's formulas compute them up to isomorphism (Vélu, C. R. Acad. Sci. Paris
273 (1971), UNVERIFIED). The generic case follows by embedding `\overline{ℚ(j)}` in `ℂ` with `j` sent to a
transcendental value; FLT's `cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed` gives the base-change
compatibility. So `ModularEquationGeneric` is a **consequence of published theorems**, not a single printed
display. Under strict accounting it is flagged "pending reading", like `CyclicQuotientJBijOn` itself. It is
weaker than the FLT theorem, which has been proved in Lean (on Lean 4.33.1).

**Sanity check of the definitions the leaf uses** (computed, 30 inputs). `scratch/flt-cqj/velu_check.py`
re-implements `cyclicQuotientJ` from the Lean text: the steps `kernelXSet`, `coKernelXSet`,
`xVeluCurve`/`twoVeluCurve`, `xVeluX`/`twoVeluX`, `subgroupOfX`, then `cqjStep` with `ℓ = minFac`, and finally
`j = c₄³/Δ`. It compares the result with PARI's `ellisogeny` on 30 random curves over `F_p`, with
`N ∈ {2,…,10,12}`. For prime `N` it also checks `Φ_N(j_lean, j(E)) = 0` with `polmodular`. All 30 agree
(`velu_check-output.txt`). The replica follows the Lean text by reading; it is not machine-checked.

## 2. The proof (`ModularEquation.lean`, 473 lines, no sorry)

* **Counting glue.**
  * `J_eq`: `J(N) = #{a ∈ (ℤ/N)² | ord a = N} = ψ(N) φ(N)`. The proof uses CRT multiplicativity (`J_mul`), the
    prime-power count `J(p^k) + p^{2(k−1)} = p^{2k}` (`J_prime_pow`, via `#{x ∈ ℤ/n | ord x ∣ d} = d` from
    `∑_{e∣d} φ(e) = d`), and FLT's ported `dedekindPsi_mul_of_coprime` and `dedekindPsi_prime_pow`.
  * `ncard_cyclic_mul_totient`: in a finite abelian group, `#{cyclic H, |H| = N} · φ(N) = #{a | ord a = N}`.
  * `ncard_cyclic_sq`: `(ℤ/N)²` has `ψ(N)` cyclic subgroups of order `N`.
  * `ncard_cyclic_ejBar`: so does `E_j`, by T36 (`ZInQ.RLeaf.t36_torsionStructure`, proved). Every subgroup of
    order `N` lies in `E_j[N]`.
* **`bijOn_of_modularEquation`.**
  * The image of `C ↦ j(E_j/C)` is Galois-stable, by FLT's ported equivariance theorem with `E_j^σ = E_j`
    (`cyclicQuotientJ_galPt`).
  * `Φ_N(X, j)` is irreducible over `ℚ(j)` (FLT, ported), so `Aut(\overline{ℚ(j)}/ℚ(j))` is transitive on its
    roots (`Normal.minpoly_eq_iff_mem_orbit`). Hence the map is onto the roots.
  * `Φ_N(X, j)` is separable, since it is irreducible in characteristic 0, and has degree `ψ(N)`. So it has
    `ψ(N)` roots. The source also has `ψ(N)` elements, so the map is injective (`Set.injOn_of_ncard_image_eq`).
* **`x0Transitive_of_modularEquationGeneric`.** This is the argument of the cloud worker's `Bridge.lean`, run
  on this bijection.
* **`modularEquationGeneric_of_bijOn : CyclicQuotientJBijOn → ModularEquationGeneric`.** This shows the new
  statement is the smaller one.

Checks (all VERIFIED):
* `lake build ZInQKernel.Contrib.CloudB2X0Transitive.ModularEquation`: success (9575 jobs).
* `#print axioms` for `x0Transitive_of_modularEquationGeneric` and for `modularEquationGeneric_of_bijOn`:
  `[propext, Classical.choice, Quot.sound]`.
* `lake build ZInQKernel.Contrib.CloudB2X0Transitive.Reduction`, the cloud worker's 250 vendored modules on fork
  main w71 after the merge: success (9574 jobs).
* `#discharges` with `Main`, `Discharges` and the new module (`scratch/flt-cqj/DischargesCheck.lean`) reports
  "65 open hypotheses, 1200 theorems checked, 3 discharge one". The three are other contributions already in
  `Main`'s closure. None comes from this module, as expected: no theorem here has type `IgusaGL2`.

## 3. Why the port is blocked

* Searches on this host:
  * `find / -xdev` for `Thm_WeierstrassCurve_bijOn*`, `*cyclicQuotientJ_isRoot*` and `fermats-last-theorem*`:
    no hits.
  * `git log --all -S "bijOn_cyclicQuotientJ_isRoot_modularPolynomial"`: only cdd05f1c, the statement in
    `Bridge.lean`.
  * Every path ever committed under an `AnthropicFLT/` directory, in any ref: 389 files. They are
    CloudB2X0Transitive's 250 `.lean` files plus metadata, and CloudW02Connectedness's 135.
* The cdd05f1c commit message: "That work-in-progress is not committed." Its report gives 15 failing frontier
  modules, about 10 Mathlib API changes, and 24 names in 3 bijOn-only files that collide with Tau Ceti. None of
  these modules or names is listed anywhere in the repository.
* The task forbids `curl` and every other network command. The upstream files at
  anthropics/fermats-last-theorem@6e837e75 therefore cannot be fetched.
* **What a run with the source would need:**
  1. Fetch the 411 missing cone modules at 6e837e75.
  2. Relocate their imports as the 250 committed ones were (SOURCE_MANIFEST.json).
  3. Namespace the FLT copies of the 24 colliding names.
  4. Fix the ~10 API changes.
  5. Prove `ModularEquationGeneric` as `(bijOn …).mapsTo`; `modularEquationGeneric_of_bijOn` already does this
     step.

  One collision risk is already ruled out. `FoldBypass*.lean` imports `ZInQKernel.OneProof.Main` together with
  the CloudB2 vendor tree and the new module, and compiles. So the committed FLT modules clash with nothing in
  the single proof's closure.

## 4. Fold (for the integrator)

* `scratch/flt-cqj/autofold.json` deliberately has no `discharges` key. `autofold.py` cannot express this fold,
  and without the key it stops instead of writing an empty fold. The file records the bypass spec instead.
* `python3 scratch/flt-cqj/gen_bypass.py OUT.lean modeq` writes the bypass.
  * It copies the 48 declarations of `TailX`…`TailZ32` that read `OpenTextbookLeaves7`…`11`, each with suffix
    `_cqj`.
  * In those bundles it replaces `igusaGL2` by `modularEquationGeneric`.
  * It sets `x0Transitive := FltCqj.x0Transitive_of_modularEquationGeneric t.modularEquationGeneric` in
    `textbookLeaves6_of_open7_cqj`.
  * It ends with `sixContactMin_of_open26_cqj` and `frozenTarget_cqj`. Everything else is copied verbatim.
* The fold does not change the GLUE counts: one LEAF (Igusa) is replaced by one leaf candidate (the modular
  equation). Once a port supplies a proof of the leaf, a one-field fold on top of the bypass removes it.
* The bypass fold was compiled as a scratch file only. It was not folded into `OneProof/H`, as this task's rules
  require.

## 5. Files

* `ZInQKernel/Contrib/CloudB2X0Transitive/ModularEquation.lean` (new).
* `scratch/flt-cqj/`:
  * `Count.lean`, `ModEqMain.part`, `assemble.py` → `ModEq.lean`, the scratch form of the module.
  * `Statement.lean`.
  * `gen_bypass.py`, `FoldBypass.lean`, `FoldBypassModEq.lean`.
  * `DischargesCheck.lean`, `autofold.json`.
  * `velu_check.py`, `velu_check-output.txt`.
  * `log.md`.
* No vendored file was modified. The new module is new code that calls the vendored theorems (Apache-2.0,
  `Vendor/AnthropicFLT/LICENSE`, `NOTICE.upstream`).
