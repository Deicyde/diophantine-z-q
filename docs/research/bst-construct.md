# bst-construct: Berger's `B_st = B_max[log [p̃]]` inside `B_dR`, and the leaves of `r11r12` over it

Task bst-construct, 2026-11-16. Base: wip/pb-fix2 401a75236, merged with origin/main 0caafe661. Lean:
`ZInQKernel/Contrib/OneProof/BergerBst.lean`. It imports `ZInQKernel.Contrib.OneProof.PanBergerPrinted` and
`ZInQKernel.Contrib.OneProof.DSThm965Weak`, not `Main`. It is generated from `scratch/bst-construct/Bst.lean` by
`scratch/bst-construct/mkcontrib.py`. Results log: `scratch/bst-construct/log.md`. This is model work; no person
has reviewed it.

Marks used below:

* **VERIFIED**: compiled here, or read in a named file.
* **STANDARD**: published, with an exact reference.
* **UNVERIFIED**: a theorem number or wording given from memory. This host has no network, and I have not read
  Berger 2002 §1.2.

## 1. Result

**`r11r12 : HDec.PkgI4.PanBerger` is discharged by `panBerger_of_printedB_weak`.** It uses two leaves,
`PanPrintedB` (Pan 2022, Thm 1.0.4) and `BergerPrintedB` (Berger 2002, Thm 0.7), plus the bundle's existing fields
`dsThm965Weak` and `dsThm966`. Both leaves state potential semistability over **Berger's period rings built in
Lean inside Mathlib's `B_dR`**:

* `A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf, a_n → 0}`;
* `B_max = A_max[1/p][1/t]`;
* `B_st = B_max[log [p̃]]`.

"Semistable" is Fontaine's admissibility, `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`. There is no
abstract `B_cris[X]` and no dimension normalization any more. "De Rham" at `K = ℚ_p` keeps pb-fix2's form
`dim_{ℚ_p} (B_dR ⊗ V)^{G_{ℚ_p}} = dim V`, which is Fontaine's `dim_K D_dR = dim V` with `K = ℚ_p`.

I rate both leaves **printed form** (§3), so the fold is **−1 GLUE**: the composite `r11r12` (GLUE) is replaced by
two published leaves flagged unread. All of this compiles with only the standard axioms (VERIFIED, §4).

The deeper facts about these rings that the printed definitions presuppose are **proved in Lean**, with no new
hypothesis:

* `B_max^+`, `B_max` and `B_st` are `G_{ℚ_p}`-stable (`bmaxPlus_stable`, `bmax_stable`, `bst_stable`).
* `σ(log [p̃]) = log [p̃] + log [u_σ]`, with `σ(p̃) = p̃·u_σ` and `u_σ^♯ = 1` (`bdrAct_logPTilde`, `exists_uSigma`).
* `log((1+y)(1+z)) = log(1+y) + log(1+z)` in `B_dR^+` for `y, z ∈ ker θ` (`logPlus_add`).
* `log [ε] ∈ A_max` for `ε^♯ = 1` (`logTeich_mem_amax`), so `t ∈ B_max^+` and `B_max = B_max^+[1/t]` inverts an
  element of `B_max^+`.
* **`t ≠ 0`.** `log [ε] ≠ 0` for every `ε ≠ 1` with `ε^♯ = 1`, and such `ε` exist, so the inverted `t` is a
  genuine unit of `B_dR` (`logTeich_ne_zero`, `exists_t_ne_zero`).
* `A_max` does not depend on the choice of generator of `ker θ` (`amaxOf_eq_amax`).
* The trivial representation is `B`-admissible for every `B ⊆ B_dR` and every `H` (`isAdmissible_trivial`), so
  potential semistability is non-vacuous.
* `B_dR^+ → B_dR` is injective (`toBdR_injective`).

Two classical theorems are isolated as named Props (§3.3). **The fold uses neither:**

* `LogPTildeTranscendental`: `log [p̃]` is transcendental over `B_max`. From it, `B_st ≅ B_max[X]`
  (`bstEquivPolynomial`) is proved.
* `FontaineBstInvariants`: `dim_{ℚ_p} B_st^{G_K} = [K_0 : ℚ_p]`. From it, admissibility is shown to be pb-fix2's
  normalization `dim_{ℚ_p} D_st,K = [K_0 : ℚ_p] · dim V` (`isSemistableB_iff_K0`).

## 2. The construction (VERIFIED: compiled, `scratch/bst-construct/Bst.lean` §§1-12)

All definitions are in namespace `HDec.PkgI4.BergerBst`.

* **The setting.** Mathlib defines `A_inf = W(𝓞_ℂ_p♭)` (`WittVector`, `PreTilt`) and
  `B_dR^+ = BDeRhamPlus 𝓞_ℂ_p p`, the `ker θ`-adic completion of `A_inf[1/p]`. `B_dR` is pkg-I4's `BdR p`, which
  is Mathlib's `BDeRham` (by `rfl`), with pkg-I4's `G_{ℚ_p}`-action `bdrAct`.
* **`psEval I hx : A⟦X⟧ →+* Â_I`** for `x ∈ I`. It evaluates a power series at `x` as the `I`-adic limit of
  its truncations. It is a ring hom (proved), equivariant for maps of adic completions (`adicMap_psEval`).
* **`Amax`** is the image in `B_dR^+` of the power series over `A_inf` whose coefficients tend to `0`
  `p`-adically (`restricted`, a subring: proved), evaluated at `ω/p`.
  * Here `ω = ξ = p − [p̃]`, with `ker θ = (ξ)` from bdr-kertheta.
  * `amaxOf_eq_amax`: every generator of `ker(θ : A_inf → 𝓞_ℂ_p)` gives the same ring. For example
    `[p̃] − p` works.
* **The logarithms.** `logPlus hy = log(1+y) = Σ_{n≥1} (−1)^{n+1} y^n/n` for `y ∈ ker θ`, as a
  `ker θ`-adic series in `B_dR^+`.
  * `logTeich h = log [ε]`, for `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1`.
  * `logPTilde = log [p̃] := log([p̃]/p)`, since `[p̃]/p − 1 = −ξ/p ∈ ker θ`. Here `p̃` is bdr-kertheta's `pFlat`,
    with `p̃^♯ = p`.
* **`BmaxPlus = adjoin_ℚp (A_max)`.** This is `A_max[1/p]`, since `1/p ∈ ℚ_p`.
* **`Bmax = adjoin_ℚp (A_max ∪ {log[ε]⁻¹ : ε^♯ = 1, ε ≠ 1})`.** This is `B_max^+[1/t]`.
  * Each `log [ε]` is `a·t` with `a ∈ ℤ_p ∖ 0` (STANDARD).
  * Inverting all of them avoids choosing `ε`, as pb-bypass's `B_cris` also does.
  * `Ring.inverse` is the inverse in the field `B_dR`.
* **`Bst = adjoin_ℚp (A_max ∪ tInv ∪ {log [p̃]})`.** `bst_eq_adjoin` proves `Bst = B_max[log [p̃]]`, the
  `B_max`-algebra generated by `log [p̃]`, by `rfl`.
* **Fontaine's functor.** For a `ℚ_p`-subalgebra `B ⊆ B_dR` and `H ≤ G_{ℚ_p}`:
  * `fixedSub B H = B^H`, a `ℚ_p`-subalgebra of `B`;
  * `dB B H ρ = (B ⊗_{ℚ_p} V)^H`, the action computed in `B_dR ⊗ V`, a `B^H`-submodule;
  * `IsAdmissible B H ρ :⇔ finrank_{B^H} (dB B H ρ) = finrank_{ℚ_p} V`.
* **The predicates.** `IsSemistableB K ρ := IsAdmissible (Bst p) K.fixingSubgroup ρ`;
  `IsPstB ρ := ∃ K finite, IsSemistableB K ρ`; `LocalIsPstB` is as pb-fix2's `LocalIsPstU`, with a model over a
  finite `E ⊆ ℚ̄_p`.

The leaves:

```lean
def BergerPrintedB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstB p n ρ

def PanPrintedB : Prop :=   -- pb-fix2's PanPrintedU with LocalIsPstU replaced by LocalIsPstB
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstB p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) → ∃ N k χ g, … (verbatim PanPrintedU)

theorem panBerger_of_printedB_weak (hP : PanPrintedB) (hB : BergerPrintedB)
    (hW : DS965Weak.DSThm965Weak) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) : PanBerger
```

`panBerger_of_printedB` is pb-fix2's proof verbatim: Berger is applied to `ρ^∨`, and Berger's output is Pan's
input on the same `ρ^∨`. The `_weak` form converts the current bundle's `dsThm965Weak` with ds965-weak's
`dsThm965_of_weak`.

### Proof notes

* **`logPlus_add`.** Fix `N` and put `Y = yT`, `Z = zT`, `W = Y + Z + YZ` in `A[T]`. Let `P_N` be the truncated
  logarithm.
  * `T^N` divides `Q = P_N(W) − P_N(Y) − P_N(Z)`. The proof: `Q(0) = 0`, and `(1+X) P_N' = 1 − (−X)^{N−1}`, so
    `(1+Y)(1+Z) Q'` is divisible by `T^{N−1}`. Then `1 + T·V` is invertible modulo `T^{N−1}`, and `j+1` is
    invertible in `A_inf[1/p]`.
  * `Q` lies in Mathlib's Rees algebra `reesAlgebra (ker θ)`, so `Q(1) ∈ (ker θ)^N`.
* **`logTeich_ne_zero`.** Write `[ε] − 1 = ξ^s w` with `θ(w) ≠ 0` and `s ≥ 1` (pb-sanity's `ξ`-adic
  separatedness of `A_inf`, copied). Modulo `(ker θ)^{s+1}`, `log [ε] ≡ [ε] − 1`, which is nonzero there.
* **`logTeich_mem_amax`.** Write `[ε] − 1 = ξc`. Then
  `log [ε] = Σ (−1)^{n+1} (p^n/n) c^n (ξ/p)^n`, and `p^k ∣ p^n/n` in `ℤ_p` once `n ≥ 2k`
  (`exists_logCoeff`, `val_bound`).
* **`bst_stable`.** By `bdrAct_evalB`, `σ(Σ a_k x^k) = Σ σ(a_k) σ(x)^k`.
  * `σ(ξ) = ξc` gives the stability of `A_max` (by rescaling).
  * `σ(log [ε]) = log [σε]` gives the stability of the set of inverted `t`'s.
  * `σ([p̃]/p − 1) = y + z + yz`, with `y = [u_σ] − 1` and `z = [p̃]/p − 1`, together with `logPlus_add` gives
    `σ(log [p̃]) = log [u_σ] + log [p̃]`. Since `log [u_σ] ∈ A_max`, this lies in `B_st`.
  * `u_σ` exists by bdr-kertheta's `dvd_of_coeff_zero`.

## 3. Ratings

### 3.1 `bergerPrintedB`: printed form

Source: Berger, Invent. Math. 148 (2002), Théorème 0.7 (= Cor. 5.22 of the published version, author copy
pp. 6 and 52; = arXiv:math/0102179v3 Thm 0.6 = Thm 5.19; locators R11). It says: every de Rham representation of
`G_K` is potentially semistable. The leaf applies it at `K = ℚ_p` to the `ℚ_p`-representation `V = E^n`
underlying a continuous `ρ`.

* **The period rings are built as Berger prints them**, as subrings of Mathlib's `B_dR`:
  * `B_st = B_max[log [p̃]]`, `B_max = B_max^+[1/t]`, `B_max^+ = A_max[1/p]`;
  * `A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf → 0}`;
  * `log [p̃] = log([p̃]/p)`, `t = log [ε]`.

  These are genuine Mathlib-based definitions, not abstract structures. Their `G_{ℚ_p}`-stability is proved.
* **Semistable is Fontaine's admissibility**, `dim_{B_st^{G_K}} D_st,K(V) = dim V`, as in Fontaine's formalism of
  `(ℚ_p, G)`-regular rings. Berger writes `dim_F D_st(V)` with `F = Frac W(k) = K_0`, using Fontaine's theorem
  `B_st^{G_K} = F`, so the two definitions are the same object.
  * In Lean, `isSemistableB_iff_K0` proves that admissibility equals the `ℚ_p`-dimension form
    `dim_{ℚ_p} D_st,K = [K_0 : ℚ_p] · dim V`, with pb-fix2's `K_0 = W(k_K)[1/p]`, given `FontaineBstInvariants`.
  * The leaf itself does not depend on that theorem: it uses `B_st^{G_K}` directly.
* **De Rham** at `K = ℚ_p` is `dim_{ℚ_p} D_dR(V) = dim V`. This is Fontaine's and Berger's `dim_K D_dR = dim V`
  with `K = ℚ_p`.
* **Flags carried in kinds.tsv (unread):**
  1. Berger's §1.2 wording of `A_max` and `B_max` is recalled, not read (UNVERIFIED):
     * coefficients in `Ã^+ = A_inf` tending to `0` `p`-adically;
     * `B_max^+ = A_max[1/p]`;
     * `B_max = B_max^+[1/t]`.

     If Berger instead takes coefficients `a_n ∈ B̃^+ = A_inf[1/p]` tending to `0`, the ring is the same:
     finitely many denominators are cleared by a power of `p`.
  2. Admissibility is over `B_st^{G_K}`, not over `F` (see above).
  3. The Springer pagination is UNVERIFIED (as in pb-fix2).

  `t ≠ 0` is proved (`exists_t_ne_zero`), so `B_max ≠ B_max^+` as Berger intends; it is no longer a flag.
* **Not stronger than the print.** It is the theorem for one representation of `G_{ℚ_p}`. The conclusion keeps
  the same model `E`.

### 3.2 `panPrintedB`: printed form, under the eigenform reading

* The leaf is pb-fix2's `PanPrintedU` verbatim, except that "potentially semistable" is computed over Berger's
  `B_st` (`LocalIsPstB`). It keeps the same source, conventions and flags:
  * the eigenform reading;
  * the Burnside form of irreducibility;
  * the JAMS numbering, UNVERIFIED.
* Pan's hypothesis "potentially semistable" is Fontaine's notion. Computing it with Berger's rings and Fontaine's
  admissibility is a printed form of it.
* **Why Pan is restated.** pb-fix2's glue feeds Berger's conclusion into Pan's hypothesis. With Berger now over
  `B_st ⊆ B_dR`, keeping `PanPrintedU` (abstract `B_cris[X]`) would need a comparison of the two `B_st`'s.
  * That comparison is not available: pb-bypass's `B_cris` is the `p`-adic completion of `A_cris^0`, which does
    not map into `B_dR` without the injectivity `B_cris → B_dR`, a Fontaine theorem.
  * It would be an extra GLUE Prop, and the fold would no longer be −1.
* **Any settlement of `PanPrintedU`'s eigenform reading applies verbatim to `PanPrintedB`**, because the two have
  the same conclusion.

### 3.3 Named inputs not used by the fold

| Prop | statement | rating |
| --- | --- | --- |
| `LogPTildeTranscendental` | `Transcendental (Bmax p) log [p̃]` (⇔ `B_max[X] → B_dR` injective, `logPTildeTranscendental_iff`) | published (Fontaine, Astérisque 223 Exp. II §3 for `B_cris`; Colmez for `B_max`; UNVERIFIED numbering); a leaf over genuine definitions, but not needed: `B_st = B_max[log [p̃]]` is a subring by definition, and the admissibility predicates do not see whether `log [p̃]` is transcendental |
| `FontaineBstInvariants` | `dim_ℚp B_st^{G_K} = [K_0:ℚ_p]`, `K_0 = W(k_K)[1/p]` | published (Fontaine's `B_st^{G_K} = K_0`, Astérisque 223 Exp. II/III, UNVERIFIED numbering); dimension form of the print; used only for the normalization comparison `isSemistableB_iff_K0` |

On the transcendence: the task asked to show `log [p̃]` transcendental over `B_max`, or `B_max[X] → B_dR`
injective. It is not proved here.

* Fontaine's proof first reduces to `log [p̃] ∉ Frac(B_max)`, using the `G_{ℚ_p}`-action (which is now proved
  here) and `B_dR^{G_{ℚ_p}} = ℚ_p`.
* The remaining step uses the Kummer cocycle of `p` and needs Fontaine's cohomological input.
* Neither leaf needs it: `bstEquivPolynomial` shows it is only what identifies the subring `B_st` with the
  abstract polynomial ring.

## 4. Deliverables and checks (VERIFIED)

* `ZInQKernel/Contrib/OneProof/BergerBst.lean` (77 KB, no warnings). `lake build ZInQKernel.Contrib.OneProof.BergerBst`
  succeeds. The file contains no `sorry`.
* `python3 scripts/one_proof/sandbox/scan_contrib.py 0caafe661 HEAD` reports `BergerBst.lean: 0 likely hit(s),
  0 possible hit(s)`.
* **Axioms.** `scratch/bst-construct/Axioms.lean` prints 23 declarations, including the glue, the stability
  theorems, `logPlus_add`, `logTeich_ne_zero` and the bridges. All use only `[propext, Classical.choice,
  Quot.sound]` (`axioms-output.txt`).
* **`#discharges`** (`scratch/bst-construct/Discharges.lean` → `discharges-output.txt`):
  ```
  DISCHARGES [OpenResearchLeaves26.r11r12] by HDec.PkgI4.BergerBst.panBerger_of_printedB_weak
    still assumes: [HDec.PkgI4.BergerBst.PanPrintedB,
   HDec.PkgI4.BergerBst.BergerPrintedB,
   DS965Weak.DSThm965Weak,
   ZInQ.Contrib.HodgeSplit.DSThm966]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 56 open hypotheses, 3354 theorems checked, 12 discharge one
  ```
  (`panBerger_of_printedB`, with `DSThm965` in place of `DSThm965Weak`, also discharges it.)
* **Autofold.** The spec is `scratch/bst-construct/autofold.json`, field `r11r12`. The proof is
  `_root_.HDec.PkgI4.BergerBst.panBerger_of_printedB_weak {n}.panPrintedB {n}.bergerPrintedB {n}.dsThm965Weak
  {n}.dsThm966`. Both leaves have kind `published` and flag `unread: …` (flags as in §3).
  * The dry run (`autofold-dryrun.txt`) reports `strict count: 34/11 on 45 -> 36/10 on 46; strictest 34/11 ->
    36/10`.
  * Its output, with the first line stripped, is `FoldDryRun.lean`. It compiles, and `sixContactMin_of_open36`
    uses only the standard axioms (`folddryrun-output.txt`).
* **Reproduce** from the repository root:
  ```
  python3 scratch/bst-construct/mkcontrib.py      # regenerates the contribution from Bst.lean
  lake build +ZInQKernel.Contrib.OneProof.BergerBst
  lake env lean scratch/bst-construct/Axioms.lean
  lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  lake env lean scratch/bst-construct/Discharges.lean
  python3 scripts/one_proof/autofold.py scratch/bst-construct/autofold.json --dry-run
  ```
  Build note: the `OneProof` closure oleans were copied from another worktree with identical sources (checked
  with `cmp` on all 2801 closure files) and then completed by `lake build`.

## 5. What remains

* Read Berger 2002 §1.2 against `Amax`, `Bmax` and `Bst` (flag 1 of §3.1).
* The two named inputs of §3.3 (Fontaine), if a later consumer needs them. Neither is needed for `r11r12`.
* Locator rows for `bergerPrintedB` and `panPrintedB` in locators.md. That file belongs to other tasks. Proposed:
  R11/R12 as in pb-fix2, with the predicates in `BergerBst.lean`.
* The fold itself (integrator): `autofold.py scratch/bst-construct/autofold.json` on the integration branch. If
  pb-fix2's `PanPrintedU`/`BergerPrintedU` spec is folded instead, this spec supersedes it, with the same field
  and the same proof shape.
