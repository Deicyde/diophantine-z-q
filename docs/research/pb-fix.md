# pb-fix: Pan and Berger restated in printed form (repair of pb-bypass)

Task pb-fix, 2026-11-15. Base: pb-bypass c1636db9, fast-forwarded to origin/wip/pb-sanity 9dbaabbd3 (pb-sanity's
report and `PanBergerSanity.lean` are included). Lean: `ZInQKernel/Contrib/OneProof/PanBergerFix.lean`. Results
log: `scratch/pb-fix/log.md`. This is model work and no person has reviewed it.

Marks: **VERIFIED** means compiled here or read in a named file. **STANDARD** means published, with an exact
reference. **UNVERIFIED** means a theorem number or locator given from memory; this host has no network.

## 1. Result

**`r11r12 : HDec.PkgI4.PanBerger` is discharged by `panBerger_of_printedT` from two restated leaves,
`PanPrintedT` (Pan 2022, Thm 1.0.4) and `BergerPrintedT` (Berger 2002, Thm 0.7).** It also uses `DSThm965` and
`DSThm966`, which are already leaves of the same bundle (`OpenResearchLeaves22`). The proof compiles and uses only
the standard axioms (VERIFIED).

I rate both new leaves **printed form**; the reasons are in §3. The review's two objections are repaired:

1. **Berger: the normalization.** pb-bypass's `IsSemistableOver` divided by `dim B_st^{G_K}`. The new
   `IsSemistableOverT` is in the printed tensor form `(B_st ⊗ V^*)^{G_K}` and uses the explicit `[K_0 : ℚ_p]`
   (`K0`). So `BergerPrintedT` is Berger's theorem with Fontaine's definition, with no Fontaine-invariants step.
2. **Pan: transport along `ι_p`.** `PanPrintedT` quantifies over every isomorphism `ι_p : ℚ̄_p ≃+* ℂ` and
   concludes `tr ρ(σ_arith) = ψ(σ) · ι_p⁻¹(a_q(g))`, so it no longer asserts that the coefficients are algebraic.
   The glue proves algebraicity from `DSThm965`/`DSThm966` (through `r14Det_of_printed`, TailT §18). It also
   proves the existence of `ℂ ≃+* ℚ̄_p` (Steinitz).

If both ratings stand, the fold is **−1 GLUE**. The autofold dry run gives strict 46/10 on 56 → 48/9 on 57 and
strictest 45/11 → 47/10. Its output compiles (VERIFIED).

That `B_cris ≠ 0` and that `t` is not nilpotent was already proved by pb-sanity (`nontrivial_bcris`,
`logOf_not_isNilpotent`, … in `ZInQKernel/Contrib/OneProof/PanBergerSanity.lean`; merged here, VERIFIED present).
So `LocalIsPst` and `LocalIsPstT` are not trivially true for a degenerate reason.

## 2. The statements (VERIFIED: copied from the compiled file)

All are in namespace `HDec.PkgI4.PanBergerSplit` and use pb-bypass's `B_st`, `stAct` and `dstSpace`, unchanged.

```lean
def K0 (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p]
    {x : PadicAlgCl p | x ∈ K ∧ ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ x ^ m = 1}

def dstT (K) (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] (Bst p ⊗[ℚ_[p]] Module.Dual ℚ_[p] (Fin n → E))
  -- carrier: {x | ∀ σ ∈ K.fixingSubgroup, TensorProduct.map (stLin p σ) (dualAct p ρ σ) x = x},
  -- dualAct σ f = f ∘ ρ(σ)⁻¹ (the contragredient)

def IsSemistableOverT (K) (ρ) : Prop :=
  finrank ℚ_[p] (dstT p K ρ) = finrank ℚ_[p] (K0 p K) * finrank ℚ_[p] (Module.Dual ℚ_[p] (Fin n → E))
def IsPstT (ρ) : Prop := ∃ K, FiniteDimensional ℚ_[p] K ∧ IsSemistableOverT p K ρ
def LocalIsPstT (n) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=   -- as pkg-I4's LocalIsDeRham
  ∃ E (_ : FiniteDimensional ℚ_[p] E) ρE, (∀ σ, GL.map (algebraMap E _) (ρE σ) = ρ σ) ∧ IsPstT p ρE

def PanPrintedT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstT p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    GaloisRep.DistinctHTWeights (ρ := ρ) p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl p) * ιp.symm (coeff g q)

def BergerPrintedT : Prop :=
  BergerDR fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsPstT p n ρ

theorem panBerger_of_printedT (hP : PanPrintedT) (hB : BergerPrintedT)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) : PanBerger
```

`K0` is `ℚ_p(μ_{prime to p}(K))`. For finite `K/ℚ_p` with residue field `𝔽_q` this is `ℚ_p(μ_{q−1})`, the
maximal unramified subextension: the `K_0` of Fontaine's definition (STANDARD: Serre, *Local Fields* IV §4;
Neukirch II.7.12; numbers UNVERIFIED).

**Proved in the file (VERIFIED, standard axioms, `scratch/pb-fix/axioms-output.txt`):**

| theorem | content |
| --- | --- |
| `panBerger_of_printedT` | `r11r12` from the two new leaves and `DSThm965`, `DSThm966` |
| `panFor_of_printedT` | `PanFor LocalIsPstT` from `PanPrintedT`, `DSThm965` and `DSThm966`. It chooses `ι_p`, an arbitrary `ι_C : ℚ̄ → ℂ` and `ι_L = ι_p⁻¹ ∘ ι_C`, and enlarges `S` by the ramified primes of `ρ` and the primes `≤ Np` |
| `coeff_mem_range` | `a_q(g) ∈ ι_C(ℚ̄)` for `q ∤ Nℓ`, from `r14Det_of_printed` (weights 1 and ≥ 2) |
| `exists_complex_equiv` | `Nonempty (ℂ ≃+* ℚ̄_p)` (Steinitz; copied from g8-tate) |
| `isSemistableOverT_iff` | tensor form ⇔ Hom form `Hom_{G_K}(V, B_st)`, both with the explicit `[K_0 : ℚ_p]` (`dualTensorHomEquiv`) |
| `isPst_iff_T`, `localIsPst_iff_T` | if Fontaine's `dim B_st^{G_K} = [K_0 : ℚ_p]` holds (`BstInvariantsDim`, a hypothesis), pb-bypass's `IsPst`/`LocalIsPst` equal the new predicates, so pb-sanity's checks carry over |
| `isSemistableOverT_trivial_iff` | the trivial character is semistable over `K` in the printed sense ⇔ `dim B_st^{G_K} = [K_0 : ℚ_p]` |
| `isPstT_trivial` | the trivial character is pst, given `BstInvariantsDim` |
| `K0_le`, `finrank_K0_pos`, `finrank_K0_bot` | `K_0 ⊆ K`; `[K_0 : ℚ_p] ≥ 1`; `K_0(ℚ_p) = ℚ_p` |

## 3. Ratings of the new leaves

**`bergerPrintedT`: printed form.** Berger, Invent. Math. 148 (2002), Théorème 0.7 (= Cor. 5.22 of the published
version, author copy pp. 6 and 52; = arXiv:math/0102179v3 Thm 0.6 = Thm 5.19; locators R11): every de Rham
representation of `G_K` is potentially semistable.

* The leaf applies the theorem to the representation `V^* = Hom_{ℚ_p}(E^n, ℚ_p)`, with Fontaine's definitions on
  both sides.
* The conclusion is literally Fontaine's "semistable over some finite `K`": `(B_st ⊗ V^*)^{G_K}` has
  `ℚ_p`-dimension `[K_0 : ℚ_p] · dim V^*`, i.e. `K_0`-dimension `dim V^*`.
* `D_st,K` is a `K_0`-space because `K_0 ⊆ B_st^{G_K}`; pb-sanity proved that inclusion in dimension form.
* Lean's `finrank` is 0 on infinite-dimensional spaces. With the explicit `[K_0 : ℚ_p] ≥ 1` this makes the
  predicate *false*, not true, when `D_st` is infinite-dimensional. Fontaine proves `D_st` is always
  finite-dimensional, so nothing is added in either direction.
* The hypothesis is pkg-I4's `LocalIsDeRham`. Its `Hom_{G}(E^n, B_dR)` is `(B_dR ⊗ V^*)^{G}` by the canonical
  `B ⊗ V^* ≅ Hom(V, B)` (the same linear algebra as `isSemistableOverT_iff`; TailS §15 proves it for its
  `D_dR`). It is normalized by `[ℚ_p : ℚ_p] = 1`, which is Fontaine's definition over `ℚ_p`.
* So the leaf is the printed theorem at one representation, with no step about `B_st^{G_K}`. This settles the
  review's objection.

**`panPrintedT`: printed form, under the eigenform reading.** Pan, JAMS 35 (2022), Thm 1.0.4 (= arXiv:1901.07166v2
Thm 1.0.4 with Conj. 1.0.1; h-a011 §1.1; locators R12; JAMS numbering UNVERIFIED). Pan fixes `ι_p : ℚ̄_p ≅ ℂ` and
uses geometric Frobenius and cyclotomic HT weight −1 (h-a011 §1.1, VERIFIED there). The leaf is his theorem for
each `ι_p`, applied to `ρ^∨`:

* **Hypotheses.** `LocalIsPstT` and `DistinctHTWeights` are computed on the contragredient of the underlying
  space, as `LocalIsDeRham` is, so they are the pst and HT hypotheses for `ρ^∨`. Irreducible, finitely ramified
  and odd hold for `ρ^∨` iff they hold for `ρ`.
* **Conclusion.** Pan gives `ρ^∨ ≅ ρ_{g,ι_p} ⊗ ψ'`, where `tr ρ_{g,ι_p}(Frob_q) = ι_p⁻¹(a_q(g))` for `q ∤ Np`
  and `Frob_q` is geometric (this is the eigenform reading).
* At `σ` an arithmetic Frobenius, `tr ρ(σ) = tr ρ^∨(σ⁻¹) = ψ'(σ)⁻¹ ι_p⁻¹(a_q(g))`. That is the displayed
  identity with `ψ = ψ'⁻¹`. No conjugate eigenform and no algebraicity are needed.
* **What the leaf no longer claims.** The old `PanFor` asked for `α ∈ ℚ̄` with `ι_C(α) = a_q(g)` (algebraicity
  of the Hecke eigenvalues). That is now glue proved from `DSThm965`/`DSThm966`.
* **The one interpretive step** is the reading of "comes from a cuspidal eigenform up to twist", which Pan's
  introduction does not define (h-a011 §1.1). The review named this step and accepted it ("leaves only the
  eigenform reading").
* **Not stronger than the print.** `p ≥ 5` only. `1 ≤ k` is weaker than Pan's regular weight. The statement
  claims nothing about the primes in `S`. The unramifiedness the old template carried is now derived from the
  `FinitelyRamified` hypothesis in the glue.

**Proposed locators.md rows** (not added: locators.md belongs to other tasks).
* R11: `bergerPrintedT` (pb-fix), Berger Thm 0.7 at `V^*`, pst with Fontaine's `[K_0 : ℚ_p]`.
* R12: `panPrintedT` (pb-fix), Pan Thm 1.0.4 at `ρ^∨` with Pan's `ι_p`, conclusion `tr ρ(σ_arith) = ψ(σ) ι_p⁻¹(a_q(g))`.

## 4. Wording fixes

pb-bypass's file has two citation errors:
* Brinon–Conrad "§6.1" for the admissibility formalism should be §5 (Thm 5.2.1).
* Fontaine "Exp. VIII" for "`V` pst iff `V^∨` pst" should be Exp. III, 1.5.

These numbers come from the review and are UNVERIFIED here. The new file's docstrings use the corrected
citations. The task rules forbid editing other files under `ZInQKernel/`, so the fix to `PanBerger.lean` is not
applied: it is the docstring-only patch `scratch/pb-fix/PanBerger-wording.patch` (no constant changes).

## 5. What remains

* **`B_st^{G_K} ⊆ K_0`** (Fontaine) is still not in Lean (pb-sanity §3). The leaves no longer depend on it for
  their meaning. But no representation can yet be shown pst, or not pst, in the printed sense:
  `isSemistableOverT_trivial_iff` shows that even the trivial character needs `dim B_st^{G_K} = [K_0 : ℚ_p]`.
  With that fact as a hypothesis (`BstInvariantsDim`), pb-bypass's and pb-sanity's predicates and results
  transfer through `localIsPst_iff_T`.
* **The eigenform reading in Pan** (§3) is a reading, not a Lean fact.

## 6. Deliverables and reproduction

* `ZInQKernel/Contrib/OneProof/PanBergerFix.lean`. It imports `ZInQKernel.Contrib.OneProof.PanBerger` and
  `ZInQKernel.OneProof.H.TailT`, not `Main`. It has no `#` commands, notation or other build-time code; the
  contribution scan finds 0 hits (VERIFIED).
* `scratch/pb-fix/autofold.json`: field `r11r12`. The proof is
  `panBerger_of_printedT {n}.panPrintedT {n}.bergerPrintedT {n}.dsThm965 {n}.dsThm966`. The new leaves
  `panPrintedT` and `bergerPrintedT` have kind `published`, with "unread" flags giving the locator status and
  what pb-fix restated.
* `#discharges` output (VERIFIED, `scratch/pb-fix/discharges-output.txt`):
  ```
  DISCHARGES [OpenResearchLeaves22.r11r12] by HDec.PkgI4.PanBergerSplit.panBerger_of_printedT
    still assumes: [HDec.PkgI4.PanBergerSplit.PanPrintedT,
   HDec.PkgI4.PanBergerSplit.BergerPrintedT,
   ZInQ.Contrib.HodgeSplit.DSThm965,
   ZInQ.Contrib.HodgeSplit.DSThm966]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 63 open hypotheses, 1952 theorems checked, 9 discharge one
  ```
* The autofold dry run is `scratch/pb-fix/autofold-dryrun.txt`. With its first line stripped it is
  `scratch/pb-fix/FoldDryRun.lean`, which compiles; `sixContactMin_of_open30` uses only the standard axioms.

```
lake build +ZInQKernel.Contrib.OneProof.PanBergerFix
lake env lean scratch/pb-fix/Axioms.lean
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
lake env lean scratch/pb-fix/Discharges.lean
python3 scripts/one_proof/autofold.py scratch/pb-fix/autofold.json --dry-run
```
