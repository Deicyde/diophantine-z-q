# pb-fix3: Pan's and Berger's leaves of `r11r12` with printed hypotheses and conclusions

Task pb-fix3, 2026-11-16/17. Base: wip/bst-construct fe8b30667, merged with origin/main c0f3d085c. Lean:
`ZInQKernel/Contrib/OneProof/PanBergerDict.lean` (namespace `HDec.PkgI4.PanDict`). It imports
`ZInQKernel.Contrib.OneProof.BergerBst`, `ZInQKernel.Contrib.OneProof.DSThm966EV` and two Tau Ceti newform
modules, not `Main`. It is generated from `scratch/pb-fix3/PanDict.lean` by `scratch/pb-fix3/mkcontrib.py`.
Results log: `scratch/pb-fix3/log.md`. This is model work; no person has reviewed it.

Marks used below:

* **VERIFIED**: compiled here, or read in a named file.
* **STANDARD**: published, with an exact reference.
* **UNVERIFIED**: a theorem number or wording given from memory. This host has no network, and Pan's TeX is
  not on it; Pan's wording is taken from the reads recorded in rv-h-a011 §2 and locators.md row R12.

## 1. Result

**`r11r12 : HDec.PkgI4.PanBerger` is discharged by `panBerger_of_printedPV` from two restated leaves,
`PanPrintedP` (Pan 2022, Thm 1.0.4) and `BergerPrintedV` (Berger 2002, Thm 0.7), and the current bundle's fields
`dsThm965Printed`, `eigenformCoeffFieldFinite` and `dsThm966Printed`.** Every hypothesis and the conclusion of
`PanPrintedP` transcribe Pan's statement, and every step from them to the forms the consumer uses is proved in
Lean:

| printed notion in `PanPrintedP` | kernel / bst-construct form the consumer uses | Lean bridge (all proved) |
| --- | --- | --- |
| Hodge–Tate weight multiplicity `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` (`htMultE`, `LocalDistinctHTP`) | `htMultU = dim_{ℚ_p}(ℂ_p(w) ⊗ V)^G / [E:ℚ_p]` (`LocalDistinctHTU`), itself from pkg-I4's `DistinctHTWeights` by pb-fix2's `localDistinctHTU_dualHom` | `htMultE_eq_htMultU`, `localDistinctHTP_iff` (an equivalence) |
| irreducible: no stable subspace but `0` and `ℚ̄_p²` (`IsIrreducibleP`) | Burnside form (`GaloisRep.IsIrreducible`: the image spans `M₂(ℚ̄_p)`) | `isIrreducibleP_of` |
| "comes from a cuspidal eigenform up to twist": a cuspidal eigenform `g` (`EigenformAwayFromLevel N k`), `ρ_g` attached through `ι_p` (`IsAttachedVia`), `ρ ≅ ρ_g ⊗ ψ` (`IsTwistOf`) | `IsNormalizedEigenform g' χ` (kernel coefficient form), `1 ≤ k`, and `tr ρ(Frob_q^geom) = ψ(Frob_q^geom) ι_p⁻¹(a_q(g'))` | `exists_normalized_of_eigenform` (and the converse `exists_eigenform_of_normalized`), `one_le_weight`, `trace_of_twist`, assembled in `panPrintedB_of_printedP` |

`BergerPrintedV` is Berger's theorem for one `p`-adic representation `V = E^n` with a continuous
`ρ_E : G_{ℚ_p} → GL_n(E)`; `bergerPrintedB_of_V` (with `continuous_model`) proves bst-construct's
`BergerPrintedB` from it.

I rate both leaves **printed form** (§3). The fold is **−1 GLUE**: the composite `r11r12` (GLUE) is replaced by
two published leaves flagged unread. All declarations use only the standard axioms (VERIFIED, §4).

**Why the reroute of the DS inputs.** bst-construct's `panBerger_of_printedB_weak` takes `DS965Weak.DSThm965Weak`
and `HodgeSplit.DSThm966`. Neither is a field of the current bundle `OpenResearchLeaves31` (TailZ50, VERIFIED):
coeff-ext and coeff-fix replaced them by `dsThm965Printed`, `eigenformCoeffFieldFinite` and `dsThm966Printed`.
bst-construct's autofold spec (`{n}.dsThm965Weak`, `{n}.dsThm966`) therefore no longer applies to main.
`panBerger_of_printedPV` uses `DSCoeffExt.dsThm965Weak_of_printed` and `DSThm966EV.dsThm966_of_printed` to
reach them from the current fields.

## 2. The statements (VERIFIED: copied from the compiled file)

```lean
-- Hodge–Tate, as printed: dim over the coefficient field
def htSpaceE (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : Submodule E ((Fin n → E) ⊗[ℚ_[p]] ℂ_[p]) where
  carrier := {x | ∀ σ : GQp p, TensorProduct.map (vAct p ρ σ) (htLin p w σ) x = x}  -- (V ⊗ ℂ_p(w))^G
def htMultE (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ := finrank E (htSpaceE p ρ w)
def LocalDistinctHTP (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin 2) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    ∀ w : ℤ, htMultE p ρE w = Multiset.count w {a, b}

def IsIrreducibleP (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, ∀ v ∈ W, (ρ.mat σ) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

def IsAttachedVia (ιp : PadicAlgCl p ≃+* ℂ) {N : ℕ} [NeZero N] {k : ℤ}
    (g : EigenformAwayFromLevel N k) (ρg : GaloisRep p 2) : Prop :=
  ∃ S : Finset ℕ, ∀ (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N), q ∉ S →
    ρg.UnramifiedAt q ∧
    ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
      (ρg.mat σ⁻¹).trace =
        ιp.symm (g.eigenvalue (q.toPNat hq.pos) (DSThm966EV.coprime_of_not_dvd hq hqN))

def IsTwistOf (ρ ρg : GaloisRep p 2) (ψ : GaloisChar p) : Prop :=
  ∃ P : GL (Fin 2) (PadicAlgCl p), ∀ σ : GQ,
    ρ.mat σ = (ψ.toHom σ : PadicAlgCl p) • ((P : Matrix _ _ _) * ρg.mat σ * ((P⁻¹ : GL _ _) : Matrix _ _ _))

def PanPrintedP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstB p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

def BergerPrintedV : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE → IsDeRhamU p ρE → IsPstB p ρE

theorem panBerger_of_printedPV (hP : PanPrintedP) (hB : BergerPrintedV)
    (h965 : DSCoeffExt.DSThm965Printed) (hK : DSCoeffExt.EigenformCoeffFieldFinite)
    (h966 : DSThm966EV.DSThm966Printed) : PanBerger
```

`LocalIsPstB`, `IsPstB` (Fontaine admissibility over Berger's `B_st = B_max[log [p̃]] ⊆ B_dR`) are
bst-construct's; `IsDeRhamU`, `htLin`, `vAct` are pb-fix2's/pb-fix's; `GaloisRep`, `IsOdd`, `FinitelyRamified`,
`UnramifiedAt`, `LiesOver`, `IsArithFrob` are pkg-I4's; `EigenformAwayFromLevel` is Tau Ceti's.

### Proved in the file (VERIFIED, standard axioms)

| theorem | content |
| --- | --- |
| `tensorMap_smul` | `σ` acts `E`-linearly on `V ⊗_{ℚ_p} ℂ_p`, so `(V ⊗ ℂ_p(w))^G` is an `E`-subspace |
| `map_comm_htU` | `ℂ_p ⊗ V ≅ V ⊗ ℂ_p` carries pb-fix2's `htU` onto `htSpaceE` |
| `htMultE_eq_htMultU` | `dim_E W = dim_{ℚ_p} W / [E : ℚ_p]`, from the tower law `dim_{ℚ_p} W = [E : ℚ_p] · dim_E W` |
| `localDistinctHTP_iff` | `LocalDistinctHTP ρ ↔ LocalDistinctHTU ρ` |
| `isIrreducibleP_of` | Burnside form ⇒ no stable subspace but `0`, `ℚ̄_ℓ^n`: the matrices preserving `W` form a subalgebra containing the image, hence all of `M_n`; a rank-one matrix `u ⊗ e_j/v_j` sends a nonzero `v ∈ W` to any `u` |
| `one_le_weight` | a nonzero cusp form on `Γ₁(N)` has weight `≥ 1`: negative weight from Mathlib's `ModularForm.isZero_of_neg_weight`; weight `0`: constant by `ModularForm.eq_const_of_weight_zero`, and `0` at `i∞` |
| `trace_of_twist` | `ρ ≅ ρ_g ⊗ ψ` ⇒ `tr ρ(σ) = ψ(σ) tr ρ_g(σ)` |
| `exists_normalized_of_eigenform` | an `EigenformAwayFromLevel N k` has the eigenvalues at `q ∤ N` of a newform `h` of level `M ∣ N` (Tau Ceti's `exists_newform_eigenvalue_eq`, Diamond–Shurman Prop. 5.8.4); `h.toEigenform` (Tau Ceti) is a full eigenform with `a₁ = 1`, so `IsNormalizedEigenformDS` and, by coeff-ext's `isNormalizedEigenform_of_DS`, the kernel's `IsNormalizedEigenform h (ofUnitHom h.χ)`, with `a_q(h) = λ_q(g)` for `q ∤ N` and `k ≥ 1` |
| `exists_eigenform_of_normalized` | converse: a kernel normalized eigenform is an `EigenformAwayFromLevel` with `λ_q = a_q` |
| `panPrintedB_of_printedP` | bst-construct's `PanPrintedB` from `PanPrintedP` |
| `continuous_model`, `bergerPrintedB_of_V` | a model `ρ_E` of a continuous `ρ` is continuous (`E ⊆ ℚ̄_p` an embedding); bst-construct's `BergerPrintedB` from `BergerPrintedV` |
| `panBerger_of_printedPV` | `r11r12` |

## 3. Ratings

### 3.1 `panPrintedP`: printed form

Source: Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. 35 (2022),
1031-1169, Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1 (FM.tex L167-177, L226-233; conventions
L253, L268, L270; read by h-a011 and rv-h-a011 §2, VERIFIED there; JAMS numbering UNVERIFIED). The leaf is the
theorem for `p ≥ 5` (Pan: `p` odd, with an extra condition only at `p = 3`), for each `ι_p`.

**Hypotheses, each as printed.**
* *continuous* (`GaloisRep`), *finitely ramified*, *odd* (`det ρ(c) = −1` for every complex conjugation): as
  pb-fix2 (Conj. 1.0.1's wording, rv-h-a011 §2).
* *irreducible*: now literally "no stable subspace but `0` and the whole space" over `ℚ̄_p`. The Burnside form
  is no longer in the leaf; the glue proves Burnside ⇒ irreducible.
* *potentially semistable in the sense of Fontaine* at `p`: bst-construct's `LocalIsPstB` (on a model `V = E^n`,
  `B_st`-admissible over some finite `K`, Berger's `B_st ⊆ B_dR`). A `ℚ̄_p`-valued continuous representation has a
  model over a finite `E`, and its pst-ness is defined through one (equivalently any) model; the leaf reads it as
  "some model", which is that definition.
* *distinct Hodge–Tate weights* of `ρ|_{G_{ℚ_p}}`: the multiplicity of `w` is `dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`
  on a model `V = E^n`, with Pan's sign convention (the cyclotomic character has weight `−1`, FM.tex L268,
  VERIFIED by rv-h-a011; check: `(E(1) ⊗ ℂ_p(w))^G ≠ 0` iff `w = −1`, by Tate). This is the standard printed
  definition of Hodge–Tate weights for an `E`-linear representation of `G_{ℚ_p}` (one embedding `ℚ_p → E`;
  e.g. Barnet-Lamb–Gee–Geraghty–Taylor, Ann. of Math. 179 (2014), §1.1, with `ℚ̄_p` coefficients: number and
  wording UNVERIFIED). The weights are "two distinct integers `a ≠ b`", which also says Hodge–Tate (total
  multiplicity `2 = dim_E V`).
  * What changed from bst-construct: `htMultU` divided a `ℚ_p`-dimension by `[E : ℚ_p]` in `ℕ`; the leaf now
    takes the `E`-dimension of the `E`-subspace directly. `localDistinctHTP_iff` proves the two forms equivalent.

**Conclusion, as printed.** "`ρ` comes from a cuspidal eigenform up to twist" is transcribed as: there are a
cuspidal eigenform `g`, the representation `ρ_g` attached to `g` through `ι_p`, and a continuous character `ψ`
with `ρ ≅ ρ_g ⊗ ψ`.
* *cuspidal eigenform*: Tau Ceti's `EigenformAwayFromLevel N k`, a nonzero cusp form on `Γ₁(N)` with nebentypus,
  an eigenvector of every `T_n`, `n` prime to `N`. This is the weakest sense of "eigenform"; a full eigenform
  (Diamond–Shurman Def. 5.8.1) or a newform is one, so the leaf is a consequence of the print under every reading
  of "eigenform". The project predicate `IsNormalizedEigenform` is gone from the leaf; reaching it needs the
  newform of the eigensystem, which the glue gets from Tau Ceti's proved Diamond–Shurman 5.8.4.
* *`ρ_g` attached through `ι_p`* (`IsAttachedVia`): for almost all primes `q ∤ N`, `ρ_g` is unramified at `q`
  and `tr ρ_g(Frob_q) = ι_p⁻¹(λ_q(g))`, `Frob_q = σ⁻¹` the geometric Frobenius (Pan's convention, FM.tex L270,
  VERIFIED by rv-h-a011), `λ_q(g)` the `T_q`-eigenvalue. This pins `ρ_g` up to semisimplification (Chebotarev and
  Brauer–Nesbitt), which is all "the representation attached to `g`" determines for an irreducible `ρ`; it is the
  weakest form of "attached".
* *up to twist* (`IsTwistOf`): `ρ(σ) = ψ(σ) P ρ_g(σ) P⁻¹` for one `P ∈ GL₂(ℚ̄_p)`.

**Flags carried in the spec (unread).**
1. JAMS number and page UNVERIFIED (arXiv v2 read by h-a011).
2. The formula `tr ρ_g(Frob_q^geom) = ι_p⁻¹(λ_q)` is the standard normalization under Pan's stated conventions
   (geometric Frobenius, `ι_p`), recalled, not read. If Pan's `ρ_g` were normalized by arithmetic Frobenius, the
   leaf's conclusion still follows from his, with `ρ_g^∨ ≅ ρ_g ⊗ det ρ_g⁻¹` (dimension 2) in place of `ρ_g`:
   `tr ρ_g^∨(σ⁻¹) = tr ρ_g(σ)` and `ρ ≅ ρ_g^∨ ⊗ (ψ det ρ_g)`.
3. "Cuspidal eigenform" read in its weakest sense (above); `ψ` continuous (the twisting characters of Galois
   representations are continuous; for irreducible `ρ`, `ψ² = det ρ / det ρ_g` is).

**Not stronger than the print.** Each hypothesis is Pan's (pst and HT computed on a model, as defined); the
conclusion asks for less than Pan's `ρ ≅ ρ_g ⊗ ψ` with Deligne's `ρ_g`: an eigenform in the weakest sense and a
`ρ_g` pinned only by almost all Frobenius traces.

### 3.2 `bergerPrintedV`: printed form

Source: Berger, Invent. Math. 148 (2002), Théorème 0.7 (= Cor. 5.22 of the published version, author copy pp. 6
and 52; = arXiv:math/0102179v3 Thm 0.6 = Thm 5.19; locators R11): every de Rham representation of `G_K` is
potentially semistable.

**The check against Thm 0.7.**
* *The object.* Berger's theorem is about a `p`-adic representation: a finite-dimensional `ℚ_p`-space with a
  continuous linear `G_K`-action. bst-construct's `BergerPrintedB` was stated for a continuous `ℚ̄_p`-valued `ρ`
  with "de Rham" and "pst" meaning "on some model `E^n`", so applying Berger needed the continuity of the model,
  which the leaf left implicit. `BergerPrintedV` is stated for the `p`-adic representation itself: `V = E^n`,
  `ρ_E : G_{ℚ_p} → GL_n(E)` continuous (`E ⊆ ℚ̄_p` with its subspace topology, which is the unique
  `ℚ_p`-vector-space topology of `E`). `continuous_model` proves in Lean that a model of a continuous `ρ` is
  continuous, so `BergerPrintedB` follows (`bergerPrintedB_of_V`).
* *de Rham*: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`), Fontaine's
  `dim_K D_dR(V) = dim V` at `K = ℚ_p`. As printed.
* *potentially semistable*: `V|_{G_K}` is `B_st`-admissible for some finite `K/ℚ_p`:
  `dim_{B_st^{G_K}} (B_st ⊗ V)^{G_K} = dim V` (`IsPstB`), Berger's `B_st = B_max[log [p̃]] ⊆ B_dR`. Fontaine's
  admissibility; Berger's `dim_F D_st(V)` uses `F = B_st^{G_K}` (Fontaine's theorem). As bst-construct.
* *K*: the leaf is the case `K = ℚ_p` of Berger's theorem (any `K` with perfect residue field), so it is an
  instance.

**Flags (unread)**: Springer pagination UNVERIFIED; Berger §1.2's wording of `A_max`, `B_max` recalled
(bst-construct §3.1, UNVERIFIED); admissibility over `B_st^{G_K}` rather than over `F` (agree by Fontaine).

**Not stronger than the print**: one representation of `G_{ℚ_p}`, conclusion over the same `V`.

## 4. Deliverables and checks (VERIFIED)

* `ZInQKernel/Contrib/OneProof/PanBergerDict.lean` (23 KB). `lake build +ZInQKernel.Contrib.OneProof.PanBergerDict
  +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` succeeds (13062 jobs, 15.5 min wall-clock; the file
  itself 7.5 s, no warnings). The file has no `sorry`.
* `python3 scripts/one_proof/sandbox/scan_contrib.py c0f3d085c HEAD`: `PanBergerDict.lean: 0 likely hit(s), 0
  possible hit(s)`.
* **Axioms.** `scratch/pb-fix3/Axioms.lean` prints 11 declarations (the glue, both dictionaries, `one_le_weight`,
  `isIrreducibleP_of`, `continuous_model`, `trace_of_twist`); all use only `[propext, Classical.choice,
  Quot.sound]` (`axioms-output.txt`).
* **`#discharges`** (`scratch/pb-fix3/Discharges.lean` → `discharges-output.txt`):
  ```
  DISCHARGES [OpenResearchLeaves31.r11r12] by HDec.PkgI4.PanDict.panBerger_of_printedPV
    still assumes: [HDec.PkgI4.PanDict.PanPrintedP,
   HDec.PkgI4.PanDict.BergerPrintedV,
   DSCoeffExt.DSThm965Printed,
   DSCoeffExt.EigenformCoeffFieldFinite,
   DSThm966EV.DSThm966Printed]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 35 open hypotheses, 10328 theorems checked, 39 discharge one
  ```
  The last three are existing fields of `OpenResearchLeaves31`.
* **Autofold.** Spec `scratch/pb-fix3/autofold.json`, field `r11r12`, proof
  `_root_.HDec.PkgI4.PanDict.panBerger_of_printedPV {n}.panPrintedP {n}.bergerPrintedV {n}.dsThm965Printed
  {n}.eigenformCoeffFieldFinite {n}.dsThm966Printed`; both leaves kind `published`, flag `unread: …` (flags of
  §3).
  * Dry run (`autofold-dryrun.txt`): `strict count: 11/18 on 29 -> 13/17 on 30; strictest 11/18 -> 13/17`
    (GLUE 18 → 17).
  * Its output with the first line stripped is `scratch/pb-fix3/FoldDryRun.lean`; it compiles, and
    `sixContactMin_of_open49` uses only the standard axioms (`folddryrun-output.txt`).
  * The fold needs `ZInQKernel/Contrib/OneProof/BergerBst.lean` (bst-construct, on this branch, not yet on main).
    bst-construct's own spec (`scratch/bst-construct/autofold.json`) is superseded: it names the fields
    `dsThm965Weak`, `dsThm966`, which main no longer has.
* **Reproduce** from the repository root:
  ```
  python3 scratch/pb-fix3/mkcontrib.py
  lake build +ZInQKernel.Contrib.OneProof.PanBergerDict +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  lake env lean scratch/pb-fix3/Axioms.lean
  lake env lean scratch/pb-fix3/Discharges.lean
  python3 scripts/one_proof/autofold.py scratch/pb-fix3/autofold.json --dry-run
  ```

## 5. What remains

* Read Pan's FM.tex L253 for the exact formula attaching `ρ_g` (flag 2 of §3.1) and the JAMS numbering.
* Read Berger 2002 §1.2 against `Amax`, `Bmax`, `Bst` (bst-construct's flag, unchanged).
* Locator rows for `panPrintedP` and `bergerPrintedV` in locators.md (that file belongs to other tasks).
  Proposed: R12 → `panPrintedP` (pb-fix3; predicates in `PanBergerDict.lean`), R11 → `bergerPrintedV`.
* Not done (not needed): a model-free form of the Hodge–Tate multiplicity with `ℚ̄_p` coefficients,
  `dim_{ℚ̄_p} (ℚ̄_p² ⊗_{ℚ_p} ℂ_p(w))^G`. It equals the model form by base change of invariants along `ℚ̄_p/E`
  (STANDARD), not proved here. Pst is computed on a model as well (bst-construct), so the leaf reads both
  conditions through "some model", which is how they are defined for `ℚ̄_p`-valued representations.
