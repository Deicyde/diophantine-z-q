# pb-fix2: Pan and Berger, each for one representation in printed form

Task pb-fix2, 2026-11-16. Base: wip/pb-fix e479bc562. Lean: `ZInQKernel/Contrib/OneProof/PanBergerPrinted.lean`
(imports `ZInQKernel.Contrib.OneProof.PanBergerFix` only). Results log: `scratch/pb-fix2/log.md`. This is model
work and no person has reviewed it.

Marks: **VERIFIED** means compiled here or read in a named file. **STANDARD** means published, with an exact
reference. **UNVERIFIED** means a theorem number or wording given from memory; this host has no network.

## 1. Result

**`r11r12 : HDec.PkgI4.PanBerger` is discharged by `panBerger_of_printedU` from two new leaves, `PanPrintedU`
(Pan 2022, Thm 1.0.4) and `BergerPrintedU` (Berger 2002, Thm 0.7).** It also uses `DSThm965` and `DSThm966`, which
are already leaves of the same bundle. I rate both new leaves **printed form** (§3), so the fold is **−1 GLUE**:
strict 46/10 on 56 → 48/9 on 57, strictest 45/11 → 47/10 (autofold dry run; its output compiles). Everything
compiles with only the standard axioms (VERIFIED).

The two repairs the review asked for:

1. **Berger.** `K_0` is now defined as the print defines it: `K_0 = W(k_K)[1/p]`, the Witt vectors of the
   residue field of `K` with `p` inverted (Mathlib's `WittVector`). It is no longer `ℚ_p(μ_{prime to p}(K))`,
   which matches the print only through Hensel's lemma. The leaf needs no identification step. As a sanity check
   I proved in Lean that `[K_0 : ℚ_p]` is the residue degree: `|k_K| = p^{[K_0:ℚ_p]}` for every finite `K/ℚ_p`,
   and `[K_0(ℚ_p) : ℚ_p] = 1`. The `B_st` reading and the admissibility normalization are named as explicit flags.
2. **Pan.** The leaf is now stated for **one** representation `ρ`, with every hypothesis on `ρ` in printed form,
   including "Hodge–Tate with distinct weights" computed on the underlying space `V`. Its conclusion uses Pan's
   geometric Frobenius. The glue applies the leaf to the contragredient `ρ^∨`.
   * The step that fixes `ρ^∨`'s weights is now **proved in Lean** (`localDistinctHTU_dualHom`). It is linear
     algebra, the trace pairing `E^n ≅ (E^n)^*`, and needs **neither `AxSenTate` nor `TateTwistInvariants`**
     (reason in §3.2).
   * The eigenform hypothesis is kept as printed and its reading is flagged.

Neither leaf needs a further theorem step. What remains is reading the two prints (§5).

## 2. The statements (VERIFIED: copied from the compiled file)

All are in namespace `HDec.PkgI4.PanBergerSplit`. They use pb-bypass's `B_st` (`Bst`, `stAct`) and pkg-I4's
`B_dR`, `ℂ_p`, `cycPow`. The new period-ring functor is Fontaine's tensor form on the underlying space
`V = E^n`:

```lean
def tensorInv (act : GQp p → B →ₗ[ℚ_[p]] B) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule ℚ_[p] (B ⊗[ℚ_[p]] (Fin n → E))           -- (B ⊗ V)^H
  -- carrier := {x | ∀ σ ∈ H, TensorProduct.map (act σ) (vAct p ρ σ) x = x}

-- residue field and K_0
def intRing K : Subring (PadicAlgCl p)        -- {x ∈ K | ‖x‖ ≤ 1}
def maxIdeal K : Ideal (intRing p K)          -- {x | ‖x‖ < 1}, proved maximal
abbrev resField K := intRing p K ⧸ maxIdeal p K
def WittLoc k := Localization.Away (p : WittVector p k)   -- W(k)[1/p], ℚ_p-algebra via W(𝔽_p) = ℤ_p
abbrev K0W K := WittLoc p (resField p K)                  -- K_0 = W(k_K)[1/p]

def IsDeRhamU ρ := finrank ℚ_[p] (tensorInv p (bdrLin p) ⊤ ρ) = finrank ℚ_[p] (Fin n → E)
def htMultU ρ w := finrank ℚ_[p] (tensorInv p (htLin p w) ⊤ ρ) / finrank ℚ_[p] E   -- dim_E (ℂ_p(w) ⊗ V)^G
def IsSemistableOverU K ρ :=
  finrank ℚ_[p] (tensorInv p (stLin p) K.fixingSubgroup ρ) = finrank ℚ_[p] (K0W p K) * finrank ℚ_[p] (Fin n → E)
def IsPstU ρ := ∃ K, FiniteDimensional ℚ_[p] K ∧ IsSemistableOverU p K ρ
-- LocalIsDeRhamU, LocalIsPstU: as pkg-I4's LocalIsDeRham (a model over a finite E ⊆ ℚ̄_p);
def LocalDistinctHTU (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ∃ E (_ : FiniteDimensional ℚ_[p] E) ρE, (model) ∧
    ∀ w, htMultU p ρE w = Multiset.count w {a, b}

def BergerPrintedU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstU p n ρ

def PanPrintedU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstU p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q)

theorem panBerger_of_printedU (hP : PanPrintedU) (hB : BergerPrintedU)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) : PanBerger
```

**Proved in the file** (VERIFIED, standard axioms, `scratch/pb-fix2/axioms-output.txt`, 18 declarations):

| theorem | content |
| --- | --- |
| `panBerger_of_printedU` | `r11r12` from the two leaves, `DSThm965` and `DSThm966` |
| `dualRep`, `dualRep_isIrreducible`, `dualRep_finitelyRamified`, `dualRep_isOdd`, `trace_dualRep_inv`, `dualRep_restrictLocal` | the contragredient `ρ^∨ : σ ↦ ρ(σ⁻¹)ᵀ` is a continuous `GaloisRep`. It inherits irreducibility (Burnside form), finite ramification and oddness, and `tr ρ^∨(σ⁻¹) = tr ρ(σ)` |
| `finrank_tensorInv_dualHom` | `(B ⊗ V^∨)^H ≅ Hom_H(V, B)` for any `B` with a `ℚ_p`-linear action: `V^∨` is realized as `E^n` with the matrices `ρ(σ⁻¹)ᵀ`, through the trace pairing `(w, v) ↦ Tr_{E/ℚ_p}(v·w)` (`trEquiv`, nondegenerate since char 0) |
| `localIsDeRhamU_dualHom` | pkg-I4's `LocalIsDeRham ρ` ⇒ printed de Rham for `ρ^∨` |
| `localDistinctHTU_dualHom` | pkg-I4's `DistinctHTWeights ρ` (weights `{a,b}`) ⇒ printed "HT with distinct weights" for `ρ^∨` (weights `{−a,−b}`) |
| `finrank_wittLoc` | `[W(k)[1/p] : ℚ_p] = [k : 𝔽_p]` for every finite field `k` of characteristic `p`. The Teichmüller lifts of an `𝔽_p`-basis form a `ℤ_p`-basis of `W(k)`: relations are trivial by reduction mod `p` and `p`-torsion-freeness, and the lifts span by successive approximation, using that `ℤ_p` is complete and `W(k)` is `p`-adically separated (both in Mathlib). Then `Basis.localizationLocalization` |
| `resField_finite`, `card_resField` | the residue field of a finite `K/ℚ_p` is finite, and `|k_K| = p^{[K_0:ℚ_p]}`, i.e. `[K_0 : ℚ_p]` is the residue degree `f(K/ℚ_p)` |
| `finrank_K0W_le`, `finrank_K0W_pos`, `finrank_K0W_bot` | `1 ≤ [K_0 : ℚ_p] ≤ [K : ℚ_p]`; `[K_0(ℚ_p) : ℚ_p] = 1` |
| `isSemistableOverU_dualHom_iff` | the printed semistability of `ρ^∨` is pb-bypass's Hom form with `[K_0 : ℚ_p]` in place of `dim B_st^{G_K}` |
| `isSemistableOverU_trivial_iff`, `isPstU_trivial` | the trivial character is semistable over `K` ⇔ `dim B_st^{G_K} = [K_0 : ℚ_p]` (Fontaine's `B_st^{G_K} = K_0` in dimension form). Given `dim B_st^{G_{ℚ_p}} = 1`, it is pst |

## 3. Ratings of the new leaves

### 3.1 `bergerPrintedU`: printed form

Source: Berger, Invent. Math. 148 (2002), Théorème 0.7 (= Cor. 5.22 of the published version, author copy pp. 6 and
52; = arXiv:math/0102179v3 Thm 0.6 = Thm 5.19; locators R11). It says: every de Rham representation of `G_K` is
potentially semistable. The leaf applies it at `K = ℚ_p` to the `ℚ_p`-representation `V = E^n` that underlies `ρ`.

* **Both predicates are computed on `V`**, in Fontaine's tensor form `(B ⊗_{ℚ_p} V)^{G_K}`:
  * de Rham: `dim_{ℚ_p} D_dR(V) = dim_{ℚ_p} V`;
  * pst: `dim_{ℚ_p} D_st,K(V) = [K_0 : ℚ_p] · dim_{ℚ_p} V` for some finite `K ⊆ ℚ̄_p`.
* **`K_0` is the print's.** It is `W(k_K)[1/p]`, the Witt vectors of the residue field
  `k_K = {‖x‖ ≤ 1}/{‖x‖ < 1}` of `K` with `p` inverted.
  * Berger's §0 setting, from memory (UNVERIFIED wording): `k` perfect of characteristic `p`,
    `K_0 = W(k)[1/p]`, `K` finite totally ramified over `K_0`. Fontaine's definition of "semistable over `L`"
    uses `L_0 = W(k_L)[1/p]`.
  * Breuil's setting, which follows the same school, is read verbatim in rv-h-a011 §3.2: `K₀ = Frac W(k)`
    (VERIFIED there).
  * No identification with a subfield of `K` is used. That `[K_0 : ℚ_p]` is the residue degree is proved
    (`card_resField`).
* **Flag: `B_st` reading.** `B_st` is Fontaine's abstract `B_cris[X]` with `σ(X) = X + c(σ)t` (pb-bypass's `Bst`).
  It is not the subring `B_cris[log [p♭]]` of `B_dR`.
  * The two are `G`-isomorphic by Fontaine's theorem that `log [p♭]` is transcendental over `Frac B_cris`
    (Astérisque 223, Exp. II §3; number UNVERIFIED), so `D_st` is the same.
  * The abstract form is the definition in Fontaine's Exp. II. Berger's paper also works with `B_st` inside
    `B_dR` (UNVERIFIED).
* **Flag: admissibility normalization.** Fontaine's `dim_{K_0} D_st,K(V) = dim V` is written in
  `ℚ_p`-dimensions with the explicit factor `[K_0 : ℚ_p]`. These agree because `D_st,K` is a `K_0`-space
  (`K_0 ⊆ B_st^{G_K}`). That module structure is not built in Lean.
* **`finrank` convention.** Lean's `finrank` is 0 on an infinite-dimensional space. With `[K_0 : ℚ_p] ≥ 1`
  (proved), an infinite-dimensional `D_st` makes the predicate false, not true. Fontaine proves `D_st` is always
  finite-dimensional, so nothing is added.
* **Not stronger than the print.** The leaf is the theorem at one representation of `G_{ℚ_p}`, for every
  continuous `ρ`; the conclusion keeps the same model `E`.

### 3.2 `panPrintedU`: printed form, under the eigenform reading

Source: Pan, JAMS 35 (2022), Thm 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1; locators R12; JAMS
numbering UNVERIFIED). Pan fixes `ι_p : ℚ̄_p ≅ ℂ` and uses geometric Frobenius and cyclotomic HT weight −1
(h-a011 §1.1 and R12, VERIFIED there). The leaf holds for every `ι_p`, and every hypothesis is about the one `ρ`.

**Hypotheses.**
* **Pst** is computed on `V` (as in §3.1).
* **"Hodge–Tate with distinct weights"** is computed on `V`: the multiplicity of `w` is
  `dim_E (ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`, and these multiplicities are those of two distinct integers.
  * This is the standard convention for `E`-linear representations of `G_K`, where weights are indexed by the
    embeddings `K → E`; for `K = ℚ_p` there is one.
  * With Pan's sign (cyclotomic weight −1), `V = ℚ_p(1)` has weight −1. "Distinct" does not depend on the sign
    convention.
* **Irreducible** is the kernel's Burnside form (the image spans `M₂(ℚ̄_p)`). It implies irreducible, so the leaf
  assumes more than Pan does and is a consequence of his theorem.
* **Odd** (`det ρ(c) = −1` for every complex conjugation) and **finitely ramified** are as printed.

**Conclusion.** It is the trace identity at geometric Frobenius `σ⁻¹`: `tr ρ(σ⁻¹) = ψ(σ⁻¹) ι_p⁻¹(a_q(g))` for
almost all `q`.
* **Flag (eigenform reading).** "Comes from a cuspidal eigenform up to twist" is read as `ρ ≅ ρ_{g,ι_p} ⊗ ψ'`,
  with `ρ_{g,ι_p}` the representation attached to `g` through `ι_p`. The trace identity then holds in **every**
  normalization of `ρ_{g,ι_p}`, with `ψ` changed, because in dimension 2 these normalizations differ only by a
  character:
  * arithmetic or geometric Frobenius: `tr(M⁻¹) = tr M / det M`;
  * `ρ_g` or its dual: `ρ_g^∨ ≅ ρ_g ⊗ det⁻¹`;
  * `g` or the conjugate eigenform: `ā_q = χ̄(q) a_q` for `q ∤ N`.

  The review accepted this reading.
* No algebraicity of `a_q(g)` is asserted.
* `1 ≤ k` is weaker than Pan's regular weight.

**Why no Sen or Tate input is needed.** The review suggested deriving `ρ^∨`'s weights from `AxSenTate` and
`TateTwistInvariants`. That would be needed if the leaf were applied to `ρ` itself, since `DistinctHTWeights ρ` is
computed on `Hom_G(V, ℂ_p(i)) = (ℂ_p(i) ⊗ V^∨)^G`. The glue applies the leaf to `ρ^∨` instead:
* the underlying space of `ρ^∨` is `V^∨` (trace pairing);
* so `(ℂ_p(w) ⊗ V^∨)^G ≅ Hom_G(V, ℂ_p(w))` is pkg-I4's `htSpace ρ w`, and `ρ^∨` has weights `{−a, −b}`;
* likewise `LocalIsDeRham ρ` is printed de Rham for `ρ^∨`.

So no dual-stability theorem (Fontaine) and no Sen theory is used. Pst never has to be transferred, since Berger's
output is Pan's input on the same representation `ρ^∨`.

**Proposed locators.md rows** (not added: locators.md belongs to other tasks):
* R11: `bergerPrintedU` (pb-fix2). Berger Thm 0.7 at `K = ℚ_p` for `V`, tensor form, `K_0 = W(k_K)[1/p]`.
* R12: `panPrintedU` (pb-fix2). Pan Thm 1.0.4 for one `ρ`, Pan's `ι_p`, geometric Frobenius, pst and HT-distinct
  on `V`.

## 4. Deliverables and reproduction

* `ZInQKernel/Contrib/OneProof/PanBergerPrinted.lean` (50 KB). It imports
  `ZInQKernel.Contrib.OneProof.PanBergerFix`, not `Main`, and has no build-time code
  (`scripts/one_proof/sandbox/scan_contrib.py e479bc562 HEAD`: 0 hits, VERIFIED).
* `scratch/pb-fix2/autofold.json`: field `r11r12`. The proof is
  `panBerger_of_printedU {n}.panPrintedU {n}.bergerPrintedU {n}.dsThm965 {n}.dsThm966`. Both leaves have kind
  `published` and flag `unread: …`, which carries the locator status and the readings above (`B_st` reading,
  `K_0` normalization, eigenform reading, Burnside form).
* `#discharges` (VERIFIED, `scratch/pb-fix2/discharges-output.txt`):
  ```
  DISCHARGES [OpenResearchLeaves22.r11r12] by HDec.PkgI4.PanBergerSplit.panBerger_of_printedU
    still assumes: [HDec.PkgI4.PanBergerSplit.PanPrintedU,
   HDec.PkgI4.PanBergerSplit.BergerPrintedU,
   ZInQ.Contrib.HodgeSplit.DSThm965,
   ZInQ.Contrib.HodgeSplit.DSThm966]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 63 open hypotheses, 2107 theorems checked, 10 discharge one
  ```
* Autofold dry run: `scratch/pb-fix2/autofold-dryrun.txt`. With its first line stripped it is
  `scratch/pb-fix2/FoldDryRun.lean`, which compiles; `sixContactMin_of_open30` uses only the standard axioms.

```
lake build +ZInQKernel.Contrib.OneProof.PanBergerPrinted
lake env lean scratch/pb-fix2/Axioms.lean
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
lake env lean scratch/pb-fix2/Discharges.lean
python3 scripts/one_proof/autofold.py scratch/pb-fix2/autofold.json --dry-run
```

## 5. What remains

* **Statement checks against the prints.** Both leaves are flagged unread.
  * Berger's §0 wording `K_0 = W(k)[1/p]` is from memory here (UNVERIFIED).
  * The JAMS numbering of Pan's theorem is UNVERIFIED.
* **Fontaine's `B_st^{G_K} = K_0`** is not in Lean. The leaves do not depend on it for their meaning. But without
  it, no representation can be shown pst in Lean: `isSemistableOverU_trivial_iff` shows that even the trivial
  character needs it.
* **pb-fix's `PanPrintedT`/`BergerPrintedT`** are superseded and no longer used by the fold. pb-fix's file is
  unchanged.
