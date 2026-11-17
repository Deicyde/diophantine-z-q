# htmult-model: the Hodge–Tate multiplicities do not depend on the finite coefficient model

Task htmult-model, 2026-11-17. Base: fork main 06660f4a (contains fold-b112 f3402e89) with `wip/pb-dimform`
(3d69c488) merged. No other branch merged. Results log: `scratch/htmult-model/log.md`. This is model work; no person
has reviewed it.

Marks: **VERIFIED** (compiled here, or read in the source), **STANDARD** (published, exact reference),
**UNVERIFIED** (from memory), **on-the-spot** (provenance (c): a step in neither the manuscript nor a source it
cites).

## 1. Main result

__RESULT__

This was a proof-only task. No bundle field, statement or kinds row changed, nothing was folded, and no leaf was
added. The only file added under `ZInQKernel/` is `ZInQKernel/Contrib/OneProof/HTModel.lean`. It imports
`ZInQKernel.Contrib.OneProof.PstModel`, does not import `ZInQKernel.OneProof.Main`, and nothing imports it yet.
Its scratch copy is `scratch/htmult-model/HTModel.lean`.

**Co-step cleared.** The reviewer's verdict on `panPrintedF` listed three co-steps. One was the model clause of
Pan's Hodge–Tate hypothesis, `LocalDistinctHTP` (`PanBergerDict.lean:83`): "Hodge–Tate with distinct weights" is
read on *some* finite model `E ⊆ ℚ̄_p` of `ρ|_{G_{ℚ_p}}`, and before this task Lean had only same-model lemmas
(`htMultE_eq_htMultU`, `localDistinctHTP_iff`, `htMultE_le`). `localDistinctHTP_iff_forall` closes this co-step.
"Some model" and "every model, with the same pair of weights" are equivalent. So the Lean hypothesis is the print's
model-free "ρ|_{G_{ℚ_p}} is Hodge–Tate with distinct Hodge–Tate weights". The rating does not change, because the
Brinon–Conrad 9.2.10 step remains (see the lead's request).

## 2. The new theorems (namespace `HDec.PkgI4.HTModel`)

Shared hypotheses for §2.1–2.2: `E, L` are fields with `ℚ_p → E → L` a scalar tower, both finite over `ℚ_p`,
and `b : Basis (Fin d) E L`. The models are `ρE : GQp p →* GL (Fin n) E` and `ρL : GQp p →* GL (Fin n) L`, with
`hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E L) (ρE σ) = ρL σ`, i.e. `ρ_L = ρ_E ⊗_E L`.

### 2.1 Invariants under a change of coefficient field (§1 of the file)

For any `ℚ_p`-module `A` with a `ℚ_p`-linear action `act : GQp p → A →ₗ[ℚ_[p]] A` and any subgroup `H`:

```lean
theorem psi_map (hρ) (σ : GQp p) (y : A ⊗[ℚ_[p]] (Fin n → L)) (j : Fin d) :
    psi p b ℚ_[p] A (TensorProduct.map (act σ) (vAct p ρL σ) y) j =
      TensorProduct.map (act σ) (vAct p ρE σ) (psi p b ℚ_[p] A y j)
theorem mem_tensorInv_iff (hρ) (H : Subgroup (GQp p)) (x : A ⊗[ℚ_[p]] (Fin n → L)) :
    x ∈ tensorInv p act H ρL ↔ ∀ j, psi p b ℚ_[p] A x j ∈ tensorInv p act H ρE
def tensorInvEquiv (hρ) (H : Subgroup (GQp p)) :
    tensorInv p act H ρL ≃ₗ[ℚ_[p]] (Fin d → tensorInv p act H ρE)
theorem finrank_tensorInv (hρ) (H : Subgroup (GQp p)) :
    finrank ℚ_[p] (tensorInv p act H ρL) = d * finrank ℚ_[p] (tensorInv p act H ρE)
```

`psi` (`PstModel.lean` §2) is pb-dimform's `A ⊗ L^n ≅ (A ⊗ E^n)^d`, built from `phiE : (E^n)^d ≅ L^n`. The
proofs reuse `psi`, `psi_tmul`, `phiE_symm_equivariant` and `finrank_fin_pi_sub` from `PstModel.lean`.
`psi_map` is pb-dimform's `psi_act`, whose statement is fixed to `A = B_dR`, restated for an arbitrary `A`. Its
proof is the same three lines. `tensorInvEquiv` follows the pattern of `dBEquiv`, but over `ℚ_p` and for
`tensorInv` (`PanBergerPrinted.lean:175`).

### 2.2 The multiplicities (§2 of the file)

```lean
theorem htMultU_eq_of_basis (hρ) (w : ℤ) : htMultU p ρL w = htMultU p ρE w
theorem htMultE_eq_of_basis (hρ) (w : ℤ) : htMultE p ρL w = htMultE p ρE w
```

Proof. Take `A = ℂ_p` with the twisted action `htLin p w` and `H = ⊤`. Then
`dim_{ℚ_p} (ℂ_p(w) ⊗ L^n)^G = d · dim_{ℚ_p} (ℂ_p(w) ⊗ E^n)^G` (`finrank_tensorInv`) and
`[L : ℚ_p] = [E : ℚ_p] · d` (`Module.finrank_mul_finrank`). The finrank form
`htMultU = dim_{ℚ_p}(htU) / [· : ℚ_p]` is therefore unchanged (`Nat.mul_div_mul_left`). pb-fix3's dictionary
`htMultE_eq_htMultU` (`PanBergerDict.lean:108`) then carries the result to the printed form
`htMultE = dim_E (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`. So the scalars are compared through `dim_{ℚ_p}`, `[L : E]` and
`[E : ℚ_p]`, as the lead asked. No `L`-structure needs to be built.

### 2.3 Models inside `ℚ̄_p` (§3 of the file)

```lean
theorem htMultE_eq_of_le {E L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hEL : E ≤ L)
    [FiniteDimensional ℚ_[p] L] (ρE : GQp p →* GL (Fin n) E) (ρL : GQp p →* GL (Fin n) L)
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) =
      Matrix.GeneralLinearGroup.map (algebraMap L (PadicAlgCl p)) (ρL σ)) (w : ℤ) :
    htMultE p ρE w = htMultE p ρL w

theorem htMultE_model_eq {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E'] {ρ : GQp p →* GL (Fin n) (PadicAlgCl p)}
    (ρE : GQp p →* GL (Fin n) E) (ρE' : GQp p →* GL (Fin n) E')
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ)
    (hE' : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) (w : ℤ) :
    htMultE p ρE w = htMultE p ρE' w

theorem localDistinctHTP_iff_of_model {ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)}
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin 2) E)
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) :
    LocalDistinctHTP p ρ ↔ ∃ a b : ℤ, a ≠ b ∧ ∀ w : ℤ, htMultE p ρE w = Multiset.count w {a, b}

theorem localDistinctHTP_iff_forall (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)) :
    LocalDistinctHTP p ρ ↔
      (∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
          (ρE : GQp p →* GL (Fin 2) E),
          ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
        ∃ a b : ℤ, a ≠ b ∧
          ∀ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
            (ρE : GQp p →* GL (Fin 2) E),
            (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
            ∀ w : ℤ, htMultE p ρE w = Multiset.count w {a, b}

theorem localDistinctHTU_iff_of_model {ρ : GQp p →* GL (Fin 2) (PadicAlgCl p)}
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] (ρE : GQp p →* GL (Fin 2) E)
    (hE : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) :
    LocalDistinctHTU p ρ ↔ ∃ a b : ℤ, a ≠ b ∧ ∀ w : ℤ, htMultU p ρE w = Multiset.count w {a, b}
```

These mirror `PstModel.lean` §4–§5:

| `PstModel.lean` (pst) | `HTModel.lean` (Hodge–Tate) |
|---|---|
| `isAdmissible_iff_of_basis` | `htMultE_eq_of_basis` |
| `isAdmissible_iff_of_le` | `htMultE_eq_of_le` |
| `isPstF_model_iff` | `htMultE_model_eq` |
| `localIsPstF_iff_of_model` | `localDistinctHTP_iff_of_model` |
| `localIsPstF_iff_forall` | `localDistinctHTP_iff_forall` |

The two models are compared through the compositum `E ⊔ E'`, which is finite over `ℚ_p`
(`IntermediateField` instance).

## 3. Axioms

__AXIOMS__

## 4. Known issues

1. **On-the-spot (provenance (c)).** Neither the manuscript nor a source it cites states that the Hodge–Tate
   multiplicities of a `ℚ̄_p`-representation are independent of the finite coefficient model. The step is standard:
   on underlying `ℚ_p`-representations, extending the coefficients is a finite direct sum. The manuscript states
   this fact in its de Rham lemma, L10976–10977, for the de Rham property, and uses it implicitly for the weights
   at L721–723 and L755–757. It is now proved in Lean.
2. **"At every coefficient embedding" versus `htMultE`.** The manuscript's lemma (L10948–10950) states the weights
   *at every coefficient embedding* `τ : C_ℓ → ℚ̄_ℓ`. Lean's `htMultE` is the `E`-dimension of
   `(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`, a quantity with no embedding index. They agree because `G_{ℚ_p}` permutes
   the embeddings transitively, so the embedding-wise multiset is the same at every `τ` and equals `htMultE`. That
   argument is from memory (UNVERIFIED as a citation; standard). This task neither formalizes nor uses it. It
   concerns how Lemma `lem:de-rham-descent` is read, not this task's theorems.
3. **Finiteness is not needed.** The theorems use `finrank`, which is `0` on infinite-dimensional spaces, but every
   identity used holds for any spaces: `finrank_fin_pi_sub` over the domain `ℚ_p`, and `Module.finrank_mul_finrank`
   for free modules. So no Ax–Sen–Tate finiteness (`HTFinite.finiteDimensional_htSpaceE`) is used, and the results
   hold even where the invariants would be infinite-dimensional.
4. **No error found** in the manuscript or in a source on the steps checked (§5).

## 5. Manuscript check

__MSCHECK__

## 6. Reproduction

```
lake build ZInQKernel.Contrib.OneProof.PstModel          # dependencies of the new file
lake env lean ZInQKernel/Contrib/OneProof/HTModel.lean   # the new file, with #print axioms in the scratch copy
```
