# Task: `T_p(A)` from the `F̄`-points equals `T_p(A)` from the `ℂ_p`-points, `G_F`-equivariantly (for `colmez1992DeRhamAbVar`)

You are running unattended, so nobody will answer questions while you work. Make small decisions yourself and list them in the report. If something would change what a statement means, stop and report instead. All paths are relative to the repository root.

The evidence below was read at commit `01ad7955bb1a02aeecf770a1834b04bbf8d69ca0`. Work on the base commit named in your launch note. Launch note: your base is `f3add5ae8029bd36f55ccb84a4317bc0a3a5121a` (fork main at launch); your worktree is on branch `wip/tate-cp-ident` at that commit. Confirm with `git rev-parse HEAD` before anything else, and stop if it differs. If line numbers have moved, find each declaration by its name.

## 1. Goal and why

* **The field.** The frozen field `colmez1992DeRhamAbVar` belongs to bundle `HDec.HSyn.OpenAddedLeaves30` (`ZInQKernel/OneProof/H/TailZ106.lean:26`), which `ZInQ.OneProof.frozenTarget` takes at `ZInQKernel/OneProof/Main.lean:276`. Its row is `DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar` (`ZInQKernel/Contrib/OneProof/TatePrints/Rows.lean:54-61`). The row reads Colmez, Math. Ann. 292 (1992), Théorème 5.2 (i)-(ii), p. 639.
* **The mismatch.** The row builds its Tate module from the `F̄`-points: `A.T ℓ := Tate.T ℓ (Additive (A.Pt (AlgebraicClosure K)))` (`ZInQKernel/Contrib/G9/I4Layer.lean:661`). Colmez builds `T_p(X)` from `X(C_p)` (quoted at `Rows.lean:29-33`; reading point at `Rows.lean:52-53`).
* **Why it is GLUE.** The readings call the passage between the two a reading step that no Lean theorem covers (`docs/research/tate-prints-adversarial-readings.md:108-116`). The fidelity rule (`docs/one-proof/STATEMENT-CHECKS.md:202-203`) allows only four verdicts: match, match after a proved identification named by its Lean theorem, direct instance, or mismatch. So the field is rated GLUE.
* **What your theorem does.** It is the named identification. With it, this point becomes "match after a proved identification", which reopens the LEAF path. It proves no frozen field, so no count changes. A rating change also needs separate rulings by the lead (proper model, `ℤ_p`-linearity). Those rulings are not part of this task.

## 2. Rules

1. **Add-only.** Create exactly one Lean file: `ZInQKernel/Contrib/OneProof/TatePrints/CpPoints.lean` (module `ZInQKernel.Contrib.OneProof.TatePrints.CpPoints`). Your report files `.fleet/tate-cp-ident.md` and `scratch/tate-cp-ident/log.md` are the only other files you add.
   * Edit no existing file. That includes `Rows.lean`, `Glue.lean`, `FoldCheck.lean`, `ZInQKernel/Contrib/AllContrib.lean`, any doc, `lakefile.toml` and `lake-manifest.json`.
   * Do not run `lake update`. Do not import `ZInQKernel.OneProof.Main`.
2. **Never weaken or restate the row.** Do not write a variant of `Colmez1992DeRhamAbVar`, and do not prove anything "toward" it.
3. **The content of the section 3 statements is fixed.** You may fix elaboration details: implicit or named arguments, coercion arrows, `show`/`change`, local `set_option`s. List every such fix in the report. You may not:
   * drop a conjunct;
   * add a hypothesis;
   * change the `F`-structure on `ℂ_p`, the map `κ`, or either Galois action.
4. **No `sorry`, `admit`, new `axiom`, `native_decide`, `#eval`, `run_cmd`, notation or macros in committed code.** Every commit must build. Keep work in progress in an uncommitted scratch file.
5. **`Algebra F ℂ_[p]` is a low-priority local instance only.** Mark the definition `@[instance_reducible] def cpAlgF ...` (the tree's pattern: `ZInQKernel/Contrib/G9/G9.lean:39-41`) and register it with `attribute [local instance low] cpAlgF`. Even as a local instance it can also match `Algebra ℚ_[p] ℂ_[p]` (take `F := ℚ_[p]`) and `Algebra (fieldF p F) ℂ_[p]`, and those matches are not definitionally equal to the existing instances, because `embF` is a `Classical.choose`. After Step 1, check in an uncommitted scratch file with `#synth` that, inside your section, `Algebra ℚ_[p] ℂ_[p]` and `Algebra (fieldF p F) ℂ_[p]` still resolve to the pre-existing instances. If either does not, drop the attribute, put `letI : Algebra F ℂ_[p] := cpAlgF p F` inside each statement and definition that needs it, and report the switch. Never make it a global instance.
6. **Do not `open HDec`.** The tree contains second copies of the same names:
   * `HDec.ZInQ.Contrib.G9.embF`, `.phiF`, `.iotaCp`, … in `ZInQKernel/OneProof/H/TailC.lean`, inside `namespace HDec` from line 16;
   * `HDec.PkgI4.cpAct`, `.oAct`, `.gfToGqp` in `ZInQKernel/OneProof/H/LPrefix.lean`.

   Use the `ZInQ.Contrib.G9.*` and `ZInQ.Contrib.G9.PkgI4.*` versions, which are the ones the row resolves to (`Rows.lean:23`). Also write the kernel copy as `_root_.PkgI3.*` everywhere: under `open ZInQ.Contrib.G9`, a bare `PkgI3.Tate.map` or `PkgI3.AbVar` resolves to G9's third copy (`ZInQKernel/Contrib/G9/I3Layer.lean:537`, `:603`, `:622`).
7. **Stage only your files, by explicit path** (`git add ZInQKernel/Contrib/OneProof/TatePrints/CpPoints.lean`, and the two report files). Never use `git add -A`. Commit on your branch `wip/tate-cp-ident` (only that branch) after each step that builds; a background job pushes it, so do not run `git push` or `git fetch`. This host can be released without warning, and only pushed commits survive.

## 3. Target statements (draft, not compiled; `...` marks bodies you write)

```lean
import ZInQKernel.Contrib.OneProof.TatePrints.Rows
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# `T_p` of an abelian variety from its `F̄`-points and from its `ℂ_p`-points
(One paragraph, mathematics only. `F/ℚ_p` is finite. `ℂ_p` is an `F`-algebra through
`F ≅ F' ⊆ ℚ̄_p ⊆ ℂ_p`. `κ : F̄ → ℂ_p` is the inverse of `embF` followed by `ℚ̄_p ⊆ ℂ_p`.
Because `[pⁿ]` is finite, the `ℂ_p`-points of `A[pⁿ]` come from `F̄`. `G_F` acts on `ℂ_p`
through `gfToGqp` and `cpAct`, the automorphism whose restriction `oAct` defines `bdrAct`.)
-/

namespace DeRhamScholze.TatePrints

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `ℂ_p` as an `F`-algebra: `F ≅ F' = fieldF p F ⊆ ℚ̄_p ⊆ ℂ_p`, through `phiF`. -/
@[instance_reducible] def cpAlgF : Algebra F ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp (phiF p F).toRingHom).toAlgebra

attribute [local instance low] cpAlgF   -- rule 5: check with #synth, else switch to letI

/-- `κ : F̄ → ℂ_p`: the inverse of `embF` (the embedding behind `gfToGqp`), then `ℚ̄_p ⊆ ℂ_p`. -/
def fbarToCp : AlgebraicClosure F →ₐ[F] ℂ_[p] :=
  { (algebraMap (PadicAlgCl p) ℂ_[p]).comp (embFEquiv p F).symm.toRingHom with
    commutes' := fun _ => rfl }   -- fallback: `by simp [phiF]`

/-- `σ ∈ G_F` acting on `ℂ_p` by `cpAct (gfToGqp σ)`, as an `F`-algebra automorphism. -/
def cpGalF (σ : Field.absoluteGaloisGroup F) : ℂ_[p] ≃ₐ[F] ℂ_[p] := ...   -- Step 2

theorem cpGalF_apply (σ : Field.absoluteGaloisGroup F) (z : ℂ_[p]) :
    cpGalF p F σ z = cpAct p (gfToGqp p F σ) z := rfl

/-- `A(F̄) → A(ℂ_p)`, `P ↦ P ∘ Spec κ`. -/
def ptFbarToCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    A.Pt (AlgebraicClosure F) →* A.Pt ℂ_[p] :=
  ZInQ.Contrib.AbVarBC.extPt (DeRhamPrint.toKer A) (fbarToCp p F)

/-- `T_p` from `F̄`-points equals `T_p` from `ℂ_p`-points, `G_F`-equivariantly, for the actions
the row uses. -/
theorem colmezTateFbarCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    -- (a) the `F`-structure of `ℂ_p` is `F ≅ F' ⊆ ℚ̄_p ⊆ ℂ_p`
    (∀ y : F, algebraMap F ℂ_[p] y = iotaCp p F (equivFieldF p F y)) ∧
    -- (b) `κ ∘ embF` is the inclusion `ℚ̄_p ⊆ ℂ_p`
    (∀ x : PadicAlgCl p, fbarToCp p F (embF p F x) = (x : ℂ_[p])) ∧
    -- (c) `κ ∘ σ = cpAct (gfToGqp σ) ∘ κ`
    (∀ (σ : Field.absoluteGaloisGroup F) (y : AlgebraicClosure F),
      fbarToCp p F (galF F σ y) = cpAct p (gfToGqp p F σ) (fbarToCp p F y)) ∧
    -- (d) on `𝓞_ℂ_p`, `cpGalF σ` is `oAct (gfToGqp σ)`, from which `bdrAct (gfToGqp σ)` is built
    (∀ (σ : Field.absoluteGaloisGroup F) (z : 𝓞_ℂ_[p]),
      ((oAct p (gfToGqp p F σ) z : 𝓞_ℂ_[p]) : ℂ_[p]) = cpGalF p F σ (z : ℂ_[p])) ∧
    -- (e) `G_F`-equivariance on points
    (∀ (σ : Field.absoluteGaloisGroup F) (P : A.Pt (AlgebraicClosure F)),
      ptFbarToCp p F A (A.galAct σ P) = A.galAct (cpGalF p F σ) (ptFbarToCp p F A P)) ∧
    -- (f) injective
    Function.Injective (ptFbarToCp p F A) ∧
    -- (g) onto the `pⁿ`-torsion, for every `n`
    (∀ (n : ℕ) (q : A.Pt ℂ_[p]), q ^ (p ^ n) = 1 → ∃ P, ptFbarToCp p F A P = q) ∧
    -- (h) bijective from the row's `A.T p` to `T_p(A(ℂ_p))`
    Function.Bijective
      (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A))) ∧
    -- (i) `G_F`-equivariant on `T_p`
    (∀ (σ : Field.absoluteGaloisGroup F) (x : A.T p),
      ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A))
          (A.galT (ℓ := p) σ x) =
        ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (A.galAct (cpGalF p F σ)))
          (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (ptFbarToCp p F A)) x)) := ...

/-- The `V_p` form, stated against the row's `A.galRep p`. -/
theorem colmezVpFbarCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    ∃ Ψ : A.V p ≃ₗ[ℚ_[p]]
        ℚ_[p] ⊗[ℤ_[p]] ZInQ.Contrib.G9.PkgI4.I3.Tate.T p (Additive (A.Pt ℂ_[p])),
      (∀ t : A.T p, Ψ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t) =
        (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]]
          ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A)) t) ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (v : A.V p),
        Ψ (A.galRep p σ v) =
          (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (A.galAct (cpGalF p F σ)))).baseChange ℚ_[p] (Ψ v) := ...

end

end DeRhamScholze.TatePrints
```

Both imports are already in the import closure of `ZInQKernel.OneProof.Main`:
* `Rows` is imported by `TatePrints/Glue.lean`, then by `OneProof/H/TailZ106.lean`, then by `Main.lean:1`.
* `AbVarBC.Main` is imported by `OneProof/H/LF4T5.lean:11`, then by `DeRhamPrint`, `DeRhamPrintDirect` and `DeRhamRange`, then by `Main.lean:3`.

`Rows` already brings in `G9.Galois`, `G9.Local`, `DeRhamPrint`, `DeRhamPrintDirect` and `DeRhamScholze`.

## 4. What exists (checked at the evidence commit)

**The row's abelian varieties** (`ZInQKernel/Contrib/G9/I4Layer.lean`, namespace `ZInQ.Contrib.G9.PkgI4.I3`):
* `AbVar`: :526-534.
* `AbVar.ptObj`: :618-619 (`L` explicit).
* `AbVar.Pt`: :622 (`A.Pt L`; needs `[Algebra K L]`).
* `AbVar.galHom`: :627-632.
* `AbVar.galAct`: :648-651 (`L` implicit; `galHom σ ≫ P`, i.e. `σ` applied to coordinates; left action, see `galHom_mul` :640).
* `AbVar.T`: :661. `AbVar.V`: :664.
* `AbVar.galT`: :669-670 (`ℓ` implicit). `AbVar.galRep`: :683-703.
* `Tate.T`: :426-436. `Tate.pow_smul_eq_zero`: :441. `Tate.map`: :507-510 (`ℓ` implicit). `Tate.map_apply`: :512.

**The Galois action** (same file, namespace `ZInQ.Contrib.G9.PkgI4`, `p` explicit):
* `GQp`: :802.
* `cpAct`: :830-831, the completion of `σ`. `cpAct_coe`: :833-835. `cpAct_algebraMap`: :837. `continuous_cpAct`: :968. `cpAct_inv_apply`: :976.
* `oAct`: :983-986, defined as `(cpAct p σ).restrict 𝓞_ℂ_[p] 𝓞_ℂ_[p] _`.
* `BdR`: :995. `bdrAct`: :1000-1001, defined as `DR.bdrMap p (oAct p σ) (oAct p σ⁻¹) …`.
* `gfToGqp`: :1180-1182 (`F` explicit).
* Also `cpAct_mul` (:65) and `cpAct_one` (:72) in `ZInQKernel/Contrib/G9/Local.lean`, namespace `ZInQ.Contrib.G9`.

**The embedding behind `gfToGqp`** (`ZInQKernel/Contrib/G9/Galois.lean`, namespace `ZInQ.Contrib.G9`):
* `galF`: :28.
* `exists_emb_gfToGqp`: :31-40.
* `embF`: :43, a `Classical.choose`. `embF_algebraMap`: :45.
* `embF_gfToGqp`: :49-51, which says `embF p F (gfToGqp p F σ x) = galF F σ (embF p F x)`.
* `embF_bijective`: :53. `embFEquiv`: :68. `embFEquiv_apply`: :71 (rfl).
* `phiF`: :74-80, with `toRingHom := (embFEquiv p F).symm.toRingHom.comp (algebraMap F (AlgebraicClosure F))`.
* `embF_phiF`: :82. `fieldF`: :87. `equivFieldF`: :90.
* Lines 127-130 show that `gfToGqp p F σ` fixes `phiF p F y`.

**Fixed-point lemmas with no Galois hypothesis on `F`** (the row has none):
* `DeRhamPrint.Direct.gfToGqp_fix`: `ZInQKernel/Contrib/OneProof/DeRhamPrintDirect.lean:74-79`.
* `DeRhamPrint.Direct.cpAct_iotaCp_gf`: same file, :81-86.
* `ZInQ.Contrib.HodgeSplit.range_gfToGqp_eq`: `ZInQKernel/OneProof/H/TailS.lean:374`.
* Not usable, because they need `[IsGalois ℚ_[p] F]`: `ZInQ.Contrib.G9.range_gfToGqp` (Galois.lean:123, under :98) and `ZInQ.Contrib.G9.cpAct_iotaCp` (Local.lean:169-175).
* `ZInQ.Contrib.G9.iotaCp` (Local.lean:165-167) is `F' ⊆ ℚ̄_p ⊆ ℂ_p`. It equals the `F'`-algebra map of `ℂ_[p]` by `rfl` (`DeRhamScholze.HT.algebraMap_algCp`, `ZInQKernel/Contrib/OneProof/DeRhamScholzeHT.lean:293`).

**Algebraic geometry, proved for the kernel copy** `_root_.PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean:162-170`; `ptObj` :254, `Pt` :258, `T` :297, `galRep` :319). Namespace `ZInQ.Contrib.AbVarBC`; every field is `: Type`.
* `ZInQKernel/Contrib/AbVarBC/Points.lean`:
  * `extHom`: :159-165. `epi_spec_map_field`: :171-181.
  * `extPt`: :188-191. `extPt_apply`: :193. `extPt_injective`: :196-197.
  * `extPt_galAct`: :201-214. It needs `σ : Ω₂ ≃ₐ[K] Ω₂` and `∀ x, κ (τ x) = σ (κ x)`.
* `ZInQKernel/Contrib/AbVarBC/Torsion.lean`:
  * `exists_lift_of_isFinite`: :41-90. `Ω` is algebraically closed, `Ω₂` is any field, `κ : Ω →ₐ[K] Ω₂`, `g : Z ⟶ Spec K` is finite.
  * `comp_natCast_hom`: :99-107.
  * `torsionDescends_of_isFinite`: :113-148. This is your template. Its target is `AlgebraicClosure L`, reached through `bcPt` at :119 and :142-143.
* `ZInQKernel/Contrib/AbVarBC/Tate.lean`:
  * `tate_map_bijective_of_torsion`: :39-53, stated for `PkgI3.Tate.map`.
  * Patterns: `tateBC_bijective_of_torsionDescends` :111-113, `tateBC_galT` :98-103, `vBC` and `vBC_galRep` :130-151.
* Finiteness of `[n]`:
  * `ZInQ.Contrib.AbVarBC.mulIsogeny : G0FibreSimple.MulIsogeny` (`ZInQKernel/Contrib/AbVarBC/Main.lean:27`; definition at `Mul.lean:133-135`: in characteristic 0, `[n]` is finite and surjective for `n ≠ 0`).
  * Its recorded axioms are the standard three (`scratch/g9-abvarbc/axioms-output.txt:33`, not re-run).
  * `G9Mul.lean:54-59` shows how to get `IsFinite [ℓⁿ].left` from it.
* Moving between the two copies:
  * `DeRhamPrint.toKer` (`ZInQKernel/Contrib/OneProof/DeRhamPrint.lean:355-356`) builds the kernel copy from the same fields.
  * Precedents that the copies agree definitionally (`rfl`): `ZInQ.Contrib.AbVarBC.vToI4` and `vToI4_galRep` (`ZInQKernel/Contrib/AbVarBC/G9Instance.lean:59-63`), and `DeRhamScholze.galRep_apply_toKer` (`ZInQKernel/Contrib/OneProof/DeRhamScholze.lean:279-282`).
  * `PkgI3.Tate.map_injective`: `ZInQKernel/HDecomp/I3Linalg/TateBC.lean:27-31`.

**Mathlib** (pinned rev `56a005855ea17e0b0958f73ec801ae140b0a1679`, `lake-manifest.json:19`). Citations were read in a local checkout whose HEAD is exactly this rev, with a clean tree. Paths are under `.lake/packages/mathlib/`.
* `Mathlib/NumberTheory/Padics/Complex.lean`:
  * `PadicAlgCl`: :54. `PadicComplex`: :137 (notation `ℂ_[p]` at :140).
  * `PadicComplex.coe_eq`: :151 (rfl). The `IsScalarTower` instance: :155.
  * `charZero`: :240. `isAlgClosed`: :244.
  * `PadicComplexInt` (notation `𝓞_ℂ_[p]`): :251-254.
* `Field.absoluteGaloisGroup.map`: `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean:84-91`. It is restriction along `IsAlgClosed.lift`, which Mathlib documents as "a (random) homomorphism" (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean:350-353`).
* `charZero_of_injective_algebraMap`: `Mathlib/Algebra/CharP/Algebra.lean:76`.
* `RingHom.coe_restrict_apply` (rfl): `Mathlib/Algebra/Ring/Subsemiring/Basic.lean:761`.
* `AlgHom.equivFieldRange` (simp lemma `equivFieldRange_apply_coe`): `Mathlib/FieldTheory/IntermediateField/Basic.lean:557-558`.

**Missing from the tree:**
* an `Algebra F ℂ_[p]`;
* any map `AlgebraicClosure F → ℂ_[p]`;
* `A.Pt ℂ_[p]`.

Torsion descent into any target field already exists: `T5Torsion.exists_extPt_eq` (`ZInQKernel/OneProof/H/LF4T5.lean:335`), with binders `{K : Type} [Field K] (A : _root_.PkgI3.AbVar K) {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) (N : ℕ) (hfin : IsFinite ((((N : ℤ)) : _root_.PkgI3.AbVar.End A).hom.left)) (q : A.Pt Ω₂) (hq : q ^ N = 1) : ∃ p : A.Pt Ω, extPt A κ p = q`.

## 5. Route (commit after each step that builds)

**Step 0. Check the build.**
* Run `lake build +ZInQKernel.Contrib.OneProof.TatePrints.Rows`. On a tree where `+ZInQKernel.OneProof.Main` is already built, this compiles nothing new. If it would build the closure from scratch, follow your launch note on builds.
* Always build your module by name: `lake build +ZInQKernel.Contrib.OneProof.TatePrints.CpPoints`. The default `lake build` (target `ZInQKernel`) does not import it. When it lands, the lead's integration chain adds it to the contrib aggregation, and the chain's contrib build compiles it at every later landing; do not edit `ZInQKernel/Contrib/AllContrib.lean` yourself.

**Step 1. Maps between fields.** Write the header, `cpAlgF`, the local instance and `fbarToCp`, then prove:
* `cpAlgF_algebraMap (y : F) : algebraMap F ℂ_[p] y = iotaCp p F (equivFieldF p F y)`. Try `rfl`; otherwise `simp [iotaCp, equivFieldF]`.
* `fbarToCp_embF (x : PadicAlgCl p) : fbarToCp p F (embF p F x) = (x : ℂ_[p])`. Use `embFEquiv_apply`, `RingEquiv.symm_apply_apply` and `PadicComplex.coe_eq`.
* `fbarToCp_galF (σ) (y) : fbarToCp p F (galF F σ y) = cpAct p (gfToGqp p F σ) (fbarToCp p F y)`. Put `x := (embFEquiv p F).symm y`, so that `y = embF p F x`. Rewrite with `embF_gfToGqp` from right to left, then use `cpAct_coe`.

Build, then commit.

**Step 2. `cpGalF`.** Sketch:

```lean
def cpGalF (σ : Field.absoluteGaloisGroup F) : ℂ_[p] ≃ₐ[F] ℂ_[p] where
  toFun := cpAct p (gfToGqp p F σ)
  invFun := cpAct p (gfToGqp p F σ)⁻¹
  left_inv := cpAct_inv_apply p (gfToGqp p F σ)
  right_inv z := by simpa using cpAct_inv_apply p (gfToGqp p F σ)⁻¹ z
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' r := by
    -- `algebraMap F ℂ_[p] r = ↑(phiF p F r)`; then `cpAct_coe` and
    -- `DeRhamPrint.Direct.gfToGqp_fix p F σ ⟨phiF p F r, r, rfl⟩`
    sorry  -- placeholder in this brief only; do not commit
```

Then prove `cpGalF_apply` (rfl) and `coe_oAct_gfToGqp (σ) (z : 𝓞_ℂ_[p]) : ((oAct p (gfToGqp p F σ) z : 𝓞_ℂ_[p]) : ℂ_[p]) = cpGalF p F σ z`. The last one is `rfl` or `RingHom.coe_restrict_apply`. Build, then commit.

**Step 3. The map on points.**
* Define `ptFbarToCp` as in section 3. The row's copy and the kernel copy are the same definitionally.
* `ptFbarToCp_injective` follows from `extPt_injective`.
* `ptFbarToCp_galAct (σ P)` follows from `extPt_galAct`, with `τ := σ`, target automorphism `cpGalF p F σ`, and hypothesis `fbarToCp_galF`.
* If Lean refuses to accept a term of one copy at the other copy's type, copy `extHom`, `extPt`, `extPt_injective` and `extPt_galAct` (`Points.lean:159-214`) for `ZInQ.Contrib.G9.PkgI4.I3.AbVar.ptObj`.

Build, then commit.

**Step 4. Torsion descent into `ℂ_p`.** Use the existing lemma; do not transcribe `Torsion.lean`.
* Prove `ptFbarToCp_torsion (n) (q) (hq : q ^ (p ^ n) = 1) : ∃ P, ptFbarToCp p F A P = q` by applying `T5Torsion.exists_extPt_eq` to `DeRhamPrint.toKer A` with `Ω := AlgebraicClosure F`, `Ω₂ := ℂ_[p]`, `κ := fbarToCp p F` and `N := p ^ n`.
* For `hfin`: get `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective`, then finiteness from `(ZInQ.Contrib.AbVarBC.mulIsogeny F (DeRhamPrint.toKer A) _ h).1` with `h : ((p ^ n : ℕ) : ℤ) ≠ 0`, as in `G9Mul.lean:58-59`.
* If the row's copy and the kernel copy do not unify at `ptFbarToCp`, bridge them with `show`/`change` (definitional precedents in section 4) and report it.

Build, then commit.

**Step 5. `T_p`.**
* Bijectivity: apply `ZInQ.Contrib.AbVarBC.tate_map_bijective_of_torsion` with `htors := fun n q hq => ptFbarToCp_torsion p F A n (Additive.toMul q) hq` (pattern at `Tate.lean:111-113`).
* That lemma concludes about `PkgI3.Tate.map`, while the statement uses the row's `ZInQ.Contrib.G9.PkgI4.I3.Tate.map`. The two have the same body, so try `exact`. If Lean refuses, port `PkgI3.Tate.map_injective` (4 lines) and `tate_map_bijective_of_torsion` (15 lines) to the row's `Tate` namespace, using `ZInQ.Contrib.G9.PkgI4.I3.Tate.pow_smul_eq_zero` (`I4Layer.lean:441`).
* Conjunct (i): `Subtype.ext; funext n`, then `congrArg Additive.ofMul (ptFbarToCp_galAct …)`, as in `tateBC_galT`.
* Assemble `colmezTateFbarCp`.

Build, then commit.

**Step 6. `V_p`.**
* Set `Ψ := (LinearEquiv.ofBijective _ hb).baseChange ℤ_[p] ℚ_[p] _ _`.
* The first clause follows from `LinearEquiv.baseChange_tmul`.
* The second clause is induction on the tensor product, as in `vBC_galRep` (that lemma goes in the inverse direction).

Build, then commit.

**Step 7. Final check (not committed).**
* Create a local `ProofCheck.lean` at the repository root that imports the module.
* It should run `#check @DeRhamScholze.TatePrints.colmezTateFbarCp`, `#check @DeRhamScholze.TatePrints.colmezVpFbarCp`, and `#print axioms` for both.
* Run `lake env lean ProofCheck.lean`. The only axioms allowed are `propext`, `Classical.choice` and `Quot.sound`.
* You do not need `#discharges`, because no frozen field is discharged.

**Routes not to use:**
* Counting (`card_torsion`, `ZInQKernel/Contrib/OneProof/MumfordTorsionAlgClosed.lean:27-30`). It works over a different formalism and would need a `ℂ_p` transport.
* `tateBC_galT` or `ptBC_galAct` with `L = ℂ_[p]`. They intertwine only `Aut(L̄/L)`, which is not the row's action.
* `IsAlgClosed.lift` as `κ`. A different embedding breaks the intertwining with `gfToGqp`.

## 6. Stop rule

* **Expected outcome:** no stop. Every deep input is already proved: `mulIsogeny`, `exists_lift_of_isFinite`, `extPt_injective` and `extPt_galAct`.
* **When to stop a step:** if it needs a theory that is in neither Mathlib nor the tree, and is more than an adaptation of the files above. Examples: models over `𝒪_F`, the valuative criterion for such a model, continuity of the Galois action, counting torsion over `ℂ_p`.
* **What to do when you stop:**
  1. Add a `def <Name> : Prop` to the new file that states the smallest missing fact.
  2. Prove the rest of the target from it as `<target>_of_<name>`, with the Prop as an explicit hypothesis (never as an instance).
  3. Build, commit, and report.
* **If Step 4 nevertheless fails** (it should not: the lemma exists), for a reason other than elaboration, the Prop is:

```lean
def CpTorsionDescends : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (n : ℕ) (q : A.Pt ℂ_[p]),
    q ^ (p ^ n) = 1 → ∃ P, ptFbarToCp p F A P = q
```

* **If a section 3 conjunct looks false or ill-typed for reasons beyond syntax,** stop. Report the exact error and your diagnosis, and do not change the conjunct's meaning.
* **Out of scope:** proper models, Colmez's pairing, and the row itself.

## 7. Report

Write the report to `.fleet/tate-cp-ident.md` (first lines: whether both target theorems build, their `#print axioms`, and the final SHA) and keep a results log at `scratch/tate-cp-ident/log.md` (commands, outcomes, wall times; no narrative). Commit the report last and give the final SHA in your last message. Resuming: if `scratch/tate-cp-ident/log.md` exists, an earlier run was interrupted; read it and continue where it stopped. You run unattended: keep working until the report is written and committed.

The report contains:

1. The branch and final commit, with SHAs copied from `git rev-parse HEAD` output (never retyped), plus `git log --oneline` of your commits.
2. The final text of `cpAlgF`, `fbarToCp`, `cpGalF`, `ptFbarToCp`, `colmezTateFbarCp` and `colmezVpFbarCp`, copied from the file.
3. The `lake env lean ProofCheck.lean` output: the `#check` lines and the `#print axioms` lines.
4. The build command and the last lines of its output.
5. Every syntax-level departure from section 3, with the reason.
6. If you stopped: each named Prop, its exact statement, why it needs more than an adaptation, and what is proved from it.

## 8. Hygiene

For everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer"). Theorem numbers you give from memory are UNVERIFIED; you have no network.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.
Throttle (the lead, 11-21): run every Lean build as `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build ...`. Never touch other worktrees or their processes.
Build note: never let a single tool call run longer than 2 hours: the tool stops background jobs at 2 hours. If a build would run longer, build its imports one module at a time (`lake build <Module>`, each in its own call, one after another) and then resume; lake resumes incrementally. Check single files with `lake env lean <file>` after their imports are built.
