# tate-cp-ident report

**Both target theorems build**, with no `sorry` and no stop rule triggered.
* `#print axioms`:
```
'DeRhamScholze.TatePrints.colmezTateFbarCp' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamScholze.TatePrints.colmezVpFbarCp' depends on axioms: [propext, Classical.choice, Quot.sound]
```
* Lean commit (last commit before this report): `4085769627fd5226df28ea60226263cec2bdb38a` (copied from `git rev-parse HEAD`). This report is
  committed after it on `wip/tate-cp-ident`; the final SHA is the commit that adds this file.

## 1. Branch and commits

Branch `wip/tate-cp-ident`, base `f3add5ae8029bd36f55ccb84a4317bc0a3a5121a` (confirmed by `git rev-parse HEAD` at start).
```
408576962 TatePrints/CpPoints: A(Fbar) -> A(C_p), torsion descent, T_p and V_p identification (colmezTateFbarCp, colmezVpFbarCp)
d1575c659 TatePrints/CpPoints: F-structure on C_p, kappa : Fbar -> C_p, G_F action on C_p (steps 1-2)
```

## 2. Final text (copied from `ZInQKernel/Contrib/OneProof/TatePrints/CpPoints.lean`)

```lean
@[instance_reducible] def cpAlgF : Algebra F ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp (phiF p F).toRingHom).toAlgebra

def fbarToCp : AlgebraicClosure F →ₐ[F] ℂ_[p] :=
  { (algebraMap (PadicAlgCl p) ℂ_[p]).comp (embFEquiv p F).symm.toRingHom with
    commutes' := fun _ => rfl }

def cpGalF (σ : Field.absoluteGaloisGroup F) : ℂ_[p] ≃ₐ[F] ℂ_[p] where
  toFun := cpAct p (gfToGqp p F σ)
  invFun := cpAct p (gfToGqp p F σ)⁻¹
  left_inv := cpAct_inv_apply p (gfToGqp p F σ)
  right_inv z := by simpa using cpAct_inv_apply p (gfToGqp p F σ)⁻¹ z
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' r := by
    show cpAct p (gfToGqp p F σ) (iotaCp p F (equivFieldF p F r)) = iotaCp p F (equivFieldF p F r)
    exact DeRhamPrint.Direct.cpAct_iotaCp_gf p F σ _

def ptFbarToCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    A.Pt (AlgebraicClosure F) →* A.Pt ℂ_[p] :=
  ZInQ.Contrib.AbVarBC.extPt (DeRhamPrint.toKer A) (fbarToCp p F)

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
            (MonoidHom.toAdditive (ptFbarToCp p F A)) x)) :=
  ⟨cpAlgF_algebraMap p F, fbarToCp_embF p F, fbarToCp_galF p F, coe_oAct_gfToGqp p F,
    ptFbarToCp_galAct p F A, ptFbarToCp_injective p F A, ptFbarToCp_torsion p F A,
    ptFbarToCp_tate_bijective p F A, ptFbarToCp_tate_galT p F A⟩

theorem colmezVpFbarCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    ∃ Ψ : A.V p ≃ₗ[ℚ_[p]]
        ℚ_[p] ⊗[ℤ_[p]] ZInQ.Contrib.G9.PkgI4.I3.Tate.T p (Additive (A.Pt ℂ_[p])),
      (∀ t : A.T p, Ψ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t) =
        (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]]
          ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A)) t) ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (v : A.V p),
        Ψ (A.galRep p σ v) =
          (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (A.galAct (cpGalF p F σ)))).baseChange ℚ_[p] (Ψ v) := by
  let e := LinearEquiv.ofBijective _ (ptFbarToCp_tate_bijective p F A)
  refine ⟨e.baseChange ℤ_[p] ℚ_[p] _ _, fun t => ?_, fun σ v => ?_⟩
  · rw [LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
  · induction v using TensorProduct.inductionOn with
    | tmul a t =>
      change e.baseChange ℤ_[p] ℚ_[p] _ _ ((A.galT (ℓ := p) σ).baseChange ℚ_[p] (a ⊗ₜ t)) = _
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        ptFbarToCp_tate_galT p F A σ t]
    | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
```

Supporting lemmas in the file: `cpAlgF_algebraMap` (rfl), `fbarToCp_embF`, `fbarToCp_galF`,
`cpGalF_apply` (rfl), `coe_oAct_gfToGqp` (rfl), `ptFbarToCp_injective`, `ptFbarToCp_galAct`,
`ptFbarToCp_torsion`, `ptFbarToCp_tate_bijective`, `ptFbarToCp_tate_galT`.

## 3. `lake env lean ProofCheck.lean` output (ProofCheck.lean not committed)

```
DeRhamScholze.TatePrints.colmezTateFbarCp : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (F : Type) [inst_1 : Field F]
  [inst_2 : Algebra ℚ_[p] F] [inst_3 : FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
  (∀ (y : F), (algebraMap F ℂ_[p]) y = (ZInQ.Contrib.G9.iotaCp p F) ((ZInQ.Contrib.G9.equivFieldF p F) y)) ∧
    (∀ (x : PadicAlgCl p), (DeRhamScholze.TatePrints.fbarToCp p F) ((ZInQ.Contrib.G9.embF p F) x) = ↑x) ∧
      (∀ (σ : Field.absoluteGaloisGroup F) (y : AlgebraicClosure F),
          (DeRhamScholze.TatePrints.fbarToCp p F) ((ZInQ.Contrib.G9.galF F σ) y) =
            (ZInQ.Contrib.G9.PkgI4.cpAct p ((ZInQ.Contrib.G9.PkgI4.gfToGqp p F) σ))
              ((DeRhamScholze.TatePrints.fbarToCp p F) y)) ∧
        (∀ (σ : Field.absoluteGaloisGroup F) (z : ↥𝓞_ℂ_[p]),
            ↑((ZInQ.Contrib.G9.PkgI4.oAct p ((ZInQ.Contrib.G9.PkgI4.gfToGqp p F) σ)) z) =
              (DeRhamScholze.TatePrints.cpGalF p F σ) ↑z) ∧
          (∀ (σ : Field.absoluteGaloisGroup F) (P : ZInQ.Contrib.G9.PkgI4.I3.AbVar.Pt (AlgebraicClosure F) A),
              (DeRhamScholze.TatePrints.ptFbarToCp p F A) ((A.galAct σ) P) =
                (A.galAct (DeRhamScholze.TatePrints.cpGalF p F σ)) ((DeRhamScholze.TatePrints.ptFbarToCp p F A) P)) ∧
            Function.Injective ⇑(DeRhamScholze.TatePrints.ptFbarToCp p F A) ∧
              (∀ (n : ℕ) (q : ZInQ.Contrib.G9.PkgI4.I3.AbVar.Pt ℂ_[p] A),
                  q ^ p ^ n = 1 → ∃ P, (DeRhamScholze.TatePrints.ptFbarToCp p F A) P = q) ∧
                Function.Bijective
                    ⇑(ZInQ.Contrib.G9.PkgI4.I3.Tate.map
                        (MonoidHom.toAdditive (DeRhamScholze.TatePrints.ptFbarToCp p F A))) ∧
                  ∀ (σ : Field.absoluteGaloisGroup F) (x : ZInQ.Contrib.G9.PkgI4.I3.AbVar.T p A),
                    (ZInQ.Contrib.G9.PkgI4.I3.Tate.map
                          (MonoidHom.toAdditive (DeRhamScholze.TatePrints.ptFbarToCp p F A)))
                        ((A.galT σ) x) =
                      (ZInQ.Contrib.G9.PkgI4.I3.Tate.map
                          (MonoidHom.toAdditive (A.galAct (DeRhamScholze.TatePrints.cpGalF p F σ))))
                        ((ZInQ.Contrib.G9.PkgI4.I3.Tate.map
                            (MonoidHom.toAdditive (DeRhamScholze.TatePrints.ptFbarToCp p F A)))
                          x)
DeRhamScholze.TatePrints.colmezVpFbarCp : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (F : Type) [inst_1 : Field F]
  [inst_2 : Algebra ℚ_[p] F] [inst_3 : FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
  ∃ Ψ,
    (∀ (t : ZInQ.Contrib.G9.PkgI4.I3.AbVar.T p A),
        Ψ (1 ⊗ₜ[ℤ_[p]] t) =
          1 ⊗ₜ[ℤ_[p]]
            (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (MonoidHom.toAdditive (DeRhamScholze.TatePrints.ptFbarToCp p F A))) t) ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (v : ZInQ.Contrib.G9.PkgI4.I3.AbVar.V p A),
        Ψ (((ZInQ.Contrib.G9.PkgI4.I3.AbVar.galRep p A) σ) v) =
          (LinearMap.baseChange ℚ_[p]
              (ZInQ.Contrib.G9.PkgI4.I3.Tate.map
                (MonoidHom.toAdditive (A.galAct (DeRhamScholze.TatePrints.cpGalF p F σ)))))
            (Ψ v)
'DeRhamScholze.TatePrints.colmezTateFbarCp' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamScholze.TatePrints.colmezVpFbarCp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Build

Command: `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build +ZInQKernel.Contrib.OneProof.TatePrints.CpPoints`
(the line quoted above `✔` comes from a linter note in an upstream module that the build replays, not from this file; the build shows no warnings from `CpPoints`):
```
Basis.equivFun_apply, Algebra.smul_def]

✔ [11070/11070] Built ZInQKernel.Contrib.OneProof.TatePrints.CpPoints (7.2s)
Build completed successfully (11070 jobs).
```

## 5. Departures from section 3, and small decisions

* The statements of `colmezTateFbarCp` and `colmezVpFbarCp` are the section 3 text, with no change to their elaboration.
  `cpAlgF` and `ptFbarToCp` are verbatim. `fbarToCp` is verbatim, and `commutes' := fun _ => rfl` worked, so no fallback was needed.
* `cpGalF.commutes'`: proved with `show cpAct p (gfToGqp p F σ) (iotaCp p F (equivFieldF p F r)) = iotaCp p F (equivFieldF p F r)`
  and `DeRhamPrint.Direct.cpAct_iotaCp_gf p F σ _`, in place of the sketched `phiF`/`gfToGqp_fix` route. The definition's content is unchanged.
* Rule 5: kept `attribute [local instance low] cpAlgF`. A `#synth` check in a temporary uncommitted section, placed after Step 2 inside
  the section, gave `Algebra ℚ_[p] ℂ_[p]` → `UniformSpace.Completion.algebra (PadicAlgCl p) ℚ_[p]` and
  `Algebra (fieldF p F) ℂ_[p]` → `(fieldF p F).instAlgebraSubtypeMem`, both pre-existing instances. So there was no switch to `letI`.
* Step 4 `hfin`: used `have` instead of `haveI` for `CharZero F` (linter). The `(p ^ n : ℕ) : ℤ) ≠ 0` proof is `exact_mod_cast (pow_pos _ n).ne'`.
* No bridging was needed between the row's `ZInQ.Contrib.G9.PkgI4.I3` copy and the kernel copy `_root_.PkgI3`. `extPt`, `extPt_injective`,
  `extPt_galAct`, `T5Torsion.exists_extPt_eq` and `ZInQ.Contrib.AbVarBC.tate_map_bijective_of_torsion` (stated for `PkgI3.Tate.map`)
  were applied directly at the row's types, with no `show`/`change` and no ported copies.
* `colmezVpFbarCp`: `Ψ := (LinearEquiv.ofBijective _ (ptFbarToCp_tate_bijective p F A)).baseChange ℤ_[p] ℚ_[p] _ _`, with the
  Galois clause proved by `TensorProduct.inductionOn` (the non-deprecated form of `induction_on`), as in `vBC_galRep`.
* No existing file was edited. Added: `ZInQKernel/Contrib/OneProof/TatePrints/CpPoints.lean`, `.fleet/tate-cp-ident.md` and
  `scratch/tate-cp-ident/log.md`. `ZInQKernel/Contrib/AllContrib.lean` was not touched, so the lead's integration chain adds the module.

## 6. Stop rule

Not triggered. No named Prop was added.

The theorem proves no frozen field and changes no count. Rating `colmez1992DeRhamAbVar` as "match after a proved identification"
still needs the lead's separate rulings (proper model, `ℤ_p`-linearity).
