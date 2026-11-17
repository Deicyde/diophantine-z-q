# hodgetate-from-dr: `hodgeTateDecompAbVar` removed (−1 field, −1 GLUE)

Task hodgetate-from-dr, 2026-11-16. Base `wip/integrate-w82` at 5e235a40a (origin/main and origin/wip/integrate-w82
were already merged in it). Log: `scratch/hodgetate-from-dr/log.md`.

## Verdict

The open research field `hodgeTateDecompAbVar` (`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`, TailS l. 347:
`ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`, `G_F`-equivariant, rated **consequence / GLUE** because the coordinate form needs
`dim t_A = dim t*_{A'} = g`) is **proved in Lean**, with its exact type, from

* **one new leaf**, `HodgeTateFromPairing.HodgeTateDecompExists`: the same decomposition with
  **both** exponents left unnamed (`ℂ_p(1)^a ⊕ ℂ_p^b` for some `a`, `b`). It is Fontaine's printed theorem with
  bases chosen and nothing else: no dimension of `t_A` or `t*_{A'}` is used (rating below);
* open fields already in the bundles (no new GLUE): the textbook field `mumfordTorsionAlgClosed` (T5, giving
  `T_p(A)` free of rank `2g`) and the added fields `picRepresentableAbVar`, `picZeroAbVar`,
  `mumfordKLFiniteSectionAC`, `mumfordPhiSurjectiveAC`, `weilPairingMumford` (the four Picard leaves behind T9, giving
  a polarization and the Weil pairing over any field);
* theorems: Tate's two theorems (`tateTwistInvariants_proof`, `axSenTate_proof`) and the isogeny quasi-inverse
  (`milneIsogenyQuasiInverse_proof`), all from contributions already folded.

```
theorem ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_printed (hHT : HodgeTateDecompExists)
    (hM : AvSplit.MumfordTorsionAlgClosed) (h1 : T09Pic.PicRepresentableAbVar) (h2 : T09Pic.PicZeroAbVar)
    (h3 : PicFix.MumfordKLFiniteSectionAC) (h4 : PicDict.MumfordPhiSurjectiveAC) (h5 : T09Pic.WeilPairingMumford) :
    ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
```

`ZInQKernel/Contrib/OneProof/HodgeTatePairing.lean`; axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`lake build`). The leaf is not stronger than the field: `hodgeTateDecompExists_of_field : HodgeTateDecompAbVar →
HodgeTateDecompExists` is proved (VERIFIED).

The de Rham route the task proposed is not used; §4 says why it cannot lower the GLUE count with the kernel as it is.

## 1. Consumers (VERIFIED by grep)

The field is read once: TailX l. 195, `deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar l.tateTwistInvariants
l.axSenTate r.deRhamH1AbVarT` (every other occurrence copies it from bundle to bundle). That theorem takes from the
decomposition (i) `htMultOver w = g([w = 0] + [w = −1])` and (ii) `FiniteDimensional ℚ_p V_p(A)`. So the consumer
needs both Hodge–Tate multiplicities, i.e. the whole numerical content; there is no smaller part to prove.

## 2. The proof

1. **Leaf**: `e : ℂ_p ⊗ V ≅ ℂ_p^a × ℂ_p^b`, `e(σ ⊗ ρ(σ) x) = (χ(σ)σ(e x)₁, σ(e x)₂)`.
2. **Count from `e`** (hodge-split's TailS §6 generalized from `(g, g)` to `(a, b)`): with Tate's theorems,
   `dim_{ℚ_p} Hom_{G_F}(V, ℂ_p(1)) = a·[F:ℚ_p]` (`finrank_htSpaceOver_of_decomp2`).
3. **Weil pairing** (`tateGSp_field`): T9 + isogeny quasi-inverse + T5 give a nondegenerate alternating
   `B : V × V → ℚ_p` with `B(ρσx, ρσy) = χ_{F̄}(σ)B(x, y)`, and `dim V = 2g`. These are the proofs of
   `HSyn.tatePairingZl_of_leaves4` and `G0Galois.tateGSp_of_zl`, which are stated over number fields but use
   `NumberField K` only for `(ℓ : K) ≠ 0`; here they are repeated over any field with `NeZero (ℓ : K)`
   (`HodgeTatePairingWeil.lean`).
4. **Cyclotomic characters agree** (`cyc_gfToGqp`): pkg-I4's `χ(gfToGqp σ)` on `ℚ̄_p` equals Mathlib's
   `cyclotomicCharacter (AlgebraicClosure F) p σ`, by naturality of the cyclotomic character along the embedding
   `ℚ̄_p → F̄` behind `Field.absoluteGaloisGroup.map` (`cyclotomicCharacter_eq_of_comm`, a general lemma).
5. **`a = b`** (`eq_of_pairing`): `Ψ_B : ℂ_p ⊗ V ≅ Hom_{ℚ_p}(V, ℂ_p)`, `c ⊗ x ↦ B(x, ·)c`, satisfies
   `Ψ_B(gw)(ρσv) = χ(σ)σ(Ψ_B(w)(v))`, so `Hom_{G_F}(V, ℂ_p(1)) = Ψ_B((ℂ_p ⊗ V)^{G_F})`; and `e` maps
   `(ℂ_p ⊗ V)^{G_F}` onto `(ℂ_p(1)^{G_F})^a × (ℂ_p^{G_F})^b`, of dimension `b·[F:ℚ_p]` by Tate. With step 2,
   `a = b`.
6. **`a + b = dim V = 2g`** (`add_eq_finrank`, `dim_{ℂ_p} ℂ_p ⊗ V = dim V`), so `a = b = g` and `e` is the field's
   isomorphism.

The objects are transported between pkg-I4's copy of the abelian variety (`G9.PkgI4.I3.AbVar`) and the kernel's
`PkgI3.AbVar` through `AbVarBC.toI4` / `vToI4` (definitional, as in `AbVarBC.G9Instance`).

## 3. The new leaf and its rating

```
def HodgeTateDecompExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))
```

**Rating: printed form with bases chosen; a specialization of the printed statement with no further input.**
Fontaine, Invent. Math. 65 (1982), Théorème principal (with Tate 1967 §4 for good reduction and Faltings, JAMS 1
(1988)), prints a `G_F`-equivariant isomorphism `ℂ_p ⊗ V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t*_{A'})` (locator and
exact wording UNVERIFIED: no network; the same citation as the field's docstring). Choosing `F`-bases of the two
finite-dimensional `F`-spaces gives the Lean form with `a = dim t_A`, `b = dim t*_{A'}`; the leaf asserts only that
some `a`, `b` exist. The dictionary ruling's objection to the field (the exponent `g` on the `t*_{A'}` factor needs the
dual abelian variety, Mumford §8 and §13) does not apply: neither exponent is named. The tangent space and the dual
abelian variety are not in Mathlib, so the printed objects cannot be written; this is the closest statable form.
Objects: pkg-I4's genuine abelian variety, Tate module, `ℂ_p` action and Mathlib's cyclotomic character, as in the
field. Proposed `locators.md` row (not added: other tasks' files are not mine to edit): *Fontaine 1982 Théorème
principal, both exponents unnamed (`HodgeTateFromPairing.HodgeTateDecompExists`), locator UNVERIFIED.*

**Relation to dict-galois** (`origin/wip/dict-galois`, not in this base): it proposed the leaf
`HodgeTateDict.HodgeTateDecompAbVarPrinted` = `ℂ_p(1)^g ⊕ ℂ_p^b` and got `b = g` from T26. That leaf still uses
`dim t_A = g`. `HodgeTateDecompExists` is weaker (it follows from dict-galois's leaf by `a := g`), at the cost of the
Weil pairing, whose inputs are already open fields. dict-galois's contribution file is also named
`ZInQKernel/Contrib/OneProof/HodgeTateDecompAbVar.lean`; mine are `HodgeTatePairing*.lean` so both can be merged.

## 4. Why not "de Rham implies Hodge–Tate"

The kernel has `deRhamH1AbVarT` (`dim_F D_dR(V^∨) = dim V`), `B_dR^+` a DVR with uniformizer `ξ` and
`θ⁺ : B_dR^+ → ℂ_p` with kernel `(ξ)` (KerTheta). It has no filtration on `D_dR`, no `t = log[ε]`, no
`gr^i B_dR ≅ ℂ_p(i)`, no `H¹_dR(A/F)` and no dual abelian variety (VERIFIED by grep). The standard argument gives
`dim (ℂ_p(i) ⊗ V^∨)^{G_F} = dim gr^i D_dR(V^∨)`; to get `g` and `g` one needs the Hodge numbers of
`gr D_dR(H¹_ét)`, i.e. the filtered comparison `D_dR(H¹_ét) ≅ H¹_dR(A/F)` with `h^{1,0} = h^{0,1} = g`. Over the
kernel's objects that is statable only as "the graded pieces of `D_dR(V^∨)` have dimension `g`", a composite
consequence (Faltings/Tsuji comparison + Hodge numbers of abelian varieties), so it would be rated GLUE, and the
`gr B_dR` and "de Rham ⇒ Hodge–Tate" steps (Fontaine, Astérisque 223 (1994) Exp. II–III; Brinon–Conrad §4, §6,
numbering UNVERIFIED) would be further leaves or a large formalization. That route trades one consequence-GLUE for
another; the Weil-pairing route removes it.

## 5. What compiles (all VERIFIED with `lake build`)

| file | imports | content |
| --- | --- | --- |
| `Contrib/OneProof/HodgeTatePairingDecomp.lean` | TailS, AbVarBC.G9Instance | the leaf; counts for `ℂ_p(1)^a ⊕ ℂ_p^b`; `eq_of_pairing`; `add_eq_finrank`; cyclotomic naturality |
| `Contrib/OneProof/HodgeTatePairingWeil.lean` | TailK | `tatePairingZl_field`, `tateGSp_field` |
| `Contrib/OneProof/HodgeTatePairingCore.lean` | the two above | `hodgeTateDecompAbVar_of_leaves` (hypotheses: leaf, Tate, AST, T9, quasi-inverse, T5) |
| `Contrib/OneProof/HodgeTatePairing.lean` | Core, contributions, TailZ24 | `hodgeTateDecompAbVar_of_printed` (hypotheses: leaf + open fields) |

The linear algebra is in a module importing only TailS: in later environments (TailK, TailX) the same proofs time out
in typeclass search (`Module.Free`, `IsDomain ℚ_[p]`). Core needs `maxHeartbeats 1000000` for the transport between
the two copies of the abelian variety. No `#eval`, `run_cmd`, notation, macros. `scratch/hodgetate-from-dr/Statement.lean`
copies the field verbatim and checks it `Iff.rfl` against TailS.

## 6. `#discharges` and the fold

`#discharges` output: §7 (from `scratch/hodgetate-from-dr/Discharges.lean`, full output in
`Discharges-output.txt`; built with `lake build ZInQKernel.Contrib.OneProof.HodgeTatePairing +ZInQKernel.OneProof.Main
+ZInQKernel.OneProof.Discharges`, 14105 jobs, success).

Autofold spec: `scratch/hodgetate-from-dr/autofold.json` (field `hodgeTateDecompAbVar`, research bundle; proof uses
`{t}.mumfordTorsionAlgClosed` and five `{l}` fields; new leaf `hodgeTateDecompExists`, kind published, flag empty, so
autofold flags it "unread"). `autofold.py --dry-run` (VERIFIED): `strict count: 16/21 on 37 -> 17/20 on 37; strictest
16/21 -> 17/20`, i.e. GLUE 21 → 20 and LEAF 16 → 17 in both columns. The dry-run module
(`scratch/hodgetate-from-dr/AutofoldDry.lean`, the output without its first line) compiles against TailZ45:
`sixContactMin_of_open39` depends on `[propext, Classical.choice, Quot.sound]` (VERIFIED). Nothing in the tree was
written by the dry run.

## 7. `#discharges` output

```
DISCHARGES [OpenResearchLeaves28.hodgeTateDecompAbVar] by ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_leaves
  still assumes: [ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists,
 ZInQ.Contrib.HodgeSplit.TateTwistInvariants,
 ZInQ.Contrib.HodgeSplit.AxSenTate,
 HDec.WeilPairing.T09_SymmIsogenyExists,
 HDec.WeilPairing.IsogenyQuasiInverse,
 PkgI2.TorsionStructure]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves28.hodgeTateDecompAbVar] by ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_printed
  still assumes: [ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists,
 AvSplit.MumfordTorsionAlgClosed,
 T09Pic.PicRepresentableAbVar,
 T09Pic.PicZeroAbVar,
 PicFix.MumfordKLFiniteSectionAC,
 PicDict.MumfordPhiSurjectiveAC,
 T09Pic.WeilPairingMumford]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 45 open hypotheses, 6739 theorems checked, 15 discharge one
```
