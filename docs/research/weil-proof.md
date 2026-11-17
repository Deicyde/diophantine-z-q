# weil-proof: the field `weilPairingMumford`

Task weil-proof. Base `0caafe66` (fork main 2880fef1 + STATUS w80), with `origin/wip/pic-dict` (4e95795b) and
`origin/wip/pic-fix` (be79cb5b) merged (both clean; their `PicDictionary.lean` and `PhiAmpleIsogeny.lean` are the
same blobs as in `origin/wip/leaf-fold32b`). Field `HDec.HSyn.OpenAddedLeaves17.weilPairingMumford :
T09Pic.WeilPairingMumford` (`ZInQKernel/OneProof/H/TailZ24.lean:708`). pic-dict had reduced it to seven of
Mumford's displays over an algebraically closed field (`PicDict.weilPairingMumford_final`).

## 1. Result

**The field is not removed outright.** It now rests on **four** Mumford displays and one open field, against
pic-dict's seven; **three of pic-dict's seven displays are Lean theorems with no hypotheses**:

| pic-dict leaf | Mumford | status here |
|---|---|---|
| `MumfordWeilPairingAC` | §20: `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` well defined, `μ_n`-valued, bilinear | **proved** (`WeilProof.mumfordWeilPairingAC_proof`) |
| `MumfordWeilAltAC` | §23: `e^L_n(x, x) = 1` | **proved** (`WeilProof.Theta.mumfordWeilAltAC_proof`) |
| `MumfordKLFiniteAC` | §6 App. 1 | no longer used: replaced by the open field `phiAmpleIsogeny` (its only use) |
| `MumfordSquareAC`, `MumfordMulNPicZeroAC`, `MumfordPhiSurjectiveAC` | §6 Cor. 4, §8 (iv), §8 Thm 1 | still leaves (line-bundle statements, no `ē_n`) |
| `MumfordWeilNondegAC` | §20 nondegeneracy | still a leaf |

All VERIFIED: compiled, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (`scratch/weil-proof/Axioms.lean`).

```lean
theorem WeilProof.Theta.weilPairingMumford_final (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
    (h8 : MumfordPhiSurjectiveAC) (h20b : MumfordWeilNondegAC) (h3 : T09Pic.PhiAmpleIsogeny) :
    T09Pic.WeilPairingMumford
```

`h3` is the open field `phiAmpleIsogeny` of the same bundle; in leaf-fold32 it is
`PicFix.phiAmpleIsogeny_of_printed` of the two leaves `mumfordKLFiniteSectionAC`, `mumfordPhiSurjectiveAC`
(spec `scratch/weil-proof/autofold-lf32.json`, dry-run on a temporary worktree of `origin/wip/leaf-fold32b` at
6b7a45445 with the two files added: `strict count: 16/21 on 37 -> 18/21 on 39; strictest 16/21 -> 18/21` — that
base rates many rows GLUE, and this fold leaves its GLUE count unchanged; the printed module
`scratch/weil-proof/FoldDryRunLF32.lean` compiled there to `sixContactMin_of_open39`, standard axioms).

**Count** (autofold dry runs on this base; each printed module compiles to `sixContactMin_of_open36` with the
standard axioms):

| spec | flag of `mumfordWeilNondegAC` | dry run |
|---|---|---|
| `scratch/weil-proof/autofold.json` (**recommended, honest**) | pending reading (stated for the formula; §5) | `34/11 on 45 -> 37/11 on 48; strictest 34/11 -> 37/11` (no rise) |
| `scratch/weil-proof/autofold-unread.json` | unread (pic-dict's rating) | `34/11 on 45 -> 38/10 on 48; strictest 34/11 -> 38/10` |

So the fold is GLUE-neutral now and −1 once a reading confirms that Mumford §20 states `ē_n` by the formula.

**Why the rest is out of reach.** §20 nondegeneracy needs descent along `n_X` (right kernel) and
`#X̂[n] = #X[n]` (left kernel; dimension of `Pic⁰` and degree of `n`); §6 Cor. 4 and §8 (iv) need the seesaw /
theorem of the cube (cohomology and base change); §8 Thm 1 needs cohomology of nontrivial `Pic⁰` bundles. None of
these is in the tree.

## 2. Files

* `ZInQKernel/Contrib/OneProof/WeilFormula.lean` (namespace `WeilProof`; imports
  `ZInQKernel.OneProof.H.TailZ24`, the module that defines the statement, and
  `ZInQKernel.Contrib.OneProof.PicDictionary`): the formula calculus, §20 (`mumfordWeilPairingAC_proof`),
  `pullbackCompMonoidal_proof`.
* `ZInQKernel/Contrib/OneProof/WeilFormulaTheta.lean` (imports `WeilFormula` and the tree's
  `Contrib.OneProof.MulEtale`): the theta-group calculus, §23 (`mumfordWeilAltAC_proof`), divisibility
  (`divisibleAC`), and the final theorem `weilPairingMumford_final` (**the theorem for the fold**).
* Both build with `lake build`; no build-time code. They need pic-dict's `PicDictionary.lean` (merged here,
  identical to leaf-fold32b's).
* `scratch/weil-proof/`: `Discharges.lean` + `discharges.txt`, `Axioms.lean`, the specs, `FoldDryRun*.lean`,
  development copies (`Generic.lean`, `PBM.lean`, `Mates.lean`, `Theta.lean`, `Alt.lean`, `Div.lean`), `log.md`.

`#discharges` (excerpt of `scratch/weil-proof/discharges.txt`):

```
DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by WeilProof.Theta.weilPairingMumford_final
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.MumfordWeilNondegAC,
 T09Pic.PhiAmpleIsogeny]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 56 open hypotheses, 3185 theorems checked, 23 discharge one
```

(The other `WeilProof.*` lines are intermediate forms: `weilPairingMumford_proof`, `_of_div`, `_of_six`,
`_of_bilinRight`, `_of_pullbackCompMonoidal`.)

## 3. The proofs

Notation: `X` a scheme, `m, t : X ⟶ X`, `t ≫ m = m`, `ψ : 𝒪 ≅ m^*M`; pic-dict's
`wf t m h M ψ = (pOU t)⁻¹ ≫ t^*ψ ≫ θ_t ≫ ψ⁻¹ ∈ End(𝒪) = Γ(X, 𝒪)`, `θ_t = pullbackComp ≫ pullbackCongr`.

### 3.1 §20, the formula (`WeilFormula.lean`)

* `wf_comp` (cocycle `wf(t₁ ≫ t₂) = t₁^*(wf t₂) · wf t₁`), `wf_id`, `wf_change` (another `ψ'` changes the
  value by `t^*(a)/a`, `a = ψ'ψ⁻¹`), `tr_appTop` (translations fix `Γ(X, 𝒪)`: every global function is
  constant, vendored `bijective_appTop_of_isProper_of_geometricallyIntegral`).
* (i) `formula_indep`, (ii) `formula_root`, (iii) `formula_mul` follow.
* (iv) multiplicativity in `M`: `alpha_tensor`/`wf_tensor_ratio` compute the formula of `λ⁻¹(ψ ⊗ ψ')μ` from
  `PullbackCompMonoidal`, Eckmann–Hilton and the left unitality of `t^*`; the ratio of `pOU⁻¹` and `ε` is shown to
  be `1` for translations (`unitRatio_tr`), so no unit coherence is assumed.
* `pullbackCompMonoidal_proof` (section `PullbackCompMonoidalSec`): the vendored monoidal structure of
  `pullback` comes from `Localization.Monoidal.functorMonoidalOfComp` (`mu_sheafified`). On sheafified objects
  the identity reduces (`main_sheafified`) to (E) `ee_comp` — Mathlib's `pullbackComp` versus
  `sheafificationCompPullback` and the presheaf `pullbackComp` (a unit chase: `unit_leftAdjointUniq_hom_app`,
  `unit_conjugateEquiv_symm`) — and (P) `pcP_monoidal` — the presheaf `pullbackComp` is monoidal, from the new
  general lemma `Mates.leftAdjointCompIso_δ` (via `Adjunction.isMonoidal_comp`) and `eF_monoidal` (presheaf
  `pushforwardComp`, a `tmul` computation). All modules follow by the counit `L(M.val) ≅ M` and naturality.

### 3.2 §23 (`WeilFormulaTheta.lean`)

The theta-group argument: `e_n(x, φ_L(x))` is the commutator of two lifts to `N = n^*L`, and the second lift's
`n`-th power lies over `x`.

* Lifts `α : t^*N → N` over endomorphisms, products `prod` (associative, `prod_assoc`), the commutator relation
  `Comm` (multiplicative in the first variable, `comm_prod_left`), `comm_pw` (a lift commutes with its powers).
* `theta_rho`: pseudofunctor coherence transporting `θ_t` along `m^*t^*L ≅ s^*m^*L` (`m ≫ t = s ≫ m`).
* `tensor_relation`: tensoring `ψ` with `N` conjugates `θ_t(Φ ⊗ L)` into `θ_t(L)` times `λ⁻¹(α ▷ N)λ`.
* `alt_core` (any scheme): from `y` with `t = s^n` (`s = t_y`), `Φ ⊗ L ≅ t^*L`, `N` invertible with a tensor
  inverse: the formula is `1`. The commutator scalar is `λ⁻¹(α ▷ N)λ`; the theta argument and the vendored
  `exists_eq_smulHom` make it `1`; monoidal faithfulness (`unit_endo_eq_id_of_whisker`) gives `α = 1`.
* `divisibleAC`: `[n]` is étale (the tree's `mulEtaleAbelianScheme_proof`), so open
  (`isOpenMap_of_generalizingMap`, `Flat.generalizingMap`); proper, so closed; `X` connected, so `[n]` is surjective;
  the fibre over a `k`-point is a nonempty proper `k`-scheme, with a `k`-point (`pointOfClosedPoint`).
* `mumfordWeilAltAC_proof := mumfordWeilAltAC_of_div divisibleAC`.

## 4. Consumers and narrowing

* The field is read once on the route, at `TailZ24.lean:808` (`t09SymmIsogenyExists_of_four`), VERIFIED by grep.
  weil-used (origin/wip/weil-used, probe over the closure of `frozenTarget`): below `T09_SymmIsogenyExists` only
  the left half of perfectness, Galois, compatibility and `e_n(x, λ_L x) = 0` (very ample `L`) are read; the
  `weilScalar` pin, the adjoint clause and the right half of perfectness are inert.
* No narrowing (characteristic 0, number fields, the abelian varieties used) makes the remaining leaves provable:
  the four displays are as deep in characteristic 0. A narrower field (weil-used's `WeilPairingRead`) would drop
  only the inert clauses and needs a reroute through older bundles; not done.

## 5. Leaves of the fold and their rating

| leaf | kind | printed form? | reason |
|---|---|---|---|
| `mumfordSquareAC` (pic-dict) | published | yes (unread) | Mumford §6 Cor. 4 over `k = k̄`; line bundles only |
| `mumfordMulNPicZeroAC` (pic-dict) | published | yes (unread) | Mumford §8 (iv); line bundles only |
| `mumfordPhiSurjectiveAC` (pic-dict) | published | yes (unread; already a field in leaf-fold32) | Mumford §8 Thm 1 |
| `mumfordWeilNondegAC` (pic-dict) | published | **pending reading** | stated for the formula `t_x^*ψ ∘ ψ⁻¹`; it is the print only if §20 states `ē_n` by this formula and not only through the duality of §15 (pic-fix's note) |

No new leaf. Locators UNVERIFIED (no copy of Mumford on the host).

## 6. What remains

* `mumfordWeilNondegAC`: right kernel by descent of the `X[n]`-invariant trivialization along the finite étale
  `n_X` (the vendored fpqc section descent may suffice); left kernel needs `#X̂[n] = #X[n]`.
* A reading of Mumford §20 for the formula (clears the flag; the fold is then −1).
* The other three displays need the seesaw / theorem of the cube.
