# pic-dict: the three Pic-dictionary rows

Task pic-dict. Base e22df37cd (fork main after leaf-fold30). Rows (all fields of `HDec.HSyn.OpenAddedLeaves17`,
`TailZ34.lean:111`; statements in `ZInQKernel/OneProof/H/TailZ24.lean`): `T09Pic.PicZeroAbVar` (l.302),
`T09Pic.PhiAmpleIsogeny` (l.366), `T09Pic.WeilPairingMumford` (l.708). On fork main after leaf-fold31 all
three are rated `consequence`, GLUE/GLUE.

## 1. Result

| row | result | leaves | glue | strict / strictest change on the lf31 rating |
|---|---|---|---|---|
| `weilPairingMumford` | **replaced by leaves + Lean glue** | 7 of Mumford's displays over `k = k̄`: §6 Cor. 4, §6 App. 1, §8 (iv), §8 Thm 1, §20 (definition, well defined, bilinear), §20 (nondegenerate), §23 | all proved | **−1 / −1** |
| `phiAmpleIsogeny` | **replaced by leaves + Lean glue** | 2 of them: Mumford §6 App. 1 and §8 Thm 1 over `k̄` | all proved | **−1 / −1** |
| `picZeroAbVar` | **reduced to four statements, glue proved**; one is pending reading | Kleiman 9.4.8, SGA 3 VI_A 2.4, Kleiman 9.5.4 (printed); `picZeroSmooth` (`Pic⁰_{A/K}` smooth; pending reading) | all proved | 0 / 0 now; −1 / −1 once `picZeroSmooth` is read as one print |

Folding `weilPairingMumford` and `phiAmpleIsogeny` (`scratch/pic-dict/autofold-both.json`) gives
`strict count: 37/11 on 48 -> 44/9 on 53; strictest 37/11 -> 44/9` on the lf31 rating, that is **−2 / −2**, with 7
new printed leaves shared by the two rows.

Everything below is VERIFIED: compiled, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

* `ZInQKernel/Contrib/OneProof/PicDictionary.lean`, namespace `PicDict`, about 125 KB, no build-time code, no
  `sorry`. It imports `ZInQKernel.OneProof.H.TailZ24` and vendored or Contrib modules already in the tree
  (`…/Modules/FreeGeneratorPullback`, `…/Picard/Descent`, `…/Modules/PullbackMonoidal`, `…/IdealSheaf/Image`,
  `…/Modules/StructureSheaf`, `ZInQKernel.Contrib.SmoothFibre.Basic`). `lake build
  ZInQKernel.Contrib.OneProof.PicDictionary` succeeds.
* **Main results:**

  ```lean
  theorem PicDict.weilPairingMumford_final (hsq : MumfordSquareAC) (h8iv : MumfordMulNPicZeroAC)
      (h8 : MumfordPhiSurjectiveAC) (h20a : MumfordWeilPairingAC) (h20b : MumfordWeilNondegAC)
      (h23 : MumfordWeilAltAC) (hKL : MumfordKLFiniteAC) : T09Pic.WeilPairingMumford
  theorem PicDict.phiAmpleIsogeny_final (hKL : MumfordKLFiniteAC) (h8 : MumfordPhiSurjectiveAC) :
      T09Pic.PhiAmpleIsogeny
  theorem PicDict.picZeroAbVar_of_leaves (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
      (h3a : PicZeroSmooth) (h3b : PicZeroProper) : T09Pic.PicZeroAbVar
  ```

* Intermediate forms, compiled and listed by `#discharges`:
  * `*_of_printed`: leaves stated at `X = A_K̄` in the kernel's coordinates;
  * `*_of_ac`, `*_of_leaves`, `*_of_mumford`: forms that still take statements that are now theorems.
* Statements proved on the way, which were leaves or glue before:
  * **L5** (`picPointsAlgClosed : T09Pic.PicPointsAlgClosed`, Kleiman 9.2.5 at `Spec K̄`);
  * L6 (no longer needed);
  * the **Galois clause** (Milne 1986 §16; `weilFormulaGaloisEx`);
  * the **adjoint and compatibility clauses** (Mumford §20 (5), printed for isogenies only, and §20;
    `mumfordWeilDual_of_pairing`, `mumfordWeilCompat_of_pairing`);
  * the identification of the kernel's `B(K̄)` with Mumford's `Pic⁰(A_K̄)` in both directions. This includes the
    composite "the `K̄`-points of `Pic⁰` are translation-invariant" (Kleiman 9.5.10 + Mumford §8;
    `picZeroPtsTranslInv_of_leaves`);
  * EGA II 4.6.13 at `K̄` (`ampleBaseChangeAlgClosure`);
  * `𝒪_T = f_{T*}𝒪` universally (`pushforwardUnitUniversal`, from the vendored library);
  * products of geometrically integral abelian varieties (`geomIntegralProd`);
  * `finiteOfFiniteKerPts`;
  * smooth ⇒ geometrically reduced (`geometricallyReduced_of_smooth`).
* The consumer `T09Pic.t09SymmIsogenyExists_of_four` and its users are unchanged.

`#discharges` (`scratch/pic-dict/Discharges.lean`; full output in `scratch/pic-dict/discharges.txt`, 17 matching
lines including the intermediate forms). The three final lines:

```
DISCHARGES [OpenAddedLeaves17.phiAmpleIsogeny] by PicDict.phiAmpleIsogeny_final
  still assumes: [PicDict.MumfordKLFiniteAC, PicDict.MumfordPhiSurjectiveAC]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.picZeroAbVar] by PicDict.picZeroAbVar_of_leaves
  still assumes: [PicDict.PicLocFinType, PicDict.IdentityComponentLFT, PicDict.PicZeroSmooth, PicDict.PicZeroProper]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_final
  still assumes: [PicDict.MumfordSquareAC,
 PicDict.MumfordMulNPicZeroAC,
 PicDict.MumfordPhiSurjectiveAC,
 PicDict.MumfordWeilPairingAC,
 PicDict.MumfordWeilNondegAC,
 PicDict.MumfordWeilAltAC,
 PicDict.MumfordKLFiniteAC]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 59 open hypotheses, 3063 theorems checked, 17 discharge one
```

### Autofold

Each spec was dry-run twice: on this base, and on the lf31 rating (the three rows set to consequence GLUE/GLUE in a
temporary copy of `kinds.tsv`, then restored). Every printed module (`FoldDryRun*.lean`, line 1 stripped) compiles
to `sixContactMin_of_open35` with the standard axioms.

| spec | discharges | new leaves | this base | lf31 rating |
|---|---|---|---|---|
| `autofold-both.json` (**recommended**) | `weilPairingMumford` by `weilPairingMumford_final`; `phiAmpleIsogeny` by `phiAmpleIsogeny_final` | 7 published | `40/8 on 48 -> 45/8 on 53; strictest 39/9 -> 45/8` | `37/11 -> 44/9; strictest 37/11 -> 44/9` |
| `autofold.json` | `weilPairingMumford` only | 7 published | `40/8 -> 46/8 on 54; strictest 39/9 -> 46/8` | `37/11 -> 44/10; strictest 37/11 -> 44/10` |
| `autofold-all.json` | the three rows | 7 + 4 (`picZeroSmooth` flagged pending reading, counted GLUE) | `40/8 -> 47/9 on 56; strictest 39/9 -> 47/9` (`--allow-rise`) | `37/11 -> 47/9; strictest 37/11 -> 47/9` |

None of the first two needs `--allow-rise`. `autofold-all.json` has the same count as the recommended spec on the
lf31 rating; it would be −3 once `picZeroSmooth` is cleared by a reading.

## 2. Glue

The kernel's side:

* the fppf sheaf `picardFunctor A.X.hom`, the sheafification of `T ↦ Pic(A ×_K T)`;
* a representing `P`;
* `B` with `IsPicZero rep B j`;
* the classes `picClass rep j y ∈ Pic(A_K̄)` and `weilScalar`.

Mumford's side is an abelian variety `X` over an algebraically closed field `k`:

* `X(k) = (𝟙_ ⟶ X.X)` and `t_x = lift (𝟙, toUnit ≫ x) ≫ μ` (`AC.tr`), `n_X = 𝟙^n` (`AC.mul`);
* `Pic⁰(X)`: the classes invariant under every `t_x` (`AC.IsTI`), and `X̂_n` (`AC.IsDT`);
* `φ_L(x) = t_x^*L ⊗ L⁻¹` (`AC.phi`);
* `ē_n(x, M) = t_x^*ψ ∘ ψ⁻¹` (`AC.formula`), which is the right side of `T09Pic.weilScalar_spec`.

1. **L5.** Every fppf covering sieve of a scheme contains every point with values in an algebraically closed field
   (induction on `Precoverage.Saturate`; Mathlib's `pointOfClosedPoint`, Nullstellensatz). So at `T = Spec K̄` every
   covering sieve is maximal, and Mathlib's `isLocallyInjective_toSheafify'` and `isLocallySurjective_toSheafify'`
   give bijectivity.
2. **Base change.** `A_K̄ := Over.pullback (Spec K̄ → Spec K)` of `A`, as an `AbVar K̄` (`AKbar`).
   * `pts : A(K̄) ≃* A_K̄(K̄)`.
   * `(t_{pts x}).left = (transl x).left` (`tr_pts`, via Mathlib's `μ_pullback_left_*`).
   * `n_{A_K̄} = n_A` (`mul_AKbar`).
   * Mumford's formula on `A_K̄` is the kernel's `weilFormula` (`formula_bridge`).
   * Each `*AC` leaf gives its instance at `A_K̄` (`*_of_ac`).
3. **Dictionary.**
   * `y ↦ M_y` is an injective homomorphism `B(K̄) → Pic(A_K̄)`.
   * `M_{λ_L x} = φ_{L_K̄}(x)` (`picClass_phiL`).
   * `M_{f^∨ y} = (f × 1)^* M_y` and `M_{σy} = (1 × Spec σ)^* M_y`.
   * `Pic⁰ ⊆ B(K̄)` by Mumford §8 Thm 1, with ampleness of `L_K̄` (`isAmple_pullback`).
   * `B(K̄) ⊆ Pic⁰` by item 6.
   * For `y ∈ B[n]` a trivialization exists, so `weilScalar = weilFormula`.
4. **Transport of Mumford's formula** (`Transport.wf_transport`, `wf_transport₂`). The proof uses
   `pullbackObjUnitIso_comp` (`𝒪`-pull-back versus `pullbackComp`, via the adjunction mate) and the pseudofunctor
   coherences `coherence_I`–`coherence_III` (from Mathlib's `pseudofunctor_associativity`). It has three instances:
   Galois with `g = 1 × Spec σ`, adjoint with `g = f × 1`, and compatibility with `g = m_A`.
5. **`λ_L` finite and surjective.**
   * `surjective_of_forall_pt`: the image of the proper `λ_L` is closed and contains every closed point.
   * `finiteOfFiniteKerPts`: finitely many `K̄`-points over each closed point give quasi-finiteness at closed points.
     Mathlib's `isOpen_quasiFiniteAt` (ZMT) and Jacobson give quasi-finite everywhere, and proper plus quasi-finite
     is finite.
6. **`K̄`-points of `Pic⁰` are translation-invariant.**
   * The vendored Kleiman 9.2.5 (`picardFunctorNormalizedIso`, with `𝒪 = f_*𝒪` universally, also vendored)
     identifies the Picard sheaf with honest classes on `A ×_K T`, normalized along `0`.
   * The renormalized `t_a^*c ⊗ c⁻¹` is natural in `T`. Classifying it at `T = A ⊗ B` gives `Ψ : A ⊗ B → P`, trivial
     on both axes.
   * `A ⊗ B` is geometrically integral (`geomIntegralProd`), so `Ψ` lands in `B`. It is a homomorphism by the
     project's rigidity theorem, hence trivial; at `K̄`-points this says `t_x^*M_y = M_y`.
7. **`picZeroAbVar`.**
   * The open subscheme on the identity component, with multiplication, unit and inverse lifted through the open
     immersion, is a group object (`AVGlue.grpObjOfMono`).
   * It is proper by (Z3b) and smooth by (Z3a). Smooth gives geometrically reduced (`isReduced_of_smooth_field`, via
     `ZInQ.SmoothFibre.isReduced_of_smooth_of_field`); with (Z2) it is geometrically integral.

## 3. Leaves and their rating

The `*AC` leaves quantify over every algebraically closed field `k` and every `X : AbVar k`. Each states one of
Mumford's displays in the definitions of §2, and none mentions the kernel's `P`, `rep`, `B`, `j` or `K`. All
locators are UNVERIFIED: there is no copy of Mumford, Kleiman, EGA, SGA or Milne on the host. For
`docs/research/locators.md`, each new leaf is a row with the locator below, verdict UNVERIFIED.

| leaf (field) | display | printed form? | reason |
|---|---|---|---|
| `mumfordSquareAC` | Mumford §6 Cor. 4 (theorem of the square) | yes | for every `L` and `x, y ∈ X(k)` |
| `mumfordKLFiniteAC` | Mumford §6 App. 1: `K(L)` finite for ample `L` | yes, with a note | printed for `L = 𝒪(D)`, `D` effective; general ample `L` via `L^m` effective and `K(L) ⊆ K(L^m)` |
| `mumfordMulNPicZeroAC` | Mumford §8 (iv): `n^*L ≅ Lⁿ` for `L ∈ Pic⁰` | yes | stated for `n ∈ ℕ`; Mumford states it for `n ∈ ℤ` |
| `mumfordPhiSurjectiveAC` | Mumford §8 Thm 1: `L` ample, `M ∈ Pic⁰` ⇒ `M ≅ t_x^*L ⊗ L⁻¹` | yes | `IsAmple` is the EGA/Stacks notion, Mumford's on a complete variety |
| `mumfordWeilPairingAC` | Mumford §20: `ē_n` by `t_x^*ψ ∘ ψ⁻¹` is well defined, `μ_n`-valued and bilinear | yes, with a note | well-definedness (independence of `ψ`) belongs to the definition; stated for `p ∤ n` |
| `mumfordWeilNondegAC` | Mumford §20: `ē_n` nondegenerate, `p ∤ n` | yes | "both kernels trivial" is a consequence of "perfect" |
| `mumfordWeilAltAC` | Mumford §23: `e^L_n(x, x) = 1`, `e^L_n(x, y) = ē_n(x, φ_L(y))` | yes | for every `L` |
| `picLocFinType` | Kleiman 9.4.8: `Pic_{X/S}` exists, separated, locally of finite presentation | yes, with a note | stated for every representing object, isomorphic to Kleiman's by Yoneda |
| `identityComponentLFT` | SGA 3 VI_A 2.4 (Stacks 0B7R; Kleiman 9.5.1): `G⁰` open, a subgroup, geometrically irreducible | yes | for group schemes locally of finite type over a field |
| `picZeroProper` | Kleiman 9.5.4: `Pic⁰_{X/K}` proper for `X` proper and geometrically normal | yes (instance) | an abelian variety is geometrically normal |
| `picZeroSmooth` | `Pic⁰_{A/K}` smooth | **pending reading** | see §4 |

Notes:

* Each formula-based leaf quantifies over trivializations `ψ : 𝒪 ≅ n^*M`. Such a `ψ` exists for every `M ∈ X̂_n`
  by `mumfordMulNPicZeroAC`. Given that, "for every `ψ`" agrees with Mumford's `ē_n(x, M)`, so no leaf is
  stronger than the print.
* `mumfordMulNPicZeroAC` at `n = 0` is true: `0_X` factors through `Spec k`, and `Pic(Spec k) = 1`.

**Smoothness of `B`** (question in the brief). `B : AbVar K` carries Mathlib's `Smooth`. Mumford §13 gives `Â` as an
abelian variety, a complete group variety over `k = k̄`. Nonsingular implies smooth over an algebraically closed
field, and a reduced group scheme of finite type over `k̄` is smooth (Mumford §4; UNVERIFIED). Over `K`, smoothness
of `Pic⁰_{A/K}` descends from `K̄`: it is fpqc local on the base (EGA IV 17.7.1(ii); Mathlib has the descent,
`DescendsAlong @Smooth`), and `Pic⁰_{A/K} ×_K K̄ = Pic⁰_{A_K̄/K̄}` (Kleiman 9.5.1). So smooth versus nonsingular is
two theorem steps, nonsingular to smooth and descent, as the unif-printed review counted. In the decomposition here
they are the one pending leaf, `picZeroSmooth`.

## 4. The one statement still combined: `picZeroSmooth`

`picZeroAbVar_of_leaves` needs (Z3a), smoothness of the identity component of `Pic_{A/K}` over `K`. Mumford §13
gives it over `k̄`: `Â = Pic⁰` is reduced, since `dim T₀ = h¹(𝒪_A) = g = dim Â`. Over `K` this is combined with:

* the identification of Mumford's `Â` with the identity component of the fppf Picard scheme, as schemes;
* descent along `K̄/K`.

A single print over an arbitrary field ("`Pic⁰_{A/K}` is an abelian variety": BLR 8.4, FGA Explained 9.5, Milne
1986 §10; pending reading) would clear it, and then all three rows are −1. Properness is not derived from `λ_L`:
every surjectivity argument of §2 presupposes that `B` is an abelian variety, so that would be circular. Kleiman
9.5.4 supplies it directly.

## 5. What remains

* Reading:
  * a one-statement source for `picZeroSmooth`;
  * the locators of §3, in particular that §23 states `e^L_n(x, x) = 1` (not only skew-symmetry), that §20 includes
    well-definedness, and Kleiman 9.4.8 and 9.5.4.
* Optional Lean: parts of `MumfordWeilPairingAC` (independence of `ψ`, constancy and additivity in `x` are formal;
  bilinearity in `M` needs pull-back of tensor products).

Files: `scratch/pic-dict/README.md` lists them. The deliverable is `ZInQKernel/Contrib/OneProof/PicDictionary.lean`;
the specs are `autofold-both.json` (recommended), `autofold.json` and `autofold-all.json`.
