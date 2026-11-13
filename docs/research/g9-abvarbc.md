# g9-abvarbc: `G9Bridge.AbVarBaseChange` proved; `KerUnitOpen` and `MulIsogeny` proved

Status: research note, task g9-abvarbc, 2026-11-13. Branch `wip/g9-abvarbc`. All Lean files are
new, under `ZInQKernel/Contrib/AbVarBC/`. No existing project file was edited.
Log: `scratch/g9-abvarbc/log.md`.

Marks: **VERIFIED** = compiled in Lean, or read in a source; **STANDARD** = published, with a
reference; **SPECULATIVE** = an assessment. Locators recalled from memory are marked UNVERIFIED.

## 1. Main result

**`G9Bridge.AbVarBaseChange` is a theorem, proved from Mathlib alone** (no leaf, no hypothesis).
VERIFIED: compiled, `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

```lean
-- ZInQKernel/Contrib/AbVarBC/Main.lean
theorem ZInQ.Contrib.AbVarBC.abVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange

-- the statement, unchanged (ZInQKernel/Contrib/G9/LocalModel.lean, task g9-derham)
def G9Bridge.AbVarBaseChange : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (L : Type) [Field L] (i : K →+* L)
    (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ (A' : PkgI4.I3.AbVar L) (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ), A'.dim = A.dim ∧
      ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)
```

The witness is the base change `A' = A ×_K L` (`PkgI3.AbVar.baseChange`), transported to G9's
copies of the objects by `rfl`. Consequences:

```lean
theorem ZInQ.Contrib.AbVarBC.g9Glue_of_r10Weights
    (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) : ZInQ.Contrib.G9.G0Galois.G9Glue
theorem ZInQ.Contrib.AbVarBC.kerUnitOpen : MulRigidity.KerUnitOpen      -- mul-rigidity's leaf
theorem ZInQ.Contrib.AbVarBC.mulIsogeny : G0FibreSimple.MulIsogeny      -- g0-fibresimple's leaf
theorem ZInQ.Contrib.AbVarBC.abVarBaseChangeK : ZInQ.Contrib.AbVarBC.AbVarBaseChangeK
```

(`MulRigidity` and `G0FibreSimple` here are `ZInQ.Contrib.AbVarBC.MulRigidity`,
`ZInQ.Contrib.AbVarBC.G0FibreSimple`: mul-rigidity's `scratch/mul-rigidity/Mul.lean`, copied into
`Contrib/AbVarBC/Mul.lean` with only the namespaces moved; the statements are its text verbatim.)

So **glue step G9 now rests on `R10Weights` alone** (with task g9-derham's
`g9Glue_of_abVarBaseChange`); g9-derham recommends adding `R10Weights` to leaf R10 as part of
the same published Hodge–Tate statement.

`#print axioms` (file `scratch/g9-abvarbc/Axioms.lean`, output
`scratch/g9-abvarbc/axioms-output.txt`; all 41 lines read `[propext, Classical.choice, Quot.sound]`):

```
'ZInQ.Contrib.AbVarBC.abVarBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.g9Glue_of_r10Weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.kerUnitOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.mulIsogeny' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.abVarBaseChangeK' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.tateBC_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PkgI3.AbVar.dim_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.dimBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.AbVarBC.bcT_bijective_charZero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build: `lake build ZInQKernel.Contrib.AbVarBC.Main ZInQKernel.Contrib.AbVarBC.Consumers
ZInQKernel.Contrib.AbVarBC.E1SubBC` succeeds (VERIFIED); these three import all 12 files. No
`sorry`, no `axiom`, no raised heartbeat limit.

## 2. The reusable API (over the kernel's `PkgI3.AbVar`, `ZInQKernel/HDecomp/Objects.lean`)

General lemmas, separate from the instance:

| declaration | statement | file |
|---|---|---|
| `dim_baseChange_scheme` | `X` loc. of finite type over a field `K`, `L/K` ⇒ `dim (X ×_K L) = dim X` (Stacks 00P4) | Dim.lean (g0-dim's proof) |
| `PkgI3.AbVar.dim_baseChange` | `(A.baseChange L).dim = A.dim` | Dim.lean |
| `PkgI3.AbVar.dim_finite` | `∃ n : ℕ, A.dim = n` | Dim.lean |
| `bcPt` | `(A.baseChange L).Pt Ω ≃* A.Pt Ω`, natural for `Aut_L(Ω)` (`bcPt_galAct`) | Points.lean (unram-tate's) |
| `epi_spec_map_field` | `Spec` of a map of fields is an epimorphism (flat + surjective + qc ⇒ effective epi, Mathlib Stacks 023Q) | Points.lean |
| `extPt`, `extPt_injective`, `extPt_galAct` | `A(Ω) ↪ A(Ω₂)` along a `K`-embedding, Galois-natural | Points.lean |
| `ptBC`, `ptBC_injective`, `ptBC_galAct` | `A(K̄) ↪ A_L(L̄)` along `κ : K̄ →ₐ[K] L̄` | Tate.lean |
| `tateBC`, `tateBC_galT` | `T_ℓ(A) →ₗ[ℤ_ℓ] T_ℓ(A_L)`, injective, `κ ∘ τ = σ ∘ κ ⇒` intertwines `galT τ`, `galT σ` | Tate.lean |
| `TorsionDescends`, `tateBC_bijective_of_torsionDescends` | if the `ℓ`-power torsion of `A_L(L̄)` comes from `A(K̄)`, `tateBC` is bijective | Tate.lean |
| `tateBC_bijective_of_tateModuleFree` | the same from leaf T26 | Tate.lean |
| `vBC`, `vBC_galRep` | `V_ℓ(A_L) ≃ₗ[ℚ_ℓ] V_ℓ(A)` intertwining `ρ_{A_L}(σ)` and `ρ_A(τ)` | Tate.lean |
| `exists_lift_of_isFinite` | `Z` finite over `K`, `Ω` alg. closed: every `Ω₂`-point over `K` comes from an `Ω`-point | Torsion.lean |
| `torsionDescends_of_isFinite` | `[ℓⁿ]` finite for all `n` ⇒ `TorsionDescends` | Torsion.lean |
| `Tangent.ptRing`, `ptRing_ext`, `ptRing_ofRing`, `ptRing_specMap_comp`, `ptRing_comp` | `Spec Λ → X` landing in an affine open `U` ↔ ring maps `Γ(X,U) → Λ` (`Λ` local) | Tangent.lean |
| `Tangent.D`, `D_mul`, `D_zpow`, `eq_of_D_eq` | tangent vectors at the origin (`K[ε]`-points); their derivation is additive under the group law (via `K ⊕ K²`-points) | Tangent.lean |
| `Tangent.eq_one_of_comp_intCast` | char 0, `n ≠ 0`: a tangent vector killed by `[n]` is trivial | Tangent.lean |
| `Tangent.derivation_eq_zero` | every `K`-derivation at the origin of `A[n]` vanishes | KerUnit.lean |
| `Tangent.ker_le_sq_of_derivations` | no derivations ⇒ `P ≤ P²` (commutative algebra) | KerUnit.lean |
| `Tangent.ks_isOpenImmersion` | char 0, `n ≠ 0`: the unit section of `A[n]` is an open immersion | KerUnit.lean |
| `torsionDescends`, `tateBC_bijective` | the two above, unconditional in characteristic 0 | Main.lean |
| `AbVarBaseChangeK` / `abVarBaseChangeK` | `AbVarBaseChange` over the kernel's `PkgI3.AbVar`, witness pinned to `A.baseChange L` | G9Mul.lean / Main.lean |

Derivations of the instance (all VERIFIED): `abVarBaseChange_of_torsionDescends`,
`abVarBaseChange_of_tateModuleFree` (T26), `abVarBaseChange_of_mulIsogeny`,
`…_of_kerUnitOpen`, `…_of_mulEtale`, `…_of_cotangent` (G9Instance.lean, G9Mul.lean); and
`g9Glue_of_tateModuleFree`, `g9Glue_of_kerUnitOpen`, `g9Glue_of_cotangent`.

## 3. Consumers discharged

| consumer | hypothesis removed | new theorem |
|---|---|---|
| g9-derham `g9Glue_of_abVarBaseChange` | `AbVarBaseChange` | `g9Glue_of_r10Weights : R10Weights → G9Glue` |
| g9-derham `localModel_of_abVarBaseChange`, `g9_partial` | `AbVarBaseChange` | apply to `abVarBaseChange` |
| hodge-lattice `ZInQ.DefFaltings.HodgeLattice.DimBaseChange` | — | `dimBaseChange : DimBaseChange` |
| hodge-lattice `hodgeLatticeTheorem_of_tangent` | `DimBaseChange` | `hodgeLatticeTheorem_of_tangent' : TangentDimAtOrigin → HodgeLatticeTheorem` |
| `hodgeLatticeTheorem_of_abVarFacts`, `…_of_varieties`, `…_of_abVar`, `tangentDim_of_abVar`, `dimOrigin_of` | `DimBaseChange` | the same names with `'` (Consumers.lean) |
| e1-sub `E1Sub.bcT_bijective` | `hdim` | `bcT_bijective'` (still with T26) |
| e1-sub `E1Sub.bcT_bijective` | `TateModuleFree` **and** `hdim` (char 0) | `bcT_bijective_charZero` (E1SubBC.lean) |
| g4-weilres `hdim : ∀ e, ((conjData K A).A e).dim = 2` (scratch, branch `wip/g4-weilres`) | `hdim` from `A.dim = 2` | `fun e => (dim_overPullback A (e : K →+* Qbar)).trans hA`; checked against a verbatim copy of `bcAlong` in `scratch/g9-abvarbc/G4Check.lean` |
| g0-split `HSyn.G0Split.DimBaseChange` (scratch) | — | already proved by g0-dim; same proof here over the kernel object |
| g0-fibresimple FS3 and `fibreSimple_of_leaves` (scratch, via mul-rigidity) | `MulIsogeny` / `KerUnitOpen` | `mulIsogeny`, `kerUnitOpen` (statements verbatim from mul-rigidity) |

## 4. Findings

**F1 (statement check). `AbVarBaseChange` is correctly stated and needed no change** (VERIFIED by
proof). Its object `A'` is existential, but the `V_ℓ` clause pins it enough to be true and useful.

**F2. What the `V_ℓ` clause really needs.** `T_ℓ(A) → T_ℓ(A_L)` is always injective
(`tateBC_injective`), since `Spec L̄ → Spec K̄` is an epimorphism. Surjectivity is exactly
`TorsionDescends`: every `ℓ`-power torsion point over `L̄` is defined over `K̄`. This is the
finiteness of `A[ℓⁿ]` (Mumford §4, UNVERIFIED locator). Two routes were formalized:
- from leaf T26 `TateModuleFree` plus `dim A_L = dim A` (`abVarBaseChange_of_tateModuleFree`, via
  the kernel's `PkgI3.Tate.map_bijective`);
- from finiteness of `[ℓⁿ]` (`torsionDescends_of_isFinite`): `A[ℓⁿ]` is finite over `K`, so it is
  `Spec R` with `R` finite over `K`, and the image of `R → L̄` is algebraic over `K`, hence inside
  `κ(K̄)` (`mem_range_of_isIntegral`, from `Polynomial.Splits.mem_range_of_isRoot`).
The second route is the one that became unconditional.

**F3. `KerUnitOpen` (hence `MulIsogeny`) is provable from Mathlib by tangent vectors**, without
stalks of fibre products (the gap mul-rigidity reported). Proof (STANDARD content: `d[n] = n` on
the tangent space, Mumford §4, UNVERIFIED locator):
1. Points `Spec Λ → X` with `Λ` local landing in an affine open `U` are ring maps `Γ(X, U) → Λ`
   (`Tangent.ptRing`), natural in `Λ` and in `X`.
2. A tangent vector at the origin of `A` is an `Over`-morphism `Spec K[ε] → A` reducing to the
   origin; its derivation `D` is the `ε`-part of `Γ(A, U) → K[ε]`. Using `K ⊕ K²`-points and only
   the facts that precomposition is a monoid map and that `v · 1 = v`, `D(v·w) = D v + D w`
   (`D_mul`), so `D(vⁿ) = n D v` (`D_zpow`).
3. `v ≫ [n] = vⁿ` (`comp_intCast_hom`). In characteristic 0 a tangent vector with `v ≫ [n] = 1`
   has `D v = 0`, so `v = 1` (`eq_one_of_comp_intCast`).
4. A `K`-derivation `D` of `T = Γ(A[n], W)` at the origin gives a tangent vector of `A[n]`
   (`ev + ε D`, via `IsAffineOpen.fromSpec`); its image in `A` is killed by `[n]` (pullback
   square), hence trivial, hence the vector is the constant one and `D = 0`
   (`derivation_eq_zero`).
5. With no derivations, the maximal ideal `P` of the origin satisfies `P = P²`
   (`ker_le_sq_of_derivations`: a functional on `P/P²` is a derivation); `T` is Noetherian, so
   `P = (e)` with `e` idempotent (`Ideal.isIdempotentElem_iff_of_fg`).
6. On the basic open `D(1 − e)` (an affine open containing the origin, `Γ = T_{1−e}`), the map
   from `K` is surjective, so `D(1−e) → Spec K` is formally unramified; the unit section is a
   section of it, hence an open immersion (mul-rigidity's `isOpenImmersion_of_section`, Stacks
   024T).
Then mul-rigidity's proved chain gives `MulIsogeny` (formally unramified via the diagonal, ZMT).
mul-rigidity's two cotangent glue statements (`KerUnitOpenOfCotangentSurj`, `CotangentMulN`) are
no longer needed and were not proved.

**F4.** The `Over`-category pullback `A[n] = pullback [n] η` was used directly: tangent vectors
of `A[n]` are `Over`-morphisms into it, so no comparison with the scheme pullback was needed.

## 5. What remains

Nothing for `AbVarBaseChange`. For G9: only `G9Bridge.R10Weights` (g9-derham F1). Not done here:
`CotangentMulN` as stated by mul-rigidity (moot), and the removal of T26 from e1-sub's other
consumers (they use it for finiteness/freeness, not for base change).

## 6. Files (all new)

`ZInQKernel/Contrib/AbVarBC/`: `Dim.lean`, `Points.lean`, `Tate.lean`, `Torsion.lean`,
`Mul.lean` (mul-rigidity's file, namespaced), `Tangent.lean`, `KerUnit.lean`, `G9Instance.lean`,
`G9Mul.lean`, `Main.lean`, `Consumers.lean`, `E1SubBC.lean`. Checks: `scratch/g9-abvarbc/Axioms.lean`,
`axioms-output.txt`, `G4Check.lean`. Provenance: Dim.lean §1-2 are g0-dim's proofs; Points.lean §1
is unram-tate's `BCPoints.lean`; Mul.lean is mul-rigidity's `Mul.lean`; all are fork-internal
(no Tau Ceti code, so `ThirdParty/TauCeti/NOTICE` is unchanged).
