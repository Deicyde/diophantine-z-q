# y3-412-lattice: the lattice step of Deligne's 4.12 for the kernel's PEL datum

**No count change.** This task retires no frozen field. The code is additive (new files only under
`ZInQKernel/Contrib/OneProof/Y3Lattice412/`) and nothing is folded.

Base: `d28aef9839b8c12dcda2b24b3a22c993f4975dbf`. PEL datum: `B = (2, −3 | ℚ)` (`LeafQM.B`), `V = B`
(left multiplication), `V_ℤ = 𝒪` (`LeafQM.O`), `K = K₃` (`ShimuraCFT.K3Q`).

## 1. What is proved (all VERIFIED: compiled with `lake build`, no `sorry`, no new axioms)

Every theorem below reports `[propext, Classical.choice, Quot.sound]` under `#print axioms`
(`ZInQKernel/Contrib/OneProof/Y3Lattice412/Check.lean`, 30 lines; output in
`scratch/y3-412-lattice/axioms.txt`). Namespace `Y3Lattice412`; opens `LeafQM ShimuraCFT RayClassCFT`.

| part | theorem | exact type |
|---|---|---|
| A0 | `rat_mem_ZhatQ_iff` | `(r : ℚ) : algebraMap ℚ AQ r ∈ ZhatQ ↔ ∃ z : ℤ, r = z` |
| A1 | `bEmb_mem_OhatQ_iff` | `(b : LeafQM.B) : bEmb b ∈ OhatQ ↔ InO b` |
| A2 (def) | `latticeAt` | `(g : BAQˣ) : Set LeafQM.B := {b \| bEmb b * (g : BAQ) ∈ OhatQ}` |
| A2 | `latticeAt_of_mem_OhatU` | `{u : BAQˣ} (hu : u ∈ OhatU) : latticeAt u = {b \| InO b}` |
| A2 | `latticeAt_mul_OhatU` | `(g : BAQˣ) {u : BAQˣ} (hu : u ∈ OhatU) : latticeAt (g * u) = latticeAt g` |
| A3 | `latticeAt_zero`, `latticeAt_add`, `latticeAt_neg` | `0 ∈ latticeAt g`; `a ∈ L → b ∈ L → a + b ∈ L`; `a ∈ L → -a ∈ L` (`L = latticeAt g`); bundled as `latticeAtAddSubgroup g : AddSubgroup LeafQM.B` |
| A3 | `latticeAt_mul_left` | `{g : BAQˣ} {a b : LeafQM.B} (ha : InO a) (hb : b ∈ latticeAt g) : a * b ∈ latticeAt g` |
| A3 | `latticeAt_bounds` | `(g : BAQˣ) : ∃ N : ℕ, 0 < N ∧ (∀ b : LeafQM.B, InO b → (N : ℚ) • b ∈ latticeAt g) ∧ (∀ b ∈ latticeAt g, InO ((N : ℚ) • b))` |
| A3 | `latticeAt_basis` | `(g : BAQˣ) : ∃ e : Fin 4 → LeafQM.B, LinearIndependent ℚ e ∧ Submodule.span ℚ (Set.range e) = ⊤ ∧ latticeAt g = {x \| ∃ n : Fin 4 → ℤ, x = ∑ i, ((n i : ℤ) : ℚ) • e i}` |
| A3 | `latticeAt_eq_O_mul` | `(g : BAQˣ) : ∃ α : LeafQM.B, ShimuraGlue.nrdQ ℚ α ≠ 0 ∧ latticeAt g = (fun b => b * α) '' {b \| InO b}` |
| A4 | `latticeAt_dc` | `{γ : LeafQM.B} (hγ : γ ≠ 0) {g g' k : BAQˣ} (hk : k ∈ K3Q) (h : (g' : BAQ) = bEmb γ * (g : BAQ) * (k : BAQ)) : latticeAt g' = (fun b => b * binv γ) '' latticeAt g` |
| A4 | `latticeAt_dc_of_OhatU` | same with `(hγ : ShimuraGlue.nrdQ ℚ γ ≠ 0)` and `(hk : k ∈ OhatU)` |
| A4 | `latticeAt_of_DCRel` | `{τ τ' : UpperHalfPlane} {g g' : BAQˣ} (h : DCRel τ g τ' g') : ∃ γ : LeafQM.B, 0 < ShimuraGlue.nrdQ ℚ γ ∧ latticeAt g' = (fun b => b * binv γ) '' latticeAt g` |
| A4 | `binv_spec` | `{γ : LeafQM.B} (hγ : γ ≠ 0) : γ * binv γ = 1 ∧ binv γ * γ = 1` (`binv` is the tree's `γ⁻¹`; `LeafQM.B` has no `Inv` instance) |
| A5 (def) | `delElt`, `delLattice` | `delElt g : GAf := toGAf g⁻¹`; `delLattice g : Set BAQ := DeligneY3Bridges.app (delElt g)⁻¹ '' VZhat` (that is `k⁻¹(V̂_ℤ)`) |
| A5 | `delLattice_eq` | `(g : BAQˣ) : delLattice g = (fun v => v * ((g⁻¹ : BAQˣ) : BAQ)) '' OhatQ` |
| A5 | `latticeAt_eq_deligne` | `(g : BAQˣ) (b : LeafQM.B) : b ∈ latticeAt g ↔ bEmb b ∈ delLattice g` |
| A5 | `delElt_dcRel` | `(z z' : Y3Hodge.HPM) (g g' : BAQˣ) : DCRelDel z (delElt g) z' (delElt g') ↔ Y3Hodge.DCRelPM z' g' z g` |
| B1 (def) | `IsHodgeH1PrintAt` | `(P : QML3 ℂ) (τ : UpperHalfPlane) (L : Set LeafQM.B) : Prop` — `IsHodgeH1Print` with `c : L → Path 1 1`, bijectivity of `b ↦ loopClass (c b)` on `L`, the `𝒪`-clause `∀ (a : O) (b : L) (hab : (a : B) * b ∈ L), loopClass (pushLoop (P.q.iota a) (c b)) = loopClass (c ⟨_, hab⟩)`, the same path and Hodge clauses |
| B1 | `isHodgeH1PrintAt_O_iff` | `(P : QML3 ℂ) (τ : UpperHalfPlane) : IsHodgeH1PrintAt P τ {b \| InO b} ↔ IsHodgeH1Print P τ` |
| B2 (def) | `ModuliAtLattice` | `(Y) (Φ : PtEquiv Y) (Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop := ∀ τ g, ∃ P : QML3 ℂ, Φ ℂ (Ψ (toPM τ) g) = M3.mk P ∧ IsHodgeH1PrintAt P τ (latticeAt g)` |
| B2 | `moduliAtUnitsHP_of_lattice` | `(h : ModuliAtLattice Y Φ Ψ) : ModuliAtUnitsHP Y Φ Ψ` |
| B2 | `moduliAtUsedUnitsHP_of_lattice` | `(h : ModuliAtLattice Y Φ Ψ) : ModuliAtUsedUnitsHP Y Φ (fun τ g => Ψ (toPM τ) g)` |

Helpers also checked: `mem_latticeAt`, `mul_mem_OhatQ_iff_of_OhatU`, `latticeAt_one`, `exists_den_unit`,
`nrdQ_ne_zero_of_ne_zero`, `K3Q_subset_OhatU`, `ofInt_eq_sum`, `eq_sum_oVec`, `oVec_linearIndependent`.

Notes on the proofs.
* A0 and A1 were already in the tree (`ShimuraCFT.rat_mem_zhat_iff`, `inO_of_bEmb_mem`,
  `bEmb_mem_of_inO`, `RayClassShimura.lean`); A0, A1 here restate them.
* The bounds in A3 use `RayClassCFT.exists_den_B` (a finite adele is integral at all but finitely many
  places, `FiniteAdeleRing.cofinite_mem_adicCompletionIntegers`).
* Full rank: `latticeAt_eq_O_mul` comes from the tree's `RayClassCFT.classNumberOneB_proof`
  (`g = γ u`, `u ∈ 𝒪̂^×`), A4 and A2: `L_g = 𝒪 γ⁻¹`. The basis is `eᵢ = oVec i * γ⁻¹`, where
  `oVec i` is the basis `1, i, (1+j)/2, (i+k)/2` of `𝒪`.
* B3 is respected: nothing about the converse, and `ModuliAtLattice` is not put in place of any
  frozen clause. It is stronger than `ModuliAtUnitsHP`.

## 2. Convention check (A5)

**Result: the print's lattice is `B ∩ 𝒪̂ g⁻¹`, the convention of `latticeAt`. No switch to
`B ∩ g𝒪̂` is needed.**

* Lean side (VERIFIED). The bridges map Deligne's class of `toGAf g` to the kernel's class of `g⁻¹`
  (`PEL.dcRelDel_iff_PM`). So the kernel's point `[h, g]` is Deligne's point with element
  `k = delElt g = toGAf g⁻¹`, that is `x ↦ x g` (`app_toGAf`). Then `k⁻¹ = toGAf g` is `x ↦ x g⁻¹`,
  so `k⁻¹(V̂_ℤ) = 𝒪̂ g⁻¹` (`delLattice_eq`). Its points in `B` are exactly `latticeAt g`
  (`latticeAt_eq_deligne`). `delElt_dcRel` checks that `delElt` turns Deligne's relation into the
  kernel's `DCRelPM`.
* Reading side. 4.12 is cited as the bridges' README cites it: printed pp. 148–149, "T̂(B) = k⁻¹(V̂_ℤ)",
  an AI reading of a hashed copy. One step is not in that README: that the level datum of Deligne's
  point `(h, k)` in 4.11 (c) is the element `k` itself, not `k⁻¹`. I take it from the README's row U
  (`L_g = B ∩ 𝒪̂ g⁻¹`) and from the docstrings in `RayClassShimura.lean`. Status: UNVERIFIED against
  the print, since I have no network.
* Structural cross-check (VERIFIED by A2–A4). Of the four candidates `𝒪̂g⁻¹`, `𝒪̂g`, `g𝒪̂`, `g⁻¹𝒪̂`,
  `H₁` must be stable under `L_ℤ = 𝒪` acting on the left, and the lattice must depend only on the
  class `gK₃`. `B ∩ 𝒪̂g⁻¹` has both properties (`latticeAt_mul_left`, `latticeAt_mul_OhatU`).
  `g𝒪̂` and `g⁻¹𝒪̂` are only right `𝒪̂`-modules. `𝒪̂g` is not right-`K₃`-invariant as a function of `g`
  (`𝒪̂ g k ≠ 𝒪̂ g` in general). So the convention is also forced by the kernel's left-`B^×`,
  right-`K₃` double cosets.

## 3. Proposed row U for `ZInQKernel/Contrib/OneProof/DeligneY3Bridges/README.md`

Not applied; the README is unchanged. Proposed text:

| U | `ModuliAtUnitsHP`: at `u ∈ OhatU`, `IsHodgeH1Print` | 4.12 p.148–149: `T̂(B) = k⁻¹(V̂_ℤ)`, i.e. `H₁ = L_g = B ∩ 𝒪̂ g⁻¹` | `PEL.mem_OhatU_iff` (`OhatU ↔ G(Ẑ)`); `Y3Lattice412.latticeAt_eq_deligne` (`L_g = B ∩ k⁻¹(V̂_ℤ)` for Deligne's `k = toGAf g⁻¹`); `Y3Lattice412.latticeAt_of_mem_OhatU` (`L_u = 𝒪` for `u ∈ 𝒪̂^×`); `Y3Lattice412.latticeAt_dc` (`L_{γgk} = L_g γ⁻¹`); `Y3Lattice412.latticeAt_basis` (full `𝒪`-lattice); `Y3Lattice412.moduliAtUnitsHP_of_lattice` (the print's description in `L_g` form, `ModuliAtLattice`, implies the clause; `isHodgeH1PrintAt_O_iff` checks the generalization at `L = 𝒪`) | match on `H₁`; polarization and level dropped (weaker); the existence of `B` with `T̂(B) = k⁻¹(V̂_ℤ)` in each isogeny class is asserted in 4.12, not proved in Lean (see y3-412-lattice report, part C) |

## 4. Part C: the existence step of 4.12 (report only, no Lean)

4.12 also asserts that each isogeny class `(A, ρ, p̄, k̄)` of Scholie 4.11 with level class `k̄`
contains a `B` with `T̂(B) = k⁻¹(V̂_ℤ)`, unique up to isomorphism. This passage from 4.11's isogeny
classes to 4.12's isomorphism classes is what turns the isogeny-class moduli of 4.11 into the
lattice description that `ModuliAtLattice` formalizes.

### 4.1 A Lean statement over ℂ, in the tree's language

Write `Λ_{τ,L} = {ι(b)(τ, 1)ᵀ : b ∈ L} ⊂ ℂ²` for a lattice `L ⊆ B`; `qmLattice` is the case `L = 𝒪`.
Proposed Prop (SPECULATIVE as a formalization; not compiled):

```lean
/-- 4.12's existence and uniqueness over ℂ, lattice form. -/
def IsogenyLatticeStep : Prop :=
  ∀ (P : QML3 ℂ) (τ : UpperHalfPlane) (Φ : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φ →
    HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φ →
    ∀ L : AddSubgroup LeafQM.B, (∀ a b, InO a → b ∈ L → a * b ∈ L) →
      (∃ N : ℕ, 0 < N ∧ (∀ b, InO b → (N : ℚ) • b ∈ L) ∧ ∀ b ∈ L, InO ((N : ℚ) • b)) →
    -- existence
    (∃ (Q : QML3 ℂ) (ΦQ : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
      IsUniformization (RingHom.id ℂ) (latLattice τ L) ΦQ ∧
      HDec.HSyn.G0Split.FibreQM.IotaCompatible Q ΦQ ∧
      IsHodgeH1PrintAt Q τ L) ∧
    -- uniqueness: two such objects are 𝒪-isomorphic (level structures aside)
    (∀ Q Q' ΦQ ΦQ', IsUniformization _ (latLattice τ L) ΦQ → IsUniformization _ (latLattice τ L) ΦQ' →
      IotaCompatible Q ΦQ → IotaCompatible Q' ΦQ' → Nonempty (QMIsoNoLevel Q Q'))
```

Here `latLattice τ L : Submodule ℤ (Fin 2 → ℂ)` is the span of `Λ_{τ,L}`, and `QMIsoNoLevel` is
`QML3.Iso` without the level clause. The level-3 structure of `Q` is whatever transported datum one
chooses. The kernel's `QML3` requires one, but `ModuliAtLattice` does not read it.

Applied with `L = latticeAt g`, which is a left-`𝒪`-stable lattice squeezed between `N𝒪` and `N⁻¹𝒪`
(A3, proved), this statement and the field's object at `g = 1` would give `ModuliAtLattice` from
`ModuliAtUnitsHP`. By B3 that converse is out of scope here and is only recorded.

### 4.2 What a proof from Scholie 4.11's isogeny form would need

| # | missing piece | connects | status in the tree |
|---|---|---|---|
| C1 | Quotient of an abelian variety over `ℂ` by a finite subgroup (here the constant subgroup `N⁻¹L/𝒪 ⊂ A[N](ℂ)`), with kernel and universal property | `ShimuraSteps.Quotient.finiteSubgroupQuotient_exists` (`AbVarQuotientFinite.lean`) → an `AbVar ℂ` analogue | VERIFIED (read): proved over `ℚ` only (`B : AbVar ℚ`, base `Spec ℚ`). Its inputs (`finiteSchemeQuotient`, `cartierSmooth_proof ℚ`) look characteristic-0 generic, but whether they generalize to `ℂ` is UNVERIFIED. The general-field stabilizer quotient `CloudR2Poincare.L4.FiniteStabilizerQuotientExists` is an internal unproved input |
| C2 | The quotient's uniformization: `q ∘ Φ` is an `IsUniformization` with kernel `N⁻¹Λ_{τ,L}`; then rescale by `N` to get kernel `Λ_{τ,L}` | `ZInQ.LeafPush2.IsUniformization` (`HDecomp/LeafPush2/R22.lean`), `IsFiniteSubgroupQuotient.kernel` on `ℂ`-points | missing. Needs: `ℂ`-points of the scheme kernel are the finite subgroup; surjectivity of `q` on `ℂ`-points; holomorphy of regular functions of `Q` along `q ∘ Φ` (local sections of `Q` pull back to sections of `A`) |
| C3 | QM structure on the quotient: `ι(a)` preserves `N⁻¹Λ_{τ,L}`, so `ι_A(a)` descends | `IsFiniteSubgroupQuotient.lift_unique`, or `HomUnify.HomLatticeCorr` clause 2 (realization over `ℂ`) with `M = ι(a)` | `HomLatticeCorr` is a textbook LEAF (not proved); the descent route through `lift_unique` needs only C1 |
| C4 | Hodge form of the new object: `IsUniformization` with lattice `Λ_{τ,L}` plus `IotaCompatible` ⇒ `IsHodgeH1PrintAt Q τ L` | generalize `Y3Hodge.print_iff_hodge` and `Y3Hodge.bOf_bijective` (`Y3HodgePrint.lean` §§3–4) from `𝒪` to `L` | within reach: the `𝒪`-proof uses `RayClassCFT.iota_eig_inj` and `mem_qmLattice_iff`, which are not specific to `𝒪` |
| C5 | Uniqueness: same lattice ⇒ isomorphic | `HomUnify.HomLatticeCorr` clause 2 with `M = id` both ways; or `HDecomp/Analytic/Uniformization.lean` (`IsUniformization.exists_equiv`, `exists_complexLinear`) plus an algebraization step | the analytic comparison (`exists_equiv`) is VERIFIED (read); turning the analytic isomorphism into an algebraic one is GAGA, i.e. `HomLatticeCorr` (LEAF) or `T11b_Rigidity` |
| C6 | Scholie 4.11 in isogeny form as a Lean statement (points ↔ isogeny classes `(A, ρ, p̄, k̄)`) | none in the tree (no declaration mentions Scholie 4.11 outside the bridges' docstrings) | missing. With the field's moduli clause at units, 4.11's isogeny form is not needed over `ℂ`: the object at `g = 1` is supplied by `ModuliAtUnitsHP`/`IsShimuraHolFamilyHP` |
| C7 | Every complex abelian variety has an analytic uniformization | `BPAnalytic.Uniformization.UniformizationLeafAll`, `ZInQ.LeafPush2.exists_isUniformization_of_leaf` | LEAF (not proved); not needed if one starts from an object that already has `IsHodgeH1Print` (which yields a uniformization) |

### 4.3 Is an analytic proof over ℂ within reach?

**Partly.** The lattice algebra is done: A3 shows that `L_g` is a full `𝒪`-stable lattice, and `L_g = 𝒪γ⁻¹`.
The analytic comparison is in the tree (`IsUniformization.exists_*`). C4 looks within reach. The real
gap is C1+C2: constructing the complex abelian variety `ℂ²/Λ_{τ,L}` as an `AbVar ℂ`. The other route,
algebraizing the torus via Riemann's theorem 4.7, is also not in the tree. The finite-quotient route
needs `finiteSubgroupQuotient_exists` over `ℂ` and the analytic description of the quotient's
`ℂ`-points. The tree has neither.

**Class-number-one shortcut for this datum (SPECULATIVE, not attempted, out of scope by B3).**
Because `L_g = 𝒪γ⁻¹` (proved), and `γ` can be taken with `nrd γ > 0` (`𝒪^×` contains `1 + i`, of
reduced norm `−1`), the existence step needs no quotient construction. Take the object `P` at the
point `γ⁻¹·τ` with `IsHodgeH1Print P (γ⁻¹·τ)`, and transport it by `b ↦ bγ⁻¹ : 𝒪 → L_g` and
`β_new(M) = β(M ι(γ))`. The 𝒪-clause holds trivially; the Hodge clause needs
`ι(γ) J_{γ⁻¹τ} ι(γ)⁻¹ = J_τ` (the conjugation law of `Jmat`, cf. `Y3Hodge.iota_mul_Jmat`, not
checked here). In the kernel's double cosets `Ψ(τ, γu) = Ψ(γ⁻¹τ, u)`, so for a `Ψ` with the
fibre clause this gives `ModuliAtLattice` from `ModuliAtUnitsHP`. This is a converse to B2. Per B3 it is
not stated in Lean and must not replace a frozen clause.

## 5. Files

* `ZInQKernel/Contrib/OneProof/Y3Lattice412/Lattice.lean`: A0–A4 (imports `RayClassShimura`).
* `ZInQKernel/Contrib/OneProof/Y3Lattice412/Convention.lean`: A5 (imports the bridges' `Statement`).
* `ZInQKernel/Contrib/OneProof/Y3Lattice412/Moduli.lean`: B1, B2 (imports `DeligneNarrow`).
* `ZInQKernel/Contrib/OneProof/Y3Lattice412/Check.lean`: `#print axioms`.
* `scratch/y3-412-lattice/log.md`, `scratch/y3-412-lattice/axioms.txt`.

No existing file was changed. `ZInQKernel.OneProof.Main` is not imported, and the new modules are
not imported by any existing module.
