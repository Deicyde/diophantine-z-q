# kernel-field: `KernelFieldExists` (G4 + B1) from six leaves and two named glue Props

Task kernel-field, 2026-11-13.
- Lean: `scratch/kernel-field/KernelField.lean` (5659 lines). `scratch/kernel-field/assemble.sh`
  generates it from verbatim copies plus the new part, `scratch/kernel-field/New.lean` (1903
  lines).
- Results log: `scratch/kernel-field/log.md`. Compiler output: `scratch/kernel-field/build_final.txt`.
- Lattice check: `scratch/kernel-field/omax_cosets.py`.
- Base: `wip/integrate-w36b` (2dd83306), merged with `origin/wip/qm-pin` and
  `origin/wip/mobius-glue`. The other four branches named in the task were already in the base.

## 1. Main result

**g0-mod-field's `KernelFieldExists` is proved in Lean with its statement unchanged.** The inputs
are six leaves and two named glue Props. VERIFIED: `lake env lean
scratch/kernel-field/KernelField.lean` gives 0 errors and no `declaration uses 'sorry'` (about
75 s). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem listed
in §2.

```
theorem G0ModField.KernelField.kernelFieldExists_of_rigidity
    (hHFF : PkgI3.HomFreeFinite)              -- leaf T6, TextbookLeaves.t6 (Mumford §19 Thm 3)
    (hNOS : PkgI2.NeronOggShafarevich.{0})    -- leaf, ResearchLeaves.r7a (Serre–Tate 1968 Thm 1)
    (hRay : PkgI2.RaynaudCriterion.{0})       -- leaf, ResearchLeaves.r6
    (hTors : PkgI2.TorsionStructure.{0})      -- leaf, TextbookLeaves.t5 (A(K̄)[n] ≅ (ℤ/n)^{2g})
    (t27 : PkgI3.QMDichotomyYu)               -- leaf T27, TextbookLeaves.t27 (Yu 2013 Thm 1.1)
    (hRig : G0FibreSimple.RigidityHom)        -- textbook leaf (g0-fibresimple): Mumford §4 Cor. 1
    (h5 : G0FibreSimple.FibreComTrivial)      -- glue FS5 (g0-fibresimple): End_𝒪(P.A) = ℤ (NoCM)
    (hG : ConjIsogMaps)                       -- glue: the conjugacy maps m_σ (geometric part)
    : G0ModField.KernelFieldExists
```

Five of the leaves are fields of the bundles in `scratch/h-decomposition/Leaves.lean`: r6 and r7a
of `ResearchLeaves`; t5, t6 and t27 of `TextbookLeaves` (VERIFIED by reading L32972-33100).
`RigidityHom` is g0-fibresimple's new textbook leaf (rigidity: a morphism of abelian varieties
preserving the identity is a homomorphism). It is not yet in the bundles. Locators are
UNVERIFIED. FS5 and `RigidityHom` are copied verbatim from g0-fibresimple's `Tail.lean`.

**The task's two requests.**

1. **Connect G4 to `KernelFieldExists`.**
   - g4-weilres, inertia-homs and morph-descend proved the Hom field. Their theorem hides the
     kernel field `E` and the group `G ≤ GL_r(ℤ)` that `KernelFieldOut` asks for.
   - `kernelField_core` re-runs `homField_core` with `E = ℚ̄^{ker ρ}` and `G = ρ(G_ℚ)` exposed,
     and `[E:ℚ] = |G|`.
   - `kernelField_of_model` gives G4 in `KernelFieldOut`'s shape. Its leaves are `HomFreeFinite`
     and NOS. It uses morph-descend's `homDescends` and inertia-homs' `conjAction_inertia'`.
   - G4's side hypotheses on a rational fibre `PK/K` are proved:
     - `hdim`: `conj_dim`, from g0-dim's `G0Dim.dim_baseChange`;
     - `hgood`: `good_of_QML3`, from `LeafQM.AV.QML3.goodReduction` (NOS, Raynaud,
       TorsionStructure), using `3 ∈ T`;
     - `hK`: `galUnramifiedOutside_iff`.
2. **Skolem–Noether descent.**
   - **Twist removal.** `aut_O_inner` proves that every ring automorphism of `𝒪` is conjugation
     by a unit of `B = (2,-3)_ℚ` (from T13). `blinear_of_twisted_iso` uses it: A7's twisted QM
     isomorphism `e : (A, ι∘α) ≅ (A', ι')` becomes the nonzero `𝒪`-linear homomorphism
     `μ = e.φ ∘ ι(b)`, which is N5's `μ_σ`.
   - **Where NoCM enters.** The explicit `End⁰ = B` hypothesis is FS5's conclusion
     `End_𝒪(P.A) = ℤ`. `endEqOFibre_of` turns it into `End(P.A) = ι(𝒪)`, using T27, the proof of
     FS4 from T6 (copied), and the maximality of `𝒪` (`oMaximal`, proved).
   - **Integrality and commutation.** `conjMaps_of_qm` proves both from `End = ι(𝒪)`:
     - a discrepancy that is an endomorphism up to a nonzero integer is `ι(b)` with `b` central
       (`faithful_O`), hence an integer (`center_O`);
     - `conjugacyData_of_maps` then produces the rational cocycle `c`, its inflation,
       `c(1,1) = 1`, and the kernel-degree identity.

## 2. What is proved (new; all compiled, standard axioms)

| declaration | content |
|---|---|
| `conjugacyData_of_maps` | **B1's discrepancy algebra.** Maps with `ConjugacyData`'s clauses 1-4 and 10, plus `d·m_σ m_τ = n·m_στ`, on a group with `\|V[n]\| = n⁴`, give `c = n/d` with all of `ConjugacyData`. `c` is well defined and nonzero, is a 2-cocycle inflated from `Gal(L/ℚ)`, has `c(1,1) = 1`, and satisfies `\|ker m_σ\|\|ker m_τ\| = c⁴\|ker m_στ\|` |
| `kernelField_core`, `kernelField_of_model` | G4 with `E` and `G ≤ GL_r(ℤ)` exposed, `r ≤ 16F₀²`, `E` unramified outside `T`, and `G_{E⊔K}` fixing every homomorphism between conjugates |
| `conj_dim`, `bc_dim`, `good_of_QML3` | G4's `hdim` and `hgood` on a rational fibre |
| `torsionCountPts_of_leaf` | `\|A(ℚ̄)[n]\| = n⁴` for surfaces over `L ⊆ ℚ̄`, from `TorsionStructure`, transported along `AlgebraicClosure L ≅ ℚ̄` |
| `aut_O_inner` | Skolem–Noether on `𝒪`: `α(a) = u a u⁻¹` with `u ∈ B^×` |
| `blinear_of_twisted_iso` | Skolem–Noether descent on homomorphisms (above) |
| `center_O`, `faithful_O`, `int_of_rat_mem_O`, `exists_nat_mul_mem_O` | `Z(𝒪) = ℤ`; `𝒪` acts faithfully on any group with `\|V[n]\| = n⁴` (norm form anisotropic); clearing denominators |
| `int_of_integral`, `oMaximal` | **`𝒪` is a maximal order.** An element of `B` integral over `ℤ` has integral reduced trace and norm (Gauss's lemma). For `x` in an order `R ⊇ 𝒪`, `24·nrd(x)` is a quadratic form in the four traces `trd(x·eᵢ)`, and the congruences mod 3 and mod 8 (`decide`) put `x` in `𝒪`. Python check: of the 36 classes of `𝒪^∨/𝒪`, only `0` has integral norm |
| `endEqOFibre_of` | `End_𝒪(P.A) = ℤ ⟹ End(P.A) = ι(𝒪)`, from T27, T6 (via FS4) and `oMaximal` |
| `conjMaps_of_qm` | `TorsCount` + `End = ι(𝒪)` + the geometric clauses ⟹ `ConjMaps` |
| `endEqO_of_iso`, `endTransport_of` | `End = ι(𝒪)` moves along a `QML3` isomorphism. R1's naturality at `K ⊆ ℚ̄` gives the base change `Q` of `PK` with `[Q] = [P]` |
| `endTransportBC_of_rigidity` | **`End(Q.A) = ι_Q(𝒪) ⟹ End_L(A_L) = ι_L(𝒪)` from `RigidityHom`.** `(A_L)_ℚ̄` and `Q.A` are two pullbacks of `PK.A` along `Spec ℚ̄ → Spec K` (pasting; `isoIsPullback`). The isomorphism preserves the identity (`η(0) = 0`, `G4Conj.one_left_fst`), so it is a homomorphism by rigidity. It carries `ι_L(a)_ℚ̄` to `ι_Q(a)` (`pullback.lift_fst`). Base change `L → ℚ̄` is faithful (`endBC_injective`, bp-qmmoduli) |
| `conjIsogMapsAt_bot` | sanity check: the new clause list is satisfiable (an abelian variety over `ℚ` with its Galois action) |
| `kernelFieldExists_of_pieces`, `_of_leaves`, `_of_leaves_FS5`, `_of_split`, `_of_split'`, `_of_split''`, `_of_final`, `_of_final'`, `_of_rigidity` | the successive reductions (§3) |

## 3. What remains (glue, not leaves)

1. **`ConjIsogMaps`** (geometric; no NoCM content; large).
   - Setting: moduli data with R1fp-R2fp, a `ℚ̄`-point over a rational `j₀` with object `P`, a
     rational fibre `PK/K` over `P`, and a Hom field `L ⊇ K` of `PK.A` (g4-weilres'
     `conjAction` is trivial on `G_L`).
   - It asks for maps `m_σ` on `A_L(ℚ̄)` with `ConjIsogMapsAt`:
     - the Galois action on `G_L`, and inflation from `Gal(L/ℚ)`;
     - `𝒪`-linearity for `ι_L = endBC ∘ PK.q.iota`;
     - surjective with finite kernel;
     - `e·m_σ m_τ = δ∘m_στ` with `δ ∈ End_L(A_L)` and `e ≠ 0`;
     - algebraicity `m_σ(x) = F_σ∘x∘Spec σ`.
   - Proved inputs:
     - A7 `conj_twist_of_rational` (kernel, valid for every R1fp-R2fp triple);
     - `blinear_of_twisted_iso`, which gives `μ_σ`.
   - Missing (model check, no human review):
     - moving `μ_σ` from `P` to the conjugates `conjData K PK.A`. The same pasting and rigidity
       argument as `endTransportBC_of_rigidity` applies;
     - Galois descent of the `G_L`-fixed `μ_σ` to `L`;
     - the quasi-inverse `ψ μ_στ = [e]` (Mumford §8; the same input as g0-split's
       `ReverseIsogeny`);
     - points-level bookkeeping for `m_σ = μ_σ∘σ`, and the semilinear `F_σ`.
   - It holds for CM fibres too.
2. **`EndTransport` is now proved from the leaf `RigidityHom`** (`endTransport_of`,
   `endTransportBC_of_rigidity`).
   - **Finding** (VERIFIED by reading `IsBaseChangeOf` and `IsModelOver`): these record only a
     pullback square of schemes (with `ι` and `η` compatible), not the group law.
   - So the identification `(A_L)_ℚ̄ ≅ Q.A` is a homomorphism only by rigidity. `η(0) = 0` gives
     `0 ↦ 0`, and rigidity then applies.
3. **`G0FibreSimple.FibreComTrivial`** (FS5, owned by g0-fibresimple). For `u ∉ 𝒞`,
   `End_𝒪(P.A) = ℤ`. Of the inputs above, it is the only one whose truth for an arbitrary triple
   depends on pinning `Φ`. qm-pin's repair (`R1famProps`, `R1univProps`, `MobiusGlue`) transfers
   it from the leaf's own triple.

Intermediate Props that are now theorems: `TorsionCountPts`, `ConjMapsOnHomField`,
`ConjMapsNoCM`, `EndEqOOnHomField`, `EndEqOFibre`, `OMaximal`, `EndTransport`,
`EndTransportBC`.

## 4. Findings

- **`KernelFieldExists` needs NoCM, through clause 3 of `ConjugacyData`** (mathematical argument,
  not compiled).
  - Take a CM fibre: `End⁰ = M₂(F)` with `F` imaginary quadratic.
  - Then `f ↦ μ_σ ^σf μ_σ⁻¹` restricts to `σ|_F` on the centre. When `σ` moves `F`, it is not
    inner, so no `m_σ` commutes with all of `End_L(A_L)`.
  - So the quantifier over all triples carries FS5's pinning issue. The split isolates that issue
    in FS5 alone: `ConjIsogMaps` holds for every triple (model check), and `EndTransport` is
    proved.
- **`KernelFieldOut` does not use `P`, and links `G` to `E` only by `[E:ℚ] = |G|`.** Neither is a
  defect.
  - The degree bound needs only the cardinality.
  - `ConjugacyData` on `A_{E⊔K}` forces `μ_σ` to be defined over `E ⊔ K`.
  - `kernelField_of_model` produces the genuine kernel field.
- **`ConjugacyData`'s clause order is consistent** (VERIFIED by reading, together with
  g0-mod-field's compiled `descentDatum_bot`). Because `Spec` is contravariant,
  `m_{σk} = m_σ m_k` and `m_{kσ} = m_k m_σ` match `F_{σk} = F_{kσ} = F_σ` and `F_k = id`.
- **Copies.** All copies are verbatim, listed in `assemble.sh` and the section headers:
  - `Descend.lean` 3-401;
  - `InertiaHoms.lean` 7-2089;
  - `G4Closed.lean` 1867-1897;
  - `Dim.lean` 107-305;
  - `ModField.lean` 17-end;
  - from `Tail.lean`: FS5, lines 38-117, 152-164 (FS4), 208-282 and 357-363 (`RigidityHom`);
  - from `QMAbVar.lean`: `endBC`, lines 528-556, and lines 558-575 (faithful base change,
    `endBC_injective`), with `AbVar` qualified.

## 5. Integration

`New.lean` needs only `ZInQKernel/HDecomp/` modules, ModField.lean's imports and
`HDecomp/Textbook/SkolemNoether`. It can follow ModField.lean, InertiaHoms/G4Closed, Dim.lean
and Tail.lean as a module. In g0-mod-field's `fieldDescentUnr` and
`modularConstituent_of_ranges_T14`, replace `hKer : KernelFieldExists` by
`kernelFieldExists_of_rigidity hHFF hNOS hRay hTors t27 hRig h5 hG`.

## 6. Labels

- **VERIFIED (compiled):** every declaration in §2 and its axiom list (`build_final.txt`).
- **VERIFIED (computed):** the 36-class check (`omax_cosets.py`).
- **VERIFIED (read):** the definitions `KernelFieldExists`, `KernelFieldOut`, `ConjugacyData`,
  `FibreCtx`, `RationalFibre`; `homField_core`, `homField_of_model_leaves'`; `QML3.goodReduction`,
  `TorsionStructure`, `conj_twist_of_rational`, `R1fpProps`, `IsBaseChangeOf`, `QMIso`,
  `LeafSkolemNoether`, `B6_commute_i_j`, `aniso_rat`; FS5 and FS4.
- **SPECULATIVE (model check, no human review):** the truth argument for `ConjIsogMaps`, and the
  CM finding of §4.
- **UNVERIFIED locators:** Mumford §19 Thm 3, §4 Cor. 1, §8; Serre–Tate 1968 Thm 1; Yu 2013
  Thm 1.1; Vignéras III §5.
