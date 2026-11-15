# sir-printed: `shimuraIntegralModelRep` against its printed source (Lan / Kottwitz PEL form)

Task sir-printed, 2026-11-15. Base `9a100aa7` (leaf-fold22b). Lean: `ZInQKernel/Contrib/OneProof/ShimuraIntegralModelUsed.lean`
(new); scratch: `scratch/sir-printed/` (`log.md`, `Check.lean`, `TwistAlgebra.lean`, `Discharges.lean` with its output,
`BypassFold.lean` with its output, `autofold.json`). Marks: **VERIFIED** (read in a source, computed or compiled),
**STANDARD** (published, reference given), **SPECULATIVE**. No network: every theorem number recalled from memory is
**UNVERIFIED**.

## 1. Result

**The goal as posed cannot be reached in Lean today, and the field does not need it.**

1. *Not statable.* Kottwitz 1992 §5 and Lan 2013 Thm 1.4.1.11 are PEL moduli problems. Their objects carry a
   polarization `λ : A → A^∨` over the base. Lan's level structures are symplectic for the Weil pairing `e^λ` on
   `A[n]`. Kottwitz's are `K^p`-orbits of rational Tate-module isomorphisms, taken up to prime-to-`p` isogeny. Mathlib
   v4.35 and the kernel have no dual abelian scheme over a base, no polarization over a base and no Weil pairing over
   a base (VERIFIED, §6). So the PEL functor cannot be stated over genuine definitions. The relative Lemma P (step (a))
   and the integral comparison of level structures (step (b)) cannot be stated either, let alone proved.
2. *Not needed (proved in Lean).* The field's only consumer uses the universal property at two kinds of base:
   `S = Spec ℚ̄`, and `S = 𝒴` for the Hecke relabelings of the universal object. The new leaf
   `SIRPrinted.ShimuraIntegralModelUsed` asks exactly this, and two theorems are compiled with standard axioms:

   ```lean
   theorem SIRPrinted.shimuraIntegralModelUsed_of_rep :
       SGRSplit.ShimuraIntegralModelRep → SIRPrinted.ShimuraIntegralModelUsed      -- never stronger
   theorem SIRPrinted.shimuraGoodReductionNoGuard_of_used :
       SIRPrinted.ShimuraIntegralModelUsed → HDec.CurveSplitGR.ShimuraGoodReductionNoGuard  -- enough
   ```
3. *The new leaf needs neither (a) nor (b) (paper, §3, with the algebra compiled).* It follows from Lan's printed
   PEL theorem by three ingredients:
   - **Lemma P over `ℚ̄` only.** This is the characteristic-0 field version of rv-qm-polar, the same premise the
     kernel's char-0 moduli leaves are already read with.
   - **The level-structure comparison over `ℚ̄` only.** It is elementary.
   - **Yoneda for the Hecke clauses.** It is applied to explicit automorphisms of the PEL functor, whose
     polarizations are written down: `λ ↦ λ ∘ ι(ε v_α)`.

   The PEL-datum algebra behind the Hecke clauses is compiled in `scratch/sir-printed/TwistAlgebra.lean` (§3.3).
4. *Level 3 at `3 | D` is not a problem for the PEL sources.*
   - Lan works at `□ = {p}` with a level `H ⊂ G(Ẑ^p)`. Kottwitz only asks `K_p` to be hyperspecial. Both allow full
     level 3 at `3 ≠ p`.
   - The risk the review raised concerns Buzzard 1997 and Morita 1981. These are demoted to secondary sources.
   - Primes `p = 2, 3`: the field is false there. At `p | D` the curve has bad (Čerednik–Drinfeld) reduction, so no
     smooth model exists (STANDARD). Neither the field nor any consumer uses them: every consumer asks only for
     `p > 324` and needs every such `p` (§2).

**Leaf rating.** `shimuraIntegralModelUsed` is **not the printed form**. It is a consequence of the printed PEL theorem
(Lan 2013 Thm 1.4.1.11 with Thm 5.3.3.1; Kottwitz 1992 §5 via Lan §1.4.3) together with Lemma P over `ℚ̄`. The
derivation is in §3 and is paper-only. The reason is that the PEL functor itself cannot be written in Lean.

- Proposed kind: **published, flag "pending reading"**. That counts GLUE until a reader confirms that Lan's hypotheses
  hold for this datum at `□ = {p}` and level `U^p(3)` (§3.1).
- The strict counts are the same before and after the fold: one GLUE row is replaced by one GLUE row.
- What changes is the reading task, which shrinks:
  - before: Kottwitz's PEL functor, plus the relative Lemma P over every locally noetherian base, plus the
    rational-to-integral level comparison, plus the level-at-`D` question for Buzzard/Morita;
  - after: Lan 1.4.1.11 and 5.3.3.1 for one PEL datum, plus Lemma P over `ℚ̄`.

**The fold** has to be done by hand. The new leaf is weaker than the field, so `autofold.py` cannot fold it: it maps
generation `k+1` to `k`, which would need the field. A bypass fold maps the new generation straight to
`OpenAddedLeaves16`, where `shimuraGoodReductionNoGuard` is a field. The dry run compiles, including a copy of
`frozenTarget` on the new bundle (§7).

## 2. The consumers (VERIFIED, read)

| use | where | what it needs |
|---|---|---|
| `shimuraIntegralModelRep` | `TailZ34.openAddedLeaves16_of_OpenAddedLeaves17` | only through `SGRSplit.shimuraGoodReductionNoGuard_of_printed` |
| `hRep` in `SGRSplit.shimuraGoodReductionNoGuard_of_rep` (l.267-363) | injectivity on `ℚ̄`-points | uniqueness of the classifying map over `S = Spec ℚ̄` |
| | surjectivity on `ℚ̄`-points | existence over `S = Spec ℚ̄` |
| | Hecke `Aut 𝒪` / `𝒪^×` | existence over `S = 𝒴` for `twistAb 𝒜 α`, `twistAb 𝒜 α⁻¹`, `rightMulAb 𝒜 u`, `rightMulAb 𝒜 u⁻¹`; uniqueness over `𝒴` for `𝒜` (to make the two maps inverse) |
| `ShimuraGoodReductionNoGuard` | `TailW.shimuraGoodReduction_of_noGuard` → `ShimuraGoodReduction` | all `p > 324` |
| `ShimuraGoodReduction` | `TailN.heckeVertWitness_of_leaves5`, `TailL.heckeVertGauss_of_goodReduction` (`hL p hp324` for every prime `p > 324` of `HeckeVertGauss`) | all `p > 324` |

So the primes cannot be restricted further. `p = 2, 3` never occur. The bases that occur are `Spec ℚ̄` and `𝒴`.

## 3. The new leaf and its derivation from the printed theorem

### 3.1 Statement (`ZInQKernel/Contrib/OneProof/ShimuraIntegralModelUsed.lean`)

```lean
def ShimuraIntegralModelUsedAt (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMAbScheme 𝒴.left),
    IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧
    (∀ 𝒜' : QMAbScheme (Spec (CommRingCat.of Qbar)),
      ∃! y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left, QMFamFibre 𝒜.toQMFamily y 𝒜'.toQMFamily) ∧
    (∀ α : O ≃+* O, ∃ g : 𝒴 ≅ 𝒴, QMFamFibre 𝒜.toQMFamily g.hom.left (twistAb 𝒜 α).toQMFamily) ∧
    (∀ u : Oˣ, ∃ g : 𝒴 ≅ 𝒴, QMFamFibre 𝒜.toQMFamily g.hom.left (rightMulAb 𝒜 u).toQMFamily)

def ShimuraIntegralModelUsed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p → ShimuraIntegralModelUsedAt p
```

`QMAbScheme`, `QMFamFibre`, `twistAb`, `rightMulAb`, `Zloc` and `Qbar` are the kernel's and sgr-split's definitions,
unchanged. The statement quantifies over genuine abelian schemes, and it is not vacuous: it asserts that `𝒴` and `𝒜`
exist.

**Printed source** (locators UNVERIFIED):
- K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, LMS Monographs 36, Princeton 2013,
  Thm 1.4.1.11. Statement: the moduli problem `M_H` of tuples `(A, λ, i, α_H)` over locally noetherian
  `S₀`-schemes, with `H` neat, is representable by a smooth quasi-projective scheme over `S₀ = Spec 𝒪_{F₀,(□)}`.
- Lan 2013, Thm 5.3.3.1: `M_H` is proper when there are no cusps.
- Lan 2013, §1.4.3: comparison with R. Kottwitz, *Points on some Shimura varieties over finite fields*, J. AMS 5
  (1992), §5. Kottwitz's bibliographic identity is in docs/research/locators.md row R1; §5 itself is unread.

**PEL datum** (the algebra is compiled in rv-qm-polar, `ZInQKernel/HDecomp/QM/Polar.lean`):
- `B = (2, −3)`, the maximal order `𝒪`, and `□ = {p}`. Lan needs `p ∤ disc 𝒪 = 36` and `𝒪 ⊗ ℤ_p ≅ M₂(ℤ_p)`.
- Positive involution `x† = μ⁻¹x̄μ` with `μ = 2j + k` (`trd_mul_dag_pos`).
- `L = 𝒪`, with `E₀(x, y) = trd(μ⁻¹xȳ)`. This form is alternating, `†`-compatible (`E0_rosati`) and unimodular
  (`gram_det`), so `L` is self-dual everywhere.
- `G = GU(L, E₀) = B^×` (opposite action). The reflex field is `ℚ` and the relative dimension is 1.
- Level `H = U^p(3) = ker(G(Ẑ^p) → (𝒪/3𝒪)^×)`.
  - It is neat. An element of `1 + 3𝒪₃` has eigenvalues `≡ 1 mod 3`, and the only root of unity `ζ` with
    `v₃(ζ − 1) ≥ 1` is `ζ = 1`, since `v₃(ζ₃ − 1) = 1/2`.
  - It is allowed by Lan: `H ⊂ G(Ẑ^□)` and `3 ∉ □`.
- No cusps, because `B` is a division algebra. So Thm 5.3.3.1 gives properness.

**Flag for the reader:** check Lan's conditions for an integral PEL datum (Def. 1.2.1.3, 1.4.1.1-1.4.1.4; numbers
UNVERIFIED) at this datum, and the form of 5.3.3.1. The Kottwitz determinant condition is automatic, because
`𝒪 ⊗ ℤ_p ≅ M₂(ℤ_p)` and every `M₂(𝒪_S)`-module that is locally free of rank 2 is `𝒪_S² ⊗ (line bundle)` (STANDARD).

### 3.2 Derivation (paper; every step listed)

Let `(𝒴, (A, λ, i, α₃))` be Lan's `M_H` with its universal object. Set `𝒜 := (A, i, η)` with `η(a) := α₃(a mod 3)`;
it is a `QMAbScheme` over `𝒴`:
- `η` is `𝒪`-linear and kills `3𝒪`;
- `η` is injective mod 3 on every field point, because `α₃` is an isomorphism `(𝒪/3)_𝒴 ≅ A[3]` and 3 is invertible;
- the group law and identity are those of `A`.

Properness and smoothness of relative dimension 1 come from Lan.

**Clause 1 (`Spec ℚ̄`).** Let `𝒜' = (A', ι', η')` be an object over `ℚ̄`. Lan's functor at `S = Spec ℚ̄` needs four
facts:
1. `(A', ι')` has exactly one principal polarization `λ'` of type `†`. This is **Lemma P over `ℚ̄`**: rv-qm-polar
   §0, characteristic 0. Its lattice steps are compiled there: `eq_smul_E0`, `eq_pm_E0_of_principal`,
   `lemmaP_lattice`.
2. `η'` defines an `𝒪`-linear bijection `𝒪/3𝒪 → A'[3](ℚ̄)`. Both sides have 81 elements, and `η'` is injective
   mod 3.
3. That bijection is a similitude for `e^{λ'}`, with some `ν`:
   - The Weil pairing on `T₃A'` is, over `ℂ ⊇ ℚ̄`, the Riemann form on `H₁ ≅ 𝒪`. That form is a `†`-compatible,
     alternating, unimodular form, hence `±E₀` (`eq_pm_E0_of_principal`).
   - So one `𝒪`-linear similitude exists.
   - Every other `𝒪`-linear isomorphism differs from it by `r_w`, `w ∈ (𝒪/3)^×`. Since
     `E₀(xw, yw) = nrd(w) E₀(x, y)` (`E0_rightMul`, compiled), each is a similitude too.
4. The determinant condition holds over a field of characteristic 0.

So `(A', λ', ι', α₃')` is a point of `M_H(ℚ̄)`, classified by a unique `y`. The pullback isomorphism forgets to
`QMFamFibre 𝒜 y 𝒜'`, which gives existence.

Uniqueness: suppose `QMFamFibre 𝒜 y 𝒜'` and `QMFamFibre 𝒜 y' 𝒜'`.
- The composite `y*𝒜 ≅ y'*𝒜` respects `ι`, `η` and the identity `η(0)`. So it is an isomorphism of abelian
  varieties (rigidity over a field).
- It carries the type-`†` principal polarization of one side to that of the other, by the uniqueness half of Lemma P
  over `ℚ̄`.
- It is therefore an isomorphism of PEL objects, and `y = y'`.

**Clauses 2–3 (`S = 𝒴`, Hecke).** Define, on PEL objects over every locally noetherian `ℤ_(p)`-scheme:

- `T_α(A, λ, i, α₃) := (A, λ ∘ i(ε v_α), i ∘ α, α₃ ∘ α)`, where `α(μ) = μ v_α` and `ε = sign trd v_α`;
- `T_u(A, λ, i, α₃) := (A, λ, i, α₃ ∘ r_u)`.

These are again PEL objects of the same datum, and every check is an identity in `B`:
- `v_α ∈ 𝒪`, `nrd v_α = 1` and `v_α† = v_α` (rv-qm-polar `twist_type`, compiled). So `λ ∘ i(εv_α)` is a principal,
  symmetric isogeny.
- `trd v_α ≠ 0` (`trd_ne_zero_of_dag`, compiled), so `ε` is defined.
- `λ ∘ i(εv_α)` is positive by the criterion "`λ ∘ φ` is a polarization iff `φ` is `λ`-symmetric and totally
  positive" (STANDARD: Mumford, *Abelian varieties* §21; Milne 1986 §17; numbers UNVERIFIED). The eigenvalues of
  `i(εv)` are those of `x² − ε trd(v) x + 1`, so it is totally positive exactly when `ε trd v > 0`. This condition is
  intrinsic and independent of the fibre.
- The Rosati involution of `λ ∘ i(εv_α)` on `i ∘ α` is `†`: `rosati_twist`, compiled.
- `α₃ ∘ α` is a similitude for `e^{λ i(εv)}` with factor `±1`: `E0_twist`, compiled.
- `α₃ ∘ r_u` is a similitude for `e^λ` with factor `nrd u = ±1`: `E0_rightMul`, compiled.
- `r_u` normalizes `U^p(3)`, which is a principal congruence subgroup.

`T_{α⁻¹} ∘ T_α = id` holds on the nose. The polarization picks up `i(εε' v_α α(v_{α⁻¹})) = i(εε')` with
`v_α α(v_{α⁻¹}) = 1` (`twist_cocycle`, compiled), and positivity gives `εε' = 1`. Likewise `T_{u⁻¹} ∘ T_u = id`.

By Yoneda, `T_α` and `T_u` are induced by automorphisms `g` of `𝒴` over `ℤ_(p)`, with `T(universal) ≅ g*(universal)`.
Forgetting `λ` gives clauses 2 and 3. Note that `T_α(universal)` forgets to `twistAb 𝒜 α` and `T_u` to
`rightMulAb 𝒜 u`.

**No relative Lemma P anywhere.** Polarizations over a base are only ever transported along explicit formulas.
Existence and uniqueness of polarizations are used only over `ℚ̄`. The step from Kottwitz's isogeny classes to integral
objects is avoided by citing Lan's integral form (Lan does that comparison in §1.4.3).

### 3.3 Compiled algebra (`scratch/sir-printed/TwistAlgebra.lean`, imports rv-qm-polar; standard axioms; VERIFIED)

| lemma | statement |
|---|---|
| `trd_map`, `star_map` | every ring automorphism `α` of `𝒪` preserves `trd` and commutes with `x ↦ x̄` |
| `v_mu_v` | `α(μ) = μv ⇒ vμv = μ` |
| `rosati_twist` | `(α b)† · v = v · α(b†)` |
| `E0_twist` | `E₀(αx, v·αy) = E₀(x, y)` |
| `trd_ne_zero_of_dag` | `v† = v`, `nrd v = 1 ⇒ trd v ≠ 0` |
| `E0_rightMul` | `E₀(xu, yu) = nrd(u)·E₀(x, y)` |
| `twist_cocycle` | `α(μ) = μv`, `α⁻¹(μ) = μv' ⇒ v·α(v') = 1` |

## 4. Steps (a) and (b) of the review

**(a) Relative Lemma P.** Statement: over every locally noetherian `ℤ_(p)`-scheme, a QM abelian surface has exactly one
principal polarization of type `†`.

- *Not needed* for the field's consumer (§3.2).
- *Not statable* in Lean today (§6).
- *Truth:* TRUE, as far as this task can tell.
  - It is published in this form (Boutot–Carayol, Astérisque 196–197 (1991), Ch. III §1; it is also used in
    Kudla–Rapoport–Yang's book on Shimura curves, §3; locators UNVERIFIED).
  - SPECULATIVE sketch of uniqueness. Two such polarizations differ by an `𝒪`-linear automorphism `u` that is
    symmetric for the Rosati involution. On every geometric fibre, the commutant of `𝒪` with its induced positive
    involution is one of three things:
    - `ℤ`;
    - an imaginary quadratic order with complex conjugation;
    - in supersingular characteristic-`p` fibres, an order in the definite quaternion algebra ramified at
      `{2, 3, p, ∞}`. Here the only positive involution is the canonical one, whose symmetric elements are `ℚ`.

    So `u = 1` on fibres, and `u = 1` by rigidity.
  - SPECULATIVE sketch of existence. The locus where the polarization exists is a monomorphism, unramified and
    surjective over `S` (by the fibres). It is formally étale by Grothendieck–Messing: the Hodge filtration
    `L ⊕ L ⊂ W ⊕ W` (Morita, `p ∤ 6`) is automatically isotropic. An étale monomorphism that is surjective is an
    isomorphism.

**(b) Comparison of rational and integral level structures.**

- Kottwitz's `K^p`-orbits of `V ⊗ 𝔸_f^p ≅ H₁(A, 𝔸_f^p)`, on prime-to-`p` isogeny classes, are compared with
  integral structures in Lan §1.4.3. The new leaf cites Lan's integral form, so this comparison is the printed one.
- What remains is the comparison of Lan's symplectic `α₃` with the kernel's `η`, and it is needed only over `ℚ̄`
  (§3.2, clause 1). On the PEL side over `𝒴`, `η` is defined from `α₃`, which is the easy direction.
- *Truth:* TRUE (§3.2).

**Level at `3 | D`.** Allowed by Lan (`H ⊂ G(Ẑ^p)`, `□ = {p}`) and by Kottwitz (only `K_p` hyperspecial) (STANDARD,
locators UNVERIFIED). Whether Buzzard's and Morita's printed level structures allow it remains unread. The new leaf
does not cite them as primary sources.

**False cases.**
- At `p = 2, 3`, i.e. `p | D`, there is no smooth proper model: the Shimura curve has Čerednik–Drinfeld bad
  reduction there (STANDARD; Boutot–Carayol 1991). Neither the old field nor the new leaf asserts anything at
  `p ≤ 324`.
- The full level `U^p(3)` is neat, so the moduli problem is fine. Level 1 would not be neat: `−1` is an
  automorphism.

## 5. Not vacuous, not stronger

- `shimuraIntegralModelUsed_of_rep` (compiled) shows the new leaf is a specialization of the field.
- The paper derivation of §3.2 shows it is a consequence of Lan's theorem and Lemma P over `ℚ̄`.
- Its quantifiers range over genuine `QMAbScheme`s, which have a group law, an `𝒪`-action and level data. It
  asserts that an object exists, and objects over `ℚ̄` exist: the CM objects of `R1R2fp`, via sgr-split's
  `qml3AsQMAb_of`.

## 6. What Lean has and lacks for the PEL functor (VERIFIED by grep of Mathlib v4.35 and the kernel)

**Has:**
- the vendored Jacobian-Challenge relative Picard presheaf `AlgebraicGeometry.picardPresheaf` and its rigidified
  form `picardFunctorNormalized` (along a section, over any base);
- `Scheme.Pic` and invertible modules;
- t09-pic's field-level `T09Pic` definitions: `mumfordBundle`, `phiL`, `IsPicZero`, `IsAmple`, `IsVeryAmple`,
  `weilScalar` (Mumford's `ē_n`), and the leaves L1–L4 over a field.

**Lacks over a base `S`:**
- representability of `Pic_{A/S}` for an abelian scheme, i.e. the dual abelian scheme `A^∨` (Raynaud /
  Faltings–Chai I.1.9);
- ampleness relative to `S` and polarizations `λ : A → A^∨` (GIT Def. 6.3);
- the Weil pairing `e^λ_n` on `A[n]`, which needs Cartier duality `A[n]^∨ ≅ A^∨[n]`;
- for Kottwitz's form also: the prime-to-`p` isogeny category and Tate-module local systems.

A PEL statement could be imitated with a rigidified class on `A ×_S A` standing for `λ` and with `𝒪`-linear
(non-symplectic) level structures. That object would not be the printed functor: its level structures are weaker, so
its moduli problem has potentially more objects. It would also need the same paper glue. This task does not build it.

## 7. Lean deliverables and checks (all VERIFIED: compiled)

- `ZInQKernel/Contrib/OneProof/ShimuraIntegralModelUsed.lean`:
  - imports `ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard` (the module defining the field's
    statement, never `Main`);
  - namespace `SIRPrinted`;
  - defines `ShimuraIntegralModelUsedAt` and `ShimuraIntegralModelUsed`;
  - proves `hecke_iso_of_rep`, `shimuraIntegralModelUsed_of_rep`, `shimuraGoodReductionNoGuard_of_used_glue` and
    `shimuraGoodReductionNoGuard_of_used`.
  - `lake build ZInQKernel.Contrib.OneProof.ShimuraIntegralModelUsed`: 88 s.
  - `#print axioms` (`scratch/sir-printed/Check.lean`): `propext, Classical.choice, Quot.sound` for both theorems.
  - The file has no code that runs at build time.
- `#discharges` (`scratch/sir-printed/Discharges.lean`, output `Discharges-output.txt`): "63 open hypotheses, 1620
  theorems checked, 5 discharge one". None of the five is from this file. This is expected: the new theorems prove
  `ShimuraGoodReductionNoGuard`, which is no longer an open hypothesis. The open field `ShimuraIntegralModelRep` is
  stronger than the new leaf.
- Bypass fold dry run (`scratch/sir-printed/BypassFold.lean`, output `BypassFold-output.txt`):
  - It builds `OpenAddedLeaves18` (= `OpenAddedLeaves17` with `shimuraIntegralModelRep` replaced by
    `shimuraIntegralModelUsed`).
  - `openAddedLeaves16_of_OpenAddedLeaves18` sets
    `shimuraGoodReductionNoGuard := SIRPrinted.shimuraGoodReductionNoGuard_of_used n.shimuraIntegralModelUsed`.
  - `sixContactMin_of_open29 r t l g := sixContactMin_of_open27 (openResearchLeaves20_of_OpenResearchLeaves21 r t)
    t (openAddedLeaves16_of_OpenAddedLeaves18 l) g`.
  - A copy of `frozenTarget` on `l : OpenAddedLeaves18` is included.
  - Both `sixContactMin_of_open29` and `frozenTargetBypass` print the standard axioms only.
- `scratch/sir-printed/autofold.json` gives:
  - the leaf row: kind `published`, flag `pending reading: Lan 2013 Thm 1.4.1.11 and Thm 5.3.3.1 at box = {p}, …`,
    source, doc;
  - the bypass instructions (`bypass_note`, `bypass`), since `autofold.py` cannot express a weaker-leaf fold.
- On newer mains (for example leaf-fold25 `bc90deac`), `OpenAddedLeaves17` is still the added bundle and
  `shimuraIntegralModelRep` is unchanged. The same bypass applies, with the top theorem composed from the then-current
  research map.

**Proposed docs/research/locators.md row** (not edited here: it is a shared file):
`shimuraIntegralModelUsed | Lan, Arithmetic compactifications of PEL-type Shimura varieties (LMS Monographs 36, 2013),
Thm 1.4.1.11 (representability, neat H, □ = {p}), Thm 5.3.3.1 (properness without cusps), §1.4.3 (Kottwitz 1992 §5) |
unread; numbers from the review cove-bc, UNVERIFIED`.

## 8. What remains

- A reading of Lan 1.4.1.11 / 5.3.3.1 / 1.4.3 for the datum of §3.1. It would clear the flag, and the leaf would then
  count LEAF.
- The integrator's hand fold (§7).
- The full field `ShimuraIntegralModelRep`, with every locally noetherian base, stays a consequence that would need
  the relative Lemma P (true, published, §4) and polarizations over a base. Nothing in the proof needs it once the
  bypass fold is in.
