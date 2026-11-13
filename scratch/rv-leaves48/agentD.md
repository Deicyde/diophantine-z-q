# rv-leaves48, agent D: R19, R20, R21, H5 (height part), R16, T33, T34

Read only, no Lean run. Line numbers refer to `scratch/h-decomposition/Leaves.lean` at 01267822.
Tags: VERIFIED means read in this file and checked by hand. STANDARD means textbook mathematics,
not re-proved here. SPECULATIVE means my own judgement. UNVERIFIED marks theorem numbers recalled
from memory or taken from locators.md without my reading the source.

## 1. Verdict table (worst first)

| leaf | verdict | reason |
| --- | --- | --- |
| r20 `R20_FaltingsLemma5` (18565) | **OK** (source unread) | `\|h(A)−h(B)\| ≤ ½ log deg φ` is the standard consequence of Faltings' Lemma 5, `h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω_G`, with `0 ≤ [K:ℚ]⁻¹ log #s*Ω_G ≤ log deg φ` (STANDARD; it is tight for `E → E/μ_p` and `E → E/(ℤ/p)`). The stable form follows by base change to a common semistable field, which keeps the degree. The height enters only through reals `x`, `y` with `h = x`, `h = y`, so junk `⊤` cannot falsify it. The locator (Lemma 5 itself) is still UNVERIFIED (locators.md row R20). |
| r19 `R19_GaudronRemond` (18555) | **OK**, given the locator | `κ`, `α(g)=1024g³`, both directions bounded by `κ(A)`, `k = K`, original Faltings normalization: this matches locators.md row R19 (read by the audit; I did not read GR). `κ` is monotone in `h`, so the leaf is a consequence only if GR's `h` is Faltings' original normalization (rv-blueprints F4). rv-leaves-a reads GR's Bost constant as `−log(π√2)g`, which is the Faltings-normalized form, so that condition holds. The height enters through `h = ↑x`, never through `toReal` (18555-18560, VERIFIED). |
| r21 `R21_Bost` (18572) | **OK** | `h_D ≥ −(g/2)log 2π` (Bost, UNVERIFIED display) gives `h_F = h_D − (g/2)log π ≥ −g·log(π√2) ≈ −1.4913g ≥ −1.5g`. The Deligne reading is forced: under the Faltings reading `y²=x³+1` (`h_F = −1.3211`) would violate it. Trivially true when `h = ⊤`. |
| H5 height part `StableHeightFinite`, `NeronModelMinimal` (18767, defs 18325-18340) | **OK; it carries all the vacuity risk** | Both are true for the definition at 18110 (STANDARD; §2). `StableHeightFinite` says exactly that the index set of the infimum is nonempty for every `A` over a number field (probe P3). So if the encoding were broken, H5 would be **false**, not junk-true, and the bundle `ResearchLeaves` would be inconsistent. That is the right direction of failure for a leaf. `NeronModelMinimal` is true, and trivially true when a model has no metrization. |
| r16 `R16_EichlerShimuraJ1'` (16348) | **OK** | It is a consequence of Shimura 1973 Thm 1 (unconditional clauses only), rank 2 over `K_f⊗ℚ_ℓ`, and the char-poly form of Eichler–Shimura (Diamond–Shurman 9.5.4, UNVERIFIED number). The conventions check out (§3.1): arithmetic Frobenius (`GlueC10.IsFrobAt` at 11391; `galAct` at 2646 is σ on coordinates), covariant `V_ℓ` (2659), and the transpose action on eigenfunctionals keeps trace and det. The `ā_p`/`χ̄(p)` convention is absorbed by `∃ θ` (use `θ∘c`). Degenerate models cannot refute it (§3.2). It is vacuous without `X1ModelExists`, which no bundle contains (§3.3, INFO). |
| t34 `DimJ1Genus` (16373) | **OK** | The genus formula is right for `±Γ₁(N)`, and a fixed point of `S` (resp. `ST`) is a fixed point of its inverse because `−1 ∈ ±Γ`. The cusps are the `⟨T⟩`-orbits on the left cosets (VERIFIED, 15717-15736). The junk `Nat.card ∞ = 0` cannot occur, since `0 < N` and the index is finite. `IsJ1` pins `J` up to isomorphism, so no degenerate `J` exists. Same INFO caveat as R16. |
| t33 `JacobianExists ℚ` (16157) | **OK** | Weil–Chow with the Albanese property of the pointed Jacobian (Milne 1986 Prop. 6.1, UNVERIFIED number). A trivial `J` can satisfy `IsJacobian` only in genus 0, where it is the right answer: `univ` would force every pointed map to every abelian variety to be constant (§3.2). |

No OVER-STRONG, VACUOUS or MISSTATED finding. One wording issue (§2.4) and one usage risk (§3.3).

## 2. `stableFaltingsHeight` (18110): what can go wrong, exactly

### 2.1 The only possible junk value is `⊤`

`stableFaltingsHeight A = ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), ↑M.hodge.modelHeight`
in `EReal` (18110). There are two cases.

- **Index empty.** Then the value is `⊤` (probe P1 proves the iff).
- **Index nonempty.** Every element is a genuine model height (below), so the infimum is
  `≥ h_st(A) > ⊥`.

A real-valued junk such as "0 for every `A`" **cannot occur**. Every field that could carry junk
is pinned (VERIFIED by reading; the truth of each pin is STANDARD):

- **`lattice`.** It equals `detLattice g = ⋀^g ω_𝒢` (18089).
  - `omegaAt s` is the `𝓞_L`-span of the image of `I_{e(s)} = ker(𝒪_{𝒢,e(s)} → 𝒪_{S,s})` in
    `𝔪_ξ/𝔪_ξ²` (17912).
  - Check on `𝔾_a/𝓞_L`: the image at `𝔭` is `𝓞_{L,𝔭}·dt`, and the intersection is `𝓞_L·dt`.
  - In general `I_ξ = 𝔪_ξ` and `I_x/I_x²` is free, so `omega` is `Γ(S, e*Ω¹)`.
  - `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} V ≅ ⋀^g_L V` for an `L`-space `V` (base change of the exterior algebra).
    So `finrank_eq_one` forces `g = dim A`. The case `g = 0` is killed by surjectivity of `Φ` when
    `dim A ≥ 1`.
- **`periods τ`.** It is `ker Φ`, through the `↔` clause of `IsAnalyticUniformization` (18011).
- **`Φ` itself.** Regular functions are holomorphic along `Φ`, and affine charts are cut out by
  regular functions, so `Φ` is holomorphic.
  - It is a surjective homomorphism with full-lattice kernel. Hence `ℂ^g/Λ → A_τ(ℂ)` is a
    continuous bijection from a compact space to a Hausdorff one, and so biholomorphic.
  - So `Λ` is the true period lattice in the coordinates `z`.
  - The archimedean part of repair 6 in rv-blueprints §1.5 is therefore implemented.
- **`coeff τ`.** It is fixed on the wedges by `jacDet` (18032), and the wedges span
  (`semilinear_ext_wedge`, proved).
  - `jacDet` is independent of the chosen representative because `Φ 0 = 1` lies over `ξ` and
    `dom Φ U` is open.
  - It is `τ`-linear in the germs and vanishes on `𝔪_ξ²`, so a compatible `coeff` exists for the
    true uniformization.
  - A change `Φ ↦ Φ∘T` is absorbed by `modelHeight_recoord` (given `AnalyticUniformizationUnique`).
- **Metric.** `torusMetricSq = |c|²·covol(Λ)`, Lebesgue on `ℂ^g`, which is `(i/2)^g ∫η∧η̄`
  (Faltings). The sum runs over all `σ : L → ℂ` with `log ‖·‖`, not `log ‖·‖²`, so the degree is
  the standard one.
- **Arithmetic junk.** `secIndex` (16736) can be `0` (`Nat.card` of an infinite index), but
  `arakelovDegree` uses the `isLattice` witness with `secIndex ≠ 0`, and `norm_pos` holds. So there
  is no `log 0`.

Hence each index element has `modelHeight = h(A_L, 𝒢)`. By the Néron mapping property
`𝒢 → 𝒩_L`, we get `ω_𝒩 ⊆ ω_𝒢` and so `h(𝒢) ≥ h(𝒩_L) ≥ h_st(A)`, with equality at a semistable `L`
(STANDARD; BLR 1.2/1, SGA 7 IX 3.3, UNVERIFIED locators). So the value is **either `⊤` or the true
stable Faltings height in Faltings' normalization**. This agrees with rv-blueprints §1.1, which I
re-derived independently.

Mathematically the index set is nonempty for every `A/K` with `K` a number field: the Néron model
over a semistable `L` with its true uniformizations is an element. The value of a classical Lean
definition is fixed by mathematics. So "AN3 open" means *not yet proved* `≠ ⊤`. It does not mean
the value is undetermined or could be junk. def-faltings.md §5 says the leaves "become
non-vacuous exactly when the gaps are closed"; strictly, they *are known to be* non-vacuous then.

### 2.2 Effect of the `⊤` scenario on each leaf (VERIFIED from the statements; probes P1-P3)

| leaf | if `stableFaltingsHeight A = ⊤` | if `stableFaltingsHeight ≡ 0` (the brief's hypothetical; impossible, §2.1) |
| --- | --- | --- |
| R19 | the instance at `A` is vacuous: the hypothesis `h A = ↑x` is false (P2) | the instance becomes `κ(g,d,0)`, which is **stronger** than GR (`κ` is monotone). Not known false; e.g. `g=1, d=1` holds by Mazur–Kenku |
| R20 | vacuous unless both heights are real | trivially true (`0 ≤ ½ log deg`, `deg ≥ 1`) |
| R21 | trivially true (`↑r ≤ ⊤`, P2) | true (`0 ≥ −3g/2`) |
| H5 `StableHeightFinite` | **false** | true |
| H5 `NeronModelMinimal` | `GroupModel.height = ⊤` for unmetrizable models; true | — |

So no leaf in R19-R21 can become false through junk. R20 could fail only for non-constant,
inconsistent real values, and §2.1 excludes those. The risk lies entirely in H5: a broken encoding
would make the bundle unsatisfiable, and every theorem proved from `ResearchLeaves` vacuous. §2.1
is my evidence that the encoding is not broken (STANDARD, with SPECULATIVE confidence that no
Lean-level instance mismatch hides in `HodgeData L g (hodgeSpace g)`; the lattice and module
instances are found by the same search in `lattice_eq`, so they agree).

### 2.3 Checks of the remaining R19/R20 vocabulary (VERIFIED)

- `IsIsogeny` (18538) is `IsMonHom ∧ IsFinite ∧ Surjective`. It is a `K`-morphism of
  `Over (Spec K)`, as in GR ("isogénie sur k").
- `isogDeg` (18542) is `Nat.card` of the `K̄`-points of the kernel. It is finite and `≥ 1`, and it
  equals `deg φ` in characteristic 0. The `log` and `Nat.card` junk are harmless.
- `grKappa` (18546) at `g = 0` is `1`, which is correct for the trivial variety.
- `A.dim` is `topologicalKrullDim`. It is finite for an `AbVar`.

### 2.4 Wording repair (docstring only)

In the bundle at 19182, replace "(not yet known non-vacuous: AN3 open)" by:

> R19-R21 over def-faltings' `stableFaltingsHeight`. They are true for the definition (its value is
> `⊤` or the stable Faltings height, def §2.1). They are informative only together with
> `h5.1` (`StableHeightFinite`), which is where an encoding error would show, as a false leaf.

## 3. Modular-curve leaves

### 3.1 R16 conventions (VERIFIED for the Lean side; the source side is STANDARD/UNVERIFIED)

- `IsFrobAt g p` (11391) says `g x ≡ x^p mod 𝔓`. That is **arithmetic** Frobenius.
- `galAct σ P = galHom σ ≫ P` (2646) applies `σ` to coordinates, and it is a left action
  (`galHom_mul`).
- `V_ℓ = ℚ_ℓ ⊗ lim A(K̄)[ℓⁿ]` (2659-2662) is covariant.
- `eigenFun` (16212) consists of the `ι`-eigenfunctionals. `frobOn σ = (· ∘ ρ(σ))` is the transpose
  of `σ` on the `ι`-component, with the same trace and determinant.
- Arithmetic Frobenius on covariant `V_ℓ(A_f)` has characteristic polynomial
  `X² − a_pX + χ(p)p` (Diamond–Shurman 9.5.4; Shimura 1971 7.11; UNVERIFIED numbers).
- Under the other Hecke convention the trace is `ι(ā_p)` and the det is `ι(χ̄(p))p`. Then
  `θ' = θ∘c` works:
  - `eigenFun(θ∘c, ι) = eigenFun(θ, ι∘c)`;
  - so `tr = (ι∘c)(ā_p) = ι(a_p)` and `det = ι(χ(p))p`.
  - `c` preserves `K_f` because `K_f` is totally real or CM (STANDARD).
  - The witness `θ` is uniform in `ℓ`, so one `θ` serves every `ℓ`.
- `IsNewform` (16031) is a newform:
  - The coefficient relations with `χ(d) = 0` for `(d, N) > 1` say `T_n f = a_n f` for all `n`.
  - Strong multiplicity one: a `T_n`-eigenform (`(n, N) = 1`) in `S_2(Γ₁(N))` outside the old
    space is a multiple of a newform, and `a_1 = 1` normalizes it.
  - So R16 is not stronger than published on that side (STANDARD).
- The Shimura 1973 Fricke/`Γ₀` condition attaches only to the zeta clause, which is not used
  (rv-loc-leaves §(j); the docstring at 16320-16347 says so).

### 3.2 Can the `Jacobian`/`IsJ1` predicates be degenerate? No

- **Trivial `J`.** `IsJacobian X P₀ 0 aj` forces every pointed `f : X → A` to equal
  `aj ≫ φ = η`, i.e. to be constant. For genus `≥ 1` the true Abel–Jacobi map is a
  counterexample, so the trivial group satisfies the predicate only in genus 0, where it is the
  Jacobian. So `∃`-forms are not trivialised. Because `∃!` is used, `IsJacobian.unique` (proved)
  gives uniqueness up to unique isomorphism.
- **Degenerate models.**
  - `IsX1Model` (16131) requires smooth, proper, relative dimension 1, geometrically connected,
    integral, with function field `≃+* K_N`. A ring isomorphism in characteristic 0 is
    `ℚ`-linear.
  - So every model is `ℚ`-isomorphic to `X₁(N)`, because a smooth projective curve is determined
    by its function field (STANDARD).
  - `K_N = ℚ(j)(x(P))` with `ord P = N` is the fixed field of `{g : gP = ±P}`, whose determinant
    is surjective. So `ℚ` is algebraically closed in `K_N`, and the model is geometrically
    connected.
  - At `N = 1`, `P = 0`, `x(0) = 0` (junk), and `K_1 = ℚ(j)`, which is correct.
  - Hence `J.dim`, the quotient `A_f` and the Frobenius data are invariant under the choices, and
    the `∀ J, IsJ1 N J → …` forms cannot be refuted by a degenerate model.

### 3.3 INFO (usage risk, not a leaf defect)

R16 and T34 quantify `∀ J, IsJ1 N J → …`. `IsJ1` is inhabited only given `X1ModelExists` (16419;
the docstring says so). `X1ModelExists` is in `ModCurveLeaves` (16424) but **in neither
`ResearchLeaves` nor `TextbookLeaves`** (19109-19200; grep: it occurs only at 16130, 16419-16431).
Whoever consumes r16/t34 must prove it as glue (MC4 + MC10) or add it as a leaf (Shimura's
canonical model with a rational cusp). Otherwise `exists_J1` cannot fire, and E1/E2/C9 get nothing
from r16/t33/t34.

## 4. Lean probes (append to a copy of Leaves.lean; Mathlib + existing names only)

P1 settles that the only junk value is `⊤` exactly when the index is empty. P2 settles that `⊤`
makes R19/R20 hypotheses false and R21 true at that `A`. P3 settles that H5 forces the index set
to be nonempty for every `A`, so H5 is false if the encoding is broken.

```lean
namespace RvLeaves48D

/-- P1: the stable height is `⊤` iff `A` has no metrized model at all. -/
theorem sfh_eq_top_iff {K : Type} [Field K] (A : ZInQ.DefFaltings.AbVar K) :
    ZInQ.DefFaltings.stableFaltingsHeight A = ⊤ ↔
      ∀ (E : ZInQ.DefFaltings.FinExt K) (g : ℕ),
        IsEmpty (ZInQ.DefFaltings.MetrizedModel A E.L g) := by
  constructor
  · intro h E g
    refine ⟨fun M => ?_⟩
    have h1 := ZInQ.DefFaltings.stableFaltingsHeight_le A M
    rw [h] at h1
    exact EReal.coe_ne_top _ (top_le_iff.mp h1)
  · intro h
    exact top_le_iff.mp (ZInQ.DefFaltings.le_stableFaltingsHeight A fun E g M => by
      haveI := h E g
      exact isEmptyElim M)

/-- P2a: with no metrized model, R21's inequality at `A` holds outright. -/
theorem r21_trivial_of_empty {K : Type} [Field K] (A : ZInQ.DefFaltings.AbVar K)
    (h : ∀ (E : ZInQ.DefFaltings.FinExt K) (g : ℕ),
      IsEmpty (ZInQ.DefFaltings.MetrizedModel A E.L g)) (g : ℕ) :
    ((-(3 / 2) * g : ℝ) : EReal) ≤ ZInQ.DefFaltings.stableFaltingsHeight A := by
  rw [(sfh_eq_top_iff A).2 h]
  exact le_top

/-- P2b: with no metrized model, the hypothesis `h(A) = x` of R19/R20 is never met. -/
theorem r19r20_hyp_false_of_empty {K : Type} [Field K] (A : ZInQ.DefFaltings.AbVar K)
    (h : ∀ (E : ZInQ.DefFaltings.FinExt K) (g : ℕ),
      IsEmpty (ZInQ.DefFaltings.MetrizedModel A E.L g)) (x : ℝ) :
    ZInQ.DefFaltings.stableFaltingsHeight A ≠ (x : EReal) := by
  rw [(sfh_eq_top_iff A).2 h]
  exact (EReal.coe_ne_top x).symm

/-- P3: H5 forces a metrized model of every `A` over a number field, so H5 is exactly where a
broken encoding would surface (as a false leaf, not as junk). -/
theorem H5_forces_metrized_model (h5 : LeafAdopt.H5) {K : Type} [Field K] [NumberField K]
    (A : ZInQ.DefFaltings.AbVar K) :
    ∃ (E : ZInQ.DefFaltings.FinExt K) (g : ℕ),
      Nonempty (ZInQ.DefFaltings.MetrizedModel A E.L g) := by
  refine Classical.byContradiction fun hne => (h5.1 K A).1 ((sfh_eq_top_iff A).2 fun E g => ?_)
  exact not_nonempty_iff.mp fun hM => hne ⟨E, g, hM⟩

/-- P3': under H5 the hypothesis of R19 is satisfiable for every `A`. -/
theorem r19_hyp_satisfiable (h5 : LeafAdopt.H5) {K : Type} [Field K] [NumberField K]
    (A : ZInQ.DefFaltings.AbVar K) : ∃ x : ℝ, ZInQ.DefFaltings.stableFaltingsHeight A = x :=
  ⟨(ZInQ.DefFaltings.stableFaltingsHeight A).toReal,
    (EReal.coe_toReal (h5.1 K A).1 (h5.1 K A).2).symm⟩

end RvLeaves48D
```

Compile notes:

- `stableFaltingsHeight_le` and `le_stableFaltingsHeight` take `A` explicitly (section variable
  `(A : AbVar K)`, 18120).
- `FinExt`'s instances are global attributes, so `MetrizedModel A E.L g` elaborates.
- If `isEmptyElim` complains about the motive, use `exact (IsEmpty.false (self := h E g) M).elim`.

No probe can build a non-vacuity *witness*, i.e. a `MetrizedModel`, today. That needs Néron models
and AN3, and it is exactly H5/AN3.

## 5. Not checked

- The GR, Faltings, Bost, Shimura, Diamond–Shurman and Milne sources themselves (all theorem
  numbers UNVERIFIED by me).
- The H5 parts other than the height (the lead covers them).
- The `AbVar` copy identification `abVarEquiv` beyond reading it (18793; `rfl` both ways).
