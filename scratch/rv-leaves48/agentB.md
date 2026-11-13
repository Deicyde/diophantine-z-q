# rv-leaves48, agent B: adversarial review of 14 leaves (I4 / HSyn §1 / I1)

Read-only review. No Lean process was run. Line numbers refer to
`scratch/h-decomposition/Leaves.lean` at 01267822. Each claim is tagged VERIFIED (I read it in
Leaves.lean or in Mathlib under `.lake/packages/mathlib`), STANDARD (textbook mathematics), or
SPECULATIVE. Theorem numbers I give from memory are UNVERIFIED.

## Verdict table (worst first)

No leaf in this cluster is OVER-STRONG, VACUOUS or MISSTATED. All 14 are OK. The first four
rows carry the largest residual risk, because they sit on new, unproved infrastructure
(`B_dR`, Hodge–Tate multiplicities). For those rows the risk is a definitional one, and I checked
it by reading the definitions (see §2).

| leaf (bundle field) | Lean name, def line | verdict | reason |
|---|---|---|---|
| r11r12 | `PkgI4.PanBerger` 4616 (`PanFor` 4596) | OK (consequence) | `5 ≤ p` binder, so Pan's p=3 exception never applies. Hypotheses match Pan arXiv v2 Thm 1.0.4 as quoted in h-a011 §1.1, with "de Rham" in place of "pst" (Berger). The conclusion is existential in `g, χ, ψ, ιC, ιL, S`, so either Frobenius normalization gives it. `LocalIsDeRham`/`DistinctHTWeights` are genuine (§2) |
| r10 | `PkgI4.DeRhamComparison` 4510 | OK (consequence) | `IsDeRhamOver` (4407) is `dim_{Q_p} D_dR,F(V^∨) = [F:Q_p]·dim V`. `htMultOver` (4428) gives weights 0 and −1 with multiplicity g each, which is correct for `V_p(A)` with cyclotomic weight −1. `A.dim` is the Krull dimension of `|A|` (3749), and `T_p` is the genuine inverse limit (3628). Divisibility by `[F:Q_p]` holds because invariants are modules over `C_p^{G_F} = F′` |
| r13 | `PkgI4.EigenformHT` 4535 | OK (consequence) | Arithmetic-Frobenius trace `a_p` forces `det ρ = χ·ε^{k−1}`. With cyclotomic weight −1 the weights are `{0, 1−k}`. This matches R10 (k=2 gives {0,−1}). Valid at every level, including ℓ ∣ N |
| t23 | `PkgI4.T23_FontaineClosure` 4692 | OK (consequence; docstring says "Exact") | (i) holds formally even without continuity. (ii)–(v) carry `ContRep` on every input whose continuity is not implied, and the outputs are continuous automatically. Working on `V^∨` is harmless because of the dual clause |
| r14 | `HSyn.EigenformRepExists` 18933 | OK | Deligne (k≥2) and Deligne–Serre (k=1) give a representation for every ℓ, ιC, ιL. `a_p` is algebraic, so `α` exists. ρ_g is irreducible, hence semisimple. Continuity: Artin representations have open kernel |
| r15 | `HSyn.DeligneSerreConseq` 18942 | OK | Follows from DS Thm 4.1 + Chebotarev (density of Frobenius at p ∤ Nℓ, continuity of both traces) + Brauer–Nesbitt. `IsSemisimple` is present |
| t24 | `HSyn.EigenformTwist` 18951 | OK | Holds for **every** ψ mod m, including imprimitive ψ. See §3.1 |
| t25 | `PkgI4.NewformOfEigenform` 4564 | OK | `IsNewform` (4475) = eigenform ∉ old span. A genuine newform satisfies it because `S^new ∩ S^old = 0` and the form is nonzero. Atkin–Lehner–Li + strong multiplicity one give the newform |
| t18 | `HSyn.FrobeniusDense` 18910 | OK | Use Chebotarev on the fixed field of the normal core of U. Choose the place v so that `Frob_v|_L = σ|_L`. Then every arithmetic Frobenius τ at v has `τ⁻¹σ ∈ U`. Topology is Mathlib's `krullTopology` instance (VERIFIED, KrullTopology.lean:134) |
| t19 | `HSyn.BrauerNesbitt` 18917 | OK | Holds for any group G and any char-0 field E. The image algebra in `M_n × M_n` is semisimple (it has a faithful semisimple module), and in char 0 traces determine multiplicities (STANDARD) |
| t13 | `HSyn.SkolemNoether` 18886 | OK, exact | `IsSimpleRing B` includes nontriviality. Alpha-equivalent to `PkgI6.SkolemNoether` (4760) |
| t17 | `HSyn.KroneckerWeber` 18903 | OK, exact | |
| r4 | `PkgI1.ThetaModularity` 232 | OK | `thetaConst` is the standard θ[a,b]. Mathlib's `J = fromBlocks 0 (−1) 1 0` (VERIFIED SymplecticGroup.lean:59) gives the same group as the standard `J₀ = −J`, and `Sp` is closed under transpose. `κ⁸ = e(8φ_m) = 1`, so θ_m⁸ is permuted among the even characteristics. χ₁₀ has trivial character (STANDARD; also checked numerically by rv-leaves-a) |
| t28 | `PkgI1.IgusaClebschSeparation` 774 | OK | ⇒: `r = e²det⁶` (degrees 2, 4, 6, 10 and weight 3·deg in det). ⇐: the invariant ring is `[I2,I4,I6,I10,I15]` with `I15² ∈ [I2..I10]`. Choose `e = √r`, fix the sign of I15 with `e ↦ −e`, and stable orbits are closed. In char 0 the Lean J's are a weighted-triangular change of `I2..I10` (matched to PARI) |

## 1. Bundle field types (VERIFIED, lines 19109-19200, inside `namespace HSyn`, which ends at 19227)

- `r14 : EigenformRepExists`, `r15 : DeligneSerreConseq`, `t13 : SkolemNoether`, `t17`, `t18`,
  `t19` and `t24 : EigenformTwist` all resolve to the **HSyn** versions (18886-18956).
- `r10`, `r11r12`, `r13`, `t25` use the explicit `PkgI4.` names. `t23` is `∀ p [Fact p.Prime], PkgI4.T23_FontaineClosure p`.
- `r4` and `t28` use the explicit `PkgI1.` names.
- The HSyn and PkgI4 copies of `CF`, `coeff`, `HasNebentypus`, `IsNormalizedEigenform`,
  `EigenformTwist` and `EigenformRepExists` are textually identical (VERIFIED: 18850-18880 vs 4436-4462, 4520-4559).
  `HSyn.GaloisRep` and `PkgI4.GaloisRep`, however, are **distinct structures**. r14/r15 speak about
  `HSyn.GaloisRep`, while r13 and `PanFor` speak about `PkgI4.GaloisRep`. The (sorry'd) glue must
  transport between them. This affects glue only, not faithfulness. Probe P1 checks the field types.

## 2. Definitions under r10, r11r12, r13, t23 (the de Rham / Hodge–Tate stack)

The main risk for these four leaves is a defective definition, so I checked the stack link by link.

1. **`B_dR` (VERIFIED, Mathlib `RingTheory/Perfectoid/BDeRham.lean:62-92`).**
   - `BDeRhamPlus = AdicCompletion (ker θ[1/p]) (W(R♭)[1/p])`.
   - `BDeRham` localizes it at the closure of the images of all generators of `ker θ[1/p]`.
   - Leaves.lean `BdR` (4183) is `Localization (DR.genMonoid p 𝓞_ℂ_[p])`, the same submonoid (3591).
   - For `R = 𝓞_{C_p}`, `ker θ` is principal, generated by ξ (STANDARD). Localization is flat, so
     the generator set is nonempty, and `BdR = B_dR^+[1/ξ]` is the classical `B_dR`.
   - Caveat (SPECULATIVE failure mode, not present): if `ker θ[1/p]` had no single generator, `BdR`
     would collapse to `B_dR^+`. `IsDeRham` would then become strictly stronger: R10 and T23 would
     be false, while PanBerger would only get weaker (the safe direction).
   - The completeness instances for `𝓞_ℂ_[p]` (3316-3362) are genuine instances, and the PkgI4
     section has no `sorry` (VERIFIED, grep of 3224-4730).
2. **Galois action.**
   - `cpAct` extends σ to the completion. `oAct` restricts it to `𝓞`. `bdrAct` comes from proven
     naturality of θ (3398-3430) and `IsLocalization.map`.
   - `qpToBdR` is proved fixed (4278).
   - The `Algebra ℚ_[p] (BdR p)` instance (4293) is the only one in scope. `BDeRhamPlus` is a
     `def` and carries no competing instance.
3. **Cyclotomic character (VERIFIED, `NumberTheory/Cyclotomic/CyclotomicCharacter.lean:264-320`).**
   Mathlib's `cyclotomicCharacter` is the constant 1 **unless** L contains primitive p^i-th roots
   for all i. `PadicAlgCl p` is algebraically closed of characteristic 0, so `cyc` (4044) is
   genuine. Had it been trivial, R13's `{0, 1−k}` would be false: every `htMult w` would equal
   `dim H_0`.
4. **Hodge–Tate multiplicities.**
   - Definition: `htSpace ρ i = Hom_G(V, C_p(i))`, `htMult w = dim_{Q_p} H_{−w} / [E:Q_p]`.
   - H_i is an E-module (E acts on V by G-equivariant maps), so the ℕ-division is exact. H_i is
     finite-dimensional (the classical bound `dim (C_p ⊗ W)^G ≤ dim W`), so `finrank` is not a junk 0.
   - `htMult w = m_{V^∨}(−w)`, which equals `m_V(w) = dim_E (C_p(w) ⊗ V)^G` whenever the
     multiplicities sum to n. `HasHTWeights` forces that sum.
   - For E ⊊ Q̄_p: G permutes the factors of `C_p ⊗_{Q_p} E` transitively, so the E-dimension
     equals the HT multiplicity of V in the usual `K = Q_p` sense. Only K's embeddings label
     weights, and K = Q_p has one.
   - Convention: `htMult_cycRep_eq_zero` (4157, conditional on Tate) puts Q_p(1) at weight −1.
     This matches Pan (h-a011 §1.1, "HT weight of ε is −1"), R10's {0, −1} and R13's {0, 1−k}.
5. **`IsDeRham` (4321) / `IsDeRhamOver` (4407).**
   - They require `dim_{Q_p} D_dR(V^∨) = dim_{Q_p} V`.
   - `D_dR` is finite-dimensional, so there is no junk 0. The definition uses no continuity, but
     every leaf feeds it continuous representations: `ρE` is continuous because its image under the
     injective `algebraMap` is the continuous ρ.
6. **`decomp` / `gfToGqp`.**
   - Both use Mathlib's `Field.absoluteGaloisGroup.map`, a continuous hom `→ₜ*`
     (VERIFIED, AbsoluteGaloisGroup.lean:87).
   - For `gfToGqp`, `AlgebraicClosure ℚ_[p] → AlgebraicClosure F` is an isomorphism, so G_F is
     identified with `G_{F′}`, where F′ is the image of F.
   - `galRep` acts through the same `AlgebraicClosure F`, so the two actions are compatible.
7. **Abelian varieties (3728-3929).**
   - Proper, smooth, geometrically integral group object.
   - `galAct σ P = Spec(σ) ≫ P` is σ applied to coordinates, and `map_mul'` is proved.
   - `T` is the sequence model of `lim A(F̄)[pⁿ]`, and `V = Q_p ⊗ T` has dimension 2g (STANDARD).
   - R10's numbers: `Hom_G(V, C_p) = (H¹ ⊗ C_p)^G ≅ H¹(A, O) ⊗ F′` and
     `Hom_G(V, C_p(1)) ≅ H⁰(Ω¹) ⊗ F′`, each of F′-dimension g.

## 3. Details on points I checked independently

### 3.1 t24 EigenformTwist for imprimitive ψ (not covered by Shimura 3.64's primitive hypothesis)

- **Level.** Write `ψ(n) = Σ_a ĉ(a) e(an/m)` (finite Fourier series on ℤ/m), so `f_ψ = Σ_a ĉ(a) f|T_{a/m}`.
  For γ = [[α,β],[c,δ]] ∈ Γ₁(Nm²), `T_{a/m} γ T_{a/m}⁻¹` has entries `α + ac/m`, `δ − ac/m`, `c`
  and `β + a(δ−α)/m − a²c/m²`. All are integers with the Γ₁(N) congruences, so `f_ψ ∈ S_k(Γ₁(Nm²))`.
- **Nebentypus.** The same computation gives `χψ²` on Γ₀(Nm²), using `ψ(d²n) = ψ(d)²ψ(n)` (STANDARD).
- **Recursion.** The coefficient recursion of `IsNormalizedEigenform` holds for `g' = f_ψ`,
  `χ' = χψ²` (lifted to level Nm²) by a formal computation:
  - If `gcd(d, m) > 1` for some `d ∣ (m′, n′)`, then both sides vanish.
  - Otherwise `χ'(d)ψ(m′n′/d²) = χ(d)ψ(m′n′)`.
- So the leaf is a consequence for every ψ.

### 3.2 r11r12 Frobenius conversion (rechecked; a simpler route than the docstring's)

- Pan gives `ρ ≅ ρ_g ⊗ ψ′` with `tr ρ_g(Frob_geom) = a_q`.
- Then `tr ρ(Frob_arith) = ψ′(Frob_arith)·det ρ_g(Frob_arith)·a_q(g)`, using `tr M⁻¹ = tr M / det M` in dimension 2.
- So `AttachedUpToTwist` already holds with the **same** g and `ψ = ψ′·det ρ_g` (continuous).
- The docstring's route via `g^ρ` and `ψ′ε^{1−k}` is also correct. Either way the existential
  conclusion follows.

### 3.3 Repairs from earlier reviews: applied

- `PanFor` docstring has the p=3 proviso and the convention text (4583-4594).
- `EigenformHT` docstring cites Kato §§9.2-9.4 (4529-4534).
- `CarayolUnramified` docstring states the coverage (4567-4571; outside this cluster).
- `DeligneSerreFinite` says semisimplicity cannot be dropped (4545).
- `PkgI1` `R03`/Lin–Yang locator corrected to Ex. 29 (outside this cluster).

### 3.4 Minor (non-verdict)

- **(m1)** `T23_FontaineClosure` docstring says "Exact". It is a matrix-form consequence of
  Fontaine's Tannakian statement, on `V^∨`. Suggest the word "Consequence".
- **(m2)** r14/r15 vs r13 use different `GaloisRep` structures (§1). Glue cost only.
- **(m3)** The `IsNewform` definition (eigenform ∉ oldSpace) is weaker than "Li newform" as a
  *hypothesis*. Strong multiplicity one shows it is equivalent for eigenforms. Here it only occurs
  in conclusions (t25), where the weak form is the safe direction. As a hypothesis
  (`CarayolUnramified`, outside this cluster) the same equivalence makes it fine.

## 4. Lean probes (append to a copy of Leaves.lean; none run here)

P1 checks the bundle field types, P2 checks that duplicate definitions agree, and P3 checks that
`IsNormalizedEigenform` excludes the zero form (non-vacuity sanity).

```lean
section RvLeaves48B

-- P1: bundle field types are the ones reviewed
example (r : HSyn.ResearchLeaves) : HSyn.EigenformRepExists := r.r14
example (r : HSyn.ResearchLeaves) : HSyn.DeligneSerreConseq := r.r15
example (r : HSyn.ResearchLeaves) : PkgI4.EigenformHT := r.r13
example (r : HSyn.ResearchLeaves) : PkgI4.PanBerger := r.r11r12
example (r : HSyn.ResearchLeaves) : PkgI4.DeRhamComparison := r.r10
example (r : HSyn.ResearchLeaves) : PkgI1.ThetaModularity := r.r4
example (t : HSyn.TextbookLeaves) : HSyn.EigenformTwist := t.t24
example (t : HSyn.TextbookLeaves) : HSyn.SkolemNoether := t.t13
example (t : HSyn.TextbookLeaves) : HSyn.KroneckerWeber := t.t17
example (t : HSyn.TextbookLeaves) : HSyn.FrobeniusDense := t.t18
example (t : HSyn.TextbookLeaves) : HSyn.BrauerNesbitt := t.t19
example (t : HSyn.TextbookLeaves) : PkgI4.NewformOfEigenform := t.t25
example (t : HSyn.TextbookLeaves) : PkgI1.IgusaClebschSeparation := t.t28
example (t : HSyn.TextbookLeaves) : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p := t.t23

-- P2: the duplicated statements agree definitionally
example : HSyn.SkolemNoether = PkgI6.SkolemNoether := rfl
example : HSyn.EigenformTwist ↔ PkgI4.EigenformTwist := Iff.rfl

-- P3: the zero cusp form is never a normalized eigenform (a₁ = 0)
example (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) :
    ¬ HSyn.IsNormalizedEigenform (0 : HSyn.CF N k) χ := by
  rintro ⟨-, h1, -⟩
  have h0 : UpperHalfPlane.cuspFunction 1 (⇑(0 : HSyn.CF N k)) = 0 := by
    simp [UpperHalfPlane.cuspFunction, Function.comp_def]
  simp [HSyn.coeff, UpperHalfPlane.qExpansion_coeff, h0, iteratedDeriv_const_zero] at h1

end RvLeaves48B
```

If P2's `Iff.rfl` fails, the cause is only elaboration (unfolding `HSyn.IsNormalizedEigenform`
vs `PkgI4.IsNormalizedEigenform`). In that case use
`⟨fun h => h, fun h => h⟩` or `by unfold ...; rfl`.
If P3's `simp` leaves `(0 ∘ ofComplex)`, add `Pi.zero_comp` and `Function.Periodic.cuspFunction_zero`.

No counterexample or vacuity probe is proposed, because no failing clause was found.
