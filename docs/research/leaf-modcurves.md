# leaf-modcurves: `X₁(N)`, `J₁(N)` over `ℚ` and a concrete R16

Task leaf-modcurves, 2026-11-12, following `docs/research/bp-modcurves.md`. The Lean file is
`scratch/leaf-modcurves/ModCurveLeaves.lean` (about 840 lines; it imports the kernel modules
`ZInQKernel.HDecomp.Objects` and `ZInQKernel.HDecomp.C10.C10`). The results log is
`scratch/leaf-modcurves/log.md`.

Markers: **VERIFIED** = compiled, computed or read here. **STANDARD** = published, with a
reference. **SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (this
host has no network).

---

## §0. Main result

1. **R16 is now a concrete Lean statement over genuine definitions:**
   `LeafModCurves.R16_EichlerShimuraJ1'`. It replaces the opaque placeholder
   `R16_EichlerShimuraJ1` of `scratch/h-decomposition/Leaves.lean`. It uses only Mathlib, the
   kernel's `PkgI3.AbVar` with its Tate module and Galois representation, and the kernel's
   `GlueC10.IsFrobAt`. It is a consequence of Shimura 1973 Thm 1 (**unconditional clauses
   only**), the rank-2 freeness of `V_ℓ(A_f)` and the Eichler–Shimura congruence relation. It
   never uses the zeta clause, so Thm 1's Fricke/`Γ₀` condition plays no role (§3). VERIFIED that
   it compiles; the faithfulness argument is in §3.
2. **`X₁(N)` over `ℚ` is defined by its function field.** `IsX1Model N X` says: `X` is a smooth
   proper geometrically connected integral curve over `ℚ` whose function field is
   ring-isomorphic to `K_N = ℚ(j)(x(P))`, for `P` a point of exact order `N` of Mathlib's
   `E_j = ofJNe0Or1728 j` over `\overline{ℚ(j)}`. bp-modcurves' relative-normalization chart
   `Y1j` is kept as the constructive affine model. Existence, `X1ModelExists`, is a separate
   statement that the main theorem must consume.
3. **`J₁(N)` is defined by an Albanese predicate** over `PkgI3.AbVar ℚ`:
   - `IsJacobian X P₀ J aj` is the Albanese property.
   - `IsJ1 N J` says that `J` is a Jacobian of some model of `X₁(N)` with some rational base point.
   - Existence of the Jacobian is the leaf `JacobianExists` (Weil; Milne 1986, UNVERIFIED numbers).
   - Uniqueness is proved (`IsJacobian.unique`).
4. **The genus input of E2 is a leaf plus proved glue.**
   - Leaf `DimJ1Genus`: `dim J₁(N)` equals the genus formula of `Γ₁(N)` computed from cosets.
   - Glue `dim_J1_le` (proved): `dim J₁(N) ≤ N²`.
   - **The Belyi input is a definition plus a glue target.** `IsBelyiFunction k F t` is the
     function-field Belyi condition, and `BelyiX1` says that `j/1728` is a Belyi function on
     `K_N` of degree `≤ N²`. R18 itself still cannot be stated: it needs the Faltings height.
5. **Proved glue that the consumers will use** (all compiled, axioms `propext`,
   `Classical.choice`, `Quot.sound`):
   - `exists_J1`: `J₁(N)` exists.
   - `exists_J1_dim_le`: there is a `J₁(N)` with `dim ≤ N²`; this is E2's `g ≤ N²`.
   - `exists_J1_quotient`: `J₁(N)` together with Shimura's `A_f`, `K_f ↪ End⁰`, the rank-2
     components and the traces.
   - `rhoF_traces`: a 2-dimensional representation `ρ_{f,ι}` of `G_ℚ` with
     `tr ρ(g) = ι(a_p)` at every `GlueC10.IsFrobAt g p`, `p ∉ S`. This is exactly the shape of
     hypothesis `hρ₅` of the kernel's `GlueC10.c10`.
   - `dualAct_mem`: `G_ℚ` preserves the `ι`-eigenfunctionals. Because this is proved, R16 does
     not assume it.
   - `isFrobAt_of_isArithFrob`: `Leaves.lean`'s arithmetic Frobenius implies the kernel's
     `IsFrobAt`.
6. **An independent model review** found no false, over-strong or vacuous leaf. Its one
   sourcing finding is applied (§6).
7. **What remains before C9, E1, E2 can be instantiated** is listed in §5. In short:
   - C9 needs bridges from R16's `ρ_{f,ι}` to the abstract eigenform representation of
     `EigenformRepExists` and to C8's `r₅`.
   - E1 needs `ρ_{f,ι}` as a *sub*representation of `V_ℓ(J₁(N)_{L'}) ⊗ E`. This comes from
     Poincaré reducibility (leaf T8) and a base-change-of-Tate-modules lemma.
   - E2 needs R18, so it is blocked on the Faltings height (WP10). Its genus half is done
     modulo the leaf `DimJ1Genus`, and its Belyi half is the glue target `BelyiX1`.

---

## §1. What compiles (VERIFIED: `lake env lean scratch/leaf-modcurves/ModCurveLeaves.lean`, exit 0, no errors, no warnings, no `sorry`)

Every `#print axioms` (for `genus_Gamma1_le`, `IsJacobian.unique`, `dualAct_mem`, `dim_J1_le`,
`exists_J1_dim_le`, `exists_J1_quotient`, `rhoF_traces`, `isFrobAt_of_isArithFrob`) gives `propext`, `Classical.choice`,
`Quot.sound`.

| § | Content | Origin |
| --- | --- | --- |
| A | `pmSubgroup`, `belyiDeg`, `nu2`, `nu3`, `nuInf`, `genus`; `genus_Gamma1_le : genus (Γ₁ N) ≤ N²` (proved) | copied from bp-modcurves `Gamma1Genus.lean` |
| B | `GQ`, `IsFrobAt` (= kernel `GlueC10.IsFrobAt`), `LiesOver`, `IsArithFrob`, `zbar_mem`, `isFrobAt_of_isArithFrob` (proved), `CF`, `coeff`, `HasNebentypus`, `IsNormalizedEigenform`, `oldSpace`, `IsNewform`; new `coeffField f = ℚ(a_n(f)) ⊆ ℂ` | copied from `Leaves.lean` (`PkgI4` §2) |
| C | `Ej`, `Ej_j`, `EjBar`, `xCoord`, `fieldX1 P = ℚ(j)(x(P))`, `Y1j`, `jMap` | copied from bp-modcurves `ModularCurveDefs.lean` |
| D | `IsCurve`, `IsX1Model N X`, `RatPt` | new |
| E | `IsJacobian` (over kernel `PkgI3.AbVar`), `JacobianExists` (leaf), `IsJacobian.unique` (proved), `IsJ1 N J` | adapted from bp-modcurves `Jacobian.lean` |
| F | `homVAdd`, `endV : End⁰(A) →+ End_{ℚ_ℓ}(V_ℓ A)`, `eigenFun`, `dualAct`, `endV_comm`, `dualAct_mem`, `frobOn`, `frobOn_mul`, `rhoF` (a `Representation` of `G_ℚ`), `trace_rhoF`, `finrank_rhoF`; **`R16_EichlerShimuraJ1'`** | new |
| G | **`DimJ1Genus`** (leaf), `dim_J1_le` (proved), `IsBelyiFunction`, `BelyiX1` (glue target) | new |
| H | `X1ModelExists`, `ModCurveLeaves` (bundle), `exists_J1`, `exists_J1_dim_le`, `exists_J1_quotient`, `rhoF_traces` (all proved) | new |

---

## §2. The definitions

### §2.1 `X₁(N)` (function-field form)

```lean
def IsX1Model (N : ℕ) (X : Over SpecQ) : Prop :=
  IsCurve X ∧ ∃ (_ : IsIntegral X.left) (P : EjBar.toAffine.Point), addOrderOf P = N ∧
    Nonempty (X.left.functionField ≃+* fieldX1 P)
```

- **Why the function-field form, not the normalization of `ℙ¹`.** Mathlib v4.35 has no `ℙ¹`
  scheme by name, and no smoothness or properness theory for the normalization (bp-modcurves
  MC4, tier large). The predicate is genuine: it uses Mathlib's `IsProper`,
  `SmoothOfRelativeDimension 1`, `GeometricallyConnected`, `IsIntegral` and
  `Scheme.functionField`. It also determines `X` up to `ℚ`-isomorphism, because smooth proper
  curves over a field are equivalent to their function fields (Hartshorne I.6.12 with II.6.7,
  UNVERIFIED numbers; STANDARD).
- **`≃+*` suffices.** A ring isomorphism between fields of characteristic 0 is `ℚ`-linear, and
  the `ℚ`-structure on `X`'s function field from `X → Spec ℚ` is the unique one.
- **The constant field of `K_N` is `ℚ`** (needed because `IsCurve` asks for geometric
  connectedness). By Igusa, `Gal(ℚ(j)(E_j[N])/ℚ(j)) ≅ GL₂(ℤ/N)` (STANDARD; Shimura 1971
  Thm 6.6, UNVERIFIED number). The stabilizer of `±P` contains `(1 b; 0 d)` for every unit `d`,
  so its determinant is onto `(ℤ/N)^×`. Hence `K_N ∩ ℚ(ζ_N) = ℚ`. The `x`-coordinate field is
  unchanged by quadratic twists (`x ↦ dx`, `d ∈ ℚ(j)`), so the choice of the model `E_j` does
  not matter. Small levels: `N = 1` gives `x(0)`, Mathlib's junk value `0`, so `K_1 = ℚ(j)`, which
  is correct (`X₁(1) = ℙ¹`). `N = 2` gives the cubic field of a 2-torsion `x`, which is correct
  (`X₁(2) = X₀(2)`, degree 3). SPECULATIVE in the details, STANDARD in substance.
- **Which `ℚ`-form.** `K_N` is the field of the moduli problem `(E, ℤ/N ↪ E)`. Shimura's
  canonical model (rational `q`-expansions at `∞`) is the `μ_N`-form. The two forms are
  `ℚ`-isomorphic as curves via `(E, P) ↦ (E/⟨P⟩, E[N]/⟨P⟩ ≅ μ_N)` (the Weil pairing
  `e_N(P, ·)`; STANDARD, Diamond–Im §9.3, UNVERIFIED locator). This is bp-modcurves' leaf MC9.
  It is used once, to transfer Shimura's results to every model (§3).

### §2.2 `J₁(N)` (Albanese predicate)

```lean
structure IsJacobian (X) (P₀ : 𝟙_ _ ⟶ X) (J : AbVar K) (aj : X ⟶ J.X) : Prop where
  base : P₀ ≫ aj = η[J.X]
  univ : ∀ (A : AbVar K) (f : X ⟶ A.X), P₀ ≫ f = η[A.X] → ∃! φ : J.X ⟶ A.X, IsMonHom φ ∧ aj ≫ φ = f
def JacobianExists (K) : Prop := ∀ X, IsCurve X → ∀ P₀, ∃ J aj, IsJacobian X P₀ J aj   -- leaf
def IsJ1 (N : ℕ) (J : AbVar ℚ) : Prop :=
  ∃ (X : Over SpecQ) (P₀ : RatPt X) (aj : X ⟶ J.X), IsX1Model N X ∧ IsJacobian X P₀ J aj
```

`AbVar` is the kernel's `PkgI3.AbVar`: a group scheme over `Spec K`, proper, smooth and
geometrically integral. This is the standard notion, so `JacobianExists` is Milne 1986 Thm 1.1
with Prop. 6.1 (UNVERIFIED numbers) for pointed curves. Genus 0 is included: the Jacobian is
`Spec K`, which is an `AbVar`. Any two `J` with `IsJ1 N J` are isomorphic abelian varieties:
the models are `ℚ`-isomorphic, Jacobians are unique, and changing the base point composes `aj`
with a translation.

---

## §3. R16

```lean
def R16_EichlerShimuraJ1' : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p)
```

**The Lean encoding.**
- `endV ℓ A` sends `q ⊗ e ∈ ℚ ⊗ End(A)` to `q · V_ℓ(e)`. Here `V_ℓ(e)` is the kernel's `homT e`,
  base-changed to `ℚ_ℓ`.
- `eigenFun ℓ A θ ι` is the space of `ℚ_ℓ`-linear functionals `φ : V_ℓ(A) → ℚ̄_ℓ` with
  `φ ∘ θ(a) = ι(a) φ` for all `a ∈ K_f`. Write `V' = V_ℓ(A) ⊗ ℚ̄_ℓ = ⊕_τ V'_τ` (sum over the
  embeddings `τ : K_f → ℚ̄_ℓ`). Then `eigenFun` is the dual of `V'_ι`, of dimension
  `rank_{K_f ⊗ ℚ_ℓ} V_ℓ(A) = 2`.
- `frobOn ℓ A θ ι σ` is `φ ↦ φ ∘ ρ_ℓ(σ)` restricted to `eigenFun`, which is the transpose of
  `σ` on `V'_ι`. A transpose has the same trace and determinant. Stability of `eigenFun` is
  proved (`dualAct_mem`, from the kernel's `homT_galT`), so it is not an extra hypothesis.
- `rhoF` is the left representation `σ ↦ (frobOn σ)ᵀ` on `Dual(eigenFun) ≅ V'_ι`.
  `trace_rhoF` proves that it has the same traces.

**Faithfulness: a consequence of three published results, never stronger.**
- (i) **Shimura 1973, Thm 1** (pp. 526-527, read by the locator audit). Only the unconditional
  clauses are used: the quotient `A_f` of `J₁(N)` over `ℚ`, `K_f` acting through `End⁰`, and
  `dim A_f = [K_f:ℚ]`. Thm 1's final Euler-factor clause carries an extra `Γ₀`/Fricke-stability
  condition. That clause is **not** used: R16' contains no `L`-function or zeta identity, so the
  condition is neither needed nor silently dropped. This is `locators.md`'s reading, row R16.
- (ii) **`V_ℓ(A_f)` is free of rank 2 over `K_f ⊗ ℚ_ℓ`**, for every `ℓ` (Shimura 1971 §7.4;
  Ribet 1977; UNVERIFIED locators). This gives `finrank (eigenFun) = 2`.
- (iii) **The characteristic polynomial of Frobenius on `V'_ι`**, `X² − ι(a_p)X + ι(χ(p))p`
  for arithmetic Frobenius on the covariant `V_ℓ(A_f)`, `p ∤ Nℓ`. This is printed as such in
  Diamond–Shurman Thm 9.5.4 and in Shimura 1971 Thm 7.11 / Ribet 1977 (UNVERIFIED numbers). It
  rests on the Eichler–Shimura congruence relation `T_p = Frob_p + p⟨p⟩Frob_p⁻¹` (Shimura 1971
  Thm 7.9; Diamond–Shurman Thm 8.7.2; UNVERIFIED). *Review finding (2026-11-12):* the congruence
  relation alone only gives an annihilating polynomial of Frobenius on `V'_ι`. If its roots
  `α ≠ β`, then `Frob = α·Id` would also satisfy it, with trace `2α`. So the citation for the
  trace and determinant clauses must be the printed characteristic polynomial, not Thm 7.9
  alone. The leaf statement is unchanged; its Lean docstring now cites the characteristic
  polynomial.
- **Arithmetic Frobenius, covariant `V_ℓ`.** On the kernel's `V_ℓ` (points over `ℚ̄`, `σ` acting
  on coordinates), arithmetic Frobenius acts like the Frobenius endomorphism. For an elliptic
  curve it has trace `a_p` and determinant `p`. With geometric Frobenius the statement would be
  false (bp-modcurves review).
- **Conventions.** If the Hecke convention gives `ā_p`, `χ̄(p)` on `V'_ι`, replace `θ` by `θ ∘ c`.
  This is legitimate because `K_f` is totally real or CM (STANDARD), so complex conjugation `c`
  preserves it. `θ` is existential, so the statement is unaffected.
- **Model.** (i)-(iii) are about Shimura's canonical model. They transfer to every `X` with
  `IsX1Model N X` by the `ℚ`-isomorphism of §2.1 (MC9). Jacobians are transported by
  `IsJacobian.unique`, and quotients and traces are invariant under isomorphism.
- **Not claimed:** the Hecke algebra, `I_f`, or `A_f = J/I_f J`. `A`, `π`, `θ` are existential,
  so the leaf is weaker than Shimura's construction.

**Frobenius predicate.** `IsFrobAt` is the kernel's `GlueC10.IsFrobAt`: some prime `𝔓` of `ℤ̄`
over `p` with `g x ≡ x^p mod 𝔓` on `ℤ̄`. It is the predicate that C10 consumes, and it is the
standard notion. For `x ∈ 𝔓`, `g x ≡ x^p ≡ 0`, so `g𝔓 ⊆ 𝔓`, hence `g𝔓 = 𝔓`, and `g` induces
`x ↦ x^p` on `ℤ̄/𝔓`.
- **Proved bridge** `isFrobAt_of_isArithFrob` (VERIFIED, compiled): an arithmetic Frobenius at
  a place `v` in the sense of `Leaves.lean`'s `PkgI4.IsArithFrob` is an `IsFrobAt`, with
  `𝔓 = 𝔪_v ∩ ℤ̄`. The proof uses `zbar_mem`: `ℤ̄` lies in every valuation subring of `ℚ̄`.
- Consequence: R16' implies its `IsArithFrob` form, which is the form R14
  (`EigenformRepExists`) uses.
- The converse direction (take `v = ℤ̄_𝔓`) is not needed and was not formalized.

---

## §4. Genus and Belyi (E2, R18)

```lean
def DimJ1Genus : Prop :=                                    -- leaf (consequence)
  ∀ (N : ℕ) (J : AbVar ℚ), 0 < N → IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ (g : ℚ) = genus (CongruenceSubgroup.Gamma1 N)
theorem dim_J1_le (h : DimJ1Genus) (N) (hN : 0 < N) (J) (hJ : IsJ1 N J) :
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2               -- proved
def IsBelyiFunction (k F) [Field k] [Field F] [Algebra k F] (t : F) : Prop   -- definition
def BelyiX1 : Prop                                           -- glue target (MC1 + MC5)
```

**`DimJ1Genus` is a consequence of three published results.**
- The genus formula `g(Γ\ℍ*) = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` (Shimura 1971 Prop. 1.40,
  UNVERIFIED number). The formula counts all cusps, so the irregular cusp at `N = 4` does not
  matter.
- `X₁(N)_ℂ ≅ Γ₁(N)\ℍ*` for the canonical model (Shimura 1971 §6.7, UNVERIFIED), with MC9.
- `dim Jac X = g(X)` (Milne 1986, UNVERIFIED).

The coset conventions of `nu2`, `nu3`, `nuInf` were confirmed by the bp-modcurves review. The
values agree with the reference genus table for `N ≤ 30` (`scratch/bp-modcurves/genus_check.py`,
VERIFIED computed there).

**`IsBelyiFunction`.**
- Definition: `t` is transcendental, and for every place `w ⊇ k` of `F` with `t ∈ w` and
  `q(t) ∈ 𝔪_w` (with `q ∈ k[T]` monic irreducible, `q ≠ T, T − 1`), `q(t)` generates `𝔪_w`. Then
  `w ∩ k(t) = k[t]_{(q)}`, so this is ramification index 1. Places over `t = 0, 1, ∞` are
  unconstrained.
- In characteristic 0, ramification indices do not change when the constants are extended to
  `k̄`. So for the function field of a geometrically connected curve it gives a Belyi map
  `X_k̄ → ℙ¹` of degree `[F : k(t)]`. Javanpeykar's `deg_B` is at most this degree.
- `BelyiX1` says that `j/1728` is a Belyi function on `K_N` and that `[K_N : ℚ(j)] ≤ N²`. This
  is Glazer's "standard Belyi map" (N5 L868-870). It is provable glue: `E_j` has good reduction
  away from `j = 0, 1728, ∞` and `E[N]` is étale in characteristic 0 (bp-modcurves MC5), and the
  degree bound is `FieldX1DegreeLe` (MC1, MC3a).

**R18 is still not statable**, because Mathlib has no Faltings height (WP10). Once it exists,
R18 can be stated over the definitions here, in the consequence form "for `X` with `IsCurve X`,
a rational point, a Jacobian `J` with `dim J = g ≥ 1`, and a Belyi function on `X`'s function
field of degree `d`: `h_F(J_ℚ̄) ≤ 13·10⁶·g·d⁵`". Here `g := dim J` uses `dim Jac = genus`
(STANDARD).

---

## §5. What remains before C9, E1, E2 can be instantiated

| Step | What the kernel consumes | What this task supplies | What remains |
| --- | --- | --- | --- |
| **C9** (`r₅ ≅ ρ_{f,ι₅}`, feeding `GlueC10.c10`'s `ρ₅`, `hρ₅`, `h₅`) | a representation `ρ₅` over a field `k₅` with `tr ρ₅(g) = ι₅(a p)` at `IsFrobAt g p`, `p ∉ S`; and `h₅ : tr r₅ = tr ρ₅` | **`rhoF_traces`**: `ρ₅ := rhoF 5 A θ ι` on a 2-dimensional `ℚ̄₅`-space, `C := coeffField f`, `a p := ⟨a_p(f), _⟩`, `hρ₅` exactly, for any `S ⊇` primes of `5N` | (a) **`h₅`**: C8's `r₅` and `rhoF` have equal Frobenius traces. This needs R14's `EigenformRepExists` (attached `GaloisRep` with `ιC`, `ιL` on `ℚ̄`) and R16's `ρ_{f,ι}` matched by Brauer–Nesbitt (`BrauerNesbittChar0`, already a kernel Prop). That in turn needs semisimplicity of `rhoF` (Faltings' `FaltingsSemisimple` for `A_f`, plus `V'_ι` being a direct summand: linear algebra), continuity of `rhoF` (as glue-rho-cont did for `V_ℓ`), and the bridge `emb = ιL ∘ ιC⁻¹` on `K_f ⊂ ιC(ℚ̄)` (small). (b) The newform `f` comes from C8's eigenform by twisting and Li (`EigenformTwist`, `NewformOfEigenform`, already Props in `Leaves.lean`). (c) The `GaloisRep` (matrix) to `Representation` bridge (small). |
| **E1** (`A × Z → J₁(N)` over `L'`, from `PkgI3.E1_exists_hom_ne_zero`) | `J : AbVar L'`; subrepresentations `U ⊂ V_ℓ(A) ⊗ E`, `U' ⊂ V_ℓ(J) ⊗ E` with an equivariant isomorphism | `exists_J1_quotient`: `J₁(N)/ℚ`, `π : J ↠ A_f`, `ρ_{f,ι}` as a **quotient** of `V_ℓ(A_f) ⊗ ℚ̄_ℓ` | (a) **sub, not quotient**: Poincaré reducibility (leaf T8, `PkgI3.PoincareReducibility`) gives an abelian subvariety of `J` isogenous to `A_f`, so `V_ℓ(A_f) ↪ V_ℓ(J)`. Alternatively use semisimplicity (R9a). Medium glue. (b) Base change to `L'`: `PkgI3.AbVar.baseChange` exists in the kernel; the identification `V_ℓ(J_{L'}) ≅ V_ℓ(J)|_{G_{L'}}` (points over `\overline{L'}` against points over `ℚ̄`) is open glue, medium. (c) `Dual(eigenFun) ≅ V'_ι ⊂ V' = V_ℓ ⊗ ℚ̄_ℓ` as a subrepresentation (linear algebra, small-medium). (d) The application of T8 at E1 already needs `EndDivision A` (h-decomposition G17). |
| **E2** (`NonCMOutput`: `2 ≤ g ≤ N²`, `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`) | real numbers `g = dim J₁(N)`, `hFJ` | **`exists_J1_dim_le`**: `g = dim J₁(N) ≤ N²` (from the leaf `DimJ1Genus` and the proved `genus_Gamma1_le`) | (a) `2 ≤ g`: from E1, since `A` is isogenous to a subvariety of `J₁(N)`, `dim A = 2` (glue, small once E1 is done). (b) `hFJ ≤ 1.3·10⁷N¹²`: **R18 (Javanpeykar) needs the Faltings height (WP10, very large)**. Its other inputs are a Belyi function of degree `≤ N²` (**`BelyiX1`**, glue target, large: bp-modcurves MC5) and `g ≤ N²` (done modulo `DimJ1Genus`). (c) Existence of `J₁(N)`: `X1ModelExists` (glue target MC4 + MC10, or a leaf: Shimura's canonical model with a rational cusp) and `JacobianExists` (leaf). |

**Leaf count added by this task.**
- New leaves: `JacobianExists` (Weil/Milne), `R16_EichlerShimuraJ1'` (replacing the R16
  placeholder) and `DimJ1Genus` (Shimura Prop. 1.40 + canonical model + `dim Jac = g`).
- New glue targets: `X1ModelExists` (it may also be taken as a leaf) and `BelyiX1`.
- R18 stays a placeholder.

**Integration** (after the announcement, by the owner of `Leaves.lean`):
- Replace `R16_EichlerShimuraJ1` in `ResearchLeaves` by `LeafModCurves.R16_EichlerShimuraJ1'`.
- Add `JacobianExists ℚ`, `X1ModelExists` and `DimJ1Genus`. Their docstrings give the citations.
- Copy §A-§H in as one block. The file has no dependency on other scratch files.

---

## §6. Independent review (2026-11-12, one model review, read-only)

Verdict: **no leaf is false, stronger than its source, or vacuous, and every definition has the
right strength.** The review checked:
- `IsX1Model`: constant field `ℚ`; `N = 1..4`, with degrees 1, 3, 4, 6 over `ℚ(j)`; Shimura's
  field `ℚ(j, f_{(0,1/N)})` is literally `K_N` for some `P`; the `μ_N` form is `ℚ`-isomorphic;
  `≃+*` is adequate.
- `IsJacobian` and `JacobianExists`: genus 0 (`AbVar.zero`), the base point, universes.
- `eigenFun`: dimension 2 for every `ℓ`, including `ℓ ∣ N`.
- `frobOn` (a transpose, with the same trace and determinant); arithmetic Frobenius on the
  covariant `V_ℓ` (geometric Frobenius would be wrong).
- The `a_p`/`ā_p` conventions: `θ ↦ θ∘c` maps `eigenFun(θ∘c, ι)` to `eigenFun(θ, ι∘c)`.
- Absence of the Fricke clause.
- `DimJ1Genus` for `N = 1..4`: `(μ, ν₂, ν₃, ν∞) = (1,1,1,1), (3,1,0,2), (4,0,1,2), (6,0,0,3)`,
  all giving genus 0.
- `IsBelyiFunction`, `BelyiX1`, `X1ModelExists`: true; for example the cusp `(Tate(q), q^{1/N})`
  is rational on the `ℤ/N` form.

The one finding was **sourcing** (characteristic polynomial against congruence relation). It is
applied in §3 and in the Lean docstring. Minor: Shimura 1973 Thm 1 may be phrased for primitive
forms in `S₂(N, ψ)` (UNVERIFIED). This is harmless because R16' is restricted to newforms.

## §7. Risks and open checks

1. The locators of (ii), (iii), MC9, Prop. 1.40 and Milne are UNVERIFIED (no network). The
   locator audit read Shimura 1973 Thm 1 only.
2. `X1ModelExists` is a genuine obligation. If the main theorem used R16' without it, every
   `∀ J, IsJ1 N J → …` would be vacuous. The bundle `ModCurveLeaves` includes it, and
   `exists_J1` consumes it.
3. If `IsX1Model` were over-strong, `X1ModelExists` would be false and the main theorem vacuous.
   Each clause is a property of the actual `X₁(N)` (§2.1). The integrality clause follows from
   smooth plus geometrically connected; it is stated because Mathlib's `functionField` needs it.
4. `DimJ1Genus` relies on the monodromy identification (bp-modcurves §7.4) through Shimura's
   analytic theory. An algebraic proof would be large.
