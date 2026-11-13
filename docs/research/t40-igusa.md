# t40-igusa: Igusa transitivity, the second supplier of leaf T40

## Main result

`ZInQ.RLeaf.IgusaTransitive` (the `x`-coordinates of the points of exact order `N` on the generic
elliptic curve `E_j` over `\overline{ℚ(j)}` form one `Gal(\overline{ℚ(j)}/ℚ(j))`-orbit) is
**reduced, with all glue proved, to two strictly smaller published statements**:

```
igusaTransitive_iff : IgusaTransitive ↔ X0Transitive ∧ TateMuN
```

* `X0Transitive`: the Galois group permutes the cyclic subgroups of order `N` of `E_j`
  transitively (irreducibility of `X₀(N)`, i.e. of the modular equation `Φ_N(X, j)` over `ℚ(j)`).
* `TateMuN`: for each `N` some cyclic subgroup `⟨Q₀⟩` of order `N` has its generators permuted
  transitively (on `x`-coordinates) by the Galois group. Its source is local: the subgroup `μ_N`
  of the Tate curve at `j = ∞`. It may be proved over any algebraically closed extension of
  `ℚ(j)`, level by level (`tateMuN_of_at`, `tateMuN_of_over`), in particular over
  `\overline{ℚ((1/j))}` (`TateMuNLocal`, `tateMuN_of_local`).

Both are consequences of `IgusaTransitive` (proved: `x0Transitive_of_igusaTransitive`,
`tateMuN_of_igusaTransitive`), so neither is stronger than the target. `X0Transitive` concerns
`X₀(N)`, of degree `ψ(N) = N∏_{p|N}(1+1/p)` over the `j`-line, instead of `X₁(N)`, and `TateMuN`
is local at the cusp.

Independently, `IgusaTransitive` follows from Igusa's theorem in the form in which it is
published (`igusaTransitive_of_igusaGL2 : IgusaGL2 → IgusaTransitive`) and from its `SL₂` part on
`x`-coordinates (Shimura 1971, Thm 6.6; `igusaTransitive_of_igusaSL2X`).

Task t40-tate proves `TateCuspLaurent` (`ZInQ.RLeaf.tateCuspLaurent`, merged here from
origin/wip/t40-tate) and is proving `TateMuN` in its own file (agreed by message, 2026-11-13).
`ZInQKernel/Contrib/RLeaf/T40.lean` records the resulting reductions of T40 and T39.

All files compile (`lake env lean` on each, `lake build` of the modules), with no `sorry`; every
`#print axioms` reads `[propext, Classical.choice, Quot.sound]` (VERIFIED, §4).

### Declarations proved (namespace `ZInQ.RLeaf`)

| Declaration | Type | File |
|---|---|---|
| `exists_det_eq_one_of_addOrderOf` | `0 < N → addOrderOf u = N → ∃ c d : ZMod N, u.1 * d - u.2 * c = 1` (`u : ZMod N × ZMod N`) | `ZInQKernel/Contrib/RLeaf/IgusaSL2.lean` |
| `exists_SL2_first_column` | `0 < N → addOrderOf u = N → ∃ g : SL(2, ZMod N), matAct g (1, 0) = u` | same |
| `igusaTransitive_of_igusaSL2X` | `IgusaSL2X → IgusaTransitive` | same |
| `igusaSL2X_of_igusaGL2` | `IgusaGL2 → IgusaSL2X` | same |
| `igusaTransitive_of_igusaGL2` | `IgusaGL2 → IgusaTransitive` | same |
| `xCoord_neg`, `eq_or_eq_neg_of_xCoord_eq`, `addOrderOf_galPt`, `xCoord_galPt` | `x(-P) = x(P)`; nonzero points with equal `x` are equal up to sign; `σ` preserves orders; `x(σP) = σ(x(P))` | `ZInQKernel/Contrib/RLeaf/IgusaX0.lean` |
| `igusaTransitive_of_x0_tateMuN` | `X0Transitive → TateMuN → IgusaTransitive` | same |
| `x0Transitive_of_igusaTransitive` | `IgusaTransitive → X0Transitive` | same |
| `tateMuN_of_igusaTransitive` | `IgusaTransitive → TateMuN` | same |
| `igusaTransitive_iff` | `IgusaTransitive ↔ X0Transitive ∧ TateMuN` | same |
| `exists_map_eq_of_nsmul_eq_zero` | for `f : Kbar →ₐ[Qj] Ω` (`Ω` alg. closed), every `P ∈ E_j(Ω)` with `N • P = 0` is `map f P'` | `ZInQKernel/Contrib/RLeaf/IgusaLocal.lean` |
| `exists_restrict` | `∀ τ : Ω ≃ₐ[Qj] Ω, ∃ τ' : Kbar ≃ₐ[Qj] Kbar, ∀ a, f (τ' a) = τ (f a)` | same |
| `tateMuNAt_kbar` | `0 < N → TateMuNAt N Ω → TateMuNAt N Kbar` (`Ω` alg. closed) | same |
| `tateMuN_of_over` | `TateMuNOver Ω → TateMuN` | same |
| `tateMuN_of_at` | `(∀ N, 0 < N → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra Qj Ω) (_ : DecidableEq Ω), TateMuNAt N Ω) → TateMuN` | same |
| `transcendental_X`, `jInv_X`, `jInvLaurent_X` | `j` transcendental; `jInv j = j⁻¹`; `jInvLaurent j = (single 1 1)⁻¹ = t⁻¹` | same |
| `tateMuN_of_local` | `TateMuNLocal → TateMuN` | same |
| `igusaTransitive_of_x0_tateMuNLocal` | `X0Transitive → TateMuNLocal → IgusaTransitive` | same |
| `x1RationalCusp_of_x0_tateMuN` | `X0Transitive → TateMuN → X1Belyi.X1RationalCusp` (**T40 reduced**) | `ZInQKernel/Contrib/RLeaf/T40.lean` |
| `x1ConstantField_of_x0_tateMuN` | `X0Transitive → TateMuN → X1Belyi.X1ConstantField` (**T39 reduced**) | same |
| `x1RationalCusp_of_x0_tateMuNLocal` | `X0Transitive → TateMuNLocal → X1Belyi.X1RationalCusp` | same |
| `x1RationalCusp_of_igusaGL2`, `x1RationalCusp_of_igusaSL2X`, `x1ConstantField_of_igusaSL2X` | T40 (T39) from Igusa's theorem | same |

### The named Props (exact Lean text)

```lean
/-- The action of a `2 × 2` matrix on column vectors `(x, y) ∈ (ℤ/N)²`. -/
def matAct {N : ℕ} (g : Matrix (Fin 2) (Fin 2) (ZMod N)) (v : ZMod N × ZMod N) :
    ZMod N × ZMod N :=
  (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2)

noncomputable abbrev galPt (σ : Kbar ≃ₐ[Qj] Kbar) : EjBar.toAffine.Point →+ EjBar.toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom

def X0Transitive : Prop :=
  ∀ (N : ℕ) (P P' : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → addOrderOf P' = N →
    ∃ σ : Kbar ≃ₐ[Qj] Kbar, galPt σ P ∈ AddSubgroup.zmultiples P'

def TateMuN : Prop :=
  ∀ N : ℕ, 0 < N → ∃ Q₀ : EjBar.toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Kbar ≃ₐ[Qj] Kbar, τ (xCoord Q₀) = xCoord R

def TateMuNAt (N : ℕ) (Ω : Type) [Field Ω] [Algebra Qj Ω] [DecidableEq Ω] : Prop :=
  ∃ Q₀ : (Ej.baseChange Ω).toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Ω ≃ₐ[Qj] Ω, τ (xCoord Q₀) = xCoord R

def TateMuNOver (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra Qj Ω] [DecidableEq Ω] : Prop :=
  ∀ N : ℕ, 0 < N → ∃ Q₀ : (Ej.baseChange Ω).toAffine.Point, addOrderOf Q₀ = N ∧
    ∀ R ∈ AddSubgroup.zmultiples Q₀, addOrderOf R = N →
      ∃ τ : Ω ≃ₐ[Qj] Ω, τ (xCoord Q₀) = xCoord R

-- `TateOmega := AlgebraicClosure (LaurentSeries ℚ)` with `ℚ(j) → ℚ((t))`, `j ↦ t⁻¹`
def TateMuNLocal : Prop := TateMuNOver TateOmega

def IgusaSL2X : Prop :=
  ∀ N : ℕ, 0 < N → ∃ e : (ZMod N × ZMod N) ≃+ nTors EjBar N,
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod N), ∃ σ : Kbar ≃ₐ[Qj] Kbar,
      ∀ v : ZMod N × ZMod N,
        σ (xCoord (e v : EjBar.toAffine.Point)) = xCoord (e (matAct g v) : EjBar.toAffine.Point)

def IgusaGL2 : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors EjBar N)
    (g : GL (Fin 2) (ZMod N)), ∃ σ : Kbar ≃ₐ[Qj] Kbar,
      ∀ v : ZMod N × ZMod N,
        galPt σ (e v : EjBar.toAffine.Point) = (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) :
          EjBar.toAffine.Point)
```

Sources (all theorem numbers UNVERIFIED; no network on this host):
* `X0Transitive`: published, as the irreducibility over `ℂ(j)` of the modular equation
  `Φ_N(X, j)` (Lang, *Elliptic functions*, Ch. 5, §2, Thm 3; Cox, *Primes of the form x²+ny²*,
  Thm 11.18; Shimura 1971, §6.1), whose roots are the `j(E_j/C)`, `C` cyclic of order `N`. The
  map `C ↦ j(E_j/C)` is a Galois-equivariant bijection because `End(E_j) = ℤ` (STANDARD); this
  bridge is not formalized, so the leaf is stated on subgroups.
* `TateMuN` / `TateMuNLocal`: published, Tate's uniformization (Silverman, *Advanced topics in
  the arithmetic of elliptic curves*, Ch. V, Thm 3.1 and Thm 5.3; Tate, *A review of
  non-archimedean elliptic functions*, 1995): over `ℚ((1/j)) = ℚ((q))`, `E_j` is a quadratic
  twist of `E_q`, `E_q(Ω) ≅ Ω^×/q^ℤ` Galois-equivariantly; `Q₀` = image of `ζ_N`; the generators
  of `⟨Q₀⟩` are the images of `ζ_N^c`, permuted transitively by `Gal(ℚ((q))(ζ_N)/ℚ((q))) ≅ (ℤ/N)^×`;
  the twist changes the action by `±1`, invisible on `x`.
* `IgusaGL2`: Igusa, *Fibre systems of Jacobian varieties III*, Amer. J. Math. 81 (1959); Lang,
  *Elliptic functions*, Ch. 6, §3. `IgusaSL2X`: the `SL₂` part on `x`-coordinates, Shimura 1971,
  Thm 6.6 (`Gal(F_N/ℚ(j)) ≅ GL₂(ℤ/N)/{±1}` acting on the Fricke functions).

## 1. The proof of the reduction (paper version)

**`IgusaTransitive` from `X0Transitive` and `TateMuN`.** Let `P, P'` have order `N` and let `Q₀`
be the point of `TateMuN`. By `X0Transitive` there are `σ₁, σ₂` with `A := σ₁P ∈ ⟨Q₀⟩` and
`B := σ₂P' ∈ ⟨Q₀⟩`; Galois preserves orders, so `A, B` generate `⟨Q₀⟩`. `TateMuN` gives `τ₁, τ₂`
with `τ₁ x(Q₀) = x(A)`, `τ₂ x(Q₀) = x(B)`. Then `ρ = σ₂⁻¹ τ₂ τ₁⁻¹ σ₁` has `ρ x(P) = x(P')`.

**Converses.** If `σ x(P) = x(P')` then `σP = ±P'` (nonzero points with equal `x` are equal up to
sign, `Y_eq_of_X_eq`), so `σP ∈ ⟨P'⟩`; and `TateMuN` is `IgusaTransitive` for one `Q₀`.

**Transfer from `Ω`.** For `Ω ⊇ ℚ(j)` algebraically closed fix `f : \overline{ℚ(j)} → Ω` over
`ℚ(j)`. `E_j[N]` has `N²` points over both fields (leaf T36), and `f` induces an injective group
map, so it is onto `E_j(Ω)[N]`. An automorphism `τ` of `Ω/ℚ(j)` preserves the normal subextension
`f(\overline{ℚ(j)})` and restricts to `τ'` with `f ∘ τ' = τ ∘ f` (`AlgEquiv.restrictNormal`).

**From Igusa's theorem.** A vector `u = (a, b)` of order `N` in `(ℤ/N)²` has `gcd(a, b, N) = 1`
(else `(N/g)u = 0`); Bézout gives `c, d` with `ad − bc = 1`, so `u = g(1, 0)` with `g ∈ SL₂(ℤ/N)`.
With `σ, σ'` realising `g, g'` for `P = e(u)`, `P' = e(u')`, `σ'σ⁻¹ x(P) = x(P')`.

## 2. Decision: which proof of Igusa's theorem, and why none is formalized

Candidates (locators UNVERIFIED):
1. **Lang, *Elliptic functions*, Ch. 6; Shimura 1971, Thm 6.6** (Fricke functions / modular
   functions of level `N`). Needs the complex uniformization `ℂ/Λ_τ ≅ E_τ(ℂ)` with the ℘ addition
   law (so that the `x`-coordinates of `E_{j(τ)}[N]` are the ℘-values at `(aτ+b)/N`), the Fricke
   functions as meromorphic functions on `ℍ` with `f_a ∘ γ = f_{aγ}`, and an embedding of the
   `N`-division field of `E_j` into the meromorphic functions on `ℍ` sending `j ↦ j(τ)`; the
   arithmetic part needs the `q`-expansion principle. Mathlib (pinned) has modular forms,
   Eisenstein series and `q`-expansions, but not the ℘-uniformization of elliptic curves nor the
   link between division polynomials and ℘. Tau Ceti has the Tate (non-archimedean) curve and Weil
   pairings, not the complex uniformization.
2. **Deligne–Rapoport** (moduli of level-`N` structures). Needs moduli stacks and connectedness
   of their fibres. Not available.
3. **Igusa's own proof** (characteristic `p`: Hasse invariant, Igusa curves, specialization).
   Needs reduction of the generic curve and the ramification of the Igusa cover. Not available.
4. **Algebraic proof via the Tate curve alone** (what Tau Ceti and task t40-tate provide). The
   decomposition group at `j = ∞` acts on `E_j[N]` through `{[[c, k], [0, 1]]}` in the Tate basis
   `(ζ_N, q^{1/N})` (`c ∈ (ℤ/N)^×` cyclotomic, `k` from `q^{1/N} ↦ ζ_N^k q^{1/N}`), up to `±1`.
   Its orbits on vectors `(a, b)` keep `b` (up to sign) fixed, so for `N ≥ 3` it has more than
   one orbit on order-`N` points modulo `±1`; `j = ∞` is the only place of multiplicative
   reduction of `E_j`, and the places `j = 0, 1728` only contribute elements of order dividing
   `4` or `6` known up to conjugacy. A global input relating the local groups (irreducibility of
   `X(N)`, i.e. the monodromy `PSL₂(ℤ) = ℤ/2 * ℤ/3` of the `j`-line) is needed. (Hand
   computation, VERIFIED by inspection of the matrices; the general claim is SPECULATIVE only in
   that I did not search for an exotic algebraic proof.)

**Decision.** Use route 4 as far as it goes: the Tate curve provides exactly `TateMuN` (the
local half), and the global half is isolated as the published, strictly weaker statement
`X0Transitive` (irreducibility of `X₀(N)`), whose proofs are again routes 1-3. Separately record
the reduction to Igusa's theorem as published (`IgusaGL2`) and to Shimura's `SL₂` form
(`IgusaSL2X`), so that any of them discharges the leaf. Effort for formalizing route 1 for
`X0Transitive` (SPECULATIVE): the ℘-uniformization and the bridge `C ↦ j(E/C) ↦ j(γ N τ)`,
several thousand lines.

## 3. Remarks on the statements

* No statement change is proposed: `IgusaTransitive` is true as stated and is the correct
  consequence of Igusa's theorem for the model `E_j = ofJNe0Or1728 j` (the `x`-coordinates do not
  see the quadratic twist).
* `IgusaGL2` (on points, every basis, all of `GL₂(ℤ/N)`) is true for every model of the generic
  curve: the geometric monodromy of any model maps onto `PSL₂(ℤ)` and contains `-1` (`PSL₂(ℤ)`
  does not lift to `SL₂(ℤ)`, since `S` has order 4 and `-1` is the only involution of
  `SL₂(ℤ)`), hence equals `SL₂(ℤ)` and reduces onto `SL₂(ℤ/N)`; the determinant is the
  cyclotomic character, onto `(ℤ/N)^×` over `ℚ(j)` (STANDARD; argument SPECULATIVE in detail).
* `TateMuN` holds for every `Q₀` of order `N` (it follows from `IgusaTransitive`), but the local
  proof works only for `Q₀ ∈ μ_N`: the stabilizer of `⟨q^{1/N}⟩` in the decomposition group at
  `∞` consists of the `[[c, 0], [0, 1]]`, which fix `q^{1/N}`. Hence the leaf asks for some `Q₀`.

## 4. Compilation and axioms (VERIFIED)

`lake build ZInQKernel.Contrib.RLeaf.T40` (which builds IgusaSL2, IgusaX0, IgusaLocal and, from
task t40-tate, TateCusp): `Build completed successfully (9394 jobs)`, no errors, no `sorry`. The
`#print axioms` lines of the four files:

```
'ZInQ.RLeaf.exists_det_eq_one_of_addOrderOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.igusaTransitive_of_igusaSL2X' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.igusaSL2X_of_igusaGL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.igusaTransitive_of_igusaGL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.igusaTransitive_of_x0_tateMuN' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x0Transitive_of_igusaTransitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.tateMuN_of_igusaTransitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.igusaTransitive_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.tateMuN_of_over' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.tateMuN_of_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.jInvLaurent_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.tateMuN_of_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.igusaTransitive_of_x0_tateMuNLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1RationalCusp_of_x0_tateMuN' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1ConstantField_of_x0_tateMuN' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1RationalCusp_of_x0_tateMuNLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1RationalCusp_of_igusaGL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1RationalCusp_of_igusaSL2X' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1ConstantField_of_igusaSL2X' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No Tau Ceti file was vendored or modified by this task; `diffcheck2.py`: `MOD-UNNOTED 0`,
`NOTE-ONLY 0` (the `NOPROV` entries are task t40-tate's `Backport/` files).

## 5. Effect on the leaf list

* T40 (`X1Belyi.X1RationalCusp`) and T39 now follow from `X0Transitive` and `TateMuN`
  (`x1RationalCusp_of_x0_tateMuN`, `x1ConstantField_of_x0_tateMuN`), the Tate-curve half
  `TateCuspLaurent` being proved by t40-tate.
* `TateMuN` is local at `j = ∞` (Tate curve; t40-tate is proving it with its backport of Tau
  Ceti's Tate uniformization). If it is proved, the only elliptic input of the `X₁(N)` side of
  the decomposition is `X0Transitive`, the irreducibility of `X₀(N)` over `ℚ`.
