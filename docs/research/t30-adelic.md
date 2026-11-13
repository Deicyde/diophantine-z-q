# t30-adelic: T30 from local Kronecker–Weber, and the adelic bookkeeping of A3

Status: research note (task t30-adelic, 2026-11-12). Lean: `scratch/t30-adelic/SqrtCrit.lean`
(T30), `scratch/t30-adelic/Adelic.lean` and `scratch/t30-adelic/G1Count.lean` (G1-adelic). Log:
`scratch/t30-adelic/log.md`. Every file compiles with `lake env lean` (after
`lake build ZInQKernel.HDecomp.Sqrt.Disj ZInQKernel.HDecomp.Descent.B2Glue
ZInQKernel.HDecomp.Vigneras.Local ZInQKernel.HDecomp.Repo.A1Quaternion`), has no `sorry`, and `#print axioms` of every main theorem is
`[propext, Classical.choice, Quot.sound]` (VERIFIED).

## 1. Main results

**T30 is glue, not a leaf.** (VERIFIED, compiled)

```lean
theorem T30.leafSqrtCrit_of_localKroneckerWeber
    (hLKW : ∀ p : Nat.Primes, PkgI6.LocalKroneckerWeber (p : ℕ)) :
    GlueDescent.B2Q.LeafSqrtCrit
```

`LeafSqrtCrit` is the statement of `ZInQKernel/HDecomp/Descent/B2Glue.lean` unchanged: for every
prime `p`, Dirichlet character `χ` mod `N` and `u ∈ (ℤ/N)^×` with `u ≡ −1 mod p^k`, `u ≡ 1 mod N/p^k`
(`k = v_p(N)`), `χ ∘ cyc_N ∘ (G_{ℚ_p} → G_ℚ)` has a locally constant square root `G_{ℚ_p} → ℂ^×`
iff `χ(u) = 1`. `PkgI6.LocalKroneckerWeber p` is leaf T16 of `ZInQKernel/HDecomp/Conductor/I6Base.lean`
(finite abelian `L ⊆ \bar ℚ_p` lies in some `ℚ_p(μ_n)`). So the H decomposition's leaf `t30` of
`HSyn` (`scratch/h-decomposition/Leaves.lean`, field `t30`) follows from its field `t16a`, and T30
can be removed from the list of literature theorems. The "if" direction needs no Kronecker–Weber
(`T30.sqrt_of_chi'`).

**G1-adelic: the adelic normalizer quotient and the count of A3, `|Γ'| = 144`.** (VERIFIED,
compiled)

Objects (`Adelic.lean`, namespace `G1Adelic`), over the existing definitions
`GlueVigneras.Bp p = ℍ[ℚ_p, 2, 0, -3]` and `GlueVigneras.Op p` (N5's `𝒪 ⊗ ℤ_p`):

| Lean | Meaning |
| --- | --- |
| `BA := Πʳ p : Nat.Primes, [Bp p, OpSub p]` | `B̂ = B ⊗ 𝔸_f`, Mathlib's restricted product of the `B_p` w.r.t. the subrings `𝒪_p` |
| `Ohat` | `𝒪̂ = ∏_p 𝒪_p ⊆ B̂` |
| `Nhat : Subgroup BAˣ` | `N = {x ∈ B̂^× : x 𝒪̂ x⁻¹ = 𝒪̂}` (the normalizer, defined globally, not componentwise) |
| `K0`, `Zhat`, `K3` | `K₀ = 𝒪̂^×`; `𝔸_f^×` as the central scalars (componentwise in `ℚ_p^×`); `K₃ = {u ∈ K₀ : u_3 ≡ 1 mod 3𝒪_3}` = `ker(K₀ → (𝒪/3𝒪)^×)` |

| Lean theorem | Statement |
| --- | --- |
| `normalizer_component` | `x ∈ N` ⇒ every component `x_p` normalizes `𝒪_p` |
| `mem_sup_iff_forall` | `x ∈ 𝔸_f^× K₀` ⇔ `∀ p, x_p ∈ ℚ_p^× 𝒪_p^×` (the scalars are chosen `1` at the cofinitely many `p` with `x_p ∈ 𝒪_p^×`) |
| `comp_mem_scal_of_unramified` | `x ∈ N`, `p ∤ 6` ⇒ `x_p ∈ ℚ_p^× 𝒪_p^×` (from `GlueVigneras.unramified_normalizer`) |
| `mem_sup_iff` | for `x ∈ N`: `x ∈ 𝔸_f^× K₀` ⇔ `x_2 ∈ ℚ_2^×𝒪_2^×` and `x_3 ∈ ℚ_3^×𝒪_3^×` |
| `Phi`, `ker_Phi`, `Phi_surjective`, `quotEquiv` | `N/(𝔸_f^× K₀) ≃* B_2^×/ℚ_2^×𝒪_2^× × B_3^×/ℚ_3^×𝒪_3^×`, the restricted product of the local quotients (trivial at `p ∤ 6`, order 2 at `2, 3`) |
| `relIndex_eq_four` | `[N : 𝔸_f^× K₀] = 4` |
| `conj_mem_K3`, `sup_K3_normal` | `N` normalizes `K₃`, so `𝔸_f^× K₃` is normal in `N` and `Γ' = N/𝔸_f^×K₃` is a group |
| `gamma_count` | `[N : 𝔸_f^× K₃] = 4 · [K₀ : (𝔸_f^× ∩ K₀) K₃]`, i.e. `|Γ'| = |N/𝔸_f^×K₀| · |K₀/ℤ̂^×K₃|` |
| `Zint`, `Zhat_inf_K0` | `ℤ̂^× = ∏_p ℤ_p^×` (central scalars) and `𝔸_f^× ∩ K₀ = ℤ̂^×` |
| `R3`, `card_units_R3`, `redHom`, `redHom_eq_one_iff`, `redHom_surjective`, `redHom_scalar` | `𝒪/3𝒪` as a monoid (glue-repo's `mul3`), `|(𝒪/3𝒪)^×| = 72`, the reduction `K₀ → (𝒪/3𝒪)^×` is surjective with kernel `K₃`, `ℤ̂^×` maps onto `{±1}` |
| `relIndex_K3` | `[K₀ : ℤ̂^× K₃] = 36` |
| `gamma_order`, `gamma_count_Zint` | **`|Γ'| = [N : 𝔸_f^× K₃] = 4 · 36 = 144 = 2⁴3²`** (h-b1 M3, now a Lean theorem) |

`G1Count.lean` has the count as generic group theory (`G1Count.index_count`: for `K₃ ≤ K₀`, `Z`
normal and `Z K₃` normal, `[G : Z K₃] = [G : Z K₀] · [K₀ : (Z ∩ K₀) K₃]`, with Dedekind's modular
law `sup_inf_eq`); `gamma_count` is its adelic instance.

## 2. T30: the proof as formalized

Notation: `N = p^k N'`, `p ∤ N'`, `χ' = χ ∘ cyc_N ∘ resp_p : G_{ℚ_p} → ℂ^×`.

1. **The decomposition map** (`exists_emb`, `cyc_resp_eq`). Mathlib's
   `Field.absoluteGaloisGroup.map` restricts `σ ∈ Gal(\bar ℚ_p/ℚ_p)` along an embedding
   `g : \bar ℚ → \bar ℚ_p`, so `g(resp σ x) = σ(g x)`. Hence `cyc_N(resp σ) = u` as soon as
   `σ ζ = ζ^u` for all `ζ^N = 1` in `\bar ℚ_p` (`modularCyclotomicCharacter.unique`).
2. **CRT on roots of unity** (`exists_decomp`, `act_crt`, `cyc_resp_eq_u`). If `σ` inverts `μ_{p^k}`
   and fixes `μ_{N'}`, then `cyc_N(resp σ) = u` (Bezout decomposition `z = x y`).
3. **"If"** (`sqrt_of_chi'`, `sqrt_of_inflated`). Let `L = ℚ_p(μ_{p^{k+1}(p^{2f}−1)})`,
   `f = ord_{N'}(p)`. `χ'` is trivial on `Gal(\bar ℚ_p/L)` (`cyc_eq_one_of_restrict`), so it is
   inflated from a character `χ_L` of the abelian group `Gal(L/ℚ_p)`
   (`MonoidHom.liftOfRightInverse`). An element of order `≤ 2` of `Gal(L/ℚ_p)` restricts to `1`
   or `τ₋₁` on `ℚ_p(μ_{p^k N'})` (`restrict_sq_eq_one`, the two-torsion half of
   `GlueSqrtDisj.sqrt_criterion_level`, copied), so `χ_L` kills the two-torsion when `χ(u) = 1`.
   A `ℂ^×`-character of an abelian group killing the two-torsion is a square (`exists_sqrt_iff`:
   `ℂ^×` is divisible, hence an injective `ℤ`-module, `Module.Baer.of_divisible`). The square root
   composed with `G_{ℚ_p} → Gal(L/ℚ_p)` is locally constant (Krull topology, finite `L`).
4. **"Only if"** (`chi_of_sqrt'`). `ker φ` is open, closed and normal; its fixed field `M` is
   finite (`InfiniteGalois.isOpen_iff_finite`), Galois (`normal_iff_isGalois`) and abelian
   (commutators lie in `ker φ` since `ℂ^×` is commutative). T16 gives `M ⊆ ℚ_p(μ_{p^a b})`
   (`GlueSqrtDisj.le_muField_of_lkw`). Take `K = ℚ_p(μ_{p^{k+a} N' b})`, `τ₋₁ ∈ Gal(K/ℚ_p)` and a
   lift `σ ∈ G_{ℚ_p}`. Then `σ²` fixes `K ⊇ M`, so `σ² ∈ ker φ`
   (`InfiniteGalois.fixingSubgroup_fixedField`), and `cyc_N(resp σ) = u` by step 2:
   `χ(u) = χ'(σ) = φ(σ)² = φ(σ²) = 1`.

Kernel pitfall (VERIFIED): `rfl` for
`((algebraMap (muField p a) (muField p b) y : _) : \bar ℚ_p) = y` passes the elaborator but is a
kernel deterministic timeout (the kernel compares the carriers `ℚ_p(μ_a)` and `ℚ_p(μ_b)`); the fix
is `IntermediateField.inclusion` plus `IntermediateField.coe_inclusion` (`coe_algebraMap_mu`).

## 3. G1-adelic: the proof as formalized

- `B̂` is Mathlib's `RestrictedProduct` over `Nat.Primes` of the rings `B_p` w.r.t. the subrings
  `𝒪_p` (`OpSub`: N5's lattice is closed under multiplication, `combp_mul`, the `ℤ_p`-form of
  glue-repo's `combMul`). This is the standard description of `B ⊗_ℚ 𝔸_f` (STANDARD: `B` has the
  `ℤ[1/6]`-basis of N5's order, so `B ⊗ 𝔸_f = ∏'(B_p, 𝒪_p)`); its identification with
  `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, -3]` over Mathlib's `FiniteAdeleRing` is not formalized (Mathlib's
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` would give it componentwise).
- `normalizer_component`: test `x 𝒪̂ x⁻¹ = 𝒪̂` on the element with component `y` at `p` and `0`
  elsewhere (`RestrictedProduct.single`).
- `mem_sup_of_forall`: if every `x_p = c_p u_p` (`c_p ∈ ℚ_p^×`, `u_p ∈ 𝒪_p^×`), choose `c_p = 1`
  where `x_p ∈ 𝒪_p^×` (cofinitely many `p`, since `x, x⁻¹ ∈ B̂`); then `c = (c_p)` is an idele
  and `c⁻¹ x ∈ 𝒪̂^×`.
- `Phi_surjective`: the units with component a uniformizer (`i` at 2, `j` at 3,
  `GlueVigneras.exists_pi`) and `1` elsewhere lie in `N` (`normalizerOp_eq_univ`) and map to the
  generators.
- `gamma_count`: `relIndex_mul_relIndex` and `relIndex_sup_right` inside the group `N` (where
  `𝔸_f^× K₃` is normal), and the modular law.
- `relIndex_K3`: `redHom u` is the reduction mod 3 of the N5-coordinates of `u_3`
  (`PadicInt.toZMod` composed with `ZMod.ringEquivCongr`); multiplicative by `combp_mul`; kernel
  `K₃` because `ker toZMod = (3)`; surjective because a lift `x` of a unit of `𝒪/3𝒪` has
  `nrd x ≡ nrd3 ≠ 0 mod 3`, so `‖nrd x‖ = 1` and `x ∈ 𝒪_3^×` (`mem_OpUnits_iff`), placed at the
  component `3` (`unitSingle`). `(𝔸_f^×∩K₀) K₃` is the preimage of `{±1}` (scalars `c ∈ ℤ_3^×`
  reduce to `c mod 3 ∈ {±1}`; `−1` is a scalar), so the index is `72/2`
  (`Subgroup.index_comap_of_surjective`, `index_mul_card`).

Pitfalls (VERIFIED): `ZMod ((P3 : Nat.Primes) : ℕ)` is not reducibly `ZMod 3`; making `P3` an
`abbrev` breaks instance lookup for the local quotient (`Hloc P3 _`), so the reduction goes
through `ZMod.ringEquivCongr rfl`; the type synonym `R3` with its own `Monoid` must stay a `def`,
with an identity `R3.mk` so that rewriting keeps terms well-typed.

## 4. What remains

- The identification of `B̂` (restricted product of the `B_p`) with `ℍ[𝔸ᶠ[ℤ, ℚ], 2, 0, −3]` over
  Mathlib's `FiniteAdeleRing` (and of `Zhat` with `𝔸ᶠ[ℤ, ℚ]^×`) is not formalized; it is a
  reindexing (`Rat.HeightOneSpectrum.primesEquiv`), the componentwise isomorphisms
  `Padic.adicCompletionEquiv`, `PadicInt.adicCompletionIntegersEquiv`, and the remark that
  `𝒪_p = ℤ_p⟨1, i, j, k⟩` for `p ≠ 2`.
- The other parts of A3 (the Hecke action of `Γ'` on `Y₃` over `ℚ`, quotient `P¹_j`, `deg ≤ |Γ'|`)
  are outside this task.
- Integration: `T30.leafSqrtCrit_of_localKroneckerWeber` can replace the hypothesis `t30` of
  `HSyn` (it needs only `t16a`); `G1Adelic` imports only `ZInQKernel.HDecomp.Vigneras.Local`.

## 5. Changes to classifications

- h-decomposition T30 (`GlueDescent.B2Q.LeafSqrtCrit`): LEAF → **GLUE-proved from T16**
  (`PkgI6.LocalKroneckerWeber`). The literature list loses T30.
- G1 "adelic bookkeeping open" → **proved**: `N/(𝔸_f^×K₀)` ≅ the restricted product of the local
  quotients (order 4), `|K₀/ℤ̂^×K₃| = 36`, and `|Γ'| = 144` (h-b1 M3: VERIFIED by script before,
  now a Lean theorem, `G1Adelic.gamma_order`).
