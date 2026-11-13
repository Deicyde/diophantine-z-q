# leaf-modcurves (fleet report, 2026-11-12, final)

**Main result.** The opaque placeholder R16 (Eichler–Shimura in `J₁(N)`) is replaced by a concrete
Lean statement, `LeafModCurves.R16_EichlerShimuraJ1'`, in existential form. It is stated over
genuine definitions only: Mathlib, the kernel's `PkgI3.AbVar`/`V_ℓ`/`galRep` and the kernel's
`GlueC10.IsFrobAt`.
- **The statement.** For a weight-2 newform `f` of level `N` and any `J₁(N)`: `K_f` is a number
  field, and there are `A/ℚ`, a surjection `J ↠ A`, `θ : K_f → End⁰(A)` and `dim A = [K_f:ℚ]`.
  For every `ℓ` and every `ι : K_f → ℚ̄_ℓ`, the `ι`-component of `V_ℓ(A)` has dimension 2, with
  arithmetic Frobenius trace `ι(a_p)` and determinant `ι(χ(p))p` for `p ∤ Nℓ`.
- **Sources.** It follows from Shimura 1973 Thm 1 (**unconditional clauses only**; the
  Fricke/`Γ₀` condition belongs to the zeta clause, which is not used), rank-2 freeness of
  `V_ℓ(A_f)`, and the printed characteristic polynomial of Frobenius (Diamond–Shurman 9.5.4 /
  Shimura 7.11, UNVERIFIED numbers).

**Definitions.**
- `X₁(N)/ℚ`: `IsX1Model N X` means a smooth proper geometrically connected integral curve whose
  function field is isomorphic to `K_N = ℚ(j)(x(P))`, with `P` of exact order `N` on Mathlib's
  `E_j`.
- `J₁(N)`: the Albanese predicate `IsJacobian` over `PkgI3.AbVar`, and `IsJ1 N J`.

**New leaves:** `JacobianExists` (Weil/Milne), `R16_EichlerShimuraJ1'`, and `DimJ1Genus`
(`dim J₁(N)` = the genus formula of `Γ₁(N)`).

**New glue targets:** `X1ModelExists` (it may also be taken as a leaf), `BelyiX1` (`j/1728` is a
Belyi function of degree `≤ N²`, over the new `IsBelyiFunction`), and `VSurjOfSurjective`.

**Proved glue:**
- `IsJacobian.unique`.
- `dim_J1_le` and `exists_J1_dim_le`: E2's `g = dim J₁(N) ≤ N²`.
- `exists_J1`, `exists_J1_quotient`.
- `dualAct_mem`, and `rhoF`, a genuine `Representation` of `G_ℚ`.
- `rhoF_traces`: exactly C10's hypothesis `hρ₅`.
- `isFrobAt_of_isArithFrob`.
- `g13_constituent`: G13, a 2-dimensional `G_ℚ`-stable quotient of `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` with
  traces `ι(a_p)`.
- `rhoF_attached`: R16's `ρ_{f,ι}` satisfies the `AttachedTo` trace clause of `Leaves.lean` via
  `ι = ιL ∘ ιC⁻¹`.

An independent model review found no leaf that is false, over-strong or vacuous. Its one
sourcing finding (the congruence relation alone does not give the characteristic polynomial) is
applied.

**What compiles.** `scratch/leaf-modcurves/ModCurveLeaves.lean` (1025 lines; imports
`ZInQKernel.HDecomp.Objects` and `ZInQKernel.HDecomp.C10.C10`). `lake env lean`: exit 0, no
errors, no warnings, no `sorry`. Every `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound`. VERIFIED.

**What remains** (details in `docs/research/leaf-modcurves.md` §5):
- **C9:** semisimplicity and continuity of `rhoF` (medium), then Brauer–Nesbitt against R14's
  representation and C8's `r₅`.
- **E1:** `ρ_{f,ι}` as a *sub*representation of `V_ℓ(J₁(N)_{L'}) ⊗ E`. This needs T8 or Faltings'
  semisimplicity, `VSurjOfSurjective`, and `V_ℓ` under base change to `L'` (medium).
- **E2:** `2 ≤ g` (from E1). `h_F(J₁(N)) ≤ 1.3·10⁷N¹²` needs R18, which is blocked on the
  Faltings height (WP10). Its Belyi input is the glue target `BelyiX1` (large, bp-modcurves MC5).
- **Existence:** `X1ModelExists` (MC4 + MC10, or a leaf) must be consumed by the main theorem.
- **Integration:** replace `R16_EichlerShimuraJ1` in `Leaves.lean`'s `ResearchLeaves`, and add
  `JacobianExists ℚ`, `X1ModelExists`, `DimJ1Genus`.
- **Citations:** the locators of the rank-2 result, the characteristic polynomial, MC9
  (`ℤ/N` ≅ `μ_N` model) and Shimura Prop. 1.40 are UNVERIFIED (no network).
