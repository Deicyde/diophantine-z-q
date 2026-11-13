# x1-dirichlet: `DirichletOfFinite` and `X1ModelExists` for g0-mod-newform

Task x1-dirichlet, 2026-11-13. Lean: `scratch/x1-dirichlet/Dirichlet.lean` (standalone, imports
only `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`) and `scratch/x1-dirichlet/Connect.lean`
(assembled by `scratch/x1-dirichlet/build.sh` from a verbatim copy of
`scratch/g0-mod-newform/NewForm.lean`, the body of `Dirichlet.lean` and
`scratch/x1-dirichlet/part_connect.lean`). Log: `scratch/x1-dirichlet/log.md`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

Both glue Props that g0-mod-newform left open are **proved**. Neither statement was changed.

1. **`DirichletOfFinite` is proved from the leaf T17** in its narrowed form
   `TSkolemKW.KW.KroneckerWeberCyclic` (the field `t17` of `TextbookLeaves`), through the
   kernel's C8 glue `TSkolemKW.KW.dirichletCharacter_of_kroneckerWeberCyclic`:

   ```
   theorem X1Dirichlet.dirichletOfFinite_of_kroneckerWeberCyclic
       (hKW : KroneckerWeberCyclic) : DirichletOfFinite
   ```

   VERIFIED: `lake env lean scratch/x1-dirichlet/Dirichlet.lean` exits 0 with no error and no
   `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `cycChar_frob` and
   `dirichletOfFinite_of_kroneckerWeberCyclic`. The `def DirichletOfFinite` block (docstring
   and body) is byte-identical to `scratch/g0-mod-newform/part_new.lean` lines 727-738 (VERIFIED
   by `diff`). `Connect.lean` also checks `G0ModNewform.DirichletOfFinite ↔
   X1Dirichlet.DirichletOfFinite` by `Iff.rfl`.

2. **`X1ModelExists` needed no new proof, only a connection.** The `X1ModelExists` that
   g0-mod-newform takes as `hX` in `g16Out_with_J1`, `modularConstituent_tail` and
   `modularConstituent_tail_G` is `LeafModCurves.X1ModelExists`. `NewForm.lean` defines no
   `X1ModelExists` of its own and opens `LeafModCurves` (VERIFIED by grep). x1-belyi proved
   exactly that Prop in the kernel: `X1Belyi.x1ModelExists_of_leaves` and
   `X1Belyi.x1ModelExists_and_belyiX1 (L : X1Leaves)`, in
   `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean`. Its leaves T36 `TorsionStructure`,
   T38 `CurveOfFunctionFieldQ`, T39 `X1ConstantField` and T40 `X1RationalCusp` are the field
   `x1 : X1Belyi.X1Leaves` of `TextbookLeaves`. `Connect.lean` restates g0-mod-newform's
   theorems with these hypotheses discharged (§3).

## 2. The proof of `DirichletOfFinite`

The statement (verbatim, namespace `G0ModNewform` in g0-mod-newform): for every prime `ℓ`, every
continuous character `ψ : G_ℚ → ℚ̄_ℓ^×` (`PkgI4.GaloisChar ℓ`) of finite image and all embeddings
`ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`, there are `m > 0`, a Dirichlet character `ψD` mod `m` over `ℂ`
and a finite set `S` of primes, such that for every prime `p ∉ S` some `β ∈ ℚ̄` has
`ιC β = ψD(p)` and `ψ(τ) = ιL β` for every arithmetic Frobenius `τ` (`PkgI4.IsArithFrob τ v p`)
at every place `v` above `p` (`PkgI4.LiesOver v p`).

Steps, all compiled (VERIFIED):

- **Open kernel.** `ψ` is continuous with finite image, so its kernel is open (the kernel's
  `isOpen_ker_of_continuous`; Mathlib supplies the `T1Space` instance on `(ℚ̄_ℓ)ˣ`).
- **T17 ⇒ factorization through the cyclotomic character.** By the kernel's
  `dirichletCharacter_of_kroneckerWeberCyclic` there are `m : ℕ+` and `χ : DirichletCharacter ℚ̄_ℓ m`
  with `ψ(σ) = χ(cyc_m(σ))` for all `σ`, where `cyc_m` is Mathlib's mod-`m` cyclotomic character.
- **Values come from `ℚ̄`** (`exists_preimage_of_pow_eq_one`). On units, `χ(u)^N = 1` with
  `N = #(ℤ/m)ˣ`. `ιL` maps a primitive `N`-th root of unity of `ℚ̄` to a primitive `N`-th root of
  unity of `ℚ̄_ℓ`, whose powers are all the `N`-th roots of unity. So `χ(u) = ιL(β(u))` for a unique
  `β(u)`. Injectivity of `ιL` makes `β` multiplicative, which gives
  `χQ : (ℤ/m)ˣ →* ℚ̄ˣ`. Then `ψD := MulChar.ofUnitHom (ιC ∘ χQ)`.
- **Frobenius has cyclotomic character `p`** (`cycChar_frob`). Take `p ∤ m`, a place `v` with
  `v(p) < 1`, an arithmetic Frobenius `τ`, and a primitive `m`-th root of unity `ζ`, so that
  `τζ = ζ^a` with `a = cyc_m(τ)`. Since `v(ζ) = 1`, Frobenius gives `v(ζ^a − ζ^p) < 1`.
  Suppose `ζ^a ≠ ζ^p`, and put `η = ζ^a/ζ^p ≠ 1`. Then `η^m = 1` and `v(η − 1) < 1`, and
  `Σ_{i<m} η^i = 0`. Each term of `m = Σ_{i<m}(1 − η^i)` has valuation `< 1`, so `v(m) < 1`.
  Together with `v(p) < 1` and Bézout `1 = pA + mB`, this gives `v(1) < 1`, a contradiction. So
  `ζ^a = ζ^p`, hence `a ≡ p (mod m)`.
- **Assembly.** Take `S = primeFactors(m)`. For `p ∉ S`, let `u = p mod m` (a unit) and
  `β = β(u)`. Then `ιC β = ψD(p)` holds by construction, and
  `ψ(τ) = χ(cyc_m τ) = χ(u) = ιL β`.

The only leaf used is T17 (Kronecker–Weber for cyclic `L/ℚ`; Washington, *Introduction to
cyclotomic fields*, Thm 14.1, UNVERIFIED number). That is a consequence of the published
theorem, as the kernel proves (`kroneckerWeberCyclic_of_kroneckerWeber`).

## 3. Connection theorems (`Connect.lean`)

In namespace `X1DirichletConnect`, over g0-mod-newform's own declarations:

| theorem | statement |
|---|---|
| `dirichletOfFinite_iff` | `G0ModNewform.DirichletOfFinite ↔ X1Dirichlet.DirichletOfFinite` (`Iff.rfl`) |
| `g0_dirichletOfFinite` | `KroneckerWeberCyclic → G0ModNewform.DirichletOfFinite` |
| `g0_x1ModelExists` | `X1Belyi.X1Leaves → LeafModCurves.X1ModelExists` |
| `panOutput_of_G12Out_kw` | `panOutput_of_G12Out` with `hDF` replaced by `hKW` |
| `g12Spec_of_galois_kw` | `g12Spec_of_galois` with `hDF` replaced by `hKW` |
| `g16Out_with_J1_leaves` | `g16Out_with_J1` with `hX` replaced by `x1 : X1Leaves` |
| `modularConstituent_tail_leaves` | `modularConstituent_tail` with `hX` replaced by `x1` |
| `modularConstituent_tail_G_leaves` | `modularConstituent_tail_G` (g0-mod-newform's headline) with `hX` replaced by `x1` |

VERIFIED: `lake env lean scratch/x1-dirichlet/Connect.lean` exits 0 with no error and no
`sorry` (output: `scratch/x1-dirichlet/compile.out`). Each of the ten declarations printed
(the eight above, `cycChar_frob` and `dirichletOfFinite_of_kroneckerWeberCyclic`) depends only on
`[propext, Classical.choice, Quot.sound]`.

The headline in its new form:

```
theorem X1DirichletConnect.modularConstituent_tail_G_leaves (lv : NewformLeaves)
    (hJac : JacobianExists ℚ) (x1 : X1Belyi.X1Leaves)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧ G15RamG D u) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L)
```

After this task, g0-mod-newform's open glue Props are G14TraceCompat, G15RamG (clauses (i)-(ii)),
SwanIndependent, SwanIntegral and AdaptedExists. `DirichletOfFinite` and `X1ModelExists` are now
closed.

## 4. Integration notes

- `Dirichlet.lean` needs only `ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`. It can be adopted
  as a kernel module, e.g. `ZInQKernel/HDecomp/Textbook/DirichletOfFinite.lean`. Its
  `DirichletOfFinite` should then replace the copy in g0-mod-newform's section, or the two should
  be identified by `Iff.rfl` as here.
- In the leaf bundle, `t.t17` supplies `hKW` and `t.x1` supplies `X1Leaves`.

## 5. Compile record (VERIFIED)

- `lake build ZInQKernel.HDecomp.Textbook.KroneckerWeberUse`: success.
- `lake env lean scratch/x1-dirichlet/Dirichlet.lean`: exit 0 (second run, after fixing Mathlib
  names), 2 standard-axiom prints.
- `lake build` of NewForm's imports and `ZInQKernel.HDecomp.ModCurves.X1Belyi`: success.
- `lake env lean scratch/x1-dirichlet/Connect.lean`: exit 0 (first run), 10 standard-axiom prints.

Details: `scratch/x1-dirichlet/log.md`.

## 6. Caveats

- `Connect.lean` contains a copy of g0-mod-newform's `NewForm.lean` as of base 2dd83306. If that
  file changes, `build.sh` has to be rerun after copying the new version over `newform_src.lean`.
- No theorem number above was checked against a source. The leaves' own locators are those
  recorded by t-skolem-kw and x1-belyi.
