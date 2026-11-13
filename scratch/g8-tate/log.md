# g8-tate results log

## Step 0 (2026-11-13 09:28-09:45 PST): setup
- Fresh start (no earlier log). Merged origin/wip/alg-frob-red (94799bde) into wip/g8-tate.
- `lake build ZInQKernel.Main` (5m16s; needed for the upstream `ZInQ.*` helper modules: without
  it `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` fails with "unknown module prefix 'ZInQ'").
- Read: g8-object report/part_split (OnL, WildTateTrivial, LinkedTateObjS, G7Data lacks [L:ℚ] ≤ D),
  frob-trace report/part_frob (TateBridge35 from I3.M0 + AlgFrobLink; operators
  `Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, scalars `aQ g = βQ g / γQ(hgh⁻¹)`), alg-frob-red report
  (AlgFrobRed from GoodRedCofinite, SmoothGeomConnIntegral, I2-Red, FExtendGen, AbsFrob).

## Plan (Lean)
- `TateBridge35OnL`: TateBridge35's conclusion plus `ψ₅, ψ₃` and `G8Object.OnL` for frob-trace's
  operators. Math: for σL ∈ G_L, g = resQ L σL ∈ G_L. Λ = trPt κ : A(L̄) ≅ A(ℚ̄) (κ : L̄ ≃ₐ[L] ℚ̄),
  t = κ ∘ g_L ∈ G_ℚ (g_L the embedding of resQ), so Λ ∘ σL = m_{tgt⁻¹} ∘ Λ. X = Θ ∘ m_{ht⁻¹} ∘ Λ
  (isogeny-level; quasi-inverse Λ⁻¹ ∘ m_{th⁻¹} ∘ Θ⁻¹ by the cocycle clause and m₁ = id).
  m_{hgh⁻¹} m_{ht⁻¹} = m_{hgt⁻¹} = m_{ht⁻¹} m_{tgt⁻¹} (coset clauses of DescentDatum).
  ψ⁻¹ = ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(X) (bijective). Scalar clause: aQ = 1 on G_L since a = 1 on G_L and
  β(hgh⁻¹) = β(g) (ε trivial when one argument is in G_L).

## Step 1 (09:45-10:05 PST): `onL_exists` (VERIFIED)
- `scratch/g8-tate/build_dev.sh` assembles `Dev.lean` = alg-frob-red's `AlgFrobRed.lean` verbatim
  (inside `section AlgFrobRedCopy`, one `end` added to close the anonymous section the copy leaves
  open, so that ModField's file-level opens do not leak; 3 extra imports) + g0-mod-galois'
  `part_galois.lean` L27-152 verbatim + g8-object's `part_split.lean` L48-59 (`OnL`) verbatim with
  part_split's opens + `part_onl.lean`.
- New: `G8Tate.Wb`, `opW` (ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(f) for f : M →+ N), `opW_comp`, `opW_id`, `opW_add`,
  `opWHom`, `opW_zsmul`, `opW_bijective` (quasi-inverse on both sides ⇒ bijective),
  **`onL_exists`**: for `m` with DescentDatum's G_L-, coset- and n/d-clauses, any `Θ`, `h`, ℓ:
  ∃ ψ : Vb(A') ≃ Vb(A), ∀ σL, opV A' ℓ (conjE Θ (m (h * resQ L σL * h⁻¹))) = ψ⁻¹ ∘ tate A ℓ σL ∘ ψ.
- Compile: `lake env lean scratch/g8-tate/Dev.lean` exit 0, 2m27s; axioms of `opW_bijective`,
  `onL_exists`: [propext, Classical.choice, Quot.sound].
- Pitfalls: `m (h * g * h⁻¹)` with `h : PkgI4.GQ` multiplies in `PkgI4.GQ`; rewriting with
  `hmLL` (multiplication in `GQ`) needs `let k : GQ := h * g * h⁻¹` and `show … ; group`.
  The group law on `A.Pt Qbar` needs `open … MonObj`.

## Step 2 (10:05-10:20 PST): `TateBridge35OnL` (VERIFIED)
- New (part_onl.lean): `TateBridge35OnL` (TateBridge35's text + witnesses ψ₅, ψ₃ + conjuncts
  `G8Object.OnL L A Tm₅ (j₅ ∘ aQ) ψ₅`, `G8Object.OnL L A Tm₃ (j₃ ∘ aQ) ψ₃`),
  `tateBridge35_of_onL : TateBridge35OnL → G14Bridge.TateBridge35`,
  `scalarsQbarC` (frob-trace's `scalarsQbar` + `ιC ∘ γQ = β/a`),
  **`tateBridge35OnL_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : FrobTrace.AlgFrobLink)`**
  (frob-trace's proof copied + `onL_exists` + `aQ = 1` on G_L via `inflatedNormalized_of`),
  `tateBridge35OnL_of_algFrobRed`, **`tateBridge35OnL_of_gen`** (I3.M0 + alg-frob-red's five inputs).
- Compile: `Dev.lean` exit 0, 2m25s; all 7 new axiom prints [propext, Classical.choice, Quot.sound].
