# twist-descent results log

Base: fork main 57a7fa26 + merge of origin/wip/kf-glue.

## Step 0. Truth of `TwistDescent` (kf-glue, New.lean L685-698)
- Decision: TRUE as stated (argument below; VERIFIED by the compiled proof once complete).
  For σ ∈ G_ℚ: the hypothesis gives a twisted iso φ : B_{e₀} ≅ B_{σ⁻¹e₀} over ℚ̄ (e₀ = K ↪ ℚ̄);
  Ē_σ = φ ≫ cmp_{σ⁻¹} is σ⁻¹-semilinear on B_{e₀} = (B_L)_{ℚ̄}; it descends to B_L because
  L is a Hom field (φ is fixed by G_L-conjugation). E_σ, α_σ depend only on σ|_L (coset constancy),
  with E = 𝟙, α = id on the trivial coset; α_σ := α_hyp⁻¹ matches the direction of the ι-clause.

## Step 1. Galois descent of morphisms from Mathlib — VERIFIED (compiled, `lake build`)
- `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean` (Mathlib only), namespace `TwistDescentGD`:
  `exists_open_gal` (u v : Z → Spec k' agreeing over Spec k, k'/k finite Galois ⇒ locally
  v = u ≫ Spec g; primitive element + `Algebra.IsInvariant.charpoly_mem_lifts`),
  `descend` (Galois-invariant f : X' → Y factors through X' = X ×_k k' → X; EffectiveEpi from
  Mathlib `Sites/Fpqc.lean` + `Scheme.hom_ext_of_forall`), `epi_of_isPullback_field`,
  `effectiveEpi_of_isPullback_field` (any field extension).

## Step 2. `TwistDescent` proved (dev loop against a /tmp olean of KfGlue.lean) — VERIFIED (compiled)
- Parts: `scratch/twist-descent/PartXC.lean` (generic `xc` comparisons between base changes
  along different bases: pullback square, composition, `xc_map`, `xc_one`, `xc_mul`),
  `PartHFD.lean` (`TwistDescentHFD.hfd`: a G_L-invariant ℚ̄-morphism B_{e₁} → B_{e₂} between
  conjugates is the base change of an L-morphism; EGA IV 8.8.2 `MorphDescend.exists_descend` to
  finite L₁, normal closure L', then `TwistDescentGD.descend` along L'/L),
  `PartMain.lean` (`td_hom_inv`: conjAction trivial on G_L ⇒ k∘φ = φ∘k; `td_construct`:
  E = φ_L ≫ c_τ, φ_L a homomorphism by `G0FibreSimple.rigidityHom`; `twistDescent`).
- `#print axioms G0ModField.KernelField.twistDescent`: [propext, Classical.choice, Quot.sound].

## Step 3. Single-file check — VERIFIED (compiled)
- `scratch/twist-descent/assemble.sh` → `scratch/twist-descent/TwistDescent.lean` (7882 lines):
  `scratch/kf-glue/KfGlue.lean` verbatim (one import line added:
  `ZInQKernel.Contrib.TwistDescent.GaloisDescent`) + PartXC + PartHFD + PartMain + PartFinal.
- `lake env lean scratch/twist-descent/TwistDescent.lean`: rc=0, no error, no sorry, 1m19s wall
  (`build1.txt`). All 13 new `#print axioms`: [propext, Classical.choice, Quot.sound].
- Verbatim (`verbatim_check.py`, output `verbatim_check_out.txt`): KfGlue body verbatim; New.lean
  verbatim in KfGlue; `TwistDescent`, `SemilinearTwistAt`, `bcEnd` blocks equal to the owner text
  in New.lean, each defined once.
- Corollaries (PartFinal): `conjIsogMaps_of_mulIsogeny : MulIsogeny → ConjIsogMaps`,
  `conjIsogMaps_of_kerUnitOpen'`, `conjIsogMaps_of_cotangent'`,
  `kernelFieldExists_of_kerUnitOpen'` (T6, NOS, Raynaud, TorsionStructure, T27, FS5, KerUnitOpen),
  `kernelFieldExists_of_mulIsogeny`.

## Step 4. `GaloisDescentMor` (kf-glue's standard statement, New.lean, unused there) proved — VERIFIED (compiled)
- `hfd` generalized to arbitrary `X` (qc, qs) and `Y` (lfp) over `K` (was `B.X` twice).
- `scratch/twist-descent/PartGDM.lean`: `theorem galoisDescentMor : GaloisDescentMor` (hfd with
  K = L, e₁L = e₂L = id, X ×_{L,id} L ≅ X; uniqueness from `X_{ℚ̄} → X` epi).
- Full single-file check `build3.txt`: rc=0, no error, no sorry; all new `#print axioms`
  [propext, Classical.choice, Quot.sound]. `verbatim_check_out.txt`: `GaloisDescentMor` block equal to
  the owner text, defined once.
