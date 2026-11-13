# kf-glue results log

Base: wip/integrate-w38b (f90cf864) + merges of origin/wip/kernel-field, origin/wip/mul-rigidity.

## Step 1. EndTransport (medium)
- `scratch/kf-glue/KfGlue.lean` = `assemble.sh` output: KernelField.lean (verbatim, one porting fix in a
  proof term: `hR1.2.2.2` -> `hR1.2.2.2.1`, since R1fpProps has 6 clauses on this base) + MulRigidity.lean
  lines 3-182 (verbatim) + `scratch/kf-glue/New.lean`.
- `theorem G0ModField.KernelField.endTransport : EndTransport` (no hypotheses) =
  `endTransport_of (endTransportBC_of_rigidity rigidityHom)`.
- `kernelFieldExists_of_five`: KernelFieldExists from HomFreeFinite, NOS, Raynaud, TorsionStructure,
  QMDichotomyYu, FS5, ConjIsogMaps.
- VERIFIED (compiled, `lake env lean`, rc=0, build1.txt): both axioms [propext, Classical.choice, Quot.sound].

## Step 2. ConjIsogMaps level 1 (points bookkeeping) — VERIFIED (compiled, build2.txt, rc=0)
- New Props (New.lean part 2): `LiftQbarPoints` (finite surjective ⇒ surjective on ℚ̄-points; glue),
  `FiniteFibreQbarPoints` (finite ⇒ finite fibres on ℚ̄-points; glue), `SemilinearIsogAt` / `SemilinearIsogMaps`
  (σ-semilinear finite surjective scheme endomorphisms F_σ of A_L over Spec(σ⁻¹|_L), respecting μ and ι(𝒪),
  F_k = id on G_L and constant on G_L-cosets, F_τ ≫ F_σ ≫ [e] = F_{στ} ≫ δ, δ ∈ End_L; geometric glue).
- `conjIsogMapsAt_of_semilinear`, `conjIsogMaps_of_semilinear : LiftQbarPoints → FiniteFibreQbarPoints →
  SemilinearIsogMaps → ConjIsogMaps`; axioms [propext, Classical.choice, Quot.sound].
- m_σ(x) = Spec σ ≫ x ≫ F_σ (`semHom`); additivity from the scheme-level group-law clause.

## Step 3. The two point lemmas proved from Mathlib — VERIFIED (compiled, build3.txt, rc=0)
- `scratch/kf-glue/Points.lean` (Mathlib only; also compiles alone): `exists_section` (nonempty finite
  scheme over Spec ℚ̄ has a section: maximal quotient of B = Γ(P) is ℚ̄ by `IsAlgClosed.ringHom_bijective_of_isIntegral`),
  `finite_sections` (sections ↪ B →ₐ[ℚ̄] ℚ̄, finite by `Finite.algHom`), `liftQbar`, `finiteFibreQbar`
  (via `pullback F y`).
- `liftQbarPoints : LiftQbarPoints`, `finiteFibreQbarPoints : FiniteFibreQbarPoints`,
  `conjIsogMaps_of_semilinearIsogMaps : SemilinearIsogMaps → ConjIsogMaps`,
  `kernelFieldExists_of_semilinear` (5 leaves + FS5 + SemilinearIsogMaps). All axioms standard.
- Finding (VERIFIED by reading Mathlib 4.35 `Sites/Fpqc.lean` L88-130): fpqc topology is subcanonical and
  qc surjective flat morphisms are `EffectiveEpi`; so Galois descent of morphisms along Spec L' → Spec L is
  Mathlib-derivable glue, not a literature leaf.

## Step 4. Level 2: SemilinearIsogMaps ⇐ SemilinearTwistIsos + MulIsogeny (+ RigidityHom, proved) — VERIFIED (compiled, build4.txt, rc=0)
- New Props: `SemilinearTwistAt` / `SemilinearTwistIsos` (σ-semilinear scheme automorphisms E_σ of A_L over
  Spec(σ⁻¹|_L), preserving μ and η, ι(a) E_σ = E_σ ι(α_σ a) for α_σ ∈ Aut 𝒪, E = id / α = id on G_L,
  coset-constant). `G0FibreSimple.MulIsogeny` copied verbatim (MulRigidity.lean L321-323).
- Proved: `exists_b` (Skolem–Noether linear form: b α(a) = a b, b ≠ 0), `exists_quasi_inv` (c b = N = b c),
  `iota_isogeny` (ι(b) finite & surjective from MulIsogeny via ι(c)ι(b) = [N]), `semilinearIsogAt_of_twist`
  (F_σ = E_σ ≫ ι(b_σ); discrepancy δ = ι(b_σ) ι(α_σ b_ρ) D ι(c), D = E_{σρ}⁻¹ E_ρ E_σ ∈ End_L via rigidityHom),
  `semilinearIsogMaps_of_twist`, `conjIsogMaps_of_twist : MulIsogeny → SemilinearTwistIsos → ConjIsogMaps`,
  `kernelFieldExists_of_twist`. All axioms standard.
- Finding: the quasi-inverse needs no leaf (Mumford §8 / IsogenyQuasiInverse not used): ι(N b⁻¹).

## Step 5. Level 3: SemilinearTwistIsos ⇐ TwistDescent (A7 on conjugates proved) — VERIFIED (compiled, build5.txt, rc=0)
- New: `bcEnd` (base change of End B to conjugate B_e), `TwistDescent` (Prop, glue, no moduli content:
  Hom field + pairwise twisted isos between conjugates over ℚ̄ ⇒ SemilinearTwistAt on B_L).
- Proved: `bc_transport` (IsBaseChangeOf e PK Q ⇒ B_e ≅ Q.A as AbVar with 𝒪-action; pasting + rigidityHom),
  `conjTwist_of_rational` (A7 manuscript form `conj_iso_of_rational` + transport ⇒ the hypothesis of
  TwistDescent for PK), `semilinearTwistIsos_of_descent` (π(yK) = j₀ in K from Φ injective + val_comp),
  `conjIsogMaps_of_descent : MulIsogeny → TwistDescent → ConjIsogMaps`, `kernelFieldExists_of_descent`.
  All axioms standard.

## Step 6. MulIsogeny's reductions included — VERIFIED (compiled, build6.txt, rc=0, no sorry)
- Assembly now includes MulRigidity.lean L205-604 verbatim (Mul.lean body; my MulIsogeny copy removed).
- `conjIsogMaps_of_kerUnitOpen : KerUnitOpen → TwistDescent → ConjIsogMaps`,
  `conjIsogMaps_of_cotangent : KerUnitOpenOfCotangentSurj → CotangentMulN → TwistDescent → ConjIsogMaps`,
  `kernelFieldExists_of_kerUnitOpen` (6 leaves: T6, NOS, Raynaud, TorsionStructure, T27, KerUnitOpen; glue: FS5, TwistDescent).
