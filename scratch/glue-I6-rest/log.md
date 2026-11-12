# glue-I6-rest results log

## I6Base.lean (pkg-I6's I6.lean copied, plus glue)
- Copied scratch/pkg-I6/I6.lean. `artinConductor_le_of_upper` (sorry in pkg-I6) turned into an
  open statement `def ArtinConductorLeOfUpper : Prop` (no sorry in the file).
- `exists_sq_eq_one_add` adopted verbatim from scratch/glue-conductor/Dyadic.lean.
- PROVED `sq_principalUnits` (D3) from it with s = r − e.
- PROVED `finrank_splittingField_le_factorial`: f separable ⇒ [SplittingField f : K] ≤ (deg f)!
  (Gal f ↪ Perm(rootSet), #rootSet ≤ deg f).
- PROVED `finrank_isSplittingField_le_factorial` (any splitting field).
- PROVED `ramificationIdx_le_finrank_of_numberField`: P.ramificationIdx ℤ ≤ [L:ℚ]
  (Mathlib `sum_ramification_inertia_eq_finrank`, `inertiaDeg_pos`; P = ⊥ case separately).
- PROVED `ramificationIdx_le_factorial`: L splitting field over ℚ of separable f ⇒
  e(P) ≤ (deg f)!, the hypothesis `hea` of glue-conductor's `D1_genuine`.
- Compile 22:28: `lake env lean scratch/glue-I6-rest/I6Base.lean`, no errors; all #print axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED).

## SqrtChar.lean
- PROVED `GlueI6Rest.exists_half_iff`: for any abelian group Γ and χ : Γ →+ ℚ/ℤ
  (`AddCircle (1:ℚ)`), (∃ ψ, ∀ g, 2•ψ g = χ g) ↔ χ kills Γ[2]. Via Baer injectivity of ℚ/ℤ
  (`CharacterModule.dual_surjective_of_injective`). Group-theoretic core of B2's criterion.
- Compile 22:31: no errors; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).

## Cyclic inflation, step (b)
- carry_f(a mod f, b mod f) ≡ h(a)+h(b)−h(a+b mod 2f) (mod 2), h(a)=⌊a/f⌋, a,b∈[0,2f):
  brute-force python check f=1..12, all pairs: True (VERIFIED, 22:4x).

## Conductor.lean (D4)
- pkg-I6 Part II definitions copied verbatim (lowerRam, lowerRamR, herbrandPhi, upperRam,
  codimInv, artinConductor).
- PROVED `PkgI6.artinConductor_le_of_upper`, pkg-I6's statement with fewer hypotheses
  (only `[Finite (B ≃ₐ[A] B)]`, `[IsLocalRing B]`, `[FiniteDimensional k V]`; no IsDomain/DVR):
  if ρ σ = 1 for σ ∈ upperRam v, all v > U ≥ 0, then f(V) ≤ dim V·(1+U).
  Lemmas: `lowerRamR_anti`, `hInt_anti` (integrand antitone ⇒ interval integrable),
  `phi_sub_ge` ((u'−u)h(u') ≤ φ(u')−φ(u)), `phi_strictMono`, `upperRam_phi_nat`
  (G^{φ(b)} = G_b via IsLeast.csInf_eq), `sum_hInt_le` (Σ_{i≤b} g_i/g_0 ≤ 1+φ(b)),
  `phi_nat_ge` (φ(i) ≥ i/g_0, gives finite support), `codimInv_eq_zero`.
- Compile 22:34: no errors; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).

## Inflation.lean (B2 item 1, finite part)
- PROVED `GlueI6Rest.inflation_two_eq_coboundary`: for any abelian M with 2M = 0 and any
  inhomogeneous 2-cocycle c of ℤ/f (trivial action, `IsCocycleTriv`), its pullback along
  `ZMod.castHom : ℤ/2f → ℤ/f` is a coboundary δh, h(x) = c(0,0) − Σ_{j<x.val} c(1,j).
  Lemmas: `cocycle_zero_left`, `cocycle_eq` (c(a,b) = c00 − S a − S b + S(a+b), a,b ∈ ℕ),
  `cocS_add_f` (S(m+f) = S m + S f), `cocS_add_two_f`.
  No normal form for H²(ℤ/f) needed.
- Compile 22:37: no errors; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
