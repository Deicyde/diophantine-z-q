/-! ## x1-belyi (wave 25; leaf-adopt3 fold): `X1ModelExists` and `BelyiX1` from five leaves

Copied verbatim from `scratch/x1-belyi/X1Belyi.lean` (which imported
`ZInQKernel.HDecomp.ModCurves.Glue`; every kernel name it uses is in `LeafModCurvesSec` above with
the same body). Changes: the import and the `#print axioms` lines are dropped; the file-level
`set_option linter.unusedSimpArgs false` is scoped to this section; the bridge
`X1Belyi.exists_J1_of_leaves` is added at the end. New leaf Props: `X1Belyi.TorsionStructure`,
`GoodReductionUnramified`, `CurveOfFunctionFieldQ`, `X1ConstantField`, `X1RationalCusp` (bundled
as `X1Belyi.X1Leaves`). No proof holes. -/

section X1BelyiSec

set_option linter.unusedSimpArgs false


/-!
# x1-belyi: the glue targets `X1ModelExists` and `BelyiX1` from literature leaves

Task x1-belyi (2026-11-12), nodes MC4, MC5, MC10 of `docs/research/bp-modcurves.md`.
The targets are the definitions `LeafModCurves.X1ModelExists` and `LeafModCurves.BelyiX1` of
`ZInQKernel/HDecomp/ModCurves/Leaves.lean` (imported, not restated).

Leaves (`def … : Prop`, published statements or consequences of them, over genuine
definitions):
* `TorsionStructure`: `E[N](K) ≅ ℤ/N × ℤ/N` over an algebraically closed field of
  characteristic 0 (Silverman, AEC, Cor. III.6.4(b), UNVERIFIED number).
* `GoodReductionUnramified`: good reduction at a place of `k(T)` with residue characteristic 0
  ⇒ the field of an `N`-torsion `x`-coordinate is unramified there (Serre–Tate 1968, Thm 1 /
  Néron–Ogg–Shafarevich, Silverman AEC Prop. VII.4.1, UNVERIFIED numbers).
* `CurveOfFunctionFieldQ`: a finite extension `F` of `ℚ(T)` with constant field `ℚ` is the
  function field of a smooth proper geometrically connected integral curve over `ℚ`, which has a
  `ℚ`-point when `F` has a place of degree 1 (Stacks, Curves and function fields; UNVERIFIED tags).
* `X1ConstantField`: `ℚ` is algebraically closed in `K_N = ℚ(j)(x(P))` (Igusa; geometric
  irreducibility of `X₁(N)` over `ℚ`; UNVERIFIED).
* `X1RationalCusp`: `K_N` has a place of degree 1 over `ℚ` (a `ℚ`-rational cusp of `X₁(N)`;
  UNVERIFIED).

Proved (glue): `belyiX1_of_leaves : TorsionStructure → GoodReductionUnramified → BelyiX1` and
`x1ModelExists_of_leaves : TorsionStructure → CurveOfFunctionFieldQ → X1ConstantField →
X1RationalCusp → X1ModelExists`.
-/

noncomputable section

namespace X1Belyi

open LeafModCurves
open WeierstrassCurve AlgebraicGeometry CategoryTheory
open Polynomial

/-! ## Definitions -/

/-- The `N`-torsion subgroup `W[N]` of the points of a Weierstrass curve over a field. -/
def nTors {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (N : ℕ) :
    AddSubgroup W.toAffine.Point where
  carrier := {P | N • P = 0}
  zero_mem' := nsmul_zero N
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ha, neg_zero]

/-- `ℚ → F` for a field `F` over `ℚ(T)` (avoids a second `ℚ`-algebra instance). -/
def ratHom (F : Type) [Field F] [Algebra Qj F] : ℚ →+* F :=
  (algebraMap Qj F).comp (algebraMap ℚ Qj)

/-- `ℚ` is algebraically closed in `F`: every element of `F` algebraic over `ℚ` is rational. -/
def ConstantFieldIsQ (F : Type) [Field F] [Algebra Qj F] : Prop :=
  ∀ x : F, (∃ f : ℚ[X], f ≠ 0 ∧ f.eval₂ (ratHom F) x = 0) → x ∈ Set.range (ratHom F)

/-- `F` has a place of degree 1 over `ℚ`: a proper valuation subring containing `ℚ` whose
residue field is `ℚ` (every element of `w` is congruent to a rational modulo `𝔪_w`). -/
def HasRationalPlace (F : Type) [Field F] [Algebra Qj F] : Prop :=
  ∃ w : ValuationSubring F, w ≠ ⊤ ∧ (∀ c : ℚ, ratHom F c ∈ w) ∧
    ∀ x ∈ w, ∃ c : ℚ, x - ratHom F c ∈ w.nonunits

/-! ## Leaves -/

/-- **Leaf T1 (structure of `E[N]`).** For an elliptic curve `E` over an algebraically closed
field `K` of characteristic 0 and `N ≥ 1`, `E[N] ≅ ℤ/N × ℤ/N`. Silverman, *The Arithmetic of
Elliptic Curves*, Cor. III.6.4(b) (UNVERIFIED number; the published statement for `char K ∤ N`,
specialized to characteristic 0). -/
def TorsionStructure : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ), 0 < N → Nonempty (nTors W N ≃+ (ZMod N × ZMod N))

/-- **Leaf T2 (good reduction ⇒ unramified torsion), function-field form.** Let `k` be a field of
characteristic 0, `E/k(T)` an elliptic curve, `p ∈ k[T]` irreducible, and suppose `E` has good
reduction at `p`: its coefficients are `p`-integral and its discriminant is a `p`-adic unit. Let
`P ∈ E(\overline{k(T)})` be a torsion point and `L = k(T)(x(P))`. Then `L/k(T)` is unramified at
`p`: for every valuation subring `w` of `L` containing `k[T]` with `p ∈ 𝔪_w`, `p` generates `𝔪_w`.

Source: Néron–Ogg–Shafarevich, in the form of Serre–Tate, *Good reduction of abelian varieties*,
Ann. of Math. 88 (1968), Thm 1 (for any discretely valued field: good reduction ⇒ inertia acts
trivially on `E[m]`, `m` prime to the residue characteristic; here the residue characteristic is
0); Silverman AEC Prop. VII.4.1 for complete fields (UNVERIFIED numbers). The step from "inertia
acts trivially on `E[N]`" to "`k(T)(x(P))` has ramification index 1 at every place over `p`" is the
standard characterization of the fixed field of inertia (Serre, *Local Fields*, I §7, UNVERIFIED).
A consequence of the published statement, specialized to `K = k(T)`. -/
def GoodReductionUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic]
    [DecidableEq (AlgebraicClosure (RatFunc k))] (p : k[X]), Irreducible p →
    (∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set (RatFunc k)),
      ∃ b c : k[X], ¬ p ∣ c ∧ a * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b) →
    (∃ b c : k[X], ¬ p ∣ b ∧ ¬ p ∣ c ∧
      W.Δ * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b) →
    ∀ P : (W.baseChange (AlgebraicClosure (RatFunc k))).toAffine.Point,
    (∃ N : ℕ, 0 < N ∧ N • P = 0) →
    ∀ w : ValuationSubring (IntermediateField.adjoin (RatFunc k) {xCoord P}),
      (∀ c : k[X], algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) c) ∈ w) →
      algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) p) ∈ w.nonunits →
      ∀ x ∈ w.nonunits, ∃ y ∈ w,
        x = algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) p) * y

/-- **Leaf M1 (curves and function fields over `ℚ`).** Let `F` be a finite extension of `ℚ(T)` in
which `ℚ` is algebraically closed. Then there is a smooth proper geometrically connected integral
curve `X` over `ℚ` with function field `F`; if `F` has a place of degree 1 over `ℚ`, then `X` has
a `ℚ`-point.

Source (UNVERIFIED tags and numbers): the Stacks Project, chapter *Algebraic Curves*, section
"Curves and function fields" (a finitely generated extension of transcendence degree 1 is the
function field of a normal projective curve, whose closed points correspond to the nontrivial
valuation rings of `F/k`, with the same residue fields); normal of dimension 1 over a perfect
field ⇒ smooth; `H⁰(X, 𝒪_X)` is the algebraic closure of `k` in `F`, so `X` is geometrically
connected when `k` is algebraically closed in `F`. Hartshorne I.6.7-6.12 and II.6.7 over an
algebraically closed field. The published statement specialized to `k = ℚ`. -/
def CurveOfFunctionFieldQ : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
    ∃ X : Over SpecQ, IsCurve X ∧ (HasRationalPlace F → Nonempty (RatPt X)) ∧
      ∃ (_ : IsIntegral X.left), Nonempty (X.left.functionField ≃+* F)

/-- **Leaf M2 (constant field of `K_N`).** For `P` of exact order `N` on `E_j`, `ℚ` is
algebraically closed in `K_N = ℚ(j)(x(P))`: `X₁(N)` is geometrically irreducible over `ℚ`.
Igusa, *Fibre systems of Jacobian varieties III*, Amer. J. Math. 81 (1959) (the Galois group of
`ℚ̄(j)(E[N])/ℚ̄(j)` is `SL₂(ℤ/N)/±1` up to `±`, so the constants of `ℚ(j)(E[N])` are `ℚ(ζ_N)`, and
the subfield fixed by the stabilizer of `±P` meets them in `ℚ`); Shimura 1971 §6.2, Prop. 6.9
(UNVERIFIED numbers). -/
def X1ConstantField : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → ConstantFieldIsQ (fieldX1 P)

/-- **Leaf M3 (a rational cusp).** For `P` of exact order `N` on `E_j`, `K_N` has a place of
degree 1 over `ℚ`. (On the Tate curve over `ℚ((q))` the point `q^{1/N}` has exact order `N` and
`x(q^{1/N}) ∈ ℚ((q^{1/N}))`, totally ramified over `j = ∞` with residue field `ℚ`; all points of
exact order `N` are conjugate over `ℚ(j)` up to sign by Igusa's theorem. Silverman, *Advanced
Topics*, Thm V.3.1 for the Tate curve; the rational cusps of `X₁(N)`: Ogg, *Rational points on
certain elliptic modular curves* (1973), UNVERIFIED.) -/
def X1RationalCusp : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N → HasRationalPlace (fieldX1 P)

/-! ## Basic facts -/

instance : CharZero Kbar :=
  charZero_of_injective_algebraMap (algebraMap Qj Kbar).injective

instance : EjBar.IsElliptic := inferInstanceAs ((Ej.map (algebraMap Qj Kbar)).IsElliptic)

theorem nTors_card (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (N : ℕ) (hN : 0 < N)
    (e : nTors W N ≃+ (ZMod N × ZMod N)) : Nat.card (nTors W N) = N ^ 2 := by
  have : NeZero N := ⟨hN.ne'⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

/-- A point of exact order `N` from `E[N] ≅ ℤ/N × ℤ/N`. -/
theorem exists_addOrderOf (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (N : ℕ)
    (e : nTors W N ≃+ (ZMod N × ZMod N)) : ∃ P : W.toAffine.Point, addOrderOf P = N := by
  refine ⟨(e.symm (1, 0) : W.toAffine.Point), ?_⟩
  rw [AddSubgroup.addOrderOf_coe, AddEquiv.addOrderOf_eq, Prod.addOrderOf, ZMod.addOrderOf_one,
    addOrderOf_zero, Nat.lcm_one_right]

/-! ## The degree bound `[K_N : ℚ(j)] ≤ N²` (from leaf T1) -/

/-- `x(σ P) = σ(x(P))`. -/
theorem xCoord_map (σ : Kbar ≃ₐ[Qj] Kbar) (P : EjBar.toAffine.Point) :
    xCoord (WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom P) = σ (xCoord P) := by
  cases P with
  | zero => exact (map_zero σ).symm
  | some x y h => rfl

theorem map_mem_nTors (σ : Kbar ≃ₐ[Qj] Kbar) (N : ℕ) (P : EjBar.toAffine.Point) (hP : N • P = 0) :
    WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom P ∈ nTors EjBar N := by
  show N • _ = 0
  exact (map_nsmul _ N P).symm.trans ((congrArg _ hP).trans (map_zero _))

/-- **Degree bound (glue, proved from T1).** For `N • P = 0`, `N ≥ 1`:
`[ℚ(j)(x(P)) : ℚ(j)] ≤ N²`. The conjugates of `x(P)` over `ℚ(j)` are the `x(σP)`, `σP ∈ E[N]`. -/
theorem finrank_fieldX1_le (hT : TorsionStructure) (N : ℕ) (hN : 0 < N)
    (P : EjBar.toAffine.Point) (hP : N • P = 0) : Module.finrank Qj (fieldX1 P) ≤ N ^ 2 := by
  obtain ⟨e⟩ := hT Kbar EjBar N hN
  have hx : IsIntegral Qj (xCoord P) := Algebra.IsIntegral.isIntegral _
  rw [fieldX1, IntermediateField.adjoin.finrank hx]
  have hirr := minpoly.irreducible hx
  have hsep : (minpoly Qj (xCoord P)).Separable := hirr.separable
  have hspl : ((minpoly Qj (xCoord P)).map (algebraMap Qj Kbar)).Splits := IsAlgClosed.splits _
  rw [← card_rootSet_eq_natDegree hsep hspl]
  have hsub : (minpoly Qj (xCoord P)).rootSet Kbar ⊆ xCoord '' (nTors EjBar N : Set EjBar.toAffine.Point) := by
    intro r hr
    have hroot : aeval r (minpoly Qj (xCoord P)) = 0 := (mem_rootSet.mp hr).2
    have hmin : minpoly Qj r = minpoly Qj (xCoord P) :=
      (minpoly.eq_of_irreducible_of_monic hirr hroot (minpoly.monic hx)).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := Qj) (E := Kbar)).mp hmin
    refine ⟨WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom P,
      map_mem_nTors σ N P hP, ?_⟩
    exact (xCoord_map σ P).trans hσ
  have hfin : (nTors EjBar N : Set EjBar.toAffine.Point).Finite := by
    have : NeZero N := ⟨hN.ne'⟩
    have : Finite (nTors EjBar N) := Finite.of_equiv _ e.toEquiv.symm
    exact Set.toFinite _
  calc Fintype.card ((minpoly Qj (xCoord P)).rootSet Kbar)
      = ((minpoly Qj (xCoord P)).rootSet Kbar).ncard := Nat.card_eq_fintype_card.symm.trans (Nat.card_coe_set_eq _)
    _ ≤ (xCoord '' (nTors EjBar N : Set EjBar.toAffine.Point)).ncard := Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ (nTors EjBar N : Set EjBar.toAffine.Point).ncard := Set.ncard_image_le hfin
    _ = N ^ 2 := (Nat.card_coe_set_eq _).symm.trans (nTors_card Kbar EjBar N hN e)

/-! ## `X1ModelExists` (MC4 + MC10) -/

/-- **`X1ModelExists` (glue, proved from T1, M1, M2, M3).** -/
theorem x1ModelExists_of_leaves (hT : TorsionStructure) (hC : CurveOfFunctionFieldQ)
    (hK : X1ConstantField) (hR : X1RationalCusp) : X1ModelExists := by
  intro N hN
  obtain ⟨e⟩ := hT Kbar EjBar N hN
  obtain ⟨P, hP⟩ := exists_addOrderOf Kbar EjBar N e
  have hx : IsIntegral Qj (xCoord P) := Algebra.IsIntegral.isIntegral _
  have : FiniteDimensional Qj (fieldX1 P) := IntermediateField.adjoin.finiteDimensional hx
  obtain ⟨X, hX, hpt, hint, ⟨φ⟩⟩ := hC (fieldX1 P) (hK N P hN hP)
  exact ⟨X, (hpt (hR N P hN hP)).some, hX, hint, P, hP, ⟨φ⟩⟩

/-! ## `BelyiX1` (MC5) -/

/-- The substitution `T ↦ T/1728` of `ℚ[T]`, an automorphism (inverse `T ↦ 1728 T`). -/
def scaleEquiv : ℚ[X] ≃ₐ[ℚ] ℚ[X] :=
  AlgEquiv.ofAlgHom (aeval (C (1728⁻¹ : ℚ) * X)) (aeval (C (1728 : ℚ) * X))
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, map_mul, aeval_C,
        algebraMap_eq, AlgHom.coe_id, id_eq]
      rw [← mul_assoc, ← C_mul]
      norm_num)
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X, map_mul, aeval_C,
        algebraMap_eq, AlgHom.coe_id, id_eq]
      rw [← mul_assoc, ← C_mul]
      norm_num)

theorem scaleEquiv_apply (q : ℚ[X]) : scaleEquiv q = q.comp (C (1728⁻¹ : ℚ) * X) := rfl

theorem scaleEquiv_symm_X : scaleEquiv.symm X = C (1728 : ℚ) * X := by
  change aeval (C (1728 : ℚ) * X) X = _
  simp

theorem scaleEquiv_symm_X_sub : scaleEquiv.symm (X - 1728) = C (1728 : ℚ) * (X - 1) := by
  simp only [map_sub, scaleEquiv_symm_X, map_ofNat]
  ring

/-- `p := q(T/1728)` is irreducible and does not divide `T²(T − 1728)⁹` when `q` is monic
irreducible, `q ≠ T, T − 1`. -/
theorem scale_not_dvd (q : ℚ[X]) (hqm : q.Monic) (hqi : Irreducible q) (hqX : q ≠ X)
    (hqX1 : q ≠ X - 1) : ¬ scaleEquiv q ∣ X ^ 2 * (X - 1728) ^ 9 := by
  intro h
  have h' : q ∣ scaleEquiv.symm (X ^ 2 * (X - 1728) ^ 9) := by
    have := map_dvd scaleEquiv.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  rw [map_mul, map_pow, map_pow, scaleEquiv_symm_X, scaleEquiv_symm_X_sub] at h'
  have hp := hqi.prime
  have hu : IsUnit (C (1728 : ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  rcases hp.dvd_or_dvd h' with h1 | h1
  · have h2 := hp.dvd_of_dvd_pow h1
    rw [hu.dvd_mul_left] at h2
    exact hqX (eq_of_monic_of_associated hqm monic_X (hqi.associated_of_dvd irreducible_X h2))
  · have h2 := hp.dvd_of_dvd_pow h1
    rw [hu.dvd_mul_left] at h2
    exact hqX1 (eq_of_monic_of_associated hqm (monic_X_sub_C 1)
      (hqi.associated_of_dvd (irreducible_X_sub_C 1) (by simpa using h2)))

theorem transcendental_X_div : Transcendental ℚ (RatFunc.X / 1728 : Qj) := by
  intro h
  apply RatFunc.transcendental_X (K := ℚ)
  have := h.smul (1728 : ℚ)
  rw [Algebra.smul_def, map_ofNat, mul_div_cancel₀ _ (by norm_num : (1728 : Qj) ≠ 0)] at this
  convert this using 1
  exact Subsingleton.elim _ _

/-- **`BelyiX1` (glue, proved from T1 and T2).** -/
theorem belyiX1_of_leaves (hT : TorsionStructure) (hG : GoodReductionUnramified) : BelyiX1 := by
  intro N P hN hP
  have hNP : N • P = 0 := hP ▸ addOrderOf_nsmul_eq_zero P
  refine ⟨⟨?_, ?_⟩, finrank_fieldX1_le hT N hN P hNP⟩
  · -- transcendence
    let φ : Qj →ₐ[ℚ] fieldX1 P :=
      { algebraMap Qj (fieldX1 P) with
        commutes' := fun r => by
          change algebraMap Qj (fieldX1 P) (algebraMap ℚ Qj r) = algebraMap ℚ (fieldX1 P) r
          rw [← RingHom.comp_apply]
          exact DFunLike.congr_fun (RingHom.ext_rat ((algebraMap Qj (fieldX1 P)).comp
            (algebraMap ℚ Qj)) (algebraMap ℚ (fieldX1 P))) r }
    intro h
    exact transcendental_X_div ((isAlgebraic_algHom_iff φ φ.toRingHom.injective).mp h)
  · intro w hk ht q hqm hqi hqX hqX1 hq x hx
    have hratF : algebraMap ℚ (fieldX1 P) = (algebraMap Qj (fieldX1 P)).comp (algebraMap ℚ Qj) := RingHom.ext_rat _ _
    have hratQ : (algebraMap ℚ[X] Qj).comp C = algebraMap ℚ Qj := RingHom.ext_rat _ _
    have hr : algebraMap ℚ[X] Qj (C (1728⁻¹ : ℚ) * X) = RatFunc.X / 1728 := by
      rw [map_mul, RatFunc.algebraMap_X, ← RingHom.comp_apply, hratQ, eq_ratCast]
      push_cast
      ring
    -- the key identity `p(j) = q(t)`
    have KI : algebraMap Qj (fieldX1 P) (algebraMap ℚ[X] Qj (scaleEquiv q)) =
        Polynomial.aeval (algebraMap Qj (fieldX1 P) (RatFunc.X / 1728)) q := by
      rw [scaleEquiv_apply, Polynomial.comp, hom_eval₂, hratQ, hr, aeval_def, hratF, hom_eval₂]
    have hp : Irreducible (scaleEquiv q) := (MulEquiv.irreducible_iff scaleEquiv).mpr hqi
    have hA : algebraMap ℚ[X] Qj 1728 = 1728 := map_ofNat _ _
    have hA36 : algebraMap ℚ[X] Qj 36 = 36 := map_ofNat _ _
    have hcoef : ∀ a ∈ ({Ej.a₁, Ej.a₂, Ej.a₃, Ej.a₄, Ej.a₆} : Set Qj),
        ∃ b c : ℚ[X], ¬ scaleEquiv q ∣ c ∧
          a * algebraMap ℚ[X] Qj c = algebraMap ℚ[X] Qj b := by
      have h1 : ¬ scaleEquiv q ∣ 1 := fun h => hp.not_isUnit (isUnit_of_dvd_one h)
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · exact ⟨X - 1728, 1, h1, by simp [Ej, ofJNe0Or1728, hA, hA36]⟩
      · exact ⟨0, 1, h1, by simp [Ej, ofJNe0Or1728, hA, hA36]⟩
      · exact ⟨0, 1, h1, by simp [Ej, ofJNe0Or1728, hA, hA36]⟩
      · exact ⟨-36 * (X - 1728) ^ 3, 1, h1, by simp [Ej, ofJNe0Or1728, hA, hA36]⟩
      · exact ⟨-(X - 1728) ^ 5, 1, h1, by simp [Ej, ofJNe0Or1728, hA, hA36]⟩
    have hdisc : ∃ b c : ℚ[X], ¬ scaleEquiv q ∣ b ∧ ¬ scaleEquiv q ∣ c ∧
        Ej.Δ * algebraMap ℚ[X] Qj c = algebraMap ℚ[X] Qj b :=
      ⟨X ^ 2 * (X - 1728) ^ 9, 1, scale_not_dvd q hqm hqi hqX hqX1,
        fun h => hp.not_isUnit (isUnit_of_dvd_one h), by
        rw [Ej, ofJNe0Or1728_Δ, map_one, mul_one, map_mul, map_pow, map_pow, map_sub,
          RatFunc.algebraMap_X, hA]⟩
    have h1728 : algebraMap Qj (fieldX1 P) RatFunc.X =
        algebraMap ℚ (fieldX1 P) 1728 * algebraMap Qj (fieldX1 P) (RatFunc.X / 1728) := by
      rw [hratF, RingHom.comp_apply, ← map_mul, map_ofNat]
      congr 1
      field_simp
    have hCa : ∀ a : ℚ, algebraMap Qj (fieldX1 P) (algebraMap ℚ[X] Qj (C a)) =
        algebraMap ℚ (fieldX1 P) a := fun a => by
      rw [hratF, RingHom.comp_apply, ← hratQ, RingHom.comp_apply]
    have hc : ∀ c : ℚ[X], algebraMap Qj (fieldX1 P) (algebraMap ℚ[X] Qj c) ∈ w := by
      intro c
      induction c using Polynomial.induction_on with
      | C a => rw [hCa]; exact hk a
      | add f g hf hg => rw [map_add, map_add]; exact w.add_mem _ _ hf hg
      | monomial n a _ =>
        rw [map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X, h1728]
        refine w.mul_mem _ _ ?_ (w.pow_mem (w.mul_mem _ _ (hk 1728) ht) _)
        rw [hCa]; exact hk a
    have hπ : algebraMap Qj (fieldX1 P) (algebraMap ℚ[X] Qj (scaleEquiv q)) ∈ w.nonunits := by
      rw [KI]; exact hq
    obtain ⟨y, hy, rfl⟩ := hG ℚ Ej (scaleEquiv q) hp hcoef hdisc P ⟨N, hN, hNP⟩ w hc hπ x hx
    exact ⟨y, hy, congrArg (· * y) KI⟩

/-! ## The bundle -/

/-- **The leaves of this file.** -/
structure X1Leaves : Prop where
  torsion : TorsionStructure
  goodRed : GoodReductionUnramified
  curve : CurveOfFunctionFieldQ
  constants : X1ConstantField
  cusp : X1RationalCusp

/-- **MC4 + MC5 + MC10 (glue, proved from the leaves).** -/
theorem x1ModelExists_and_belyiX1 (L : X1Leaves) : X1ModelExists ∧ BelyiX1 :=
  ⟨x1ModelExists_of_leaves L.torsion L.curve L.constants L.cusp,
    belyiX1_of_leaves L.torsion L.goodRed⟩

/-- `ModCurveLeaves` of `ZInQKernel/HDecomp/ModCurves/Leaves.lean` with its field `x1`
discharged by the leaves of this file. -/
theorem modCurveLeaves_of (L : X1Leaves) (hJ : JacobianExists ℚ) (h16 : R16_EichlerShimuraJ1')
    (hd : DimJ1Genus) : ModCurveLeaves :=
  ⟨hJ, (x1ModelExists_and_belyiX1 L).1, h16, hd⟩

/-- **Bridge (non-vacuity of `IsJ1`).** With T33 (`JacobianExists ℚ`, field `t33`) and the five
leaves of this file, a `J₁(N)` exists for every `N ≥ 1`. -/
theorem exists_J1_of_leaves (L : X1Leaves) (hJ : LeafModCurves.JacobianExists ℚ) (N : ℕ)
    (hN : 0 < N) : ∃ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J :=
  LeafModCurves.exists_J1 hJ (x1ModelExists_and_belyiX1 L).1 N hN

end X1Belyi

end

end X1BelyiSec
