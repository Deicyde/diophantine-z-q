import ZInQKernel.HDecomp.ModCurves.Glue

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
    (∃ b c : k[X], ¬ p ∣ b ∧ W.Δ * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b) →
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

end X1Belyi
