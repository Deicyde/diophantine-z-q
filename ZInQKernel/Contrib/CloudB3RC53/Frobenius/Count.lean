import ZInQKernel.Contrib.CloudB3RC53.Frobenius.CountLemmas
import ZInQKernel.Contrib.CloudB3RC53.Frobenius.DegreeOneSub

/-!
# `|E(𝔽_{q²})| = |E(𝔽_q)| · (2q + 2 − |E(𝔽_q)|)`

Let `E = W` be an elliptic curve over a finite field `F` with `q` elements, `K ⊇ F` algebraically
closed, and `σ` the action of the base-changed Frobenius on `E(K)`, `σ(a, b) = (a^q, b^q)`.

* **Anti-fixed points** (`natCard_anti_add_natCard`): `|{P : σP = −P}| + |E(F)| = 2q + 2`. Both
  `σP = P` and `σP = −P` force `x(P) ∈ F`; for each `x ∈ F` the two `y`-roots `y₀, −b − y₀` of the
  Weierstrass equation contribute exactly two in total (`natCard_quadratic_fix_add_anti`), and `O`
  is counted twice.
* **Group theory** (`natCard_fix_sq`): `σ − 1` is the point map of the separable isogeny `π − 1`,
  hence additive and surjective on `E(K)` (Tau Ceti's `toPointHom_surjective`). So `σ` is additive
  and `|Fix(σ²)| = |Fix(σ)| · |{σP = −P}|` (`natCard_ker_sq_sub_one`).
* **Points over the quadratic extension** (`natCard_points_quadratic`): if `L ⊇ F` has `q²`
  elements, `|E(L)| = |Fix(σ²)| = |E(F)| · (2q + 2 − |E(F)|)`; in trace form
  `|E(L)| = q² + 1 − (a² − 2q)` with `a = q + 1 − |E(F)|` (`natCard_points_quadratic_trace`).

This is the finite-field input of the inert clause of `LocalFactorK` at a prime of good reduction.
Classification: PROVED.
-/

noncomputable section

open WeierstrassCurve.Affine

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

open TauCeti

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
  {K : Type*} [Field K] (f : F →+* K)

/-- Points of `W_K` that are `O`, or have `x^q = x` and `y` satisfying `R`. -/
def PtPred (R : K → K → Prop) : (W.map f).Point → Prop
  | .zero => True
  | .some x y _ => x ^ Fintype.card F = x ∧ R x y

/-- **Fibre decomposition over `x ∈ F`.** PROVED. -/
theorem natCard_ptPred (R : K → K → Prop)
    [∀ x : F, Finite {y : K // (W.map f).Equation (f x) y ∧ R (f x) y}] :
    Nat.card {P // PtPred W f R P} =
      (∑ x : F, Nat.card {y : K // (W.map f).Equation (f x) y ∧ R (f x) y}) + 1 := by
  let ψ : Option (Σ x : F, {y : K // (W.map f).Equation (f x) y ∧ R (f x) y}) →
      {P // PtPred W f R P}
    | none => ⟨.zero, trivial⟩
    | some ⟨x, y, hy⟩ => ⟨.some (f x) y (equation_iff_nonsingular.mp hy.1),
        ⟨by rw [← map_pow, FiniteField.pow_card], hy.2⟩⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro (_ | ⟨x, y, hy⟩) (_ | ⟨x', y', hy'⟩) h
      · rfl
      · exact absurd (congrArg Subtype.val h) (by simp [ψ])
      · exact absurd (congrArg Subtype.val h) (by simp [ψ])
      · have h' := congrArg Subtype.val h
        simp only [ψ, Point.some.injEq] at h'
        obtain ⟨hx, rfl⟩ := h'
        obtain rfl := f.injective hx
        rfl
    · rintro ⟨_ | ⟨a, b, h⟩, hP⟩
      · exact ⟨none, rfl⟩
      · obtain ⟨x, rfl⟩ := mem_range_of_pow_card_eq f hP.1
        exact ⟨some ⟨x, b, h.1, hP.2⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), Finite.card_option, Nat.card_sigma]

variable [IsAlgClosed K] [DecidableEq K]

/-- `y`-coefficient of the Weierstrass equation over `x`. -/
def coeffB (x : F) : K := f (W.a₁ * x + W.a₃)

/-- Right-hand side of the Weierstrass equation over `x`. -/
def coeffC (x : F) : K := f (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

omit [Fintype F] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem ma₁ : (W.map f).a₁ = f W.a₁ := rfl
omit [Fintype F] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem ma₂ : (W.map f).a₂ = f W.a₂ := rfl
omit [Fintype F] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem ma₃ : (W.map f).a₃ = f W.a₃ := rfl
omit [Fintype F] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem ma₄ : (W.map f).a₄ = f W.a₄ := rfl
omit [Fintype F] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem ma₆ : (W.map f).a₆ = f W.a₆ := rfl

omit [Fintype F] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem equation_map_iff (x : F) (y : K) :
    (W.map f).Equation (f x) y ↔ y ^ 2 + coeffB W f x * y = coeffC W f x := by
  rw [equation_iff]
  simp only [coeffB, coeffC, map_add, map_mul, map_pow, ma₁, ma₂, ma₃, ma₄, ma₆]
  constructor <;> intro h <;> linear_combination h

omit [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem powHom_f (z : F) : powHom f (f z) = f z := RingHom.congr_fun (powHom_comp f) z

/-- `y^q = y` (the `y`-condition of a Frobenius-fixed point). -/
def RFix (_ y : K) : Prop := y ^ Fintype.card F = y

/-- `y^q = −y − a₁x − a₃` (the `y`-condition of a point with `σP = −P`). -/
def RAnti (x y : K) : Prop := y ^ Fintype.card F = (W.map f).negY x y

omit [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem fibre_fix_eq (x : F) :
    Nat.card {y : K // (W.map f).Equation (f x) y ∧ RFix (F := F) (f x) y} =
      Nat.card {y : K // y ^ 2 + coeffB W f x * y = coeffC W f x ∧ powHom f y = y} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [equation_map_iff, RFix, powHom_apply])

omit [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem fibre_anti_eq (x : F) :
    Nat.card {y : K // (W.map f).Equation (f x) y ∧ RAnti W f (f x) y} =
      Nat.card {y : K // y ^ 2 + coeffB W f x * y = coeffC W f x ∧
        powHom f y = -y - coeffB W f x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [equation_map_iff, RAnti, powHom_apply, negY]
    simp only [coeffB, map_add, map_mul, ma₁, ma₃]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by rw [h2]; ring⟩)

omit [IsAlgClosed K] in
theorem ptPred_fix_iff (P : (W.map f).Point) :
    PtPred W f (RFix (F := F)) P ↔ (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = P := by
  rcases P with _ | ⟨a, b, h⟩
  · simp only [PtPred, true_iff]
    exact Isogeny.Hom.pointMap_zero _
  · rw [pointMap_frobeniusMap_some, Point.some.injEq]
    rfl

omit [IsAlgClosed K] in
theorem ptPred_anti_iff (P : (W.map f).Point) :
    PtPred W f (RAnti W f) P ↔ (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = -P := by
  rcases P with _ | ⟨a, b, h⟩
  · simp only [PtPred, true_iff]
    exact Isogeny.Hom.pointMap_zero _
  · rw [pointMap_frobeniusMap_some, Point.neg_some, Point.some.injEq]
    rfl

/-- **`|{P : σP = −P}| + |E(F)| = 2q + 2`.** PROVED. -/
theorem natCard_anti_add_natCard :
    Nat.card {P : (W.map f).Point //
        (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = -P} + Nat.card W.Point =
      2 * Fintype.card F + 2 := by
  have := fun x => finite_quadratic (coeffB W f x) (coeffC W f x) (RFix (F := F) (f x))
  have := fun x => finite_quadratic (coeffB W f x) (coeffC W f x) (RAnti W f (f x))
  have : ∀ x : F, Finite {y : K // (W.map f).Equation (f x) y ∧ RFix (F := F) (f x) y} :=
    fun x => Finite.of_injective
      (fun y => (⟨y.1, (equation_map_iff W f x y.1).mp y.2.1, y.2.2⟩ :
        {y : K // y ^ 2 + coeffB W f x * y = coeffC W f x ∧ RFix (F := F) (f x) y}))
      (fun y y' h => Subtype.ext (congrArg Subtype.val h :))
  have : ∀ x : F, Finite {y : K // (W.map f).Equation (f x) y ∧ RAnti W f (f x) y} :=
    fun x => Finite.of_injective
      (fun y => (⟨y.1, (equation_map_iff W f x y.1).mp y.2.1, y.2.2⟩ :
        {y : K // y ^ 2 + coeffB W f x * y = coeffC W f x ∧ RAnti W f (f x) y}))
      (fun y y' h => Subtype.ext (congrArg Subtype.val h :))
  rw [← natCard_fixedPoints W f,
    ← Nat.card_congr (Equiv.subtypeEquivRight (ptPred_anti_iff W f)),
    ← Nat.card_congr (Equiv.subtypeEquivRight (ptPred_fix_iff W f)),
    natCard_ptPred, natCard_ptPred]
  simp only [fibre_fix_eq, fibre_anti_eq]
  have h2 : ∀ x : F,
      Nat.card {y : K // y ^ 2 + coeffB W f x * y = coeffC W f x ∧
          powHom f y = -y - coeffB W f x} +
        Nat.card {y : K // y ^ 2 + coeffB W f x * y = coeffC W f x ∧ powHom f y = y} = 2 :=
    fun x => by
      rw [add_comm]
      exact natCard_quadratic_fix_add_anti f (powHom_f f _) (powHom_f f _)
  have hsum := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => h2 x)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

/-- **The Frobenius point map is additive, and `σ − 1` is surjective** (it is the point map of the
separable isogeny `π − 1`). PROVED. -/
theorem exists_frobenius_addHom :
    ∃ σh : (W.map f).Point →+ (W.map f).Point,
      (∀ P, σh P = (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P) ∧
        Function.Surjective (σh - AddMonoidHom.id (W.map f).Point) := by
  have hπ := hom_pullbackDifferential_frobeniusMap W f
  have hs : ((1 : ℤ) : K) ≠ 0 := by simp
  have hne := Isogeny.Hom.zsmul_sub_zsmul_id_ne_zero_of_pullbackDifferential_eq_zero hπ 1 1 hs
  have :=
    (Isogeny.Hom.isSeparable_toIsogeny_zsmul_sub_zsmul_id_iff_of_pullbackDifferential_eq_zero
      hπ 1 1 hne).mpr hs
  have := (W.map f).isIntegrallyClosed_coordinateRing
  have := (W.map f).isDedekindDomain_coordinateRing_of_isIntegrallyClosed
  set H := (Isogeny.Hom.toIsogeny hne).toPointHom
  have hH : ∀ P, H P = (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P - P := by
    intro P
    rw [← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom, Isogeny.Hom.ofIsogeny_toIsogeny,
      Isogeny.Hom.sub_pointMap, Isogeny.Hom.zsmul_pointMap, Isogeny.Hom.zsmul_pointMap, one_zsmul,
      one_zsmul, Isogeny.Hom.id_pointMap]
  refine ⟨H + AddMonoidHom.id _, fun P => ?_, ?_⟩
  · rw [AddMonoidHom.add_apply, hH, AddMonoidHom.id_apply, sub_add_cancel]
  · have e : H + AddMonoidHom.id _ - AddMonoidHom.id _ = H := add_sub_cancel_right _ _
    rw [e]
    exact Isogeny.toPointHom_surjective _

/-- **`|Fix(σ²)| = |E(F)| · |{σP = −P}|`.** PROVED. -/
theorem natCard_fix_sq :
    Nat.card {P : (W.map f).Point // (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap
        ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P) = P} =
      Nat.card W.Point * Nat.card {P : (W.map f).Point //
        (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = -P} := by
  obtain ⟨σh, hσ, hsurj⟩ := exists_frobenius_addHom W f
  have h := natCard_ker_sq_sub_one σh hsurj
  rw [← natCard_fixedPoints W f]
  have e1 : Nat.card (σh.comp σh - AddMonoidHom.id _).ker = Nat.card {P : (W.map f).Point //
      (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap
        ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P) = P} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, hσ, hσ, sub_eq_zero])
  have e2 : Nat.card (σh - AddMonoidHom.id _).ker = Nat.card {P : (W.map f).Point //
      (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = P} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, hσ, sub_eq_zero])
  have e3 : Nat.card (σh + AddMonoidHom.id _).ker = Nat.card {P : (W.map f).Point //
      (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = -P} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.add_apply, AddMonoidHom.id_apply, hσ,
        eq_neg_iff_add_eq_zero])
  rw [← e1, ← e2, ← e3, h]

section Quadratic

variable {L : Type*} [Field L] [Fintype L] (ι : F →+* L) (g : L →+* K)

omit [Fintype F] [Fintype L] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem nonsingular_incl (hg : g.comp ι = f) {x y : L} (h : (W.map ι).Nonsingular x y) :
    (W.map f).Nonsingular (g x) (g y) := by
  subst hg
  have := (map_nonsingular (W := W.map ι) g.injective x y).mpr h
  have e : (W.map ι).map g = W.map (g.comp ι) := by
    change WeierstrassCurve.map (WeierstrassCurve.map W ι) g = WeierstrassCurve.map W (g.comp ι)
    rw [WeierstrassCurve.map_map]
  rwa [e] at this

omit [Fintype F] [Fintype L] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem nonsingular_of_incl (hg : g.comp ι = f) {x y : L} (h : (W.map f).Nonsingular (g x) (g y)) :
    (W.map ι).Nonsingular x y := by
  subst hg
  have e : (W.map ι).map g = W.map (g.comp ι) := by
    change WeierstrassCurve.map (WeierstrassCurve.map W ι) g = WeierstrassCurve.map W (g.comp ι)
    rw [WeierstrassCurve.map_map]
  rw [← e] at h
  exact (map_nonsingular (W := W.map ι) g.injective x y).mp h

/-- The inclusion `W(L) → W(K)`. -/
def pointInclL (hg : g.comp ι = f) : (W.map ι).Point → (W.map f).Point
  | .zero => .zero
  | .some x y h => .some (g x) (g y) (nonsingular_incl W f ι g hg h)

omit [Fintype F] [Fintype L] [W.IsElliptic] [IsAlgClosed K] [DecidableEq K] in
theorem pointInclL_injective (hg : g.comp ι = f) : Function.Injective (pointInclL W f ι g hg) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hP <;> simp_all [pointInclL, g.injective.eq_iff]

omit [IsAlgClosed K] in
/-- **`|E(L)| = |Fix(σ²)|`** for `L ⊇ F` with `q²` elements. PROVED. -/
theorem natCard_fix_sq_eq (hg : g.comp ι = f) (hL : Fintype.card L = Fintype.card F ^ 2) :
    Nat.card {P : (W.map f).Point // (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap
        ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P) = P} =
      Nat.card (W.map ι).Point := by
  have hpow : ∀ a : K, (a ^ Fintype.card F) ^ Fintype.card F = a ^ Fintype.card L := by
    intro a; rw [← pow_mul, ← sq, hL]
  have hrange : Set.range (pointInclL W f ι g hg) = {P | (Isogeny.Hom.ofIsogeny
      (frobeniusMap W f)).pointMap ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P) = P} := by
    ext P
    constructor
    · rintro ⟨(_ | ⟨x, y, h⟩), rfl⟩
      · change (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap
          ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap 0) = 0
        rw [Isogeny.Hom.pointMap_zero, Isogeny.Hom.pointMap_zero]
      · change (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap
          ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap (.some _ _ _)) = .some _ _ _
        rw [pointMap_frobeniusMap_some, pointMap_frobeniusMap_some, Point.some.injEq, hpow, hpow,
          ← map_pow, ← map_pow, FiniteField.pow_card, FiniteField.pow_card]
        exact ⟨rfl, rfl⟩
    · rcases P with _ | ⟨a, b, h⟩
      · exact fun _ => ⟨.zero, rfl⟩
      · intro hfix
        change (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap
          ((Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap (.some _ _ _)) = .some _ _ _ at hfix
        rw [pointMap_frobeniusMap_some, pointMap_frobeniusMap_some, Point.some.injEq, hpow,
          hpow] at hfix
        obtain ⟨x, rfl⟩ := mem_range_of_pow_card_eq g hfix.1
        obtain ⟨y, rfl⟩ := mem_range_of_pow_card_eq g hfix.2
        exact ⟨.some x y (nonsingular_of_incl W f ι g hg h), rfl⟩
  have e := Equiv.ofInjective _ (pointInclL_injective W f ι g hg)
  rw [hrange] at e
  exact (Nat.card_congr e).symm

end Quadratic

omit [IsAlgClosed K] [DecidableEq K] in
/-- **`|E(L)| = |E(F)| · A` with `A + |E(F)| = 2q + 2`**, for `L ⊇ F` with `q²` elements. PROVED. -/
theorem natCard_points_quadratic_aux {L : Type*} [Field L] [Fintype L] (ι : F →+* L)
    (hL : Fintype.card L = Fintype.card F ^ 2) :
    ∃ A : ℕ, Nat.card (W.map ι).Point = Nat.card W.Point * A ∧
      A + Nat.card W.Point = 2 * Fintype.card F + 2 := by
  classical
  set g := algebraMap L (AlgebraicClosure L)
  refine ⟨_, ?_, natCard_anti_add_natCard W (g.comp ι)⟩
  rw [← natCard_fix_sq_eq W (g.comp ι) ι g rfl hL, natCard_fix_sq]

/-- **`|E(𝔽_{q²})| = |E(𝔽_q)| · (2q + 2 − |E(𝔽_q)|)`.** PROVED. -/
theorem natCard_points_quadratic {L : Type*} [Field L] [Fintype L] (ι : F →+* L)
    (hL : Fintype.card L = Fintype.card F ^ 2) :
    Nat.card (W.map ι).Point =
      Nat.card W.Point * (2 * Fintype.card F + 2 - Nat.card W.Point) := by
  obtain ⟨A, h1, h2⟩ := natCard_points_quadratic_aux W ι hL
  rw [h1, ← h2, Nat.add_sub_cancel]

/-- **Trace form: `|E(𝔽_{q²})| = q² + 1 − (a² − 2q)`, `a = q + 1 − |E(𝔽_q)|`.** PROVED. -/
theorem natCard_points_quadratic_trace {L : Type*} [Field L] [Fintype L] (ι : F →+* L)
    (hL : Fintype.card L = Fintype.card F ^ 2) :
    (Nat.card (W.map ι).Point : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + 1 -
        (((Fintype.card F : ℤ) + 1 - Nat.card W.Point) ^ 2 - 2 * Fintype.card F) := by
  obtain ⟨A, h1, h2⟩ := natCard_points_quadratic_aux W ι hL
  have h2' : (A : ℤ) = 2 * Fintype.card F + 2 - Nat.card W.Point := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast h2
  rw [h1, Nat.cast_mul, h2']
  ring

/-- **Node `QuadraticExtensionPointCount`** (the `n = 2` case of
`|E(𝔽_{q^n})| = q^n + 1 − (α^n + β^n)`, cf. Silverman, Ch. V §2; infrastructure for the inert clause
of `LocalFactorK`, not a manuscript line): for an elliptic curve `E` over `𝔽_q` and a field
`L ⊇ 𝔽_q` with `q²` elements, `|E(L)| = |E(𝔽_q)| · (2q + 2 − |E(𝔽_q)|)`, i.e.
`|E(L)| = q² + 1 − (a² − 2q)` with `a = q + 1 − |E(𝔽_q)|`. PROVED
(`quadraticExtensionPointCount_proof`). -/
def QuadraticExtensionPointCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (L : Type) [Field L] [Fintype L] (ι : F →+* L), Fintype.card L = Fintype.card F ^ 2 →
      Nat.card (W.map ι).Point = Nat.card W.Point * (2 * Fintype.card F + 2 - Nat.card W.Point)

theorem quadraticExtensionPointCount_proof : QuadraticExtensionPointCount :=
  fun _ _ _ W _ _ _ _ ι hL => natCard_points_quadratic W ι hL

end ZInQ.Contrib.CloudB3RC53.Frobenius
