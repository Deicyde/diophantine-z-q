
namespace X6Kummer

open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV LeafQM.AV.Pin PkgI3 FS5NoCM

/-! ## §G The leaf in its global (conic) form, and the fibre form from it -/

/-- The `ℚ̄`-points of the conic `C : Y² + 3X² + 3Z² = 0`: the affine part `Z = 1`
(`(X, Y) = (p.1, p.2)` with `p.2² + 3 p.1² + 3 = 0`) and the two points at infinity `[1 : b : 0]`,
`b² = −3`. -/
abbrev ConicPt : Type :=
  {p : Qbar × Qbar // p.2 ^ 2 + 3 * p.1 ^ 2 + 3 = 0} ⊕ {b : Qbar // b ^ 2 = -3}

/-- `Aut(ℚ̄/ℚ)` acting on `C(ℚ̄)` coordinatewise (`C` is defined over `ℚ`). -/
def conicGal (σ : Qbar ≃ₐ[ℚ] Qbar) : ConicPt → ConicPt
  | Sum.inl p => Sum.inl ⟨(σ p.1.1, σ p.1.2), by
      have h := congrArg σ p.2
      simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
      exact h⟩
  | Sum.inr b => Sum.inr ⟨σ b.1, by
      have h := congrArg σ b.2
      simp only [map_pow, map_neg, map_ofNat] at h
      exact h⟩

/-- **The conic model of `(X₆, π₆)` on `ℚ̄`-points**: a bijection `X(ℚ̄) ≃ C(ℚ̄)` commuting with
`Aut(ℚ̄/ℚ)`, under which `π₆ = −16(X² + Z²)/(27 Z²)` (so `∞` at the points at infinity). -/
def ConicModel (X : Over (Spec (CommRingCat.of ℚ))) (π₆ : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      π₆.val (K := Qbar) x.left = OnePoint.some (-16 * (p.1.1 ^ 2 + 1) / 27)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → π₆.val (K := Qbar) x.left = OnePoint.infty)

/-- **N2-L′ (leaf, new; the global form of `X6KummerModel`): `X₆ = X₀(6,1)` is the conic
`Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27 Z²)`, on `ℚ̄`-points of one witness.**

*Published statement* (Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979): `X₀(6,1) : x² + y² + 3 = 0`;
Elkies, ANTS-III, LNCS 1423 (1998), §3: `X*(6) = X₆/W` with coordinate `t`, `t = 0, 1, ∞` at the
CM points of discriminants `−24, −4, −3`, and `X₆ = X*(6)(√−t, √(3(t − 1)))`; locators
UNVERIFIED, no network). Put `X = √−t`, `Y = √(3(t−1))`, `Z = 1`: then `Y² + 3X² + 3 = 0`,
`t = −X²/Z²`, `W` acts by the sign changes, and `j = 16(t − 1)/27 = −16(X² + Z²)/(27 Z²)` is the
coordinate of R2fp (`j = 0, ∞, −16/27` at `−4, −3, −24`; a Möbius map is fixed by three values).
An isomorphism of `ℚ`-schemes `X₆ ≅ C` gives a bijection on `ℚ̄`-points commuting with
`Aut(ℚ̄/ℚ)`, compatible with the maps to `P¹`. Consistency checks (VERIFIED by computation in
`scratch/x6-kummer/conic_check.py`): the involutions `X ↦ −X`, `Y ↦ −Y`, `(X,Y) ↦ (−X,−Y)` fix
exactly the two points over `j = −16/27`, `0`, `∞` respectively (Riemann–Hurwitz for a
`(ℤ/2)²`-cover of `P¹` by a genus-0 curve); the residue fields there are `ℚ(√−3)`, `ℚ(i)`,
`ℚ(√−3)`, as González–Rotger Thm 5.12 (the bundle's `R5ptProps`) requires for `ℤ[√−6]` (`b = 0`,
`h = 2`), `ℤ[i]` (`b = 1`, `h = 1`, contains `ℚ(i)`), `ℤ[ζ₃]` (`b = 1`, `h = 1`, contains
`ℚ(√−3)`); `C` and Kurihara's conic both correspond to `(−1, −3)_ℚ`, ramified at `{3, ∞}`. The
fibre fields `ℚ(√−t, √(3(t−1)))` were checked against González–Rotger Thm 5.12 on all 24 rational
CM points of Elkies' table by rv-nocm §1.3 Part B. -/
def X6ConicModel : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left), R1R2fpFullProps Y Φ X Ψ fY π₆ ∧ ConicModel X π₆

/-- The fibre condition on the affine conic: `−16(a² + 1)/27 = j₀` iff `a² = −t₀`, and then
`b² = 3(t₀ − 1)`. -/
theorem conic_fibre_iff (j₀ : ℚ) (a b : Qbar) (hab : b ^ 2 + 3 * a ^ 2 + 3 = 0) :
    (-16 * (a ^ 2 + 1) / 27 = algebraMap ℚ Qbar j₀) ↔
      (a ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        b ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1)) := by
  have ht : algebraMap ℚ Qbar (1 + 27 * j₀ / 16) = 1 + 27 * algebraMap ℚ Qbar j₀ / 16 := by
    simp only [map_add, map_one, map_div₀, map_mul, map_ofNat]
  rw [ht]
  constructor
  · intro h
    refine ⟨by linear_combination (-27 / 16 : Qbar) * h, by linear_combination hab + (81 / 16 : Qbar) * h⟩
  · rintro ⟨h1, -⟩
    linear_combination (-16 / 27 : Qbar) * h1

/-- **The fibre form from the conic form (compiled).** -/
theorem kummerFibreEquiv_of_conic {X : Over (Spec (CommRingCat.of ℚ))} {π₆ : ToP1 X.left}
    (hC : ConicModel X π₆) : KummerFibreEquiv X π₆ := by
  obtain ⟨e, he, hin, hinf⟩ := hC
  intro j₀ _ _
  -- every point of the fibre is affine
  have aff : ∀ x : fieldPt Qbar ⟶ X,
      π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
      ∃ p, e x = Sum.inl p := by
    intro x hx
    rcases hex : e x with p | b
    · exact ⟨p, rfl⟩
    · rw [hinf x b hex] at hx
      exact absurd hx (by simp [OnePoint.infty, OnePoint.some])
  have val_of : ∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
      -16 * (p.1.1 ^ 2 + 1) / 27 = algebraMap ℚ Qbar j₀ := by
    intro x p hp hx
    rw [hin x p hp] at hx
    exact Option.some.inj hx
  let g : ConicPt → Qbar × Qbar := Sum.elim (fun p => p.1) (fun _ => (0, 0))
  have hg : ∀ (x : fieldPt Qbar ⟶ X),
      π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
      (g (e x)).1 ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        (g (e x)).2 ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1) := by
    intro x hx
    obtain ⟨p, hp⟩ := aff x hx
    rw [hp]
    exact (conic_fibre_iff j₀ p.1.1 p.1.2 p.2).mp (val_of x p hp hx)
  let f : {x : fieldPt Qbar ⟶ X //
        π₆.val (K := Qbar) x.left = OnePoint.some (algebraMap ℚ Qbar j₀)} →
      {p : Qbar × Qbar // p.1 ^ 2 = -algebraMap ℚ Qbar (1 + 27 * j₀ / 16) ∧
        p.2 ^ 2 = 3 * (algebraMap ℚ Qbar (1 + 27 * j₀ / 16) - 1)} :=
    fun x => ⟨g (e x.1), hg x.1 x.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
      obtain ⟨p, hp⟩ := aff x hx
      obtain ⟨p', hp'⟩ := aff x' hx'
      have h1 : g (e x) = g (e x') := congrArg Subtype.val h
      rw [hp, hp'] at h1
      have h2 : p = p' := Subtype.ext h1
      apply Subtype.ext
      apply e.injective
      rw [hp, hp', h2]
    · rintro ⟨⟨a, b⟩, hab⟩
      have hon : b ^ 2 + 3 * a ^ 2 + 3 = 0 := by
        obtain ⟨h1, h2⟩ := hab
        linear_combination h2 + 3 * h1
      let c : ConicPt := Sum.inl ⟨(a, b), hon⟩
      have hx : π₆.val (K := Qbar) (e.symm c).left = OnePoint.some (algebraMap ℚ Qbar j₀) := by
        rw [hin (e.symm c) ⟨(a, b), hon⟩ (e.apply_symm_apply c)]
        congr 1
        exact (conic_fibre_iff j₀ a b hon).mpr hab
      refine ⟨⟨e.symm c, hx⟩, ?_⟩
      apply Subtype.ext
      change g (e (e.symm c)) = (a, b)
      rw [e.apply_symm_apply]
      rfl
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro σ x hx hσx
  change g (e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x)) = (σ (g (e x)).1, σ (g (e x)).2)
  obtain ⟨p, hp⟩ := aff x hx
  rw [he σ x, hp]
  rfl

/-- **N2 from the conic leaf (compiled).** -/
theorem x6KummerModel_of_conic (hL : X6ConicModel) : X6KummerModel := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h, hC⟩ := hL
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h, kummerFibreEquiv_of_conic hC⟩

/-- **N2 `X6KummerFibre` from the conic leaf `X6ConicModel` and `MobiusGlue` (compiled).** -/
theorem x6KummerFibre_of_conic (hM : MobiusGlue) (hL : X6ConicModel) : X6KummerFibre :=
  x6KummerFibre_of_model' hM (x6KummerModel_of_conic hL)

end X6Kummer

#print axioms X6Kummer.kummerFibreEquiv_of_conic
#print axioms X6Kummer.x6KummerFibre_of_conic
