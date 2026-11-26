import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.Extension

/-! **The same-place input of the assembled `GoodRow`** (tex 8479–8492).

`SamePlaceData h₅ htame h₂ K X` holds exactly the four fields `point`, `point_W`, `point_frob`
and `frobenius_sq` of `PMWire.GoodRow` (`RC/PMWire/Model.lean:57–66`) on the pinned integral
model `Pinned.Y0Level h₅ htame h₂` with `closed := ModelNeron.closed ell`. Their types are the
`GoodRow` types, except that `point_W` names the integral Atkin–Lehner operator `Wint` of the
generic5 lane instead of `(extension q hq he).choose`; `SamePlaceData.point_W_choose` proves the
`GoodRow` form for every extension, through `eq_Wint_of_extendsAtkin`.

Owner: the same-place lane in the hCM lane. This structure is an input of the wiring, never a
leaf and never filled by a placeholder. -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.GoodRowWire

open PMQuotient (residueSource residueFrob)

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]

/-- **The same-place data at a stage** (tex 8479–8492; owner: the same-place lane in the hCM
lane). The supersingular points `X.Point` of the coarse fibre map to geometric points of the
special fibre of the pinned model `Pinned.Y0Level h₅ htame h₂` over the residue field `K`,
compatibly with the Atkin–Lehner operators (through the integral operator `Wint` of
`ModelGeneric5`, at the exact divisor `q ^ v_q(N)`), and with the prime-field Frobenius, which
is an involution on `X.Point`. The fields `point`, `point_W`, `point_frob` and `frobenius_sq` are
those of `PMWire.GoodRow` (`RC/PMWire/Model.lean`), with `Wint` for `(extension q hq he).choose` in
`point_W`. -/
structure SamePlaceData (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)
    (K : Type) [Field K] [Algebra (ZMod ell) K] (X : PMAdelic.CoarseFibre) where
  /-- The special-fibre point of each supersingular point (`GoodRow.point`). -/
  point : X.Point → (residueSource ell K ⟶
    (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).obj
      (Pinned.Y0Level h₅ htame h₂))
  /-- The Atkin–Lehner compatibility (`GoodRow.point_W`, with the integral operator `Wint`). -/
  point_W : ∀ (q : ℕ) (_hq : q.Prime) (_he : 0 < N.factorization q) (x : X.Point),
    point (X.W q x) = point x ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).map
        (ModelGeneric5.Wint h₅ htame h₂ (TauCeti.Nat.isExactDivisor_primePow (N := N) (p := q)))
  /-- The Frobenius compatibility (`GoodRow.point_frob`). -/
  point_frob : ∀ x, point (X.frobenius x) = residueFrob ell K ≫ point x
  /-- The Frobenius of the supersingular points is an involution (`GoodRow.frobenius_sq`). -/
  frobenius_sq : Function.Involutive X.frobenius

namespace SamePlaceData

variable {h₅ : 5 ≤ ell} {htame : ¬ ell ∣ N * N.totient} {h₂ : 2 ≤ N}
  {K : Type} [Field K] [Algebra (ZMod ell) K] {X : PMAdelic.CoarseFibre}

/-- **`point_W` in the exact `GoodRow` form**: for any family of extensions of the rational
Atkin–Lehner operators (in particular `ModelGeneric5.goodRow_extension`), the chosen extension
is `Wint` (`ModelGeneric5.eq_Wint_of_extendsAtkin`, i.e. `PMWire.extendsAtkin_unique`). -/
theorem point_W_choose (S : SamePlaceData h₅ htame h₂ K X)
    (ext : ∀ q : ℕ, q.Prime → 0 < N.factorization q →
      ∃ W : Pinned.Y0Level h₅ htame h₂ ⟶ Pinned.Y0Level h₅ htame h₂,
        PMWire.ExtendsAtkin (ModelNeron.source h₅ htame h₂) q W)
    (q : ℕ) (hq : q.Prime) (he : 0 < N.factorization q) (x : X.Point) :
    S.point (X.W q x) = S.point x ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (ModelNeron.closed ell)))).map
        (ext q hq he).choose := by
  rw [ModelGeneric5.eq_Wint_of_extendsAtkin h₅ htame h₂ q (ext q hq he).choose_spec]
  exact S.point_W q hq he x

end SamePlaceData

#print axioms SamePlaceData.point_W_choose

end ZInQ.Manuscript.RC.GoodRowWire
