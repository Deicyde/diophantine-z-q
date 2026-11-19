import ZInQKernel.Contrib.CloudB3RC53.Frobenius.Points

/-!
# The points fixed by the base-changed Frobenius are the points over the finite field

For a Weierstrass curve `W` over a finite field `F` with `q` elements and a field homomorphism
`f : F →+* K`, the base change `π_K` of the Frobenius isogeny (`frobeniusMap W f`) fixes exactly
the image of `W(F)` in `W(K)` (`range_pointIncl`). Hence the fixed points are in bijection with
`W(F)` (`natCard_fixedPoints`), which over `K = \bar F` is the statement that the Frobenius-fixed
points of `E(\bar{𝔽}_q)` are `E(𝔽_q)`.

The proof: `π_K` sends `(a, b)` to `(a^q, b^q)` (`pointMap_frobeniusMap_some`), and an element of
`K` with `a^q = a` lies in the image of `F` (`mem_range_of_pow_card_eq`): the `q` elements of `f(F)`
are already roots of `X^q − X`, which has at most `q` roots in `K`.

Classification: PROVED.
-/

noncomputable section

open Polynomial WeierstrassCurve.Affine

namespace ZInQ.Contrib.CloudB3RC53.Frobenius

open TauCeti

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve.Affine F)
  {K : Type*} [Field K] (f : F →+* K)

/-- **An element of `K` fixed by the `q`-power map lies in the image of `F`.** PROVED. -/
theorem mem_range_of_pow_card_eq {a : K} (ha : a ^ Fintype.card F = a) : a ∈ Set.range f := by
  classical
  by_contra hne
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  let Z : Finset K := insert a (Finset.univ.image f)
  have hZ : Z.val ⊆ (X ^ Fintype.card F - X : K[X]).roots := by
    intro z hz
    rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq), IsRoot.def, eval_sub, eval_pow,
      eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ha
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← map_pow, FiniteField.pow_card]
  have hcard := card_le_degree_of_subset_roots hZ
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_insert_of_notMem
    (fun h => hne (by obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨c, rfl⟩)),
    Finset.card_image_of_injective _ f.injective, Finset.card_univ] at hcard
  omega

/-- The inclusion `W(F) → W(K)`. -/
def pointIncl : W.Point → (W.map f).Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((map_nonsingular (W := W) f.injective x y).mpr h)

omit [Fintype F] in
theorem pointIncl_injective : Function.Injective (pointIncl W f) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hP <;> simp_all [pointIncl, f.injective.eq_iff]

variable [W.IsElliptic] [DecidableEq K]

/-- **The points of `W_K` fixed by the base-changed Frobenius are the points of `W(F)`.**
PROVED. -/
theorem range_pointIncl :
    Set.range (pointIncl W f) =
      {P | (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = P} := by
  ext P
  constructor
  · rintro ⟨(_ | ⟨x, y, h⟩), rfl⟩
    · exact Isogeny.Hom.pointMap_zero _
    · change (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap (.some _ _ _) = .some _ _ _
      rw [pointMap_frobeniusMap_some]
      simp only [← map_pow, FiniteField.pow_card]
  · rcases P with _ | ⟨a, b, h⟩
    · exact fun _ => ⟨.zero, rfl⟩
    · intro hfix
      change (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap (.some _ _ _) = .some _ _ _
        at hfix
      rw [pointMap_frobeniusMap_some, Point.some.injEq] at hfix
      obtain ⟨x, rfl⟩ := mem_range_of_pow_card_eq f hfix.1
      obtain ⟨y, rfl⟩ := mem_range_of_pow_card_eq f hfix.2
      exact ⟨.some x y ((map_nonsingular (W := W) f.injective x y).mp h), rfl⟩

/-- **Frobenius-fixed points of `W_K` ↔ points of `W(F)`**: there are exactly `|W(F)|` of them.
PROVED. -/
theorem natCard_fixedPoints :
    Nat.card {P : (W.map f).Point //
      (Isogeny.Hom.ofIsogeny (frobeniusMap W f)).pointMap P = P} = Nat.card W.Point := by
  have e := Equiv.ofInjective _ (pointIncl_injective W f)
  rw [range_pointIncl] at e
  exact (Nat.card_congr e).symm

end ZInQ.Contrib.CloudB3RC53.Frobenius
