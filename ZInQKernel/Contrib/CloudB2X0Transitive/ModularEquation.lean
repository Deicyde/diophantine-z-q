import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Reduction
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_dedekindPsi_prime_pow

/-!
# `X₀(N)`-transitivity from the modular equation for the generic curve (flt-cqj)

`ZInQ.RLeaf.X0Transitive` (row H-41) is derived from one hypothesis, `FltCqj.ModularEquationGeneric`: for
every cyclic subgroup `C` of order `N` of `E_j` over `\overline{ℚ(j)}`, `j(E_j/C)` (Anthropic FLT's iterated
Vélu `cyclicQuotientJ`) is a root of `Φ_N(X, j)`. This is the `MapsTo` half of `CyclicQuotientJBijOn`
(`Bridge.lean`) at `K = ℚ`, `L = \overline{ℚ(j)}`, `E = E_j` (`modularEquationGeneric_of_bijOn`), so the
hypothesis of `Reduction.lean` is replaced by a strictly weaker one. The other half of the bijection is
proved here:

* `ncard_cyclic_sq`: `(ℤ/N)²` has exactly `ψ(N)` cyclic subgroups of order `N` (via
  `#{a ∈ (ℤ/N)² | ord a = N} = ψ(N) φ(N)`, CRT and prime powers), hence (T36, proved in the kernel) so has
  `E_j[N]` (`ncard_cyclic_ejBar`);
* `bijOn_of_modularEquation`: the image of `C ↦ j(E_j/C)` is Galois-stable, `Φ_N(X, j)` is irreducible over
  `ℚ(j)` (Anthropic FLT, ported), so the map is onto the roots; `Φ_N(X, j)` is separable of degree `ψ(N)`,
  so both sides have `ψ(N)` elements and the map is injective;
* `x0Transitive_of_modularEquationGeneric`: the argument of `Bridge.lean` with this bijection.

New code (not vendored text); it uses the vendored FLT theorems under `Vendor/AnthropicFLT/` (Apache-2.0, see
`Vendor/AnthropicFLT/LICENSE`, `NOTICE.upstream`). No `sorry`, no `axiom`, no `native_decide`.
-/

/-! ## Cyclic subgroups of order `N` of `(ℤ/N)²` (counting glue)

`#{a ∈ (ℤ/N)² | ord a = N} = ψ(N) φ(N)` and hence a finite abelian group `G ≅ (ℤ/N)²` has exactly `ψ(N)`
cyclic subgroups of order `N` (`ψ` = FLT's `ModularCurve.dedekindPsi`). -/

open Finset

namespace FltCqj

/-- In `ℤ/n`, the elements of order dividing `d ∣ n` number `d`. -/
theorem card_addOrderOf_dvd_zmod (n d : ℕ) [NeZero n] (hd : d ∣ n) :
    #{x : ZMod n | addOrderOf x ∣ d} = d := by
  classical
  have hd0 : d ≠ 0 := fun h => NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hsplit : #{x : ZMod n | addOrderOf x ∣ d} =
      ∑ e ∈ d.divisors, #{x : ZMod n | addOrderOf x = e} := by
    rw [card_eq_sum_card_fiberwise (f := fun x => addOrderOf x) (t := d.divisors)]
    · refine sum_congr rfl fun e he => ?_
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro h; exact ⟨h ▸ (Nat.mem_divisors.mp he).1, h⟩
    · intro x hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
      exact Nat.mem_divisors.mpr ⟨hx, hd0⟩
  rw [hsplit]
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  calc ∑ e ∈ d.divisors, #{x : ZMod n | addOrderOf x = e}
      = ∑ e ∈ d.divisors, Nat.totient e := by
        refine sum_congr rfl fun e he => ?_
        exact IsAddCyclic.card_addOrderOf_eq_totient
          (by rw [hcard]; exact Nat.dvd_trans (Nat.mem_divisors.mp he).1 hd)
    _ = d := Nat.sum_totient d

/-- In `(ℤ/n)²`, the elements of order dividing `d ∣ n` number `d²`. -/
theorem card_addOrderOf_dvd_sq (n d : ℕ) [NeZero n] (hd : d ∣ n) :
    #{a : ZMod n × ZMod n | addOrderOf a ∣ d} = d * d := by
  classical
  have : ({a : ZMod n × ZMod n | addOrderOf a ∣ d} : Finset _) =
      ({x : ZMod n | addOrderOf x ∣ d} : Finset _) ×ˢ ({x : ZMod n | addOrderOf x ∣ d} : Finset _) := by
    ext ⟨x, y⟩
    simp [Prod.addOrderOf_mk, Nat.lcm_dvd_iff]
  rw [this, card_product, card_addOrderOf_dvd_zmod n d hd]

/-- `J(N) = #{a ∈ (ℤ/N)² | ord a = N}`. -/
noncomputable def J (N : ℕ) : ℕ := Nat.card {a : ZMod N × ZMod N // addOrderOf a = N}

theorem J_eq_card (N : ℕ) [NeZero N] : J N = #{a : ZMod N × ZMod N | addOrderOf a = N} := by
  classical
  rw [J, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `J(p^k) = p^{2k} - p^{2(k-1)}`, in the form `J(p^k) + (p^{k-1})² = (p^k)²`. -/
theorem J_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    J (p ^ k) + p ^ (k - 1) * p ^ (k - 1) = p ^ k * p ^ k := by
  classical
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [J_eq_card, ← card_addOrderOf_dvd_sq (p ^ k) (p ^ (k - 1)) (pow_dvd_pow p (Nat.sub_le k 1))]
  have htot : #(univ : Finset (ZMod (p ^ k) × ZMod (p ^ k))) = p ^ k * p ^ k := by
    rw [card_univ, Fintype.card_prod, ZMod.card]
  rw [← htot, ← card_union_of_disjoint]
  · congr 1
    ext a
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    have hdvd : addOrderOf a ∣ p ^ k := by
      refine addOrderOf_dvd_of_nsmul_eq_zero (Prod.ext ?_ ?_)
      · rw [Prod.smul_fst, Prod.fst_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      · rw [Prod.smul_snd, Prod.snd_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.lt_or_ge j k with h | h
    · right; rw [hj']; exact pow_dvd_pow p (by omega)
    · left; rw [hj', le_antisymm hj h]
  · rw [disjoint_filter]
    intro a _ h1 h2
    rw [h1, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
    omega

/-- Orders of elements of `(ℤ/n)²` divide `n`. -/
theorem addOrderOf_dvd_sq (n : ℕ) (a : ZMod n × ZMod n) : addOrderOf a ∣ n := by
  refine addOrderOf_dvd_of_nsmul_eq_zero (Prod.ext ?_ ?_)
  · rw [Prod.smul_fst, Prod.fst_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · rw [Prod.smul_snd, Prod.snd_zero, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- For `x ∣ m`, `y ∣ n` with `m, n` coprime and positive: `lcm x y = m n ↔ x = m ∧ y = n`. -/
theorem lcm_eq_mul_iff {m n x y : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) (hx : x ∣ m)
    (hy : y ∣ n) : x.lcm y = m * n ↔ x = m ∧ y = n := by
  constructor
  · intro hl
    have hc : x.Coprime y := (h.coprime_dvd_left hx).coprime_dvd_right hy
    rw [hc.lcm_eq_mul] at hl
    have hxm := Nat.le_of_dvd hm hx
    have hyn := Nat.le_of_dvd hn hy
    have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx hm
    have hy0 : 0 < y := Nat.pos_of_dvd_of_pos hy hn
    constructor
    · by_contra hne
      have : x * y < m * n := Nat.mul_lt_mul_of_lt_of_le (lt_of_le_of_ne hxm hne) hyn hn
      omega
    · by_contra hne
      have : x * y < m * n := Nat.mul_lt_mul_of_le_of_lt hxm (lt_of_le_of_ne hyn hne) hm
      omega
  · rintro ⟨rfl, rfl⟩
    exact h.lcm_eq_mul

/-- `J` is multiplicative (Chinese remainder theorem). -/
theorem J_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) : J (m * n) = J m * J n := by
  let c : ZMod (m * n) ≃+ ZMod m × ZMod n := (ZMod.chineseRemainder h).toAddEquiv
  let e : ZMod (m * n) × ZMod (m * n) ≃+ (ZMod m × ZMod m) × (ZMod n × ZMod n) :=
    (c.prodCongr c).trans (AddEquiv.prodProdProdComm _ _ _ _)
  have h1 : J (m * n) =
      Nat.card {b : (ZMod m × ZMod m) × (ZMod n × ZMod n) // addOrderOf b = m * n} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun a => by
      simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AddEquiv.addOrderOf_eq])
  have h2 : Nat.card {b : (ZMod m × ZMod m) × (ZMod n × ZMod n) // addOrderOf b = m * n} =
      Nat.card ({x : ZMod m × ZMod m // addOrderOf x = m} × {y : ZMod n × ZMod n // addOrderOf y = n}) :=
    Nat.card_congr ((Equiv.subtypeEquivRight fun b => by
      rw [Prod.addOrderOf]
      exact lcm_eq_mul_iff hm hn h (addOrderOf_dvd_sq m b.1) (addOrderOf_dvd_sq n b.2)).trans
      Equiv.subtypeProdEquivProd)
  rw [h1, h2, Nat.card_prod, J, J]

/-- `J(N) = ψ(N) φ(N)` for `N > 0`. -/
theorem J_eq (N : ℕ) (hN : 0 < N) : J N = ModularCurve.dedekindPsi N * N.totient := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hp' : p.Prime := hp
    have hJ := J_prime_pow p k hp' hk
    rw [ModularCurve.dedekindPsi_prime_pow p k hp' hk.ne', Nat.totient_prime_pow hp' hk]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hJ ⊢
    rw [pow_succ] at hJ ⊢
    have hp1 : 1 ≤ p := hp'.one_lt.le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith [hJ]
  | zero => omega
  | one => simp [J, ModularCurve.dedekindPsi_one]
  | coprime a b ha hb hab iha ihb =>
    rw [J_mul a b (by omega) (by omega) hab, iha (by omega), ihb (by omega),
      ModularCurve.dedekindPsi_mul_of_coprime a b hab, Nat.totient_mul hab]
    ring

/-- Two elements with the same finite order, one in the cyclic subgroup of the other, generate the
same subgroup. -/
theorem zmultiples_eq_of_mem {G : Type*} [AddGroup G] [Finite G] {a b : G}
    (hb : b ∈ AddSubgroup.zmultiples a) (h : addOrderOf b = addOrderOf a) :
    AddSubgroup.zmultiples b = AddSubgroup.zmultiples a :=
  AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hb)
    (by rw [Nat.card_zmultiples, Nat.card_zmultiples, h])

/-- **Cyclic subgroups of order `N` versus elements of order `N`**: in a finite abelian group,
`#{cyclic H of order N} · φ(N) = #{a | ord a = N}`. -/
theorem ncard_cyclic_mul_totient {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (N : ℕ) :
    {H : AddSubgroup G | IsAddCyclic H ∧ Nat.card H = N}.ncard * N.totient =
      #{a : G | addOrderOf a = N} := by
  classical
  set A : Finset G := univ.filter fun a : G => addOrderOf a = N with hA
  have himg : {H : AddSubgroup G | IsAddCyclic H ∧ Nat.card H = N} =
      ↑(A.image AddSubgroup.zmultiples) := by
    ext H
    simp only [Set.mem_ofPred_eq, coe_image, Set.mem_image, hA, coe_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hc, hcard⟩
      obtain ⟨g, hg⟩ := hc.exists_generator
      have hog : addOrderOf (g : G) = N := by
        rw [AddSubgroup.addOrderOf_coe, addOrderOf_eq_card_of_forall_mem_zmultiples hg, hcard]
      refine ⟨g, hog, AddSubgroup.eq_of_le_of_card_ge
        (AddSubgroup.zmultiples_le.mpr g.2) ?_⟩
      rw [Nat.card_zmultiples, hog, hcard]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨inferInstance, by rw [Nat.card_zmultiples, ha]⟩
  rw [himg, Set.ncard_coe_finset, card_eq_sum_card_image AddSubgroup.zmultiples A]
  rw [sum_const_nat (m := N.totient)]
  intro H hH
  obtain ⟨a0, ha0, rfl⟩ := mem_image.mp hH
  have ha0' : addOrderOf a0 = N := (mem_filter.mp ha0).2
  have hcardH : Fintype.card (AddSubgroup.zmultiples a0) = N := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zmultiples, ha0']
  have htot : #{x : AddSubgroup.zmultiples a0 | addOrderOf x = N} = N.totient :=
    IsAddCyclic.card_addOrderOf_eq_totient (by rw [hcardH])
  rw [← htot, ← card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext y
  simp only [mem_filter, hA, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hy, hz⟩
    refine ⟨⟨y, hz ▸ AddSubgroup.mem_zmultiples y⟩, ?_, rfl⟩
    rw [← AddSubgroup.addOrderOf_coe]; exact hy
  · rintro ⟨x, hx, rfl⟩
    have hx' : addOrderOf (x : G) = N := by rw [AddSubgroup.addOrderOf_coe]; exact hx
    exact ⟨hx', zmultiples_eq_of_mem x.2 (hx'.trans ha0'.symm)⟩

/-- **`(ℤ/N)²` has `ψ(N)` cyclic subgroups of order `N`.** -/
theorem ncard_cyclic_sq (N : ℕ) [NeZero N] :
    {H : AddSubgroup (ZMod N × ZMod N) | IsAddCyclic H ∧ Nat.card H = N}.ncard =
      ModularCurve.dedekindPsi N := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h := ncard_cyclic_mul_totient (G := ZMod N × ZMod N) N
  rw [← J_eq_card, J_eq N hN] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hN) h

end FltCqj

/-! ## The generic curve: the modular equation implies the bijection and `X₀(N)`-transitivity -/

namespace FltCqj

open LeafModCurves WeierstrassCurve Polynomial ZInQ.Contrib.CloudB2X0Transitive

/-- **The modular equation for the generic elliptic curve** (Kronecker; leaf candidate). For every
`N > 0` and every cyclic subgroup `C` of order `N` of `E_j` over `\overline{ℚ(j)}`, the quotient
`j`-invariant `j(E_j/C)` (iterated Vélu, Anthropic FLT's `WeierstrassCurve.cyclicQuotientJ`) is a root of
the modular polynomial `Φ_N(X, j)` (any `ModularCurve.ModularPolynomialData N`: the monic `Φ ∈ ℤ[j][X]`
of degree `ψ(N)` with `Φ(j(q^N), j(q)) = 0`, which determines it).

Sources: over `ℂ`, `Φ_N(X, j(τ)) = ∏ (X − j(γτ))` over the `ψ(N)` primitive matrices `γ` of determinant
`N` modulo `SL₂(ℤ)` (Cox, *Primes of the form x² + ny²*, Thm 11.18; Lang, *Elliptic functions*, Ch. 5,
§2, Thm 3; numbers UNVERIFIED), the curves `ℂ/Λ'` for the lattices `Λ' ⊃ Λ_τ` of cyclic index `N` being
the quotients `E_τ/C`, which Vélu's formulas compute up to isomorphism (Vélu, C. R. Acad. Sci. Paris
273 (1971), UNVERIFIED); the generic case follows by an embedding `\overline{ℚ(j)} ↪ ℂ` sending `j` to a
transcendental value (the base-change compatibility of `cyclicQuotientJ` is Anthropic FLT's
`cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed`). It is the `MapsTo` half of
`CyclicQuotientJBijOn` at `K = ℚ`, `L = \overline{ℚ(j)}`, `E = E_j` (`modularEquationGeneric_of_bijOn`). -/
def ModularEquationGeneric : Prop :=
  ∀ (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (H : AddSubgroup EjBar.toAffine.Point), IsAddCyclic H → Nat.card H = N →
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar)
        (algebraMap Qj Kbar RatFunc.X))).IsRoot (EjBar.cyclicQuotientJ H N)

/-- `j(E_j) = j` in `\overline{ℚ(j)}` (with the global instances). -/
theorem ejBar_j' : EjBar.j = algebraMap Qj Kbar RatFunc.X := by
  show (Ej.map (algebraMap Qj Kbar)).j = _
  rw [WeierstrassCurve.map_j, Ej_j]

/-- The modular equation is implied by the FLT bijection (so it is the smaller statement). -/
theorem modularEquationGeneric_of_bijOn (hB : CyclicQuotientJBijOn) : ModularEquationGeneric := by
  intro N _ data H hc hcard
  have hT : Transcendental ℚ EjBar.j := by
    rw [ejBar_j', transcendental_algebraMap_iff (algebraMap Qj Kbar).injective]
    convert RatFunc.transcendental_X (K := ℚ)
    exact Subsingleton.elim _ _
  have hNK : (N : Kbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h := (hB ℚ N data Kbar hNK EjBar hT).mapsTo ⟨hc, hcard⟩
  rw [← ejBar_j']
  exact h

/-- Elements of a subgroup of order `N` are `N`-torsion. -/
theorem le_nTors {N : ℕ} {H : AddSubgroup EjBar.toAffine.Point} (hcard : Nat.card H = N) :
    H ≤ X1Belyi.nTors EjBar N := by
  intro x hx
  show N • x = 0
  have h1 : N • (⟨x, hx⟩ : H) = 0 := by
    rw [← hcard]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard _)
  simpa using congrArg Subtype.val h1

/-- Transport of "cyclic of order `N`" along an injective hom. -/
theorem cyclic_map_iff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (hι : Function.Injective ι) (K : AddSubgroup A) (N : ℕ) :
    (IsAddCyclic (K.map ι) ∧ Nat.card (K.map ι) = N) ↔ (IsAddCyclic K ∧ Nat.card K = N) := by
  let e : K ≃+ K.map ι := K.equivMapOfInjective ι hι
  rw [Nat.card_congr e.toEquiv.symm]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨isAddCyclic_of_surjective e.symm e.symm.surjective, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨isAddCyclic_of_surjective e e.surjective, h2⟩

/-- **`E_j` has `ψ(N)` cyclic subgroups of order `N`** (T36, proved, and the count of `(ℤ/N)²`). -/
theorem ncard_cyclic_ejBar (N : ℕ) [NeZero N] :
    {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N}.ncard =
      ModularCurve.dedekindPsi N ∧
    {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N}.Finite := by
  obtain ⟨e⟩ := ZInQ.RLeaf.t36_torsionStructure Kbar EjBar N (Nat.pos_of_ne_zero (NeZero.ne N))
  let ι : ZMod N × ZMod N →+ EjBar.toAffine.Point :=
    (X1Belyi.nTors EjBar N).subtype.comp e.symm.toAddMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hrange : ι.range = X1Belyi.nTors EjBar N := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩; exact (e.symm v).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp [ι]⟩
  have himg : {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N} =
      AddSubgroup.map ι '' {K : AddSubgroup (ZMod N × ZMod N) | IsAddCyclic K ∧ Nat.card K = N} := by
    ext H
    constructor
    · rintro ⟨hc, hcard⟩
      have hle : H ≤ ι.range := hrange ▸ le_nTors hcard
      refine ⟨H.comap ι, ?_, AddSubgroup.map_comap_eq_self hle⟩
      rw [Set.mem_ofPred_eq, ← cyclic_map_iff ι hι, AddSubgroup.map_comap_eq_self hle]
      exact ⟨hc, hcard⟩
    · rintro ⟨K, hK, rfl⟩
      exact (cyclic_map_iff ι hι K N).mpr hK
  have hfin : {K : AddSubgroup (ZMod N × ZMod N) | IsAddCyclic K ∧ Nat.card K = N}.Finite :=
    Set.toFinite _
  rw [himg]
  exact ⟨by rw [Set.ncard_image_of_injective _ (AddSubgroup.map_injective hι), ncard_cyclic_sq N],
    hfin.image _⟩

/-- `ψ(N) > 0`. -/
theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < ModularCurve.dedekindPsi N := by
  have h1 : N / 1 ≤ ModularCurve.dedekindPsi N := by
    unfold ModularCurve.dedekindPsi
    exact Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd N, NeZero.ne N⟩, squarefree_one⟩)
  have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [Nat.div_one] at h1
  omega

/-- Galois equivariance of `C ↦ j(E_j/C)` (Anthropic FLT's theorem, with `E_j^σ = E_j`), for any point
map `g` acting as `σ` on coordinates (e.g. `galPt σ`). -/
theorem cyclicQuotientJ_galPt (σ : Kbar ≃ₐ[Qj] Kbar) (g : EjBar.toAffine.Point →+ EjBar.toAffine.Point)
    (hg : ∀ (x y : Kbar) (h : EjBar.toAffine.Nonsingular x y),
      ∃ h', g (.some x y h) = .some (σ x) (σ y) h')
    (H : AddSubgroup EjBar.toAffine.Point) (N : ℕ) :
    EjBar.cyclicQuotientJ (H.map g) N = σ (EjBar.cyclicQuotientJ H N) :=
  (cyclicQuotientJ_congr (σ : Kbar →+* Kbar) (ejBar_map_algEquiv σ) _ g
      (fun _ _ _ => ⟨_, rfl⟩) hg H N).symm.trans
    (WeierstrassCurve.cyclicQuotientJ_map_eq_apply_cyclicQuotientJ_of_isAlgClosed
      (σ : Kbar →+* Kbar) EjBar H N)

/-- **The cyclic-quotient bijection for the generic curve, from the modular equation**: with
`ModularEquationGeneric`, `C ↦ j(E_j/C)` is a bijection from the cyclic subgroups of order `N` of `E_j`
over `\overline{ℚ(j)}` onto the roots of `Φ_N(X, j)`. (Surjective: the image is Galois-stable and
`Φ_N(X, j)` is irreducible over `ℚ(j)`; injective: both sets have `ψ(N)` elements, the roots because
`Φ_N(X, j)` is separable of degree `ψ(N)`.) -/
theorem bijOn_of_modularEquation (hA : ModularEquationGeneric) (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    Set.BijOn (fun H : AddSubgroup EjBar.toAffine.Point => EjBar.cyclicQuotientJ H N)
      {H | IsAddCyclic H ∧ Nat.card H = N}
      {y | (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar)
        (algebraMap Qj Kbar RatFunc.X))).IsRoot y} := by
  set S := {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N} with hS
  set Φj := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar) (algebraMap Qj Kbar RatFunc.X))
    with hΦj
  set p : Polynomial Qj := (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)) with hp
  have hirr : Irreducible p :=
    ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero ℚ N data
      (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have hmon : p.Monic := (data.monic.map _).map _
  have hpmap : p.map (algebraMap Qj Kbar) = Φj := by
    rw [hp, hΦj, Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_X, RatFunc.algebraMap_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hdeg : p.natDegree = ModularCurve.dedekindPsi N := by
    rw [hp, (data.monic.map _).natDegree_map, data.monic.natDegree_map, data.natDegree_eq]
  have hR : {y | Φj.IsRoot y} = p.rootSet Kbar := by
    ext y
    rw [Set.mem_ofPred_eq, Polynomial.mem_rootSet, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, hpmap]
    exact ⟨fun h => ⟨hmon.ne_zero, h⟩, fun h => h.2⟩
  have hRcard : (p.rootSet Kbar).ncard = ModularCurve.dedekindPsi N := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Polynomial.card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hirr)
        (IsAlgClosed.splits _), hdeg]
  have hmin : ∀ z : Kbar, Φj.IsRoot z → minpoly Qj z = p := by
    intro z hz
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ hmon).symm
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hpmap]
    exact hz
  obtain ⟨hScard, hSfin⟩ := ncard_cyclic_ejBar N
  have hmaps : Set.MapsTo (fun H : AddSubgroup EjBar.toAffine.Point => EjBar.cyclicQuotientJ H N) S
      {y | Φj.IsRoot y} := fun H hH => hA N data H hH.1 hH.2
  have hsurj : Set.SurjOn (fun H : AddSubgroup EjBar.toAffine.Point => EjBar.cyclicQuotientJ H N) S
      {y | Φj.IsRoot y} := by
    intro y hy
    obtain ⟨H0, hH0⟩ : S.Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [hScard]; exact (dedekindPsi_pos N).ne')
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp
      ((Normal.minpoly_eq_iff_mem_orbit Kbar).mp ((hmin _ hy).trans (hmin _ (hmaps hH0)).symm))
    rw [AlgEquiv.smul_def] at hσ
    let g : EjBar.toAffine.Point →+ EjBar.toAffine.Point :=
      WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom
    refine ⟨H0.map g, ?_, ?_⟩
    · exact (cyclic_map_iff g (WeierstrassCurve.Affine.Point.map_injective _) H0 N).mpr hH0
    · show EjBar.cyclicQuotientJ (H0.map g) N = y
      exact (cyclicQuotientJ_galPt σ g
        (fun _ _ h => ⟨_, WeierstrassCurve.Affine.Point.map_some (W' := Ej) σ.toAlgHom h⟩) H0 N).trans hσ
  have himg : (fun H : AddSubgroup EjBar.toAffine.Point => EjBar.cyclicQuotientJ H N) '' S =
      {y | Φj.IsRoot y} := subset_antisymm hmaps.image_subset hsurj
  refine ⟨hmaps, Set.injOn_of_ncard_image_eq ?_ hSfin, hsurj⟩
  rw [himg, hR, hRcard, hScard]

/-- **`X₀(N)`-transitivity from the modular equation for the generic curve** (`ZInQ.RLeaf.X0Transitive`,
row H-41). -/
theorem x0Transitive_of_modularEquationGeneric (hA : ModularEquationGeneric) :
    ZInQ.RLeaf.X0Transitive := by
  intro N P P' hN hP hP'
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hbij := bijOn_of_modularEquation hA N data
  set p : Polynomial Qj := (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)) with hp
  have hirr : Irreducible p :=
    ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero ℚ N data
      (Nat.cast_ne_zero.mpr hN.ne')
  have hmon : p.Monic := (data.monic.map _).map _
  have hpmap : p.map (algebraMap Qj Kbar) =
      data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar) (algebraMap Qj Kbar RatFunc.X)) := by
    rw [hp, Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_X, RatFunc.algebraMap_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hmin : ∀ z : Kbar,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Kbar)
        (algebraMap Qj Kbar RatFunc.X))).IsRoot z → minpoly Qj z = p := by
    intro z hz
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ hmon).symm
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hpmap]
    exact hz
  have hcyc : ∀ Q : EjBar.toAffine.Point, addOrderOf Q = N →
      AddSubgroup.zmultiples Q ∈
        {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N} :=
    fun Q hQ => ⟨inferInstance, by rw [Nat.card_zmultiples, hQ]⟩
  have hy := hbij.mapsTo (hcyc P hP)
  have hy' := hbij.mapsTo (hcyc P' hP')
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit Kbar).mp ((hmin _ hy').trans (hmin _ hy).symm))
  rw [AlgEquiv.smul_def] at hσ
  refine ⟨σ, ?_⟩
  let g : EjBar.toAffine.Point →+ EjBar.toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom
  have hjeq : EjBar.cyclicQuotientJ ((AddSubgroup.zmultiples P).map g) N =
      EjBar.cyclicQuotientJ (AddSubgroup.zmultiples P') N := by
    exact (cyclicQuotientJ_galPt σ g
      (fun _ _ h => ⟨_, WeierstrassCurve.Affine.Point.map_some (W' := Ej) σ.toAlgHom h⟩) _ N).trans hσ
  have hginj : Function.Injective g := WeierstrassCurve.Affine.Point.map_injective _
  have hmz : (AddSubgroup.zmultiples P).map g = AddSubgroup.zmultiples (g P) :=
    AddMonoidHom.map_zmultiples g P
  have hHg : (AddSubgroup.zmultiples P).map g ∈
      {H : AddSubgroup EjBar.toAffine.Point | IsAddCyclic H ∧ Nat.card H = N} := by
    rw [hmz]
    exact hcyc _ ((addOrderOf_injective g hginj P).trans hP)
  have hsub := hbij.injOn hHg (hcyc P' hP') hjeq
  show g P ∈ AddSubgroup.zmultiples P'
  rw [← hsub]
  exact AddSubgroup.mem_map_of_mem g (AddSubgroup.mem_zmultiples P)

end FltCqj

#print axioms FltCqj.x0Transitive_of_modularEquationGeneric
#print axioms FltCqj.modularEquationGeneric_of_bijOn
