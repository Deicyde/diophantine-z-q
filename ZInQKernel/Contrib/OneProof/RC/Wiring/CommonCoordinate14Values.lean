import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate14Model

/-!
# The leaf's Frobenius data over `Λ`, and the coordinate on a rank-zero model

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-common-coordinate` (tex 4142–4194), with the inner
limit of Lemma `ex:limits-inner-limit` (tex 4385–4451): "Each finite tuple of matrix entries then
has a compatible limit at every coefficient precision, giving matrices over `Λ`. Every polynomial
identity between the matrices survives" (tex 4444–4448); and the minimal models of tex 4636–4640
("a minimal model obtained by cancelling unit entries; its ranks are the dimensions of the
cohomology").

Two independent pieces for the matrix data of a chain of relaxations (`ChainMat`, `FrobSeq`,
`CommonCoordinate14Model.lean`):

* **The leaf's Frobenius data over `Λ`.** `leafFrobΛ C Fam x ps : FrobSeq Λ` has at step `i` the
  data over `Λ` of the `i`-th prime `p = ps[i]` (of `p = 1` past the end of `ps`): `ρ_T(Fr_p)`,
  `p`, `p⁻¹ ∈ ℤ₂`, `a_p`, `z_p(x)`, `z_p(x)⁻¹` (`leafFrobΛ_apply`). `leafFrobΛ_map`: its
  push-forward along `Λ → F` has at every `i < |ps|` the values of `TriangleChain.AtLeaf`;
  `TriangleChain.AtLeaf.eq_leafFrobΛ_map`: a chain at the leaf's values carries exactly these data.
  The unit identities hold over `Λ` (`leafFrobΛ_q_mul_qi`, `leafFrobΛ_z_mul_zi`,
  `leafFrobΛ_trace_det`) and survive every ring homomorphism (`FrobSeq.map_q_mul_qi`,
  `FrobSeq.map_z_mul_zi`, `FrobSeq.map_trace`, `FrobSeq.map_det`); over `F` the two-place block
  is moreover invertible (`leafFrobΛ_map_units`).
* **The coordinate on a rank-zero model.** For a block complex over a field with
  `m₀ = m₁ = m₂ = 0` (`D¹ = H₁` and `D² = H₂` are lines, `d¹` is the single entry `d¹_{HH}`), the
  Knudsen–Mumford coordinate of `[z] ⊗ [λ]` in the orientation `σBlock` is the polynomial
  `ε z_H λ_H` with the sign `ε = −1` (`kmCoord_rankZero`). Degenerate cases: `d¹ ≠ 0` forces
  `z_H = λ_H = 0` (`rankZero_cycle_eq_zero`, `rankZero_closed_eq_zero`), and `z_H = 0` or
  `λ_H = 0` leaves the augmented complex without contraction (`rankZero_not_contraction_z`,
  `rankZero_not_contraction_lam`). Along a ring homomorphism `φ : R → F` the coordinate of pushed
  data is `φ(ε z_H λ_H)` (`kmCoord_rankZero_comp`, `kmCoord_rankZero_map`): a polynomial in the
  entries, so it commutes with the coefficient changes of the inner limit (tex 4444–4448).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate

/-! ### The unit identities survive push-forward -/

namespace FrobSeq

variable {R R' : Type} [CommRing R] [CommRing R'] (f : FrobSeq R) (φ : R →+* R') (i : ℕ)

/-- `q q⁻¹ = 1` survives push-forward (tex 4444–4448: "Every polynomial identity between the
matrices survives"). Kind: PROVED. -/
theorem map_q_mul_qi (h : f.q i * f.qi i = 1) : (f.map φ).q i * (f.map φ).qi i = 1 := by
  change φ (f.q i) * φ (f.qi i) = 1
  rw [← map_mul, h, map_one]

/-- `z z⁻¹ = 1` survives push-forward (tex 4444–4448). Kind: PROVED. -/
theorem map_z_mul_zi (h : f.z i * f.zi i = 1) : (f.map φ).z i * (f.map φ).zi i = 1 := by
  change φ (f.z i) * φ (f.zi i) = 1
  rw [← map_mul, h, map_one]

/-- `tr Fr = a` survives push-forward (tex 4444–4448). Kind: PROVED. -/
theorem map_trace (h : (f.Fr i).trace = f.a i) : ((f.map φ).Fr i).trace = (f.map φ).a i := by
  change ((f.Fr i).map φ).trace = φ (f.a i)
  rw [← h, AddMonoidHom.map_trace]

/-- `det Fr = q` survives push-forward (tex 4444–4448). Kind: PROVED. -/
theorem map_det (h : (f.Fr i).det = f.q i) : ((f.map φ).Fr i).det = (f.map φ).q i := by
  change ((f.Fr i).map φ).det = φ (f.q i)
  rw [← h, RingHom.map_det]
  rfl

end FrobSeq

/-! ### The leaf's Frobenius data over `Λ` -/

section LeafFrob

variable {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ)) (Fam : Family) (x : Addr Fam.b)

/-- **The leaf's Frobenius data over `Λ`** (tex 4142–4194, 4176–4184, 4444–4448): at step `i` the
data of the `i`-th prime `p = ps[i]` of the order `ps` (of `p = 1` past its end) over `Λ`: the
Frobenius `ρ_T(Fr_p)` with entries in `ℤ₂ ⊂ Λ`, `q = p`, `q⁻¹ = p⁻¹ ∈ ℤ₂` (`qInv`, the inverse of
the unit `p` for odd `p`), `a = a_p`, `z = z_p(x)` and `z⁻¹ = z_p(x)⁻¹`. Kind: definition. -/
def leafFrobΛ (ps : List ℕ) : FrobSeq Lambda where
  Fr i := (frobMat C (ps.getD i 1)).map PowerSeries.C
  q i := ((ps.getD i 1 : ℕ) : Lambda)
  qi i := PowerSeries.C (qInv (ps.getD i 1))
  a i := (apE ℓ (ps.getD i 1) : Lambda)
  z i := (zAt Fam x (ps.getD i 1) : Lambda)
  zi i := ((zAt Fam x (ps.getD i 1))⁻¹ : Lambdaˣ)

/-- The data of `leafFrobΛ` at a step `i < |ps|` are those of the prime `p = ps[i]`
(tex 4142–4194, 4176–4184). Kind: PROVED. -/
theorem leafFrobΛ_apply (ps : List ℕ) {i : ℕ} (hi : i < ps.length) :
    (leafFrobΛ C Fam x ps).Fr i = (frobMat C ps[i]).map PowerSeries.C ∧
      (leafFrobΛ C Fam x ps).q i = (ps[i] : Lambda) ∧
      (leafFrobΛ C Fam x ps).qi i = PowerSeries.C (qInv ps[i]) ∧
      (leafFrobΛ C Fam x ps).a i = (apE ℓ ps[i] : Lambda) ∧
      (leafFrobΛ C Fam x ps).z i = (zAt Fam x ps[i] : Lambda) ∧
      (leafFrobΛ C Fam x ps).zi i = ((zAt Fam x ps[i])⁻¹ : Lambdaˣ) := by
  have e : ps.getD i 1 = ps[i] := List.getD_eq_getElem ps 1 hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [leafFrobΛ, e]

/-- **The push-forward of the leaf's data to `F` has the leaf's values** (tex 4142–4194,
4444–4448): at a step `i < |ps|` with `p = ps[i]` odd, `(leafFrobΛ C Fam x ps).map lamToF` has the
values of `TriangleChain.AtLeaf`: `ρ_T(Fr_p)` over `F`, `p`, `p⁻¹`, `a_p`, `z_p(x)` and
`z_p(x)⁻¹`. Kind: PROVED. -/
theorem leafFrobΛ_map (ps : List ℕ) (i : ℕ) (hi : i < ps.length) (hodd : Odd ps[i]) :
    ((leafFrobΛ C Fam x ps).map lamToF).Fr i = (frobMat C ps[i]).map zTwoToF ∧
      ((leafFrobΛ C Fam x ps).map lamToF).q i = (ps[i] : FracLam) ∧
      ((leafFrobΛ C Fam x ps).map lamToF).qi i = (ps[i] : FracLam)⁻¹ ∧
      ((leafFrobΛ C Fam x ps).map lamToF).a i = (apE ℓ ps[i] : FracLam) ∧
      ((leafFrobΛ C Fam x ps).map lamToF).z i = lamToF (zAt Fam x ps[i] : Lambda) ∧
      ((leafFrobΛ C Fam x ps).map lamToF).zi i = lamToF ((zAt Fam x ps[i])⁻¹ : Lambdaˣ) := by
  obtain ⟨hFr, hq, hqi, ha, hz, hzi⟩ := leafFrobΛ_apply C Fam x ps hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((leafFrobΛ C Fam x ps).Fr i).map lamToF = _
    rw [hFr, Matrix.map_map]
    rfl
  · change lamToF ((leafFrobΛ C Fam x ps).q i) = _
    rw [hq, map_natCast]
  · change lamToF ((leafFrobΛ C Fam x ps).qi i) = _
    rw [hqi]
    exact zTwoToF_qInv hodd
  · change lamToF ((leafFrobΛ C Fam x ps).a i) = _
    rw [ha, map_intCast]
  · change lamToF ((leafFrobΛ C Fam x ps).z i) = _
    rw [hz]
  · change lamToF ((leafFrobΛ C Fam x ps).zi i) = _
    rw [hzi]

/-- A prime of an order of a set of graph primes is a graph prime (tex 4142–4194).
Kind: PROVED. -/
theorem getElem_mem_Q {ps : List ℕ} (hps : ps.toFinset ⊆ Fam.Q) {i : ℕ} (hi : i < ps.length) :
    ps[i] ∈ Fam.Q :=
  hps (List.mem_toFinset.2 (List.getElem_mem hi))

/-- An order of the unused primes is an order of a set of graph primes (tex 4142–4194).
Kind: PROVED. -/
theorem toFinset_subset_Q_of_unused {ps : List ℕ} (hps : ps.toFinset = unusedAt Fam x) :
    ps.toFinset ⊆ Fam.Q := by
  intro p hp
  rw [hps] at hp
  exact (mem_unusedAt.mp hp).1

/-- The primes of an order of odd graph primes are odd (tex 4142–4194, 4143). Kind: PROVED. -/
theorem odd_getElem (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2) {ps : List ℕ}
    (hps : ps.toFinset ⊆ Fam.Q) {i : ℕ} (hi : i < ps.length) : Odd ps[i] :=
  (hprime _ (getElem_mem_Q Fam hps hi)).1.odd_of_ne_two (hprime _ (getElem_mem_Q Fam hps hi)).2

/-- **`q q⁻¹ = 1` over `Λ`** (tex 4193: "`q^{-4}` is one also", 4444–4448) at every step whose
prime is odd, in particular past the end of `ps` (where `p = 1`). Kind: PROVED. -/
theorem leafFrobΛ_q_mul_qi (ps : List ℕ) (i : ℕ) (hodd : Odd (ps.getD i 1)) :
    (leafFrobΛ C Fam x ps).q i * (leafFrobΛ C Fam x ps).qi i = 1 := by
  change ((ps.getD i 1 : ℕ) : Lambda) * PowerSeries.C (qInv (ps.getD i 1)) = 1
  rw [← map_natCast PowerSeries.C, ← map_mul, natCast_mul_qInv hodd, map_one]

/-- **`z z⁻¹ = 1` over `Λ`** at every step (`z_p(x) ∈ Λ^×`; tex 4142–4194, 4444–4448).
Kind: PROVED. -/
theorem leafFrobΛ_z_mul_zi (ps : List ℕ) (i : ℕ) :
    (leafFrobΛ C Fam x ps).z i * (leafFrobΛ C Fam x ps).zi i = 1 :=
  Units.mul_inv (zAt Fam x (ps.getD i 1))

/-- **Trace and determinant over `Λ`** (tex 4157–4194, 4213, 4444–4448): at a step `i < |ps|`
whose prime is a good odd prime, `tr Fr = a` and `det Fr = q` (`trace_det_frobMat`).
Kind: PROVED. -/
theorem leafFrobΛ_trace_det (ps : List ℕ) {i : ℕ} (hi : i < ps.length) (hpr : ps[i].Prime)
    (hp2 : ps[i] ≠ 2) (hgood : Nonvanishing.GoodAt (Ecurve ℓ) ps[i]) :
    ((leafFrobΛ C Fam x ps).Fr i).trace = (leafFrobΛ C Fam x ps).a i ∧
      ((leafFrobΛ C Fam x ps).Fr i).det = (leafFrobΛ C Fam x ps).q i := by
  obtain ⟨hFr, hq, -, ha, -, -⟩ := leafFrobΛ_apply C Fam x ps hi
  obtain ⟨htr, hdet⟩ := trace_det_frobMat C (frobeniusTrace_proved (Ecurve ℓ)) hpr hp2 hgood
  rw [hFr, hq, ha]
  exact ⟨by rw [← AddMonoidHom.map_trace PowerSeries.C, htr, map_intCast],
    by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_natCast]⟩

/-- **The unit facts at the leaf's values over `F`** (tex 4142–4194, 4176–4184, 4444–4448): for
good odd graph primes and an order `ps` of graph primes, at every step `i < |ps|` the push-forward
`(leafFrobΛ C Fam x ps).map lamToF` has `q q⁻¹ = 1`, `tr Fr = a`, `det Fr = q`, and its two-place
block is invertible (`det = p⁴ l_p(x) ≠ 0`, `leaf_det_twoPlaceBlock_ne_zero`). For an order of
the unused primes use `toFinset_subset_Q_of_unused`. Kind: PROVED. -/
theorem leafFrobΛ_map_units (hprime : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2)
    (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q) {ps : List ℕ}
    (hps : ps.toFinset ⊆ Fam.Q) (i : ℕ) (hi : i < ps.length) :
    ((leafFrobΛ C Fam x ps).map lamToF).q i * ((leafFrobΛ C Fam x ps).map lamToF).qi i = 1 ∧
      (((leafFrobΛ C Fam x ps).map lamToF).Fr i).trace =
        ((leafFrobΛ C Fam x ps).map lamToF).a i ∧
      (((leafFrobΛ C Fam x ps).map lamToF).Fr i).det =
        ((leafFrobΛ C Fam x ps).map lamToF).q i ∧
      IsUnit (twoPlaceBlock (((leafFrobΛ C Fam x ps).map lamToF).Fr i)
        (((leafFrobΛ C Fam x ps).map lamToF).q i) (((leafFrobΛ C Fam x ps).map lamToF).z i)
        (((leafFrobΛ C Fam x ps).map lamToF).zi i)).det := by
  have hQ := getElem_mem_Q Fam hps hi
  obtain ⟨hpr, hp2⟩ := hprime _ hQ
  obtain ⟨hFr, hq, hqi, ha, hz, hzi⟩ := leafFrobΛ_map C Fam x ps i hi (hpr.odd_of_ne_two hp2)
  obtain ⟨htr, hdet⟩ := leafFr_trace_det C hpr hp2 (hgood _ hQ)
  rw [hFr, hq, hqi, ha, hz, hzi]
  exact ⟨mul_inv_cancel₀ (natCast_ne_zero_F hpr.ne_zero), htr, hdet,
    (leaf_det_twoPlaceBlock_ne_zero C Fam x hpr hp2 (hgood _ hQ)).isUnit⟩

/-- **A chain at the leaf's values carries the pushed leaf data** (tex 4142–4194, 4444–4448): if
`H.AtLeaf C Fam x ps` and the primes of `ps` are odd, then at every step `i < H.n` the Frobenius
data of `H` are those of `(leafFrobΛ C Fam x ps).map lamToF`. Kind: PROVED. -/
theorem TriangleChain.AtLeaf.eq_leafFrobΛ_map {ps : List ℕ} {H : TriangleChain FracLam}
    (hH : H.AtLeaf C Fam x ps) (hodd : ∀ i (hi : i < ps.length), Odd ps[i]) (i : ℕ)
    (hi : i < H.n) :
    H.Fr i = ((leafFrobΛ C Fam x ps).map lamToF).Fr i ∧
      H.q i = ((leafFrobΛ C Fam x ps).map lamToF).q i ∧
      H.qi i = ((leafFrobΛ C Fam x ps).map lamToF).qi i ∧
      H.a i = ((leafFrobΛ C Fam x ps).map lamToF).a i ∧
      H.z i = ((leafFrobΛ C Fam x ps).map lamToF).z i ∧
      H.zi i = ((leafFrobΛ C Fam x ps).map lamToF).zi i := by
  obtain ⟨hn, hv⟩ := hH
  have hi' : i < ps.length := hn ▸ hi
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hv i hi'
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := leafFrobΛ_map C Fam x ps i hi' (hodd i hi')
  exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm,
    a5.trans b5.symm, a6.trans b6.symm⟩

end LeafFrob

/-! ### The coordinate on a rank-zero model -/

section RankZero

open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex

/-- `Fin m` is empty when `m = 0` (the summands of a rank-zero model; tex 4636–4640).
Kind: PROVED. -/
theorem isEmpty_fin_of_eq_zero {m : ℕ} (h : m = 0) : IsEmpty (Fin m) := by
  subst h
  infer_instance

/-- **On a rank-zero model `d¹` is its single entry** (tex 4636–4640): with `m₀ = m₁ = m₂ = 0` the
index sets of `D¹` and `D²` are the points `H₁`, `H₂`, so `d¹ = 0` exactly when `d¹_{HH} = 0`.
Kind: PROVED. -/
theorem rankZero_d1_eq_zero_iff {S : Type} [CommRing S] (D : BlockComplex S) (h0 : D.m0 = 0)
    (h1 : D.m1 = 0) (h2 : D.m2 = 0) :
    D.d1 = 0 ↔ D.d1 (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inl ())) = 0 := by
  have := isEmpty_fin_of_eq_zero h0
  have := isEmpty_fin_of_eq_zero h1
  have := isEmpty_fin_of_eq_zero h2
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext (i | ⟨⟩ | i) (j | ⟨⟩ | j)
  all_goals first
    | exact isEmptyElim i
    | exact isEmptyElim j
    | exact h

variable {F : Type} [Field F]

/-- **A cycle of a rank-zero model with `d¹ ≠ 0` vanishes** (tex 3877–3892, 4636–4640):
`(d¹ z)_{H₂} = d¹_{HH} z_H`. Kind: PROVED. -/
theorem rankZero_cycle_eq_zero (D : BlockComplex F) (h0 : D.m0 = 0) (h1 : D.m1 = 0)
    (h2 : D.m2 = 0) {z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F} (hz : D.toFour.d1 *ᵥ z = 0)
    (hd : D.d1 ≠ 0) : z (Sum.inr (Sum.inl ())) = 0 := by
  have := isEmpty_fin_of_eq_zero h0
  have := isEmpty_fin_of_eq_zero h1
  have hd' := (rankZero_d1_eq_zero_iff D h0 h1 h2).not.1 hd
  have e := congrFun hz (Sum.inr (Sum.inl ()))
  change ∑ j, D.d1 (Sum.inr (Sum.inl ())) j * z j = 0 at e
  simp only [Fintype.sum_sum_type, Fintype.sum_empty, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.sum_singleton, zero_add, add_zero] at e
  exact (mul_eq_zero.mp e).resolve_left hd'

/-- **A closed functional of a rank-zero model with `d¹ ≠ 0` vanishes** (tex 3877–3892,
4636–4640): `(λ d¹)_{H₁} = λ_H d¹_{HH}`. Kind: PROVED. -/
theorem rankZero_closed_eq_zero (D : BlockComplex F) (h0 : D.m0 = 0) (h1 : D.m1 = 0)
    (h2 : D.m2 = 0) {lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F} (hlam : lam ᵥ* D.toFour.d1 = 0)
    (hd : D.d1 ≠ 0) : lam (Sum.inr (Sum.inl ())) = 0 := by
  have := isEmpty_fin_of_eq_zero h1
  have := isEmpty_fin_of_eq_zero h2
  have hd' := (rankZero_d1_eq_zero_iff D h0 h1 h2).not.1 hd
  have e := congrFun hlam (Sum.inr (Sum.inl ()))
  change ∑ j, lam j * D.d1 j (Sum.inr (Sum.inl ())) = 0 at e
  simp only [Fintype.sum_sum_type, Fintype.sum_empty, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.sum_singleton, zero_add, add_zero] at e
  exact (mul_eq_zero.mp e).resolve_right hd'

/-- **A vanishing class leaves no contraction** (tex 3877–3892, 4636–4640): on a rank-zero model a
cycle with `z_H = 0` is zero, so the augmented complex is not contractible
(`not_contraction_aug_zero_z`); its torsion and the coordinate vanish. Kind: PROVED. -/
theorem rankZero_not_contraction_z (D : BlockComplex F) (h0 : D.m0 = 0) (h1 : D.m1 = 0)
    {z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F} {lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F}
    (hz : D.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* D.toFour.d1 = 0)
    (hzH : z (Sum.inr (Sum.inl ())) = 0) :
    ¬ Nonempty (Contraction (D.toFour.aug z lam hz hlam).toBased) := by
  have := isEmpty_fin_of_eq_zero h0
  have := isEmpty_fin_of_eq_zero h1
  have hz0 : z = 0 := by
    funext j
    rcases j with j | ⟨⟩ | j
    · exact isEmptyElim j
    · exact hzH
    · exact isEmptyElim j
  subst hz0
  exact not_contraction_aug_zero_z D.toFour hz hlam

/-- **A vanishing functional leaves no contraction** (tex 3877–3892, 4636–4640): on a rank-zero
model a closed functional with `λ_H = 0` is zero, so the augmented complex is not contractible
(`not_contraction_aug_zero_lam`). Kind: PROVED. -/
theorem rankZero_not_contraction_lam (D : BlockComplex F) (h1 : D.m1 = 0) (h2 : D.m2 = 0)
    {z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F} {lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F}
    (hz : D.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* D.toFour.d1 = 0)
    (hlH : lam (Sum.inr (Sum.inl ())) = 0) :
    ¬ Nonempty (Contraction (D.toFour.aug z lam hz hlam).toBased) := by
  have := isEmpty_fin_of_eq_zero h1
  have := isEmpty_fin_of_eq_zero h2
  have hl0 : lam = 0 := by
    funext j
    rcases j with j | ⟨⟩ | j
    · exact isEmptyElim j
    · exact hlH
    · exact isEmptyElim j
  subst hl0
  exact not_contraction_aug_zero_lam D.toFour hz hlam

/-- **The coordinate on a rank-zero model is a polynomial** (tex 3877–3892, 4636–4640, 5577–5595):
for a block complex over a field with `m₀ = m₁ = m₂ = 0` (`D¹ = H₁`, `D² = H₂` lines, `d¹` the
single entry `d¹_{HH}`), a cycle `z` and a closed functional `λ`, the Knudsen–Mumford coordinate of
`[z] ⊗ [λ]` in the orientation `σBlock` is `ε z_H λ_H` with the sign `ε = −1` (the convention
`kmCoord = −τ`). There are no Smith disks, `α = z_H`, `β = λ_H`, and the remaining map `H₁ → H₂`
is `d¹_{HH}` (`kmCoord_block`); if it is nonzero then `z_H = 0` (`rankZero_cycle_eq_zero`) and
both sides vanish. Kind: PROVED. -/
theorem kmCoord_rankZero (D : BlockComplex F) (h0 : D.m0 = 0) (h1 : D.m1 = 0) (h2 : D.m2 = 0)
    (z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F) (lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F)
    (hz : D.toFour.d1 *ᵥ z = 0) (hlam : lam ᵥ* D.toFour.d1 = 0) :
    kmCoord D.toFour z lam hz hlam (σBlock D.m0 D.m1 D.m2) =
      (-1) * z (Sum.inr (Sum.inl ())) * lam (Sum.inr (Sum.inl ())) := by
  have := isEmpty_fin_of_eq_zero h0
  have := isEmpty_fin_of_eq_zero h1
  have := isEmpty_fin_of_eq_zero h2
  have hA0 : IsUnit D.A0.det := by rw [Matrix.det_isEmpty]; exact isUnit_one
  have hA1 : IsUnit D.A1.det := by rw [Matrix.det_isEmpty]; exact isUnit_one
  have hA2 : IsUnit D.A2.det := by rw [Matrix.det_isEmpty]; exact isUnit_one
  have hα : D.alphaB z = z (Sum.inr (Sum.inl ())) := by
    simp [BlockComplex.alphaB, dotProduct]
  have hβ : D.betaB lam = lam (Sum.inr (Sum.inl ())) := by
    simp [BlockComplex.betaB, dotProduct]
  have hR : D.hRem = D.d1 (Sum.inr (Sum.inl ())) (Sum.inr (Sum.inl ())) := by
    simp [BlockComplex.hRem, dotProduct]
  rw [kmCoord_block z lam hz hlam hA0 hA1 hA2, hα, hβ, hR]
  simp only [Matrix.det_isEmpty, inv_one, mul_one]
  split_ifs with hd
  · ring
  · rw [rankZero_cycle_eq_zero D h0 h1 h2 hz ((rankZero_d1_eq_zero_iff D h0 h1 h2).not.2 hd)]
    ring

/-- **The coordinate along a ring homomorphism** (tex 4444–4448: "Every polynomial identity
between the matrices survives"; tex 4636–4640): for `φ : R →+* F` and a cycle and a closed
functional over `R` pushed to `F`, the coordinate on a rank-zero model is `φ (ε z_H λ_H)`,
`ε = −1`, the image of the pairing over `R`. Kind: PROVED. -/
theorem kmCoord_rankZero_comp {R : Type} [CommRing R] (φ : R →+* F) (D : BlockComplex F)
    (h0 : D.m0 = 0) (h1 : D.m1 = 0) (h2 : D.m2 = 0) (z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → R)
    (lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → R) (hz : D.toFour.d1 *ᵥ (φ ∘ z) = 0)
    (hlam : (φ ∘ lam) ᵥ* D.toFour.d1 = 0) :
    kmCoord D.toFour (φ ∘ z) (φ ∘ lam) hz hlam (σBlock D.m0 D.m1 D.m2) =
      φ ((-1) * z (Sum.inr (Sum.inl ())) * lam (Sum.inr (Sum.inl ()))) := by
  rw [kmCoord_rankZero D h0 h1 h2, map_mul, map_mul, map_neg, map_one]
  rfl

/-- A cycle over `R` is a cycle of the pushed model (tex 4444–4448). Kind: PROVED. -/
theorem blockComplex_map_cycle {R : Type} [CommRing R] (φ : R →+* F) (D : BlockComplex R)
    {z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → R} (hz : D.d1 *ᵥ z = 0) :
    (D.map φ).toFour.d1 *ᵥ (φ ∘ z) = 0 := by
  change D.d1.map φ *ᵥ (φ ∘ z) = 0
  funext a
  rw [← RingHom.map_mulVec, hz, Pi.zero_apply, map_zero, Pi.zero_apply]

/-- A closed functional over `R` is closed on the pushed model (tex 4444–4448). Kind: PROVED. -/
theorem blockComplex_map_closed {R : Type} [CommRing R] (φ : R →+* F) (D : BlockComplex R)
    {lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → R} (hlam : lam ᵥ* D.d1 = 0) :
    (φ ∘ lam) ᵥ* (D.map φ).toFour.d1 = 0 := by
  change (φ ∘ lam) ᵥ* D.d1.map φ = 0
  funext a
  rw [← RingHom.map_vecMul, hlam, Pi.zero_apply, map_zero, Pi.zero_apply]

/-- **The coordinate of a pushed rank-zero model** (tex 4444–4448, 4636–4640): for a rank-zero
block complex over `R`, a cycle and a closed functional over `R`, and `φ : R →+* F`, the
coordinate of the pushed data is `φ (ε z_H λ_H)`, `ε = −1`: the coordinate over the field is the
image of the pairing over the coefficient ring. Kind: PROVED. -/
theorem kmCoord_rankZero_map {R : Type} [CommRing R] (φ : R →+* F) (D : BlockComplex R)
    (h0 : D.m0 = 0) (h1 : D.m1 = 0) (h2 : D.m2 = 0) (z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → R)
    (lam : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → R) (hz : D.d1 *ᵥ z = 0) (hlam : lam ᵥ* D.d1 = 0) :
    kmCoord (D.map φ).toFour (φ ∘ z) (φ ∘ lam) (blockComplex_map_cycle φ D hz)
        (blockComplex_map_closed φ D hlam) (σBlock D.m0 D.m1 D.m2) =
      φ ((-1) * z (Sum.inr (Sum.inl ())) * lam (Sum.inr (Sum.inl ()))) :=
  kmCoord_rankZero_comp φ (D.map φ) h0 h1 h2 z lam _ _

/-- **Non-vacuity** (tex 3877–3892, 4636–4640): the minimal block model `F --0--> F` is a rank-zero
model, and `kmCoord_rankZero` gives its coordinate `−1` at `z = λ = 1` over `ℚ`. Kind: PROVED. -/
theorem kmCoord_rankZero_example :
    kmCoord (minBlock ℚ).toFour 1 1 (minBlock_toFour_cycle 1) (minBlock_toFour_closed 1)
      (σBlock (minBlock ℚ).m0 (minBlock ℚ).m1 (minBlock ℚ).m2) = -1 := by
  rw [kmCoord_rankZero (minBlock ℚ) rfl rfl rfl]
  norm_num

end RankZero

end ZInQ.Manuscript.RC.Wiring
