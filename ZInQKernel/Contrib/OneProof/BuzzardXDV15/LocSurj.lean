import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs

/-!
# The orbit invariant is locally surjective

Let `A` be a false elliptic curve over a `Z[1/30]`-scheme `S`. The invariant
`invOrb A : H\F_{A/S,5} ⟶ V15`, `[P] ↦ ι(1 - e5) P`, is locally surjective for the étale
topology on `S`-schemes.

Let `Q` be a `V15`-point of `A` over `U`: a `5`-torsion point, killed by `ι(e5)`, nonzero at
every geometric point.

1. Let `i : Z ⟶ A` be the frame scheme: finite, étale and surjective over `S`, its points the
   generators. Then `T' = U ×_S Z ⟶ U` is étale and surjective and carries the universal frame
   `P₀`.
2. For a unit `g` of `O/5O`, let `W_g ⊆ T'` be the locus where `ι(1 - e5) ι(σ g) P₀` and `Q`
   agree. Both points are `5`-torsion, so they factor through `A[5]`, which is étale over `S`;
   `W_g` is the preimage of the diagonal of `A[5] ⟶ S`, an open immersion, so `W_g` is open.
3. The `W_g` cover `T'`. At a geometric point, `v ↦ (E v, X v)` identifies the `5`-torsion with
   `eV × eV` (inverse `(u, w) ↦ u · Y w`). As `E Q = 0` and `Q ≠ 0`, `w = X Q` is a nonzero vector
   of the plane `eV`; complete it to a spanning pair `(u, w)` and put `P = u · Y w`. Every
   `5`-torsion point lies in the orbit of `P`, and `ι(1 - e5) P = Y X P = Q`. Writing
   `P = ι(δ) P₀` and `P₀ = ι(δ') P`, the annihilator of `P₀` gives `δ' δ ≡ 1`, so `δ` is a unit
   modulo `5` (the ring `O/5O` is finite).
4. On the étale cover `{W_g ⟶ T' ⟶ U}`, `Q` is the invariant of the frame `ι(σ g) P₀`.
-/

noncomputable section

namespace Y3Buzzard.XDV15

open LeafQM LeafQM.AV

namespace LocSurj

/-! ## 1. Linear algebra at a geometric point -/

section Alg

/-- In a finite monoid, a right inverse is a left inverse. -/
theorem mul_eq_one_symm_of_finite {M : Type*} [Monoid M] [Finite M] {a b : M}
    (h : a * b = 1) : b * a = 1 := by
  have hinj : Function.Injective (fun y : M => b * y) := by
    intro y z hyz
    have e := congrArg (fun t => a * t) hyz
    simp only [← mul_assoc, h, one_mul] at e
    exact e
  obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 hinj 1
  have hc' : b * c = 1 := hc
  have hac : a = c := by
    calc a = a * (b * c) := by rw [hc', mul_one]
      _ = a * b * c := (mul_assoc _ _ _).symm
      _ = c := by rw [h, one_mul]
  rw [hac]
  exact hc'

/-- A nonzero vector of a plane over `F₅` (an elementary abelian group of order `25`) belongs to
a spanning pair. -/
theorem exists_span_pair_of_ne {W : Type*} [AddCommGroup W] [Finite W]
    (h5 : ∀ w : W, (5 : ℕ) • w = 0) (hcard : Nat.card W = 25) {w : W} (hw : w ≠ 0) :
    ∃ u : W, ∀ v : W, ∃ c d : ℕ, v = c • u + d • w := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Module (ZMod 5) W := AddCommGroup.zmodModule h5
  have : Module.Finite (ZMod 5) W := inferInstance
  have hfr : Module.finrank (ZMod 5) W = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := W)
    rw [hcard, Nat.card_zmod] at h1
    exact Nat.pow_right_injective (le_of_lt (by norm_num : 2 < 5))
      (show 5 ^ Module.finrank (ZMod 5) W = 5 ^ 2 by rw [← h1])
  have h1 : Module.finrank (ZMod 5) (Submodule.span (ZMod 5) {w}) = 1 :=
    finrank_span_singleton hw
  obtain ⟨u, hu⟩ : ∃ u : W, u ∉ Submodule.span (ZMod 5) {w} := by
    by_contra hc
    have htop : Submodule.span (ZMod 5) {w} = ⊤ :=
      eq_top_iff.2 (fun u _ => Classical.byContradiction (fun hu => hc ⟨u, hu⟩))
    rw [htop, finrank_top, hfr] at h1
    exact absurd h1 (by norm_num)
  have hlt : Submodule.span (ZMod 5) {w} < Submodule.span (ZMod 5) {u, w} := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert u {w})) ?_
    intro h
    apply hu
    rw [h]
    exact Submodule.subset_span (Set.mem_insert u {w})
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 := Submodule.finrank_le (Submodule.span (ZMod 5) {u, w})
  have htop : Submodule.span (ZMod 5) {u, w} = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  refine ⟨u, fun v => ?_⟩
  have hv : v ∈ Submodule.span (ZMod 5) {u, w} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hv
  have key : ∀ (c : ZMod 5) (y : W), c • y = c.val • y := fun c y => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod 5) c.val y
  exact ⟨a.val, b.val, by rw [← hab, key, key]⟩

/-- The multiplicative form: a nontrivial element of a commutative group of order `25` and
exponent `5` belongs to a generating pair. -/
theorem exists_span_pair_mul_of_ne {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (h5 : ∀ w : W, w ^ 5 = 1) (hcard : Nat.card W = 25)
    {w : W} (hw : w ≠ 1) : ∃ u : W, ∀ v : W, ∃ c d : ℕ, v = u ^ c * w ^ d := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  obtain ⟨u, h⟩ := exists_span_pair_of_ne (W := Additive W)
    (fun v => congrArg Additive.ofMul (h5 (Additive.toMul v)))
    ((Nat.card_congr Additive.toMul).trans hcard) (w := Additive.ofMul w)
    (fun h0 => hw (ofMul_eq_zero.1 h0))
  refine ⟨Additive.toMul u, fun v => ?_⟩
  obtain ⟨c, d, hv⟩ := h (Additive.ofMul v)
  exact ⟨c, d, congrArg Additive.toMul hv⟩

/-- If `a` and `b` act in the same way on `x`, then `a - b` kills `x`. -/
theorem act_sub_eq_one {H : Type*} [Group H] (T : GF5.OAct H) {a b : O} {x : H}
    (h : T.act a x = T.act b x) : T.act (a - b) x = 1 := by
  have e := T.act_add (a - b) b x
  rw [sub_add_cancel, h] at e
  exact mul_right_cancel (e.symm.trans (one_mul _).symm)

/-- The pointwise lemma. Let `P₀` generate the `5`-torsion of a group with a left action of `O`,
the `5`-torsion having `625` elements. A nonzero `5`-torsion point `Q` killed by `e5` is
`ι(1 - e5) ι(δ) P₀` for a unit `δ` modulo `5`. -/
theorem exists_unit_f5 {H : Type*} [Group H] (T : GF5.OAct H)
    (hcard : Nat.card {x : H // x ^ 5 = 1} = 625) {P₀ : H}
    (hP1 : ∀ a : O, T.act a P₀ = 1 ↔ ∃ b : O, a = ((5 : ℕ) : O) * b)
    (hP2 : ∀ x : H, x ^ 5 = 1 → ∃ a : O, x = T.act a P₀)
    {Q : H} (hQ5 : Q ^ 5 = 1) (hQE : T.act e5 Q = 1) (hQ1 : Q ≠ 1) :
    ∃ g : Y3OrderMod.G 5, T.act f5 (T.act (Y3OrderMod.σ g) P₀) = Q := by
  have hK : Nat.card T.eV = 25 := by
    have h := (Nat.card_congr T.split).symm.trans hcard
    rw [Nat.card_prod] at h
    exact Nat.mul_self_inj.1 (h.trans (by norm_num))
  have : Finite T.eV := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hQd : Q = T.act GF5.mY (T.act GF5.mX Q) := by
    have h := T.decomp hQ5
    rw [show T.act GF5.mE Q = 1 from hQE, one_mul] at h
    exact h
  have hwm : T.act GF5.mX Q ∈ T.eV := T.mem_eV.2 ⟨T.act_tors hQ5 GF5.mX,
    (T.act_comp GF5.mX GF5.mE Q).trans (T.act_congr hQ5 GF5.rel_EX)⟩
  obtain ⟨w, hw⟩ : ∃ w : T.eV, w.1 = T.act GF5.mX Q := ⟨⟨_, hwm⟩, rfl⟩
  have hw1 : w ≠ 1 := by
    intro h
    apply hQ1
    have h' : T.act GF5.mX Q = 1 := hw.symm.trans (congrArg Subtype.val h)
    rw [hQd, h', T.act_one_right]
  obtain ⟨u, hspan⟩ := exists_span_pair_mul_of_ne (W := T.eV)
    (fun a b => Subtype.ext (T.comm a.1 b.1)) (fun v => Subtype.ext (T.mem_eV.1 v.2).1) hK hw1
  obtain ⟨P, hPdef⟩ : ∃ P : H, P = u.1 * T.act GF5.mY w.1 := ⟨_, rfl⟩
  have hEP : T.act GF5.mE P = u.1 := by rw [hPdef]; exact T.split_fst u.2 w.2
  have hXP : T.act GF5.mX P = w.1 := by rw [hPdef]; exact T.split_snd u.2 w.2
  have hP5 : P ^ 5 = 1 := by
    rw [hPdef]
    exact T.tors_mul (T.mem_eV.1 u.2).1 (T.act_tors (T.mem_eV.1 w.2).1 GF5.mY)
  have hsurjP : ∀ x : H, x ^ 5 = 1 → ∃ a : O, x = T.act a P := by
    intro x hx
    obtain ⟨c1, c2, h1⟩ := hspan ⟨T.act GF5.mE x, T.mem_eV.2 ⟨T.act_tors hx GF5.mE,
      (T.act_comp GF5.mE GF5.mE x).trans (T.act_congr hx GF5.rel_EE)⟩⟩
    obtain ⟨d1, d2, h2⟩ := hspan ⟨T.act GF5.mX x, T.mem_eV.2 ⟨T.act_tors hx GF5.mX,
      (T.act_comp GF5.mX GF5.mE x).trans (T.act_congr hx GF5.rel_EX)⟩⟩
    have h1' : T.act GF5.mE x = u.1 ^ c1 * w.1 ^ c2 := congrArg Subtype.val h1
    have h2' : T.act GF5.mX x = u.1 ^ d1 * w.1 ^ d2 := congrArg Subtype.val h2
    have e1 : T.act ((c1 : O) * GF5.mE + (c2 : O) * GF5.mX) P = T.act GF5.mE x := by
      rw [T.comb, hEP, hXP, h1']
    have e2 : T.act (GF5.mY * ((d1 : O) * GF5.mE + (d2 : O) * GF5.mX)) P =
        T.act GF5.mY (T.act GF5.mX x) := by
      rw [← T.act_comp, T.comb, hEP, hXP, h2']
    refine ⟨(c1 : O) * GF5.mE + (c2 : O) * GF5.mX +
      GF5.mY * ((d1 : O) * GF5.mE + (d2 : O) * GF5.mX), ?_⟩
    rw [T.act_add, e1, e2]
    exact T.decomp hx
  have hfP : T.act f5 P = Q := by
    have hc : ∃ c : O, f5 - GF5.mY * GF5.mX = ((5 : ℕ) : O) * c := by
      obtain ⟨c, hc⟩ := GF5.rel_EYX
      refine ⟨-c, ?_⟩
      rw [mul_neg, ← hc]
      show (1 - e5) - GF5.mY * GF5.mX = -(e5 + GF5.mY * GF5.mX - 1)
      abel
    rw [T.act_congr hP5 hc, ← T.act_comp, hXP, hw]
    exact hQd.symm
  have hP05 : P₀ ^ 5 = 1 := by
    rw [← T.act_natCast]
    exact (hP1 _).2 ⟨1, (mul_one _).symm⟩
  obtain ⟨δ, hδ⟩ := hP2 P hP5
  obtain ⟨δ', hδ'⟩ := hsurjP P₀ hP05
  have h1 : T.act (δ' * δ) P₀ = T.act 1 P₀ := by
    rw [← T.act_comp, ← hδ, ← hδ', T.act_one]
  obtain ⟨d, hd⟩ := (hP1 _).1 (act_sub_eq_one T h1)
  have e1 : ((δ' : O) : Y3OrderMod.OMod 5) * (δ : Y3OrderMod.OMod 5) = 1 := by
    have h := (Y3OrderMod.coe_eq_coe_iff (M := 5) (x := δ' * δ) (y := 1)).2 ⟨d, hd⟩
    rwa [RingCon.coe_mul, RingCon.coe_one] at h
  have : Finite (Y3OrderMod.OMod 5) := Y3OrderMod.finite_OMod 5 (by norm_num)
  have e2 := mul_eq_one_symm_of_finite e1
  let g : Y3OrderMod.G 5 := ⟨(δ : Y3OrderMod.OMod 5), (δ' : Y3OrderMod.OMod 5), e2, e1⟩
  refine ⟨g, ?_⟩
  have hg : T.act (Y3OrderMod.σ g) P₀ = T.act δ P₀ :=
    T.act_congr hP05 (Y3OrderMod.coe_eq_coe_iff.1 (Y3OrderMod.σ_spec g))
  rw [hg, ← hδ, hfP]

end Alg

/-! ## 2. Points of `A` over `S`-schemes -/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory
  MonObj
open scoped CategoryTheory.Obj

attribute [local instance] FEC.grp

section Agree

variable {S : Scheme.{0}} (A : FEC S)

/-- A point `Q` of `A` over `U` with `Q ^ n = 1`, pulled back to a scheme over `U`, is
`n`-torsion. -/
theorem tors_of_pow {U : Over S} (Q : U ⟶ A.F) {n : ℕ} (hQ : Q ^ n = 1) {Y : Scheme.{0}}
    (f : Y ⟶ U.left) :
    (Over.homMk (U := Over.mk ((f ≫ Q.left) ≫ A.F.hom)) (f ≫ Q.left) rfl :
      Over.mk ((f ≫ Q.left) ≫ A.F.hom) ⟶ A.F) ^ n = 1 := by
  have h1 : Q.left ≫ A.iota (n : O) = U.hom ≫ torsZeroL A :=
    (comp_iota_eq_one_iff A Q _).1 ((comp_iotaHom_natCast A Q n).trans hQ)
  have h2 : (f ≫ Q.left) ≫ A.F.hom = f ≫ U.hom := by rw [Category.assoc, Over.w Q]
  rw [torsPow_eq_one_iff, h2, Category.assoc, h1, Category.assoc]

/-- The agreement locus of two `5`-torsion points over the same map to `S` is open, they agree
on it, and it contains every point at which they agree geometrically. It is the preimage of the
diagonal of `A[5] ⟶ S`, an open immersion since `A[5]` is étale over `S`. -/
theorem exists_open_agree (het : Etale (A.iota ((5 : ℕ) : O))) {Y : Scheme.{0}}
    (P P' : Y ⟶ A.F.left)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ 5 = 1)
    (hP' : (Over.homMk (U := Over.mk (P' ≫ A.F.hom)) P' rfl :
      Over.mk (P' ≫ A.F.hom) ⟶ A.F) ^ 5 = 1)
    (h : P ≫ A.F.hom = P' ≫ A.F.hom) :
    ∃ W : Y.Opens, W.ι ≫ P = W.ι ≫ P' ∧
      ∀ {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Y), s ≫ P = s ≫ P' →
        ∀ q, s q ∈ W := by
  have hD := LevelM.diag_open 5 A het
  have ha := LevelM.torsLift_fac 5 A P hP
  have hb := LevelM.torsLift_fac 5 A P' hP'
  have hab : LevelM.torsLift 5 A P hP ≫ LevelM.jM 5 A ≫ A.F.hom =
      LevelM.torsLift 5 A P' hP' ≫ LevelM.jM 5 A ≫ A.F.hom := by
    rw [← Category.assoc, ha, ← Category.assoc, hb, h]
  let W : Y.Opens := ⟨⇑(pullback.lift _ _ hab) ⁻¹'
      Set.range ⇑(pullback.diagonal (LevelM.jM 5 A ≫ A.F.hom)),
    IsOpen.preimage (pullback.lift _ _ hab).continuous
      (IsOpenImmersion.isOpen_range (pullback.diagonal (LevelM.jM 5 A ≫ A.F.hom)))⟩
  refine ⟨W, ?_, ?_⟩
  · have hr : Set.range ⇑(W.ι ≫ pullback.lift _ _ hab) ⊆
        Set.range ⇑(pullback.diagonal (LevelM.jM 5 A ≫ A.F.hom)) := by
      rintro _ ⟨y, rfl⟩
      have hm : W.ι y ∈ Set.range ⇑W.ι := ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι] at hm
      rw [Scheme.Hom.comp_apply]
      exact hm
    have he := IsOpenImmersion.lift_fac (pullback.diagonal (LevelM.jM 5 A ≫ A.F.hom))
      (W.ι ≫ pullback.lift _ _ hab) hr
    have h1 := congrArg (fun t => t ≫ pullback.fst (LevelM.jM 5 A ≫ A.F.hom)
      (LevelM.jM 5 A ≫ A.F.hom)) he
    have h2 := congrArg (fun t => t ≫ pullback.snd (LevelM.jM 5 A ≫ A.F.hom)
      (LevelM.jM 5 A ≫ A.F.hom)) he
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    have h3 := congrArg (fun t => t ≫ LevelM.jM 5 A) (h1.symm.trans h2)
    simp only [Category.assoc, ha, hb] at h3
    exact h3
  · intro k _ s hs q
    have hl : s ≫ pullback.lift _ _ hab =
        (s ≫ LevelM.torsLift 5 A P hP) ≫ pullback.diagonal (LevelM.jM 5 A ≫ A.F.hom) := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
        apply (cancel_mono (LevelM.jM 5 A)).1
        simp only [Category.assoc, ha, hb]
        exact hs.symm
    have e := congrArg (fun t : Spec (CommRingCat.of k) ⟶
      pullback (LevelM.jM 5 A ≫ A.F.hom) (LevelM.jM 5 A ≫ A.F.hom) => t q) hl
    simp only [Scheme.Hom.comp_apply] at e
    show (pullback.lift _ _ hab) (s q) ∈ Set.range ⇑(pullback.diagonal (LevelM.jM 5 A ≫ A.F.hom))
    exact ⟨_, e.symm⟩

end Agree

/-! ## 3. The pointwise step -/

section Point

variable {S : Over Z30Base} (A : FEC S.left)

/-- At a geometric point `t` of `U` carrying a generator `P` of the `5`-torsion, a `V15`-point
`x` is `ι(1 - e5) ι(σ g) P` for some unit `g` modulo `5`. -/
theorem exists_unit_at (hC5 : GeomCard5) {U : Over S.left} (x : U ⟶ A.F) (hx5 : x ^ 5 = 1)
    (hxE : x ≫ iotaO A e5 = 1)
    (hx0 : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ U.left),
      s ≫ x.left ≠ s ≫ U.hom ≫ torsZeroL A)
    {k : Type} [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ U.left)
    (P : Spec (CommRingCat.of k) ⟶ A.F.left) (hP : P ≫ A.F.hom = t ≫ U.hom)
    (hgen : IsGenAt 5 A (t ≫ U.hom) (Over.homMk P hP)) :
    ∃ g : Y3OrderMod.G 5, (P ≫ A.iota (Y3OrderMod.σ g)) ≫ A.iota f5 = t ≫ x.left := by
  let φ : Over.mk (t ≫ U.hom) ⟶ U := Over.homMk t rfl
  have hQ5 : (φ ≫ x) ^ 5 = 1 := by rw [← MonObj.comp_pow, hx5, MonObj.comp_one]
  have hQE : (GF5.fecAct A (Over.mk (t ≫ U.hom))).act e5 (φ ≫ x) = 1 := by
    show (φ ≫ x) ≫ iotaO A e5 = 1
    rw [Category.assoc, hxE, MonObj.comp_one]
  have hQ1 : φ ≫ x ≠ 1 := by
    intro h
    apply hx0 k t
    have h1 : (φ ≫ x) ≫ (Over.homMk (A.iota 1) (A.iota_over 1) : A.F ⟶ A.F) = 1 := by
      rw [iotaHom_one, Category.comp_id, h]
    have h2 := (comp_iota_eq_one_iff A (φ ≫ x) 1).1 h1
    rw [A.iota_one, Category.comp_id] at h2
    simpa only [φ, Over.comp_left, Over.homMk_left, Over.mk_hom, Category.assoc] using h2
  obtain ⟨g, hg⟩ := exists_unit_f5 (GF5.fecAct A (Over.mk (t ≫ U.hom)))
    (hC5 S A k (t ≫ U.hom)) (P₀ := Over.homMk P hP) hgen.1 hgen.2 hQ5 hQE hQ1
  refine ⟨g, ?_⟩
  have e : ((Over.homMk P hP ≫ iotaO A (Y3OrderMod.σ g)) ≫ iotaO A f5).left = (φ ≫ x).left :=
    congrArg (fun y : Over.mk (t ≫ U.hom) ⟶ A.F => y.left) hg
  simpa only [φ, Over.comp_left, Over.homMk_left] using e

end Point

/-! ## 4. The étale cover -/

section Cover

variable {S : Over Z30Base} (A : FEC S.left)

/-- The agreement loci `W_g ⊆ U ×_S Z` of the invariants `ι(1 - e5) ι(σ g) P₀` of the frames on
`U ×_S Z` with the pulled back point `x`. -/
theorem exists_agree_loci (hM5 : MilneProp207 5) {U : Over S.left} (x : U ⟶ A.F)
    (hx5 : x ^ 5 = 1) {Z : Scheme.{0}} {i : Z ⟶ A.F.left} (hchar : FrameChar 5 A i) :
    ∃ W : Y3OrderMod.G 5 → (pullback U.hom (i ≫ A.F.hom)).Opens,
      (∀ g, (W g).ι ≫ (pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ≫
          A.iota f5 = (W g).ι ≫ pullback.fst U.hom (i ≫ A.F.hom) ≫ x.left) ∧
      ∀ g {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ pullback U.hom (i ≫ A.F.hom)),
        s ≫ (pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ≫ A.iota f5 =
          s ≫ pullback.fst U.hom (i ≫ A.F.hom) ≫ x.left → ∀ q, s q ∈ W g := by
  have het5 : Etale (A.iota ((5 : ℕ) : O)) := (hM5 S A).2
  have hPb := tors_of_pow A x hx5 (pullback.fst U.hom (i ≫ A.F.hom))
  have key : ∀ g : Y3OrderMod.G 5, ∃ W : (pullback U.hom (i ≫ A.F.hom)).Opens,
      W.ι ≫ (pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ≫ A.iota f5 =
          W.ι ≫ pullback.fst U.hom (i ≫ A.F.hom) ≫ x.left ∧
      ∀ {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ pullback U.hom (i ≫ A.F.hom)),
        s ≫ (pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ≫ A.iota f5 =
          s ≫ pullback.fst U.hom (i ≫ A.F.hom) ≫ x.left → ∀ q, s q ∈ W := by
    intro g
    have hPa := torsion_comp_iota_pt A _ f5 5
      (isGen_comp A (pullback.snd U.hom (i ≫ A.F.hom)) (FrameTorsor.isGen_i_σ hchar g)).1
    have hab : ((pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ≫
        A.iota f5) ≫ A.F.hom = (pullback.fst U.hom (i ≫ A.F.hom) ≫ x.left) ≫ A.F.hom := by
      simp only [Category.assoc, A.iota_over, Over.w x]
      exact pullback.condition.symm
    exact exists_open_agree A het5 _ _ hPa hPb hab
  choose W hW hmem using key
  exact ⟨W, hW, hmem⟩

/-- At a geometric point `s` of `U ×_S Z`, the pulled back point `x` is the invariant of one of
the frames `ι(σ g) P₀`: the pointwise lemma. -/
theorem exists_unit_pt (hC5 : GeomCard5) {U : Over S.left} (x : U ⟶ A.F) (hx5 : x ^ 5 = 1)
    (hxE : x ≫ iotaO A e5 = 1)
    (hx0 : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ U.left),
      s ≫ x.left ≠ s ≫ U.hom ≫ torsZeroL A)
    {Z : Scheme.{0}} {i : Z ⟶ A.F.left} (hchar : FrameChar 5 A i)
    {k : Type} [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ pullback U.hom (i ≫ A.F.hom)) : ∃ g : Y3OrderMod.G 5,
      s ≫ (pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ≫
        A.iota f5 = s ≫ pullback.fst U.hom (i ≫ A.F.hom) ≫ x.left := by
  have hw0 : ((s ≫ pullback.snd U.hom (i ≫ A.F.hom)) ≫ i) ≫ A.F.hom =
      (s ≫ pullback.fst U.hom (i ≫ A.F.hom)) ≫ U.hom := by
    simp only [Category.assoc, pullback.condition]
  have hgen := (FrameTorsor.isGen_i hchar).2 k (s ≫ pullback.snd U.hom (i ≫ A.F.hom))
  have hgen' := (isGenAt_congr A ((Category.assoc _ _ _).symm.trans hw0)
    ((s ≫ pullback.snd U.hom (i ≫ A.F.hom)) ≫ i) (Category.assoc _ _ _) hw0).1 hgen
  obtain ⟨g, hg⟩ := exists_unit_at A hC5 x hx5 hxE hx0
    (s ≫ pullback.fst U.hom (i ≫ A.F.hom)) _ hw0 hgen'
  exact ⟨g, by simpa only [Category.assoc] using hg⟩

/-- A family of étale maps `f j : X j ⟶ U` covering `U`, with frames `P j` over `X j` whose
invariants are the pullbacks of `x`, makes the image sieve of `x` covering. -/
theorem imageSieve_mem_of_cover {U : Over S.left} (x : (V15Sub A).toFunctor.obj (op U))
    {J : Type} {X : J → Scheme.{0}} (f : ∀ j, X j ⟶ U.left) [∀ j, Etale (f j)]
    (hcov : ∀ t : U.left, ∃ j y, f j y = t)
    (P : ∀ j, X j ⟶ A.F.left) (hPw : ∀ j, P j ≫ A.F.hom = f j ≫ U.hom)
    (hP : ∀ j, IsGen 5 A (P j)) (h : ∀ j, P j ≫ A.iota f5 = f j ≫ x.1.left) :
    Presheaf.imageSieve (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) (ULift.up x) ∈
      etaleOver S.left U := by
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.mem_grothendieckTopology_iff.2
    ⟨Scheme.Cover.mkOfCovers J X f hcov (fun j => inferInstance), ?_⟩
  rintro _ _ ⟨j⟩
  rw [Sieve.overEquiv_iff]
  refine ⟨ULift.up (Quot.mk _ ⟨Over.homMk (P j) (hPw j), hP j⟩), ?_⟩
  apply ULift.ext
  apply Subtype.ext
  apply Over.OverMorphism.ext
  exact h j

/-- The image sieve of a `V15`-point is an étale covering sieve. -/
theorem imageSieve_mem (hM5 : MilneProp207 5) (hC5 : GeomCard5) {U : Over S.left}
    (x : (V15Sub A).toFunctor.obj (op U)) :
    Presheaf.imageSieve (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) (ULift.up x) ∈
      etaleOver S.left U := by
  obtain ⟨Z, i, -, -, het, hsurj, hchar⟩ :=
    LevelM.frameRepM_of 5 hM5 (geomFree5_of_card hC5) S A
  have hx : pt x.1 ^ 5 = 1 ∧ pt x.1 ≫ iotaO A e5 = 1 ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ U.left),
        s ≫ (pt x.1).left ≠ s ≫ U.hom ≫ torsZeroL A := x.2
  obtain ⟨hx5, hxE, hx0⟩ := hx
  obtain ⟨W, hW, hmem⟩ := exists_agree_loci A hM5 x.1 hx5 hchar
  refine imageSieve_mem_of_cover A x (J := Y3OrderMod.G 5)
    (X := fun g => ((W g : (pullback U.hom (i ≫ A.F.hom)).Opens) : Scheme.{0}))
    (fun g => (W g).ι ≫ pullback.fst U.hom (i ≫ A.F.hom)) ?_
    (fun g => (W g).ι ≫ pullback.snd U.hom (i ≫ A.F.hom) ≫ i ≫ A.iota (Y3OrderMod.σ g)) ?_
    (fun g => isGen_comp A (W g).ι (isGen_comp A _ (FrameTorsor.isGen_i_σ hchar g))) ?_
  · intro t
    obtain ⟨z, hz⟩ := hsurj.surj (U.hom t)
    have hz' : (i ≫ A.F.hom) z = (geomPt t ≫ U.hom) default := by
      simp only [Scheme.Hom.comp_apply, geomPt_apply] at hz ⊢
      exact hz
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (i ≫ A.F.hom)
      (geomPt t ≫ U.hom) z hz'
    obtain ⟨g, hg⟩ := exists_unit_pt A hC5 x.1 hx5 hxE hx0 hchar
      (pullback.lift (geomPt t) l hl.symm)
    have hm : (pullback.lift (geomPt t) l hl.symm) default ∈ Set.range ⇑(W g).ι := by
      rw [Scheme.Opens.range_ι]
      exact hmem g _ hg default
    obtain ⟨y', hy'⟩ := hm
    refine ⟨g, y', ?_⟩
    have e1 : (pullback.lift (geomPt t) l hl.symm ≫ pullback.fst U.hom (i ≫ A.F.hom)) default =
        geomPt t default := by
      rw [pullback.lift_fst]
    calc ((W g).ι ≫ pullback.fst U.hom (i ≫ A.F.hom)) y'
        = pullback.fst U.hom (i ≫ A.F.hom) ((W g).ι y') := by rw [Scheme.Hom.comp_apply]
      _ = pullback.fst U.hom (i ≫ A.F.hom) ((pullback.lift (geomPt t) l hl.symm) default) := by
          rw [hy']
      _ = (pullback.lift (geomPt t) l hl.symm ≫ pullback.fst U.hom (i ≫ A.F.hom)) default := by
          rw [Scheme.Hom.comp_apply]
      _ = geomPt t default := e1
      _ = t := geomPt_apply t default
  · intro g
    simp only [Category.assoc, A.iota_over, pullback.condition]
  · intro g
    simpa only [Category.assoc] using hW g

end Cover

end LocSurj

open CategoryTheory AlgebraicGeometry

/-- The orbit invariant `[P] ↦ ι(1 - e5) P` is locally surjective for the étale topology on
`S`-schemes. -/
theorem invOrb_locallySurjective (hM5 : MilneProp207 5) (hC5 : GeomCard5) (S : Over Z30Base)
    (A : FEC S.left) :
    Presheaf.IsLocallySurjective (etaleOver S.left)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}) :=
  ⟨fun {_} s => LocSurj.imageSieve_mem A hM5 hC5 s.down⟩

end Y3Buzzard.XDV15
