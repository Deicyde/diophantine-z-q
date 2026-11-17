import ZInQKernel.Contrib.OneProof.SelmerTwoPower

/-!
# Lemma 5.4: `dim Sel₂ = 3` gives `corank_{ℤ₂} Sel_{2^∞} = 1`

The manuscript's Lemma 5.4 (`lem:corank`, `diophantine_zq.tex` lines 1072–1084), over the genuine
Selmer groups of `ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean`: for an elliptic curve `E/ℚ` with
full rational two-torsion, `#Sel₂(E/ℚ) = 8` implies `SelmerCorankOne E`, i.e.
`Sel_{2^∞}(E/ℚ) ≅ ℚ₂/ℤ₂ × F` with `F` finite (`selmerCorankOne_of_card_selmerAt_one`). Its inputs are
the printed theorems of Mordell–Weil (`MordellWeilQ`) and Cassels–Tate (`CasselsTateSquare`); everything
else is proved here: `Sel_{2^∞}` is `2`-primary, the kernel of `Sel_{2ⁿ} → Sel_{2^∞}` is bounded by
`#E(ℚ)[2^∞]`, the `2ⁿ`-descent sequences give `#Sel_{2ⁿ} = #(E(ℚ)/2ⁿ) · #Sha[2ⁿ]`, and the structure
theorem `ZInQ.Cofinite.exists_addEquiv_of_isPPrimary` with a growth-rate comparison gives the corank.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology ZInQ.Cofinite

variable (E : WeierstrassCurve ℚ)

/-- **Every class of `H¹(G_ℚ, E[2^∞])` is killed by a power of `2`**: a representing cocycle is a
continuous map from the compact group `G_ℚ` to a discrete module, so it takes finitely many values,
each of `2`-power order. -/
theorem exists_two_pow_nsmul_H1_eq_zero (c : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) :
    ∃ k : ℕ, 2 ^ k • c = 0 := by
  classical
  induction c using QuotientAddGroup.induction_on with
  | H z =>
    have hcont : Continuous (z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff E) := (mem_Z1_iff.mp z.2).1
    have hfin : (Set.range (z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff E)).Finite :=
      (isCompact_range hcont).finite_of_discrete
    have hval : ∀ v : TwoPowerCoeff E, ∃ k : ℕ, 2 ^ k • v = 0 := fun v => by
      obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp v.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    choose k hk using hval
    obtain ⟨K, hK⟩ := (hfin.image k).bddAbove
    refine ⟨K, ?_⟩
    have hz : 2 ^ K • z = 0 := by
      apply Subtype.ext
      funext g
      have hle : k ((z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff E) g) ≤ K :=
        hK ⟨_, ⟨g, rfl⟩, rfl⟩
      change 2 ^ K • (z : AbsoluteGaloisGroup ℚ → TwoPowerCoeff E) g = 0
      rw [← Nat.sub_add_cancel hle, pow_add, mul_nsmul', hk, nsmul_zero]
    rw [← QuotientAddGroup.mk_nsmul, hz, QuotientAddGroup.mk_zero]

/-- **`Sel_{2^∞}(E/ℚ)` is `2`-primary.** -/
theorem isPPrimary_selmerTwoPower : IsPPrimary 2 (selmerTwoPower E) := fun c => by
  obtain ⟨k, hk⟩ := exists_two_pow_nsmul_H1_eq_zero E (c : H1 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E))
  exact ⟨k, Subtype.ext hk⟩

/-! ### Mordell–Weil and the torsion of `E(ℚ)` -/

/-- **The Mordell–Weil theorem for `E/ℚ`** (Mordell 1922; Silverman VIII.4.1): `E(ℚ)` is finitely
generated. A printed input. -/
abbrev MordellWeilQ : Prop := AddGroup.FG E.toAffine.Point

/-- A finitely generated abelian group is `ℤ^r × T` with `T` finite (Mathlib's structure theorem). -/
theorem exists_addEquiv_pi_int_prod_finite (A : Type) [AddCommGroup A] [AddGroup.FG A] :
    ∃ (r : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (A ≃+ (Fin r → ℤ) × T) := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (G := A)
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have hT : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ (DFinsupp.equivFunOnFintype (β := fun i => ZMod (p i ^ e i))).symm
  exact ⟨n, _, inferInstance, hT, ⟨f.trans (AddEquiv.prodCongr
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv (AddEquiv.refl _))⟩⟩

/-- In `ℤ^r × T`, an element killed by a nonzero integer has zero `ℤ^r`-part. -/
theorem fst_eq_zero_of_nsmul_eq_zero {r : ℕ} {T : Type*} [AddCommGroup T] {x : (Fin r → ℤ) × T}
    {m : ℕ} (hm : m ≠ 0) (hx : m • x = 0) : x.1 = 0 := by
  funext i
  have := congrFun (congrArg Prod.fst hx) i
  simp only [Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, Prod.fst_zero, Pi.zero_apply,
    mul_eq_zero, Nat.cast_eq_zero] at this
  exact this.resolve_left hm

/-- In `A ≅ ℤ^r × T`, two elements of `2`-power order with the same `T`-part are equal. -/
theorem eq_of_snd_eq_of_two_pow {A T : Type*} [AddCommGroup A] [AddCommGroup T] {r : ℕ}
    (e : A ≃+ (Fin r → ℤ) × T) {a b : A} {k l : ℕ} (hk : 2 ^ k • a = 0) (hl : 2 ^ l • b = 0)
    (h : (e a).2 = (e b).2) : a = b := by
  apply e.injective
  have hx' : (2 ^ (k + l)) • e a = 0 := by
    rw [← map_nsmul, pow_add, mul_comm, mul_nsmul', hk, nsmul_zero, map_zero]
  have hy' : (2 ^ (k + l)) • e b = 0 := by
    rw [← map_nsmul, pow_add, mul_nsmul', hl, nsmul_zero, map_zero]
  have hsub : (2 ^ (k + l)) • (e a - e b) = 0 := by rw [nsmul_sub, hx', hy', sub_self]
  have h1 := fst_eq_zero_of_nsmul_eq_zero (pow_ne_zero _ two_ne_zero) hsub
  refine Prod.ext ?_ h
  have : (e a).1 - (e b).1 = 0 := by simpa using h1
  exact sub_eq_zero.mp this

/-- **`H⁰(G_ℚ, E[2^∞]) = E(ℚ)[2^∞]` is finite** under Mordell–Weil. -/
theorem finite_H0_twoPowerCoeff (hMW : MordellWeilQ E) :
    Finite (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) := by
  have : AddGroup.FG E.toAffine.Point := hMW
  obtain ⟨r, T, _, hT, ⟨e⟩⟩ := exists_addEquiv_pi_int_prod_finite E.toAffine.Point
  -- the point of `E(ℚ)` attached to an invariant of `E[2^∞]`
  let toPt : H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E) → E.toAffine.Point := fun x =>
    E.basePointEquivInvariants.symm ⟨((x : TwoPowerCoeff E) : E.PointCoeff), by
      intro σ
      have hx := x.2 σ
      exact congrArg Subtype.val hx⟩
  have htoPt : Function.Injective toPt := by
    intro x y h
    have h' := congrArg (fun P => ((E.basePointEquivInvariants P : _) : E.PointCoeff)) h
    simp only [toPt, AddEquiv.apply_symm_apply] at h'
    exact Subtype.ext (Subtype.ext h')
  have htors : ∀ x, ∃ k : ℕ, 2 ^ k • toPt x = 0 := by
    intro x
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp (x : TwoPowerCoeff E).2
    refine ⟨k, ?_⟩
    apply E.basePointEquivInvariants.injective
    rw [map_nsmul, map_zero]
    apply Subtype.ext
    simp only [toPt, AddEquiv.apply_symm_apply, AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    exact hk
  refine Finite.of_injective (fun x => (e (toPt x)).2) ?_
  intro x y h
  obtain ⟨k, hk⟩ := htors x
  obtain ⟨l, hl⟩ := htors y
  exact htoPt (eq_of_snd_eq_of_two_pow e hk hl h)

/-! ### `Sel_{2^n} → Sel_{2^∞}[2^n]`: finite kernel, finiteness, counting -/

theorem torsionBy_eq_tors (A : Type*) [AddCommGroup A] (m : ℕ) :
    AddSubgroup.torsionBy A (m : ℤ) = tors A m := by
  ext x
  rw [AddSubgroup.torsionBy.nsmul_iff, mem_tors]

variable [E.IsElliptic]

/-- **The kernel of `Sel_{2^n} → Sel_{2^∞}` lies in the image of `δ⁰ : H⁰(G_ℚ, E[2^∞]) →
H¹(G_ℚ, E[2^n])`.** -/
theorem card_ker_selmerAtToTwoPower_le (n : ℕ)
    [Finite (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E))] :
    Nat.card (selmerAtToTwoPower E n).ker ≤ Nat.card (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) := by
  classical
  let δ := (twoPowerShortExact E n).explicitDelta0
  have hmem : ∀ c : (selmerAtToTwoPower E n).ker, (((c : selmerAt E n) : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)))) ∈ δ.range := by
    intro c
    have hc := congrArg Subtype.val (AddMonoidHom.mem_ker.mp c.2)
    rw [(twoPowerShortExact E n).explicitLongExact_H1A, twoPowerShortExact_inclDistribMulActionHom,
      AddMonoidHom.mem_ker]
    exact hc
  have h1 : Nat.card (selmerAtToTwoPower E n).ker ≤ Nat.card δ.range := by
    have : Finite δ.range := Finite.of_surjective _ δ.rangeRestrict_surjective
    exact Nat.card_le_card_of_injective (fun c => (⟨_, hmem c⟩ : δ.range)) (fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h'))
  exact h1.trans (Nat.card_le_card_of_surjective _ δ.rangeRestrict_surjective)

/-- `Sel_{2^n}(E/ℚ)` is finite, and `#Sel_{2^n} = #ker · #Sel_{2^∞}[2^n]`, when `H⁰(G_ℚ, E[2^∞])`
and `Sel_{2^∞}[2]` are finite. -/
theorem card_selmerAt_eq (n : ℕ) [Finite (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E))]
    (hfin : Finite (tors (selmerTwoPower E) 2)) :
    Finite (selmerAt E n) ∧ Nat.card (selmerAt E n) =
      Nat.card (selmerAtToTwoPower E n).ker * Nat.card (tors (selmerTwoPower E) (2 ^ n)) := by
  classical
  let f := selmerAtToTwoPower E n
  have hrange : f.range = tors (selmerTwoPower E) (2 ^ n) := by
    rw [range_selmerAtToTwoPower, torsionBy_eq_tors]
  have htors : Finite (tors (selmerTwoPower E) (2 ^ n)) := by
    have := finite_tors_pow (p := 2) hfin n
    exact this
  have hR : Finite f.range := by rw [hrange]; exact htors
  have hker : Finite f.ker := by
    have : Finite (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) := inferInstance
    let δ := (twoPowerShortExact E n).explicitDelta0
    have : Finite δ.range := Finite.of_surjective _ δ.rangeRestrict_surjective
    have hmem : ∀ c : f.ker, (((c : selmerAt E n) : H1 (AbsoluteGaloisGroup ℚ) (E.TorsionCoeff (2 ^ n)))) ∈ δ.range := by
      intro c
      have hc := congrArg Subtype.val (AddMonoidHom.mem_ker.mp c.2)
      rw [(twoPowerShortExact E n).explicitLongExact_H1A,
        twoPowerShortExact_inclDistribMulActionHom, AddMonoidHom.mem_ker]
      exact hc
    exact Finite.of_injective (fun c => (⟨_, hmem c⟩ : δ.range)) (fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h'))
  have hS : Finite (selmerAt E n) := by
    have hk : Finite f.rangeRestrict.ker := by rw [AddMonoidHom.ker_rangeRestrict]; exact hker
    exact finite_of_finite_ker f.rangeRestrict hk
  refine ⟨hS, ?_⟩
  rw [card_eq_card_ker_mul_of_surjective f.rangeRestrict f.rangeRestrict_surjective,
    AddMonoidHom.ker_rangeRestrict, hrange]

/-! ### The `2^n`-descent sequence: `#Sel_{2^n} = #(E(ℚ)/2ⁿE(ℚ)) · #Sha[2ⁿ]` -/

theorem isUnit_two_pow (n : ℕ) : IsUnit (((2 ^ n : ℕ) : ℚ)) :=
  isUnit_iff_ne_zero.mpr (by positivity)

/-- **`#Sel_{2^n}(E/ℚ) = #(E(ℚ)/2ⁿE(ℚ)) · #Sha(E/ℚ)[2ⁿ]`** (Tau Ceti's `m`-descent sequence,
Silverman X.4.2), when `Sel_{2^n}` is finite. -/
theorem card_selmerAt_eq_mul (n : ℕ) (hS : Finite (selmerAt E n)) :
    Nat.card (selmerAt E n) =
      Nat.card (E.toAffine.Point ⧸ (nsmulAddMonoidHom (α := E.toAffine.Point) (2 ^ n)).range) *
        Nat.card (AddSubgroup.torsionBy (sha E) ((2 ^ n : ℕ) : ℤ)) := by
  classical
  let g := E.selmerShaMap emb (2 ^ n)
  let f := E.kummerSelmerMap emb (isUnit_two_pow n)
  have hS' : Finite (E.selmerGroup emb (2 ^ n)) := hS
  have hcard := card_eq_card_ker_mul_of_surjective g (E.selmerShaMap_surjective emb (isUnit_two_pow n))
  have hker : g.ker = f.range := by
    ext c
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact E.exact_kummerSelmerMap_selmerShaMap emb (isUnit_two_pow n) c
  have hrange : Nat.card f.range =
      Nat.card (E.toAffine.Point ⧸ (nsmulAddMonoidHom (α := E.toAffine.Point) (2 ^ n)).range) :=
    Nat.card_congr (AddMonoidHom.ofInjective
      (E.kummerSelmerMap_injective emb (isUnit_two_pow n))).toEquiv.symm
  change Nat.card (E.selmerGroup emb (2 ^ n)) = _
  rw [hcard, hker, hrange]
  rfl

/-! ### The `2`-primary part of `Sha(E/ℚ)` -/

/-- **`Sha(E/ℚ)[2^∞]`**, the `2`-primary part of `Sha(E/ℚ)`. -/
def shaTwo : AddSubgroup (sha E) := AddCommGroup.primaryComponent (sha E) 2

theorem isPPrimary_shaTwo : IsPPrimary 2 (shaTwo E) := fun x => by
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
  exact ⟨k, Subtype.ext hk⟩

/-- `Sha(E/ℚ)[2^∞][2ⁿ] = Sha(E/ℚ)[2ⁿ]`. -/
def torsShaTwoEquiv (n : ℕ) :
    tors (shaTwo E) (2 ^ n) ≃ AddSubgroup.torsionBy (sha E) ((2 ^ n : ℕ) : ℤ) where
  toFun x := ⟨(x : shaTwo E), AddSubgroup.torsionBy.nsmul_iff.mpr (by
    have := mem_tors.mp x.2
    exact congrArg Subtype.val this)⟩
  invFun y := ⟨⟨y, AddCommGroup.mem_primaryComponent.mpr ⟨n, AddSubgroup.torsionBy.nsmul_iff.mp y.2⟩⟩,
    mem_tors.mpr (Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp y.2))⟩
  left_inv x := rfl
  right_inv y := rfl

/-! ### Lemma 5.4 -/

/-- **The Cassels–Tate input of Lemma 5.4** (Cassels 1962; Poonen–Stoll, Ann. of Math. 150 (1999),
§§4–5, as the manuscript cites it, line 1077): for an elliptic curve the Cassels–Tate pairing is
alternating and nondegenerate on `Sha/Sha_div`, so the finite part `F` of
`Sha(E/ℚ)[2^∞] ≅ (ℚ₂/ℤ₂)^t × F` is a square `G × G` and `#F[2]` is a square. A printed input. -/
def CasselsTateSquare : Prop :=
  ∀ (t : ℕ) (F : Type) [AddCommGroup F] [Finite F], (shaTwo E ≃+ (Fin t → Q2Z2) × F) →
    IsSquare (Nat.card (tors F 2))

/-- **Full rational two-torsion**: `#E(ℚ)[2] = 4`. -/
abbrev FullTwoTorsion : Prop := Nat.card (tors E.toAffine.Point 2) = 4

theorem card_tors_int_pi (r m : ℕ) (hm : m ≠ 0) : Nat.card (tors (Fin r → ℤ) m) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨0⟩⟩
  have ha := fst_eq_zero_of_nsmul_eq_zero (T := Unit) hm (x := ((a : Fin r → ℤ), ())) (by
    simp [mem_tors.mp a.2])
  have hb := fst_eq_zero_of_nsmul_eq_zero (T := Unit) hm (x := ((b : Fin r → ℤ), ())) (by
    simp [mem_tors.mp b.2])
  simp only at ha hb
  rw [ha, hb]

theorem two_pow_mul_sq_eq_two {a s : ℕ} (h : 2 ^ a * (s * s) = 2) : a = 1 ∧ s = 1 := by
  have hs : s = 1 := by
    have hdvd : s * s ∣ 2 := ⟨2 ^ a, by rw [mul_comm]; exact h.symm⟩
    have hle : s * s ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0; simp at h
      · exact h0
    nlinarith
  subst hs
  simp only [mul_one] at h
  exact ⟨Nat.pow_right_injective le_rfl (by simpa using h), rfl⟩

/-- **Lemma 5.4 (`lem:corank`, `diophantine_zq.tex` lines 1072–1084).** For an elliptic curve over
`ℚ` with full rational two-torsion, `dim_{𝔽₂} Sel₂(E/ℚ) = 3` (`#Sel₂ = 8`) implies
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`, given the printed inputs Mordell–Weil (`MordellWeilQ`) and the
Cassels–Tate square property (`CasselsTateSquare`).

Proof (the manuscript's, at finite levels): by the `2ⁿ`-descent sequences,
`#Sel_{2ⁿ} = #(E(ℚ)/2ⁿ) · #Sha[2ⁿ] = 2^{nr} #T[2ⁿ] · 2^{nt'} #F'[2ⁿ]`, where `E(ℚ) ≅ ℤ^r × T` and
`Sha[2^∞] ≅ (ℚ₂/ℤ₂)^{t'} × F'`; and `#Sel_{2ⁿ} = #kerₙ · #Sel_{2^∞}[2ⁿ] = #kerₙ · 2^{nt} #F[2ⁿ]` with
`Sel_{2^∞} ≅ (ℚ₂/ℤ₂)^t × F` and `kerₙ` bounded by `#E(ℚ)[2^∞]`. Comparing growth, `t = r + t'`. At
`n = 1`, `8 = 2^r · 4 · 2^{t'} · #F'[2]` with `#F'[2]` a square, so `r + t' = 1`. -/
theorem selmerCorankOne_of_card_selmerAt_one (hMW : MordellWeilQ E) (hCT : CasselsTateSquare E)
    (h2 : FullTwoTorsion E) (hSel : Nat.card (selmerAt E 1) = 8) : SelmerCorankOne E := by
  classical
  have hS1 : Finite (selmerAt E 1) := Nat.finite_of_card_ne_zero (by rw [hSel]; norm_num)
  -- `Sel_{2^∞}[2]` is the image of `Sel₂`
  have hfinSel : Finite (tors (selmerTwoPower E) 2) := by
    have hR : Finite (selmerAtToTwoPower E 1).range :=
      Finite.of_surjective _ (selmerAtToTwoPower E 1).rangeRestrict_surjective
    rw [range_selmerAtToTwoPower, torsionBy_eq_tors, pow_one] at hR
    exact hR
  have hH0 := finite_H0_twoPowerCoeff E hMW
  obtain ⟨t, F, _, hF, ⟨eS⟩⟩ :=
    exists_addEquiv_of_isPPrimary (p := 2) _ (isPPrimary_selmerTwoPower E) hfinSel
  -- `Sha[2]` is the image of `Sel₂`
  have hShaFin : Finite (tors (shaTwo E) 2) := by
    have h1 : Finite (AddSubgroup.torsionBy (sha E) ((2 ^ 1 : ℕ) : ℤ)) := by
      have : Finite (E.selmerGroup emb (2 ^ 1)) := hS1
      exact Finite.of_surjective _ (E.selmerShaMap_surjective emb (isUnit_two_pow 1))
    have h2' := Finite.of_equiv _ (torsShaTwoEquiv E 1).symm
    rw [pow_one] at h2'
    exact h2'
  obtain ⟨t', F', _, hF', ⟨eSha⟩⟩ :=
    exists_addEquiv_of_isPPrimary (p := 2) _ (isPPrimary_shaTwo E) hShaFin
  obtain ⟨s, hs⟩ := hCT t' F' eSha
  have : AddGroup.FG E.toAffine.Point := hMW
  obtain ⟨r, T, _, hT, ⟨eMW⟩⟩ := exists_addEquiv_pi_int_prod_finite E.toAffine.Point
  have hT2 : Nat.card (tors T 2) = 4 := by
    rw [← h2, card_tors_congr eMW, card_tors_prod, card_tors_int_pi r 2 two_ne_zero, one_mul]
  -- the counting identity at level `2ⁿ`
  have key : ∀ n : ℕ, Nat.card (selmerAtToTwoPower E n).ker * (2 ^ (n * t) * Nat.card (tors F (2 ^ n))) =
      (2 ^ n) ^ r * Nat.card (tors T (2 ^ n)) * (2 ^ (n * t') * Nat.card (tors F' (2 ^ n))) := by
    intro n
    obtain ⟨hSn, hcard⟩ := card_selmerAt_eq E n hfinSel
    have h1 := card_selmerAt_eq_mul E n hSn
    rw [card_quotient_nsmul_range_of_addEquiv eMW (pow_ne_zero n two_ne_zero),
      ← Nat.card_congr (torsShaTwoEquiv E n), card_tors_of_addEquiv eSha] at h1
    rw [card_tors_of_addEquiv eS] at hcard
    rw [← hcard, h1]
  -- `n = 1`: `r + t' = 1`
  have hrt : r + t' = 1 := by
    have h1 := card_selmerAt_eq_mul E 1 hS1
    rw [card_quotient_nsmul_range_of_addEquiv eMW (pow_ne_zero 1 two_ne_zero),
      ← Nat.card_congr (torsShaTwoEquiv E 1), card_tors_of_addEquiv eSha, hSel] at h1
    simp only [pow_one, one_mul] at h1
    rw [hT2, hs] at h1
    have h4 : 4 * (2 ^ (r + t') * (s * s)) = 4 * 2 := by rw [pow_add]; linarith [h1]
    exact (two_pow_mul_sq_eq_two (Nat.eq_of_mul_eq_mul_left (by norm_num) h4)).1
  -- growth: `t = r + t'`
  have hT' : Finite T := hT
  have hbF : ∀ n, 1 ≤ Nat.card (tors F (2 ^ n)) ∧ Nat.card (tors F (2 ^ n)) ≤ Nat.card F := fun n =>
    ⟨Nat.card_pos, Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  have hbF' : ∀ n, 1 ≤ Nat.card (tors F' (2 ^ n)) ∧ Nat.card (tors F' (2 ^ n)) ≤ Nat.card F' :=
    fun n => ⟨Nat.card_pos, Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  have hbT : ∀ n, 1 ≤ Nat.card (tors T (2 ^ n)) ∧ Nat.card (tors T (2 ^ n)) ≤ Nat.card T := fun n =>
    ⟨Nat.card_pos, Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  have hbK : ∀ n, 1 ≤ Nat.card (selmerAtToTwoPower E n).ker ∧
      Nat.card (selmerAtToTwoPower E n).ker ≤ Nat.card (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) :=
    fun n => by
      obtain ⟨hSn, -⟩ := card_selmerAt_eq E n hfinSel
      exact ⟨Nat.card_pos, card_ker_selmerAtToTwoPower_le E n⟩
  let C := Nat.card F * Nat.card (H0 (AbsoluteGaloisGroup ℚ) (TwoPowerCoeff E)) +
    Nat.card T * Nat.card F'
  have ht : t = r + t' := by
    refine eq_of_pow_mul_eq (b := 2) (C := C) (by norm_num)
      (fun n => Nat.card (tors F (2 ^ n)) * Nat.card (selmerAtToTwoPower E n).ker)
      (fun n => Nat.card (tors T (2 ^ n)) * Nat.card (tors F' (2 ^ n))) (fun n => ?_) (fun n => ?_)
      (fun n => ?_)
    · refine ⟨by simpa using Nat.mul_le_mul (hbF n).1 (hbK n).1, ?_⟩
      exact (Nat.mul_le_mul (hbF n).2 (hbK n).2).trans (Nat.le_add_right _ _)
    · refine ⟨by simpa using Nat.mul_le_mul (hbT n).1 (hbF' n).1, ?_⟩
      exact (Nat.mul_le_mul (hbT n).2 (hbF' n).2).trans (Nat.le_add_left _ _)
    · calc 2 ^ (n * t) * (Nat.card (tors F (2 ^ n)) * Nat.card (selmerAtToTwoPower E n).ker)
          = Nat.card (selmerAtToTwoPower E n).ker * (2 ^ (n * t) * Nat.card (tors F (2 ^ n))) := by
            ring
        _ = (2 ^ n) ^ r * Nat.card (tors T (2 ^ n)) * (2 ^ (n * t') * Nat.card (tors F' (2 ^ n))) :=
            key n
        _ = 2 ^ (n * (r + t')) * (Nat.card (tors T (2 ^ n)) * Nat.card (tors F' (2 ^ n))) := by
            rw [← pow_mul, mul_add, pow_add]
            ring
  rw [hrt] at ht
  subst ht
  exact ⟨F, inferInstance, hF, ⟨eS⟩⟩

end ZInQ.Manuscript.SelmerTwoPower
