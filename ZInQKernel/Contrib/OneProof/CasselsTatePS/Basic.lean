import ZInQKernel.Contrib.OneProof.SilvermanRankOne

/-!
# The Cassels–Tate pairing on `E_ℓ` in the form printed by Poonen–Stoll (additive evidence)

B. Poonen and M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*,
Ann. of Math. (2) 150 (1999), 1109–1149; arXiv:math/9911267v1, which carries the journal pagination.
Page numbers below are journal page numbers.

Theorem 8, (1) ⇒ (2), pp. 1122–1123, with Corollary 12 at `g = 1`, p. 1126, gives for an elliptic
curve over a global field a pairing on `Ш` that is alternating and nondegenerate on
`Ш_nd = Ш/Ш_div`.
On p. 1112, `M_div` is defined element-wise, as the infinitely divisible elements of `M`. Pulled
back to `Ш`, the print therefore gives an alternating pairing that kills the maximal divisible
subgroup and whose kernel consists of infinitely divisible elements. The row
`PoleS12.CasselsTatePairingCurves` says more: its kernel lies in `divisiblePart`. The two agree when
`Ш(E_ℓ)[p]` is finite for every prime `p`, which the tree does not have.

This file states the printed form and shows that it is weaker than the row and that it suffices for
pole completeness:

* `SelmerTwoPower.CasselsTatePairingPS E` and `PoleS12.CasselsTatePairingCurvesPS`: the printed
  form;
* `PoleS12.casselsTatePairingCurvesPS_of_current`: the row implies it;
* `SelmerTwoPower.casselsTateSquare_of_pairingPS`: the Cassels–Tate square property from it, by the
  proof of `casselsTateSquare_of_pairing`, which reads the kernel clause of the row only through
  these two properties;
* `PoleS12.SilvermanRank.poleCompleteness_of_rankOne_PS`: the consumer
  `poleCompleteness_of_rankOne` with the printed form in place of the row.

No statement is changed. Restating the row needs the holder's agreement and the maintainer's
rulings.
-/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti TauCeti.ContCohomology ZInQ.Cofinite

/-- **The Cassels–Tate pairing of `E/ℚ` as printed by Poonen–Stoll**, pulled back to `Ш(E/ℚ)`
(existence form; the pairing is not named). Clause by clause, with Poonen–Stoll's words:

* `b : sha E →+ sha E →+ QZ`: the pairing `⟨ , ⟩ : Ш × Ш → ℚ/ℤ`, bilinear; at `g = 1` the class
  `c` of Corollary 12 is `Pic⁰ = 0`, so the modified pairing `⟨ , ⟩^c` of Theorem 8 is `⟨ , ⟩`
  (p. 1126: "the element c ∈ Ш(J)[2] of Section 6 is Pic^{g−1}_{X/k}, and ⟨c, c⟩ = N/2 ∈ Q/Z,
  where N is the number of deficient places of X"; at `g = 1` no place is deficient).
* `∀ x, b x x = 0`: p. 1112, "alternating if ⟨a, a⟩ = 0 for all a ∈ M"; Theorem 8 (2), p. 1122,
  "The modified pairing ⟨ , ⟩^c is alternating and nondegenerate on Ш_nd"; remarks after
  Corollary 12, p. 1126, "For g = 1, Corollaries 7 and 12 let us recover Cassels' theorem [Ca]
  that ⟨ , ⟩ is alternating for elliptic curves."
* `∀ x ∈ divisiblePart (sha E), ∀ y, b x y = 0`: the pairing lives on `Ш_nd`, the quotient by
  `Ш_div` (p. 1112, "Denote by M_nd the quotient M/M_div"), and an element of the maximal divisible
  subgroup is infinitely divisible, so lies in `Ш_div`.
* `∀ x, (∀ y, b x y = 0) → ∀ n ≠ 0, ∃ g, n • g = x`: nondegeneracy on `Ш_nd` (Theorem 8 (2),
  p. 1122) puts the kernel in `Ш_div`, which p. 1112 defines element-wise: "Let M_div be the
  maximal divisible subgroup of M; i.e., m is in M_div if and only if for all n ≥ 1 there exists
  x ∈ M such that nx = m." The proof of Theorem 8, p. 1123, takes nondegeneracy as known:
  "nondegeneracy follows from the nondegeneracy of ⟨ , ⟩ on Ш_nd". -/
def CasselsTatePairingPS (E : WeierstrassCurve ℚ) : Prop :=
  ∃ b : sha E →+ sha E →+ QZ, (∀ x, b x x = 0) ∧
    (∀ x ∈ divisiblePart (sha E), ∀ y, b x y = 0) ∧
    ∀ x, (∀ y, b x y = 0) → ∀ n : ℕ, n ≠ 0 → ∃ g, n • g = x

/-- **The row's form implies the printed form**: a kernel inside the maximal divisible subgroup
consists of infinitely divisible elements (`exists_nsmul_eq_of_mem_divisiblePart`). -/
theorem casselsTatePairingPS_of_casselsTatePairing {E : WeierstrassCurve ℚ}
    (h : CasselsTatePairing E) : CasselsTatePairingPS E := by
  obtain ⟨b, halt, hker⟩ := h
  exact ⟨b, halt, fun x hx y => (hker x).mpr hx y,
    fun x hx _ hn => exists_nsmul_eq_of_mem_divisiblePart ((hker x).mp hx) hn⟩

/-- An element killed by two coprime integers is zero (copy of a private lemma of
`CasselsTatePairing.lean`). -/
private theorem eq_zero_of_coprime_nsmulPS {A : Type*} [AddCommGroup A] {q : A} {r s : ℕ}
    (hrs : Nat.Coprime r s) (hr : r • q = 0) (hs : s • q = 0) : q = 0 := by
  have hd := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hr)
    (addOrderOf_dvd_of_nsmul_eq_zero hs)
  rw [hrs.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at hd
  exact hd

/-- On a torsion group, an element of `2`-power order that pairs to zero with every element of
`2`-power order pairs to zero with every element (copy of a private lemma of
`CasselsTatePairing.lean`). -/
private theorem pairing_eq_zero_of_twoPrimaryPS {G : Type*} [AddCommGroup G]
    (b : G →+ G →+ QZ) {x : G} {kx : ℕ} (hx : 2 ^ kx • x = 0)
    (hfin : ∀ y : G, ∃ n : ℕ, n ≠ 0 ∧ n • y = 0)
    (h2 : ∀ s : G, (∃ k : ℕ, 2 ^ k • s = 0) → b x s = 0) (y : G) : b x y = 0 := by
  obtain ⟨N, hN0, hNy⟩ := hfin y
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hcop : Nat.Coprime (2 ^ a) m := (Nat.coprime_two_left.mpr hm).pow_left a
  have hbez : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
    have := Nat.gcd_eq_gcd_ab (2 ^ a) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at this
    exact this.symm
  have hy : y = (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m) • y +
      ((m : ℤ) * Nat.gcdB (2 ^ a) m) • y := by
    rw [← add_zsmul, hbez, one_zsmul]
  have hNy' : (((2 ^ a * m : ℕ) : ℤ)) • y = 0 := by rw [natCast_zsmul, hNy]
  have hy2 : 2 ^ a • (((m : ℤ) * Nat.gcdB (2 ^ a) m) • y) = 0 := by
    rw [← natCast_zsmul, smul_smul,
      show ((2 ^ a : ℕ) : ℤ) * ((m : ℤ) * Nat.gcdB (2 ^ a) m) =
        Nat.gcdB (2 ^ a) m * ((2 ^ a * m : ℕ) : ℤ) by push_cast; ring,
      ← smul_smul, hNy', smul_zero]
  have hy1 : m • ((((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m) • y) = 0 := by
    rw [← natCast_zsmul, smul_smul,
      show (m : ℤ) * (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m) =
        Nat.gcdA (2 ^ a) m * ((2 ^ a * m : ℕ) : ℤ) by push_cast; ring,
      ← smul_smul, hNy', smul_zero]
  have h1 : b x ((((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m) • y) = 0 := by
    refine eq_zero_of_coprime_nsmulPS ((Nat.coprime_two_left.mpr hm).pow_left kx) ?_ ?_
    · rw [← AddMonoidHom.nsmul_apply, ← map_nsmul, hx, map_zero, AddMonoidHom.zero_apply]
    · rw [← map_nsmul, hy1, map_zero]
  rw [hy, map_add, h1, h2 _ ⟨a, hy2⟩, add_zero]

section RestrictionPS

variable {E : WeierstrassCurve ℚ} {t : ℕ} {F : Type} [AddCommGroup F]

/-- The finite factor `F → Ш(E/ℚ)` of `Ш(E/ℚ)[2^∞] ≅ (ℚ₂/ℤ₂)^t × F` (copy). -/
private def finIncPS (e : AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F) :
    F →+ sha E :=
  (AddCommGroup.primaryComponent (sha E) 2).subtype.comp
    (e.symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _))

private theorem finIncPS_apply
    (e : AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F) (f : F) :
    finIncPS e f = ((e.symm (0, f) : AddCommGroup.primaryComponent (sha E) 2) : sha E) :=
  rfl

/-- The divisible factor `(ℚ₂/ℤ₂)^t → Ш(E/ℚ)` of the decomposition (copy). -/
private def divIncPS (e : AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F) :
    (Fin t → Q2Z2) →+ sha E :=
  (AddCommGroup.primaryComponent (sha E) 2).subtype.comp
    (e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _))

private theorem divIncPS_apply
    (e : AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F) (d : Fin t → Q2Z2) :
    divIncPS e d = ((e.symm (d, 0) : AddCommGroup.primaryComponent (sha E) 2) : sha E) :=
  rfl

/-- Every class of `Ш(E/ℚ)[2^∞]` is a divisible-factor class plus an `F` class (copy). -/
private theorem coe_eq_divIncPS_add_finIncPS
    (e : AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F)
    (s : AddCommGroup.primaryComponent (sha E) 2) :
    (s : sha E) = divIncPS e (e s).1 + finIncPS e (e s).2 := by
  rw [finIncPS_apply, divIncPS_apply, ← AddSubgroup.coe_add, ← map_add, Prod.mk_add_mk, add_zero,
    zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]

/-- The divisible factor lies in the maximal divisible subgroup (copy). -/
private theorem divIncPS_mem_divisiblePart
    (e : AddCommGroup.primaryComponent (sha E) 2 ≃+ (Fin t → Q2Z2) × F) (d : Fin t → Q2Z2) :
    divIncPS e d ∈ divisiblePart (sha E) := by
  have hdiv : ∀ x ∈ (divIncPS e).range, ∀ n : ℕ, n ≠ 0 →
      ∃ g ∈ (divIncPS e).range, n • g = x := by
    rintro _ ⟨d, rfl⟩ n hn
    refine ⟨divIncPS e (DivisibleBy.div d (n : ℤ)), ⟨_, rfl⟩, ?_⟩
    rw [← map_nsmul, ← natCast_zsmul, DivisibleBy.div_cancel d (by exact_mod_cast hn)]
  exact le_divisiblePart hdiv ⟨d, rfl⟩

end RestrictionPS

/-- **The printed form gives the Cassels–Tate square property.** The proof of
`casselsTateSquare_of_pairing`, with the row's `hker.mpr` replaced by the second clause (the
divisible factor is in the kernel) and `hker.mp` followed by `exists_nsmul_eq_of_mem_divisiblePart`
replaced by the third (a kernel element is divisible by `2 ^ K`). -/
theorem casselsTateSquare_of_pairingPS (E : WeierstrassCurve ℚ) (h : CasselsTatePairingPS E) :
    CasselsTateSquare E := by
  classical
  obtain ⟨b, halt, hdivk, hkerdiv⟩ := h
  intro t F _ _ e
  have hskew : ∀ x y, b x y = -b y x := fun x y => by
    have := halt (x + y)
    simp only [map_add, AddMonoidHom.add_apply, halt, zero_add, add_zero] at this
    rw [eq_neg_iff_add_eq_zero]
    rwa [add_comm] at this
  have hδ0 : ∀ d z, b z (divIncPS e d) = 0 := fun d z => by
    rw [hskew, hdivk (divIncPS e d) (divIncPS_mem_divisiblePart e d) z, neg_zero]
  have hS2 : ∀ s : AddCommGroup.primaryComponent (sha E) 2, ∃ k : ℕ, 2 ^ k • s = 0 := fun s => by
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp s.2
    exact ⟨k, Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hk)⟩
  have h2F : ∀ f : F, ∃ k : ℕ, 2 ^ k • f = 0 := fun f => by
    obtain ⟨k, hk⟩ := hS2 (e.symm (0, f))
    refine ⟨k, ?_⟩
    have := congrArg e hk
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero] at this
    simpa using congrArg Prod.snd this
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ f : F, 2 ^ K • f = 0 := by
    have := Fintype.ofFinite F
    choose k hk using h2F
    refine ⟨Finset.univ.sup k, fun f => ?_⟩
    have hle : k f ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ f)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_nsmul', hk, nsmul_zero]
  let β : F →+ F →+ QZ := (b.compl₂ (finIncPS e)).comp (finIncPS e)
  have hβ : ∀ f g, β f g = b (finIncPS e f) (finIncPS e g) := fun _ _ => rfl
  have hnd : ∀ f, (∀ g, β f g = 0) → f = 0 := by
    intro f hf
    obtain ⟨kf, hkf⟩ := h2F f
    have hx2 : 2 ^ kf • finIncPS e f = 0 := by rw [← map_nsmul, hkf, map_zero]
    have hSz : ∀ s : AddCommGroup.primaryComponent (sha E) 2, b (finIncPS e f) s = 0 :=
      fun s => by
        rw [coe_eq_divIncPS_add_finIncPS e s, map_add, hδ0, zero_add, ← hβ]
        exact hf _
    have hall : ∀ y, b (finIncPS e f) y = 0 :=
      pairing_eq_zero_of_twoPrimaryPS b hx2 (fun y => by
          obtain ⟨N, hN0, hN⟩ :=
            exists_nsmul_eq_zero_H1 E (y : H1 (AbsoluteGaloisGroup ℚ) E.PointCoeff)
          exact ⟨N, hN0, Subtype.ext (by
            rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hN)⟩)
        (fun s hs => hSz ⟨s, AddCommGroup.mem_primaryComponent.mpr hs⟩)
    obtain ⟨g, hg⟩ := hkerdiv (finIncPS e f) hall (2 ^ K) (pow_ne_zero _ two_ne_zero)
    have hgS : g ∈ AddCommGroup.primaryComponent (sha E) 2 :=
      AddCommGroup.mem_primaryComponent.mpr
        ⟨K + kf, by rw [pow_add, mul_comm, mul_nsmul', hg, hx2]⟩
    have he : (2 ^ K) • (⟨g, hgS⟩ : AddCommGroup.primaryComponent (sha E) 2) = e.symm (0, f) :=
      Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← finIncPS_apply]; exact hg)
    have := congrArg e he
    rw [map_nsmul, AddEquiv.apply_symm_apply] at this
    have hf' := congrArg Prod.snd this
    simp only [Prod.smul_snd] at hf'
    rw [← hf', hK]
  exact isSquare_card_tors_two_of_alternating h2F β (fun f => (hβ f f).trans (halt _)) hnd

end ZInQ.Manuscript.SelmerTwoPower

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Manuscript.SelmerTwoPower

/-- **The Cassels–Tate pairing for the curves `E_ℓ`, in the form printed by Poonen–Stoll**
(`SelmerTwoPower.CasselsTatePairingPS` at the curves of `CasselsTatePairingCurves`:
`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` for positive squarefree `ℓ ≡ 11 (mod 12)`). Poonen–Stoll,
Ann. of Math. 150 (1999), Theorem 8 (1) ⇒ (2), pp. 1122–1123, with Corollary 12 at `g = 1`,
p. 1126, and the definition of `M_div` on p. 1112. -/
def CasselsTatePairingCurvesPS : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → CasselsTatePairingPS (Manuscript.curve ℓ)

/-- **The current row implies the printed form**, so the printed form is not stronger. -/
theorem casselsTatePairingCurvesPS_of_current (h : CasselsTatePairingCurves) :
    CasselsTatePairingCurvesPS :=
  fun ℓ hℓ hsf hmod => casselsTatePairingPS_of_casselsTatePairing (h ℓ hℓ hsf hmod)

/-- The Cassels–Tate square property of the curves `E_ℓ` from the printed form. -/
theorem casselsTateSquareCurves_of_pairingPS (h : CasselsTatePairingCurvesPS) :
    CasselsTateSquareCurves :=
  fun ℓ hℓ hsf hmod => casselsTateSquare_of_pairingPS _ (h ℓ hℓ hsf hmod)

/-- **Lemma 5.4 at the curves `E_ℓ` from the printed form.** -/
theorem lemma54At_of_casselsTatePairingPS (h : CasselsTatePairingCurvesPS) :
    PoleRC.Lemma54At SelmerTwoPower.SelmerCorankOne :=
  lemma54At_of_casselsTate (casselsTateSquareCurves_of_pairingPS h)

end ZInQ.Manuscript.PoleS12

namespace ZInQ.Manuscript.PoleS12.SilvermanRank

/-- **The consumer `poleCompleteness_of_rankOne` from the printed form**: the same proof, with
`lemma54At_of_casselsTatePairingPS` in place of `lemma54At_of_casselsTatePairing`, and the same
conclusion. -/
theorem poleCompleteness_of_rankOne_PS
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : CasselsTatePairingCurvesPS)
    (hRank : PoleRC.KolyvaginRankOne) : PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (lemma54At_of_casselsTatePairingPS hCT) hRank)
    simultaneousConstruction

end ZInQ.Manuscript.PoleS12.SilvermanRank

end

#print axioms ZInQ.Manuscript.SelmerTwoPower.CasselsTatePairingPS
#print axioms ZInQ.Manuscript.SelmerTwoPower.casselsTatePairingPS_of_casselsTatePairing
#print axioms ZInQ.Manuscript.SelmerTwoPower.casselsTateSquare_of_pairingPS
#print axioms ZInQ.Manuscript.PoleS12.CasselsTatePairingCurvesPS
#print axioms ZInQ.Manuscript.PoleS12.casselsTatePairingCurvesPS_of_current
#print axioms ZInQ.Manuscript.PoleS12.casselsTateSquareCurves_of_pairingPS
#print axioms ZInQ.Manuscript.PoleS12.lemma54At_of_casselsTatePairingPS
#print axioms ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne_PS
