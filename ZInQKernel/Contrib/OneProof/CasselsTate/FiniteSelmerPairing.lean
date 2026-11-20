import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.OneProof.CasselsTate.SelmerMultiplication

/-! The finite-level Cassels–Tate pairing suffices for the manuscript's
square property, by taking a single level that kills the finite factor. -/

noncomputable section

namespace ZInQ.Manuscript.SelmerTwoPower

open TauCeti ZInQ.Cofinite

private theorem two_power_kills_finite_factor
    {A F : Type*} [AddCommGroup A] [AddCommGroup F] [Finite F] {t : ℕ}
    (e : AddCommGroup.primaryComponent A 2 ≃+ (Fin t → Q2Z2) × F) :
    (∀ f : F, ∃ k : ℕ, 2 ^ k • f = 0) ∧ ∃ k : ℕ, 0 < k ∧ ∀ f : F, 2 ^ k • f = 0 := by
  have hF (f : F) : ∃ k : ℕ, 2 ^ k • f = 0 := by
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp (e.symm (0, f)).2
    have hs : 2 ^ k • e.symm (0, f) = 0 := Subtype.ext hk
    have hp := congrArg e hs
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero] at hp
    exact ⟨k, congrArg Prod.snd hp⟩
  refine ⟨hF, ?_⟩
  classical
  let : Fintype F := Fintype.ofFinite F
  choose k hk using hF
  refine ⟨Finset.univ.sup k + 1, Nat.zero_lt_succ _, fun f => ?_⟩
  have hle : k f ≤ Finset.univ.sup k + 1 :=
    (Finset.le_sup (Finset.mem_univ f)).trans (Nat.le_succ _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_nsmul', hk, nsmul_zero]

private theorem pairing_skew {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (b : A →+ A →+ B) (h : ∀ x, b x x = 0) (x y : A) : b x y = -b y x := by
  have hxy := h (x + y)
  simp only [map_add, AddMonoidHom.add_apply, h, zero_add, add_zero] at hxy
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hxy)

/-- If every `2^k`-torsion group with `k > 0` has the diagonal finite Cassels–Tate pairing
with the prescribed radical, every finite factor of a `2`-primary
decomposition has square `2`-torsion order. -/
theorem square_of_pairings_on_two_pow_torsion
    {A : Type*} {F : Type} [AddCommGroup A] [AddCommGroup F] [Finite F] {t : ℕ}
    (e : AddCommGroup.primaryComponent A 2 ≃+ (Fin t → Q2Z2) × F)
    (hPair : ∀ k : ℕ, 0 < k → let B := AddSubgroup.torsionBy A (2 ^ k : ℕ)
      ∃ b : B →+ B →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
        (∀ y, b x y = 0) ↔ ∃ z : A, 2 ^ k • z = (x : A)) :
    IsSquare (Nat.card (tors F 2)) := by
  obtain ⟨hF, k, hkpos, hk⟩ := two_power_kills_finite_factor e
  obtain ⟨b, halt, hrad⟩ := hPair k hkpos
  let B := AddSubgroup.torsionBy A (2 ^ k : ℕ)
  let j : (Fin t → Q2Z2) × F →+ A :=
    (AddCommGroup.primaryComponent A 2).subtype.comp e.symm.toAddMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  let i : F →+ B := (j.comp (AddMonoidHom.inr _ _)).codRestrict B fun f => by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    change 2 ^ k • j (0, f) = 0
    rw [← map_nsmul, Prod.smul_mk, nsmul_zero, hk]
    exact map_zero j
  let β : F →+ F →+ QZ := (b.compl₂ i).comp i
  apply isSquare_card_tors_two_of_alternating hF β (fun f => halt (i f))
  intro f hf
  have hfix (y : B) : b (i f) y = 0 := by
    let y₂ : AddCommGroup.primaryComponent A 2 :=
      ⟨y, AddCommGroup.mem_primaryComponent.mpr ⟨k, AddSubgroup.torsionBy.nsmul_iff.mp y.2⟩⟩
    obtain ⟨d, g, hdg⟩ : ∃ d g, e y₂ = (d, g) := ⟨(e y₂).1, (e y₂).2, rfl⟩
    have hsplit : (y : A) = j (d, g) := by
      change (y₂ : A) = ((e.symm (d, g)) : A)
      rw [← hdg, AddEquiv.symm_apply_apply]
    have hdiv : ∃ z : A, 2 ^ k • z = ((y - i g : B) : A) := by
      let d' := DivisibleBy.div d ((2 ^ k : ℕ) : ℤ)
      refine ⟨j (d', 0), ?_⟩
      have hd' : 2 ^ k • d' = d := by
        rw [← natCast_zsmul]
        exact DivisibleBy.div_cancel d (by positivity)
      change 2 ^ k • j (d', 0) = (y : A) - j (0, g)
      rw [hsplit, ← map_nsmul, Prod.smul_mk, hd', nsmul_zero, ← map_sub]
      congr 1
      ext <;> simp
    have hz := (hrad (y - i g)).mpr hdiv (i f)
    have hzero : b (i f) (y - i g) = 0 := by
      rw [pairing_skew b halt, hz, neg_zero]
    rw [map_sub, show b (i f) (i g) = 0 from hf g, sub_zero] at hzero
    exact hzero
  obtain ⟨z, hz⟩ := (hrad (i f)).mp hfix
  have hz₂ : z ∈ AddCommGroup.primaryComponent A 2 :=
    AddCommGroup.mem_primaryComponent.mpr ⟨k + k, by
      rw [pow_add, mul_nsmul', hz]
      exact AddSubgroup.torsionBy.nsmul_iff.mp (i f).2⟩
  let w := e ⟨z, hz₂⟩
  have hw : j w = z := by simp [j, w]
  have hz' : 2 ^ k • j w = j (0, f) := by rwa [hw]
  rw [← map_nsmul] at hz'
  have hf' := congrArg Prod.snd (hj hz')
  change 2 ^ k • w.2 = f at hf'
  rw [hk] at hf'
  exact hf'.symm

private theorem exists_pairing_of_surjective
    {T S B C : Type*} [AddCommGroup T] [AddCommGroup S] [AddCommGroup B] [AddCommGroup C]
    (φ : S →+ B) (hφ : Function.Surjective φ) (ψ : T →+ S) (hψ : φ.ker ≤ ψ.range)
    (b : S →+ S →+ C) (halt : ∀ x, b x x = 0)
    (hrad : ∀ x, (∀ y, b x y = 0) ↔ x ∈ ψ.range) :
    ∃ d : B →+ B →+ C, (∀ x, d x x = 0) ∧ ∀ x,
      (∀ y, d x y = 0) ↔ x ∈ (φ.comp ψ).range := by
  let s := Function.surjInv hφ
  have hs : Function.RightInverse s φ := Function.rightInverse_surjInv hφ
  have hb : φ.ker ≤ b.ker := fun _ hx =>
    AddMonoidHom.mem_ker.mpr (AddMonoidHom.ext ((hrad _).mpr (hψ hx)))
  let c : B →+ S →+ C := φ.liftOfRightInverse s hs ⟨b, hb⟩
  have hc (x : S) : c (φ x) = b x := φ.liftOfRightInverse_comp_apply s hs _ x
  have hcKer : φ.ker ≤ c.flip.ker := by
    intro y hy
    apply AddMonoidHom.mem_ker.mpr
    ext x
    obtain ⟨x, rfl⟩ := hφ x
    change c (φ x) y = 0
    rw [hc, pairing_skew b halt, (hrad y).mpr (hψ hy) x, neg_zero]
  let d : B →+ B →+ C := (φ.liftOfRightInverse s hs ⟨c.flip, hcKer⟩).flip
  have hd (x y : S) : d (φ x) (φ y) = b x y := by
    change (φ.liftOfRightInverse s hs ⟨c.flip, hcKer⟩) (φ y) (φ x) = _
    rw [φ.liftOfRightInverse_comp_apply]
    exact DFunLike.congr_fun (hc x) y
  refine ⟨d, ?_, ?_⟩
  · intro x
    obtain ⟨x, rfl⟩ := hφ x
    rw [hd, halt]
  · intro x
    constructor
    · intro hx
      obtain ⟨x, rfl⟩ := hφ x
      obtain ⟨z, hz⟩ := (hrad x).mp (fun y => (hd x y).symm.trans (hx (φ y)))
      exact ⟨z, congrArg φ hz⟩
    · rintro ⟨z, rfl⟩ y
      obtain ⟨y, rfl⟩ := hφ y
      change d (φ (ψ z)) (φ y) = 0
      rw [hd]
      exact (hrad _).mpr ⟨z, rfl⟩ y

/-- The finite-level Cassels–Tate pairing for an elliptic curve over `ℚ`,
specialized to `m = 2^k ≥ 2`. Its left radical is the image from level `m*m`.
Fisher, *On binary quartics and the Cassels–Tate pairing*, Res. Number Theory
8 (2022), article 74, §1 (arXiv:2208.14977v1, p. 1, display after the Selmer
exact sequence), restates Cassels' theorem for all `m ≥ 2` over a number field. -/
def FiniteSelmerCasselsTatePairing (E : WeierstrassCurve ℚ) : Prop :=
  ∀ k : ℕ, 0 < k → let m : ℕ := 2 ^ k
    let S := E.selmerGroup Fam.emb m
    ∃ b : S →+ S →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
      (∀ y, b x y = 0) ↔ x ∈ (E.selmerMultiplication Fam.emb m m).range

set_option maxHeartbeats 1000000 in
/-- The finite diagonal pairings and their image formula suffice for the
Cassels–Tate square property used in the manuscript. -/
theorem casselsTateSquare_of_finiteSelmerPairing (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : FiniteSelmerCasselsTatePairing E) : CasselsTateSquare E := by
  rw [casselsTateSquare_iff_fam]
  intro t F _ _ e
  apply square_of_pairings_on_two_pow_torsion e
  intro k hk
  let m : ℕ := 2 ^ k
  have hm : IsUnit (m : ℚ) := isUnit_iff_ne_zero.mpr (by
    exact_mod_cast pow_ne_zero k (two_ne_zero : (2 : ℕ) ≠ 0))
  have hmm : IsUnit ((m * m : ℕ) : ℚ) := by rw [Nat.cast_mul]; exact hm.mul hm
  obtain ⟨b, halt, hrad⟩ := h k hk
  obtain ⟨d, hd, hker⟩ := exists_pairing_of_surjective (E.selmerShaMap Fam.emb m)
    (E.selmerShaMap_surjective Fam.emb hm) (E.selmerMultiplication Fam.emb m m)
    (E.ker_selmerShaMap_le_range_multiplication Fam.emb m m hm hmm) b halt hrad
  exact ⟨d, hd, fun x => (hker x).trans (E.mem_range_selmerShaMap_multiplication_iff
    Fam.emb m m hmm x)⟩

#print axioms square_of_pairings_on_two_pow_torsion
#print axioms casselsTateSquare_of_finiteSelmerPairing

end ZInQ.Manuscript.SelmerTwoPower

namespace ZInQ.Manuscript.PoleS12

open SelmerTwoPower

/-- Finite diagonal Cassels–Tate pairings for the manuscript's curves. -/
def FiniteSelmerCasselsTatePairingCurves : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
    FiniteSelmerCasselsTatePairing (Manuscript.curve ℓ)

theorem casselsTateSquareCurves_of_finiteSelmerPairing
    (h : FiniteSelmerCasselsTatePairingCurves) : CasselsTateSquareCurves := by
  intro ℓ hp hs hmod
  have := PoleRC.curve_isElliptic (by exact_mod_cast hp.ne' : (ℓ : ℚ) ≠ 0)
  exact casselsTateSquare_of_finiteSelmerPairing _ (h ℓ hp hs hmod)

/-- Lemma 5.4 on the manuscript curves from the finite-level pairings. -/
theorem lemma54At_of_finiteSelmerPairing (h : FiniteSelmerCasselsTatePairingCurves) :
    PoleRC.Lemma54At SelmerTwoPower.SelmerCorankOne :=
  lemma54At_of_casselsTate (casselsTateSquareCurves_of_finiteSelmerPairing h)

/-- The pole-completeness argument uses only the diagonal finite-level pairings. -/
theorem poleCompleteness_of_restrictedConverseGenuine_finiteSelmerPairing
    (hRC : RestrictedConverseGenuine) (hCT : FiniteSelmerCasselsTatePairingCurves)
    (hB : BCDTThmA) (hK : KolyvaginThm1) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverseGenuine_casselsTate hRC
    (casselsTateSquareCurves_of_finiteSelmerPairing hCT) hB hK

#print axioms casselsTateSquareCurves_of_finiteSelmerPairing
#print axioms lemma54At_of_finiteSelmerPairing
#print axioms poleCompleteness_of_restrictedConverseGenuine_finiteSelmerPairing

end ZInQ.Manuscript.PoleS12
