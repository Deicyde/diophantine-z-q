import ZInQKernel.Contrib.OneProof.CasselsTate.SelmerLayerDescent

/-! # An alternating pairing on a primary component from finite layers

For a prime `p`, finiteness of `A[p]` splits the primary component into a
divisible part and a finite group `F`. A single sufficiently deep layer of
the finite-level pairings gives a nondegenerate pairing on `F`. Pulling it
back along the projection gives the required radical on the primary component.
-/

noncomputable section

namespace ZInQ.Manuscript.CasselsTateGlobal

open SelmerTwoPower ZInQ.Cofinite

/-- A positive power of the prime kills the entire finite factor of the primary component. -/
theorem power_kills_finite_factor
    {p : ℕ} [Fact p.Prime] {A F : Type*} [AddCommGroup A] [AddCommGroup F] [Finite F] {t : ℕ}
    (e : AddCommGroup.primaryComponent A p ≃+ (Fin t → Qp p) × F) :
    ∃ k : ℕ, 0 < k ∧ ∀ f : F, p ^ k • f = 0 := by
  have hF (f : F) : ∃ k : ℕ, p ^ k • f = 0 := by
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp (e.symm (0, f)).2
    have hs : p ^ k • e.symm (0, f) = 0 := Subtype.ext hk
    have hp := congrArg e hs
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero] at hp
    exact ⟨k, congrArg Prod.snd hp⟩
  classical
  let : Fintype F := Fintype.ofFinite F
  choose k hk using hF
  refine ⟨Finset.univ.sup k + 1, Nat.zero_lt_succ _, fun f => ?_⟩
  have hle : k f ≤ Finset.univ.sup k + 1 :=
    (Finset.le_sup (Finset.mem_univ f)).trans (Nat.le_succ _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_nsmul', hk, nsmul_zero]

/-- At a level killing the finite factor, restriction gives it a nondegenerate alternating pairing. -/
theorem finite_factor_pairing {A F : Type*} [AddCommGroup A] [AddCommGroup F]
    {p : ℕ} [Fact p.Prime] {t k : ℕ}
    (e : AddCommGroup.primaryComponent A p ≃+ (Fin t → Qp p) × F)
    (hk : ∀ f : F, p ^ k • f = 0)
    (b : AddSubgroup.torsionBy A (p ^ k : ℕ) →+ AddSubgroup.torsionBy A (p ^ k : ℕ) →+ QZ)
    (halt : ∀ x, b x x = 0)
    (hrad : ∀ x, (∀ y, b x y = 0) ↔ ∃ z : A, p ^ k • z = (x : A)) :
    ∃ β : F →+ F →+ QZ, (∀ f, β f f = 0) ∧ ∀ f, (∀ g, β f g = 0) → f = 0 := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  let B := AddSubgroup.torsionBy A (p ^ k : ℕ)
  let j : (Fin t → Qp p) × F →+ A :=
    (AddCommGroup.primaryComponent A p).subtype.comp e.symm.toAddMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  let i : F →+ B := (j.comp (AddMonoidHom.inr _ _)).codRestrict B fun f => by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    change p ^ k • j (0, f) = 0
    rw [← map_nsmul, Prod.smul_mk, nsmul_zero, hk]
    exact map_zero j
  let β : F →+ F →+ QZ := (b.compl₂ i).comp i
  refine ⟨β, fun f => halt (i f), ?_⟩
  intro f hf
  have hfix (y : B) : b (i f) y = 0 := by
    let yp : AddCommGroup.primaryComponent A p :=
      ⟨y, AddCommGroup.mem_primaryComponent.mpr ⟨k, AddSubgroup.torsionBy.nsmul_iff.mp y.2⟩⟩
    obtain ⟨d, g, hdg⟩ : ∃ d g, e yp = (d, g) := ⟨(e yp).1, (e yp).2, rfl⟩
    have hsplit : (y : A) = j (d, g) := by
      change (yp : A) = ((e.symm (d, g)) : A)
      rw [← hdg, AddEquiv.symm_apply_apply]
    have hdiv : ∃ z : A, p ^ k • z = ((y - i g : B) : A) := by
      let d' := DivisibleBy.div d ((p ^ k : ℕ) : ℤ)
      refine ⟨j (d', 0), ?_⟩
      have hd' : p ^ k • d' = d := by
        rw [← natCast_zsmul]
        exact DivisibleBy.div_cancel d (by positivity)
      change p ^ k • j (d', 0) = (y : A) - j (0, g)
      rw [hsplit, ← map_nsmul, Prod.smul_mk, hd', nsmul_zero, ← map_sub]
      congr 1
      ext <;> simp
    have hz := (hrad (y - i g)).mpr hdiv (i f)
    have hzero : b (i f) (y - i g) = 0 := by
      rw [pairing_skew b halt, hz, neg_zero]
    rw [map_sub, show b (i f) (i g) = 0 from hf g, sub_zero] at hzero
    exact hzero
  obtain ⟨z, hz⟩ := (hrad (i f)).mp hfix
  have hzp : z ∈ AddCommGroup.primaryComponent A p :=
    AddCommGroup.mem_primaryComponent.mpr ⟨k + k, by
      rw [pow_add, mul_nsmul', hz]
      exact AddSubgroup.torsionBy.nsmul_iff.mp (i f).2⟩
  let w := e ⟨z, hzp⟩
  have hw : j w = z := by simp [j, w]
  have hz' : p ^ k • j w = j (0, f) := by rwa [hw]
  rw [← map_nsmul] at hz'
  have hf' := congrArg Prod.snd (hj hz')
  change p ^ k • w.2 = f at hf'
  rw [hk] at hf'
  exact hf'.symm

/-- On a primary component with finite `p`-torsion, alternating pairings on
`A[p^k]` with radical `A[p^k] ∩ p^k A` give a pairing whose radical is the
maximal divisible subgroup. The pairings may be chosen independently at each level. -/
theorem primary_pairing_of_finite_layers (A : Type*) [AddCommGroup A]
    (p : ℕ) [Fact p.Prime] (hfin : Finite (AddSubgroup.torsionBy A p))
    (hPair : ∀ k : ℕ, 0 < k → let B := AddSubgroup.torsionBy A (p ^ k : ℕ)
      ∃ b : B →+ B →+ QZ, (∀ x, b x x = 0) ∧ ∀ x,
        (∀ y, b x y = 0) ↔ ∃ z : A, p ^ k • z = (x : A)) :
    let P := AddCommGroup.primaryComponent A p
    ∃ b : P →+ P →+ QZ, (∀ x, b x x = 0) ∧ ∀ x, (∀ y, b x y = 0) ↔ x ∈ divisiblePart P := by
  let P := AddCommGroup.primaryComponent A p
  have hP : IsPPrimary p P := by
    intro x
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
    exact ⟨k, Subtype.ext hk⟩
  let ι : tors P p → AddSubgroup.torsionBy A p := fun x => ⟨(x.1 : A),
    AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val (mem_tors.mp x.2))⟩
  have hPfin : Finite (tors P p) := Finite.of_injective ι fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun y : AddSubgroup.torsionBy A p => (y : A)) h))
  obtain ⟨t, F, _, _, ⟨e⟩⟩ := exists_addEquiv_of_isPPrimary P hP hPfin
  obtain ⟨k, hkpos, hk⟩ := power_kills_finite_factor e
  obtain ⟨b, halt, hrad⟩ := hPair k hkpos
  obtain ⟨β, hβalt, hβnondeg⟩ := finite_factor_pairing e hk b halt hrad
  let π : P →+ F := (AddMonoidHom.snd _ _).comp e.toAddMonoidHom
  let χ : (Fin t → Qp p) →+ P := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
  have hχ : χ.range ≤ divisiblePart P := by
    apply le_divisiblePart
    rintro _ ⟨d, rfl⟩ n hn
    refine ⟨χ (DivisibleBy.div d (n : ℤ)), ⟨_, rfl⟩, ?_⟩
    rw [← map_nsmul, ← natCast_zsmul, DivisibleBy.div_cancel d (by exact_mod_cast hn)]
  refine ⟨(β.compl₂ π).comp π, fun x => hβalt (π x), fun x => ?_⟩
  change (∀ y, β (π x) (π y) = 0) ↔ x ∈ divisiblePart P
  constructor
  · intro hx
    have hzero : π x = 0 := hβnondeg _ fun g => by
      simpa [π] using hx (e.symm (0, g))
    apply hχ
    refine ⟨(e x).1, e.injective ?_⟩
    change e (e.symm ((e x).1, 0)) = e x
    rw [e.apply_symm_apply]
    exact Prod.ext rfl hzero.symm
  · intro hx y
    obtain ⟨z, hz⟩ := exists_nsmul_eq_of_mem_divisiblePart hx
      (pow_ne_zero k (Fact.out : Nat.Prime p).ne_zero)
    have hzero : π x = 0 := by rw [← hz, map_nsmul, hk]
    rw [hzero, map_zero, AddMonoidHom.zero_apply]

end ZInQ.Manuscript.CasselsTateGlobal
