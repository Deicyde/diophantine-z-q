import ZInQKernel.HDecomp.Objects
import ToricFinitePart.FiniteDualityV002

/-!
# Toric and finite parts of actual Tate modules: Frobenius orthogonality and the annihilator

Everything lives on the original points `A(Ω)` of abelian varieties `A, A'` over `K`, written
additively, their multiplication kernels `A(Ω)[ℓⁿ]`, and the original Tate module
`T_ℓ = lim A(Ω)[ℓⁿ]` (`PkgI3.Tate.T`). Level subgroups are given level by level; the Tate-level
objects are the compatible sequences with every component in the given level subgroups.

* `pairing_toric_finite_eq_zero`: **orthogonality of the toric part and the dual finite part by a
  Frobenius argument.** Let `ψ` act on the points of both varieties, and let the level pairings be
  `ψ`-equivariant with multiplier `Q` prime to `ℓ` (the cyclotomic value of `ψ`). Suppose `ψ` acts as
  multiplication by `Q` on the toric level subgroups, and its fixed points in the finite level
  subgroups of `A'` have order dividing a fixed `ℓ^c`. Then every compatible toric sequence pairs to
  zero with every compatible finite sequence, at every level. Proof: at level `n + c` the functional
  `e(a, ·)` is `ψ`-invariant, `ℓ^c` kills the cokernel of `ψ - 1` on the finite group, and the
  level compatibility drops `ℓ^c · e` to `0` modulo `ℓⁿ`. No biextension enters.
* `annihilator_finite_le_toric`: **the annihilator of the dual finite Tate part lies in the toric
  Tate part.** Counting at each finite level (`annL_eq_of_counts`, with orthogonality from the
  Frobenius argument on both sides) identifies the level annihilator of the coordinate image of the
  dual finite Tate part with the toric level subgroup. A Tate-level bilinear pairing reducing to the
  level pairings then has annihilator inside the levelwise toric part.
* `tate_fixed_of_levelwise`, `levelwise_mono`, `levelwise_saturated`: the levelwise toric part is
  fixed by every element fixing its level points, lies in the levelwise finite part, and is
  saturated when the toric levels are.

The inputs are named hypotheses on actual objects: level pairing properties (nondegeneracy,
compatibility, equivariance), the toric multiplier, divisibility lifts of toric points, the finite
fixed-point bound, finiteness and the two order identities. None of them is an annihilator
containment, a filtration, a rank, or the conclusion.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricFinitePart

open PkgI3

variable {K : Type} [Field K] (ℓ : ℕ)

/-- The multiplication kernel `A(Ω)[ℓⁿ]`, written additively. -/
def level (A : AbVar K) (Ω : Type) [Field Ω] [Algebra K Ω] (n : ℕ) :
    AddSubgroup (Additive (A.Pt Ω)) where
  carrier := {x | (ℓ ^ n) • x = 0}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact smul_zero _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [smul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [smul_neg, ha, neg_zero]

variable {Ω : Type} [Field Ω] [Algebra K Ω]

/-- The level-`n` component of a Tate vector, as a point of `A(Ω)[ℓⁿ]`. -/
def comp [Fact ℓ.Prime] {A : AbVar K} (t : Tate.T ℓ (Additive (A.Pt Ω))) (n : ℕ) :
    level ℓ A Ω n :=
  ⟨t.1 n, Tate.pow_smul_eq_zero t.2 n⟩

/-- The original Galois action on `A(Ω)`, written additively. -/
abbrev gal (A : AbVar K) (σ : Ω ≃ₐ[K] Ω) : Additive (A.Pt Ω) →+ Additive (A.Pt Ω) :=
  MonoidHom.toAdditive (A.galAct σ)

theorem gal_mem_level (A : AbVar K) (σ : Ω ≃ₐ[K] Ω) (n : ℕ) {x : Additive (A.Pt Ω)}
    (hx : x ∈ level ℓ A Ω n) : gal A σ x ∈ level ℓ A Ω n := by
  have hx' : (ℓ ^ n) • x = 0 := hx
  show (ℓ ^ n) • gal A σ x = 0
  rw [← map_nsmul, hx', map_zero]

/-- The original Galois action restricted to `A(Ω)[ℓⁿ]`. -/
def galLevel (A : AbVar K) (σ : Ω ≃ₐ[K] Ω) (n : ℕ) : level ℓ A Ω n →+ level ℓ A Ω n where
  toFun x := ⟨gal A σ x.1, gal_mem_level ℓ A σ n x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- Tate vectors all of whose components lie in the given level subgroups. -/
def levelwise [Fact ℓ.Prime] {A : AbVar K} (S : ∀ n, AddSubgroup (level ℓ A Ω n)) :
    Submodule ℤ_[ℓ] (Tate.T ℓ (Additive (A.Pt Ω))) where
  carrier := {t | ∀ n, comp ℓ t n ∈ S n}
  zero_mem' := by
    intro n
    have h : comp ℓ (0 : Tate.T ℓ (Additive (A.Pt Ω))) n = 0 := Subtype.ext rfl
    rw [h]
    exact (S n).zero_mem
  add_mem' := by
    intro a b ha hb n
    have h : comp ℓ (a + b) n = comp ℓ a n + comp ℓ b n := Subtype.ext rfl
    rw [h]
    exact (S n).add_mem (ha n) (hb n)
  smul_mem' := by
    intro c t ht n
    have h : comp ℓ (c • t) n = (PadicInt.toZModPow n c).val • comp ℓ t n := Subtype.ext rfl
    rw [h]
    exact (S n).nsmul_mem (ht n) _

/-- The coordinate image at level `n` of a submodule of the Tate module. -/
def coordImage [Fact ℓ.Prime] {A : AbVar K} (S : Submodule ℤ_[ℓ] (Tate.T ℓ (Additive (A.Pt Ω))))
    (n : ℕ) : AddSubgroup (level ℓ A Ω n) where
  carrier := {y | ∃ s ∈ S, comp ℓ s n = y}
  zero_mem' := ⟨0, S.zero_mem, Subtype.ext rfl⟩
  add_mem' := by
    rintro a b ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
    exact ⟨s + s', S.add_mem hs hs', Subtype.ext rfl⟩
  neg_mem' := by
    rintro a ⟨s, hs, rfl⟩
    exact ⟨-s, S.neg_mem hs, Subtype.ext rfl⟩

/-- The points of a level subgroup fixed by `σ`. -/
def fixedIn {A : AbVar K} (σ : Ω ≃ₐ[K] Ω) {n : ℕ} (F : AddSubgroup (level ℓ A Ω n)) :
    AddSubgroup (level ℓ A Ω n) where
  carrier := {y | y ∈ F ∧ galLevel ℓ A σ n y = y}
  zero_mem' := ⟨F.zero_mem, map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨F.add_mem ha hb, by rw [map_add, ha', hb']⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨F.neg_mem ha, by rw [map_neg, ha']⟩

/-- **Frobenius orthogonality.** Toric compatible sequences pair to zero with finite compatible
sequences at every level. -/
theorem pairing_toric_finite_eq_zero [Fact ℓ.Prime] {A A' : AbVar K}
    (e : ∀ n, level ℓ A Ω n →+ level ℓ A' Ω n →+ ZMod (ℓ ^ n))
    (hcompat : ∀ (t : Tate.T ℓ (Additive (A.Pt Ω))) (s : Tate.T ℓ (Additive (A'.Pt Ω)))
      (n k : ℕ), e n (comp ℓ t n) (comp ℓ s n) =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n))
          (e (n + k) (comp ℓ t (n + k)) (comp ℓ s (n + k))))
    (ψ : Ω ≃ₐ[K] Ω) (Q : ℕ) (hQ : Nat.Coprime Q ℓ)
    (hequiv : ∀ n a b, e n (galLevel ℓ A ψ n a) (galLevel ℓ A' ψ n b) = Q • e n a b)
    (Tor : ∀ n, AddSubgroup (level ℓ A Ω n))
    (hTor : ∀ n x, x ∈ Tor n → galLevel ℓ A ψ n x = Q • x)
    (Fin : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hFinSt : ∀ n y, y ∈ Fin n → galLevel ℓ A' ψ n y ∈ Fin n)
    (hFinite : ∀ n, Finite (Fin n))
    (c : ℕ) (hfix : ∀ n, Nat.card (fixedIn ℓ ψ (Fin n)) ∣ ℓ ^ c)
    {t : Tate.T ℓ (Additive (A.Pt Ω))} (ht : t ∈ levelwise ℓ Tor)
    {s : Tate.T ℓ (Additive (A'.Pt Ω))} (hs : s ∈ levelwise ℓ Fin) (n : ℕ) :
    e n (comp ℓ t n) (comp ℓ s n) = 0 := by
  rw [hcompat t s n c]
  apply cast_eq_zero_of_pow_nsmul_eq_zero (Fact.out : ℓ.Prime).pos n c
  have hQu : IsUnit (Q : ZMod (ℓ ^ (n + c))) :=
    (ZMod.unitOfCoprime Q (Nat.Coprime.pow_right (n + c) hQ)).isUnit
  haveI := hFinite (n + c)
  have ha : galLevel ℓ A ψ (n + c) (comp ℓ t (n + c)) = Q • comp ℓ t (n + c) :=
    hTor (n + c) _ (ht (n + c))
  have hinv : ∀ z : level ℓ A' Ω (n + c),
      e (n + c) (comp ℓ t (n + c)) (galLevel ℓ A' ψ (n + c) z) =
        e (n + c) (comp ℓ t (n + c)) z := by
    intro z
    have h1 := hequiv (n + c) (comp ℓ t (n + c)) z
    have h2 : e (n + c) (galLevel ℓ A ψ (n + c) (comp ℓ t (n + c)))
        (galLevel ℓ A' ψ (n + c) z) =
          Q • e (n + c) (comp ℓ t (n + c)) (galLevel ℓ A' ψ (n + c) z) := by
      calc e (n + c) (galLevel ℓ A ψ (n + c) (comp ℓ t (n + c))) (galLevel ℓ A' ψ (n + c) z)
          = e (n + c) (Q • comp ℓ t (n + c)) (galLevel ℓ A' ψ (n + c) z) := by rw [ha]
        _ = (Q • e (n + c) (comp ℓ t (n + c))) (galLevel ℓ A' ψ (n + c) z) := by
            rw [map_nsmul]
        _ = Q • e (n + c) (comp ℓ t (n + c)) (galLevel ℓ A' ψ (n + c) z) := rfl
    rw [h2, nsmul_eq_mul, nsmul_eq_mul] at h1
    exact hQu.mul_left_cancel h1
  let galH : Fin (n + c) →+ Fin (n + c) :=
    { toFun := fun y => ⟨galLevel ℓ A' ψ (n + c) y.1, hFinSt (n + c) y.1 y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun y z => Subtype.ext (map_add _ _ _) }
  let v : Fin (n + c) →+ Fin (n + c) := galH - AddMonoidHom.id _
  have hker : Nat.card v.ker = Nat.card (fixedIn ℓ ψ (Fin (n + c))) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, z.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun z => rfl
        right_inv := fun y => rfl }
    · have hz : galH z.1 - z.1 = 0 := (AddMonoidHom.mem_ker).mp z.2
      exact congrArg Subtype.val (sub_eq_zero.mp hz)
    · apply (AddMonoidHom.mem_ker).mpr
      show galH ⟨y.1, y.2.1⟩ - ⟨y.1, y.2.1⟩ = 0
      exact sub_eq_zero.mpr (Subtype.ext y.2.2)
  obtain ⟨z, hz⟩ := nsmul_mem_range_of_card_ker_dvd v (hker ▸ hfix (n + c))
    (⟨comp ℓ s (n + c), hs (n + c)⟩ : Fin (n + c))
  have hb : (ℓ ^ c) • comp ℓ s (n + c) = galLevel ℓ A' ψ (n + c) z.1 - z.1 :=
    (congrArg Subtype.val hz).symm
  rw [← map_nsmul, hb, map_sub, hinv, sub_self]

/-- The annihilator of a submodule under a bilinear map. -/
def annihilator {R : Type} [CommRing R] {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (B : M →ₗ[R] N →ₗ[R] P) (F : Submodule R N) : Submodule R M where
  carrier := {x | ∀ y ∈ F, B x y = 0}
  zero_mem' := by intro y _; simp
  add_mem' := by
    intro x z hx hz y hy
    simp only [map_add, LinearMap.add_apply, hx y hy, hz y hy, add_zero]
  smul_mem' := by
    intro a x hx y hy
    simp only [map_smul, LinearMap.smul_apply, hx y hy, smul_zero]

/-- **The annihilator of the dual finite Tate part lies in the toric Tate part.** -/
theorem annihilator_finite_le_toric [Fact ℓ.Prime] {A A' : AbVar K}
    {P : Type} [AddCommGroup P] [Module ℤ_[ℓ] P]
    (B : Tate.T ℓ (Additive (A.Pt Ω)) →ₗ[ℤ_[ℓ]] Tate.T ℓ (Additive (A'.Pt Ω)) →ₗ[ℤ_[ℓ]] P)
    (e : ∀ n, level ℓ A Ω n →+ level ℓ A' Ω n →+ ZMod (ℓ ^ n))
    (r : ∀ n, P →+ ZMod (ℓ ^ n))
    (hB : ∀ t s n, r n (B t s) = e n (comp ℓ t n) (comp ℓ s n))
    (heL : ∀ n x, (∀ y, e n x y = 0) → x = 0) (heR : ∀ n y, (∀ x, e n x y = 0) → y = 0)
    (hcompat : ∀ (t : Tate.T ℓ (Additive (A.Pt Ω))) (s : Tate.T ℓ (Additive (A'.Pt Ω)))
      (n k : ℕ), e n (comp ℓ t n) (comp ℓ s n) =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n))
          (e (n + k) (comp ℓ t (n + k)) (comp ℓ s (n + k))))
    (ψ : Ω ≃ₐ[K] Ω) (Q : ℕ) (hQ : Nat.Coprime Q ℓ)
    (hequiv : ∀ n a b, e n (galLevel ℓ A ψ n a) (galLevel ℓ A' ψ n b) = Q • e n a b)
    (Tor : ∀ n, AddSubgroup (level ℓ A Ω n)) (Tor' : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hTor : ∀ n x, x ∈ Tor n → galLevel ℓ A ψ n x = Q • x)
    (hTor' : ∀ n x, x ∈ Tor' n → galLevel ℓ A' ψ n x = Q • x)
    (hTorLift : ∀ n x, x ∈ Tor n → ∃ t ∈ levelwise ℓ Tor, comp ℓ t n = x)
    (hTorLift' : ∀ n x, x ∈ Tor' n → ∃ t ∈ levelwise ℓ Tor', comp ℓ t n = x)
    (Fin : ∀ n, AddSubgroup (level ℓ A Ω n)) (Fin' : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hFinSt : ∀ n y, y ∈ Fin n → galLevel ℓ A ψ n y ∈ Fin n)
    (hFinSt' : ∀ n y, y ∈ Fin' n → galLevel ℓ A' ψ n y ∈ Fin' n)
    (c c' : ℕ) (hfix : ∀ n, Nat.card (fixedIn ℓ ψ (Fin n)) ∣ ℓ ^ c)
    (hfix' : ∀ n, Nat.card (fixedIn ℓ ψ (Fin' n)) ∣ ℓ ^ c')
    (hfinA : ∀ n, Finite (level ℓ A Ω n)) (hfinA' : ∀ n, Finite (level ℓ A' Ω n))
    (hcount : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ Fin) n) * Nat.card (Tor n) =
      Nat.card (level ℓ A Ω n))
    (hcount' : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ Fin') n) * Nat.card (Tor' n) =
      Nat.card (level ℓ A' Ω n)) :
    annihilator B (levelwise ℓ Fin') ≤ levelwise ℓ Tor := by
  have hFinite : ∀ n, Finite (Fin n) := fun n => by
    haveI := hfinA n
    infer_instance
  have hFinite' : ∀ n, Finite (Fin' n) := fun n => by
    haveI := hfinA' n
    infer_instance
  have hlevel : ∀ n, annL (e n) (coordImage ℓ (levelwise ℓ Fin') n) = Tor n := by
    intro n
    haveI := hfinA n
    haveI := hfinA' n
    refine annL_eq_of_counts (e n) (heL n) (heR n) (Tor n) (coordImage ℓ (levelwise ℓ Fin) n)
      (Tor' n) (coordImage ℓ (levelwise ℓ Fin') n) ?_ ?_ (hcount n) (hcount' n)
    · intro x hx y hy
      obtain ⟨t, ht, rfl⟩ := hTorLift n x hx
      obtain ⟨s, hs, rfl⟩ := hy
      exact pairing_toric_finite_eq_zero ℓ e hcompat ψ Q hQ hequiv Tor hTor Fin' hFinSt'
        hFinite' c' hfix' ht hs n
    · intro y hy x hx
      obtain ⟨t, ht, rfl⟩ := hTorLift' n y hy
      obtain ⟨s, hs, rfl⟩ := hx
      exact pairing_toric_finite_eq_zero ℓ (fun n => (e n).flip) (fun t s n k => hcompat s t n k)
        ψ Q hQ (fun n a b => hequiv n b a) Tor' hTor' Fin hFinSt hFinite c hfix ht hs n
  intro t ht n
  rw [← hlevel n]
  intro y hy
  obtain ⟨s, hs, rfl⟩ := hy
  rw [← hB, ht s hs, map_zero]

/-- The levelwise part of level subgroups fixed by `σ` is fixed by the original Tate action. -/
theorem tate_fixed_of_levelwise [Fact ℓ.Prime] {A : AbVar K} (σ : Ω ≃ₐ[K] Ω)
    (S : ∀ n, AddSubgroup (level ℓ A Ω n)) (hS : ∀ n x, x ∈ S n → galLevel ℓ A σ n x = x)
    {t : Tate.T ℓ (Additive (A.Pt Ω))} (ht : t ∈ levelwise ℓ S) :
    Tate.map (MonoidHom.toAdditive (A.galAct σ)) t = t := by
  apply Subtype.ext
  funext n
  exact congrArg Subtype.val (hS n _ (ht n))

/-- Monotonicity of the levelwise construction (toric levels inside finite levels). -/
theorem levelwise_mono [Fact ℓ.Prime] {A : AbVar K} {S S' : ∀ n, AddSubgroup (level ℓ A Ω n)}
    (h : ∀ n, S n ≤ S' n) : levelwise ℓ S ≤ levelwise ℓ S' :=
  fun _ ht n => h n (ht n)

/-- Saturation: if each toric level is the `ℓⁿ`-torsion of the next, the levelwise part is
saturated under multiplication by `ℓ`. -/
theorem levelwise_saturated [Fact ℓ.Prime] {A : AbVar K} (S : ∀ n, AddSubgroup (level ℓ A Ω n))
    (hS : ∀ n (x : level ℓ A Ω n) (h : x.1 ∈ level ℓ A Ω (n + 1)),
      (⟨x.1, h⟩ : level ℓ A Ω (n + 1)) ∈ S (n + 1) → x ∈ S n)
    {t : Tate.T ℓ (Additive (A.Pt Ω))} (ht : (ℓ : ℤ_[ℓ]) • t ∈ levelwise ℓ S) :
    t ∈ levelwise ℓ S := by
  intro n
  have h1 : ((ℓ : ℤ_[ℓ]) • t).1 (n + 1) = t.1 n := by
    have h := Tate.smulSeq_congr t.2 (n + 1) (a := (ℓ : ℤ_[ℓ])) (c := ℓ) (by rw [map_natCast])
    exact h.trans (t.2.2 n)
  have hmem1 : (comp ℓ t n).1 ∈ level ℓ A Ω (n + 1) := by
    show (ℓ ^ (n + 1)) • t.1 n = 0
    rw [pow_succ', mul_smul, Tate.pow_smul_eq_zero t.2 n, smul_zero]
  apply hS n (comp ℓ t n) hmem1
  have hcomp : (⟨(comp ℓ t n).1, hmem1⟩ : level ℓ A Ω (n + 1)) =
      comp ℓ ((ℓ : ℤ_[ℓ]) • t) (n + 1) := Subtype.ext h1.symm
  rw [hcomp]
  exact ht (n + 1)

end ToricFinitePart
