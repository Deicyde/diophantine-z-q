import WeilTatePairingLimitV002

/-!
# Counting tools for left nondegeneracy, and pairings through a homomorphism

* `LevelPairing.compRight`, `compRight_cov`: `e'_k(x, y) = e_k(x, f y)` for a homomorphism `f` on the second
  factor (in the application `f = φ_L : A(K̄) → Pic⁰(A_K̄)`, giving Mumford's `e^L`), with covariance;
* `card_range_torsion_eq`: for an `n`-divisible commutative group `G` and `φ : G →* H` with finite kernel, the
  `n`-torsion of the image of `φ` has exactly as many elements as `G[n]`
  (`|φ(G)[n]| = |[n]⁻¹(ker φ)| / |ker φ| = |G[n]|`);
* `eq_one_of_count`: if `d ↦ e(·, d)` embeds `D` into `Hom(M, μ)`, `#Hom(M, μ) ≤ #D`, and characters
  separate the points of `M`, then the left kernel is trivial.
-/

noncomputable section

namespace WeilTate

section CompRight

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N N' : Type*} [CommGroup M] [CommGroup N] [CommGroup N']
  {Ω : Type} [Field Ω]

/-- `e'_k(x, y) = e_k(x, f y)`. -/
def LevelPairing.compRight (P : LevelPairing ℓ M N Ω) (f : N' →* N) : LevelPairing ℓ M N' Ω where
  e k x y := P.e k x (f y)
  mul_left k x x' y hx hx' hy := P.mul_left k x x' (f y) hx hx' (tors_map f hy)
  mul_right k x y y' hx hy hy' := by
    rw [map_mul]
    exact P.mul_right k x _ _ hx (tors_map f hy) (tors_map f hy')
  compat k x y hx hy := P.compat k x (f y) hx (tors_map f hy)

theorem LevelPairing.compRight_cov (P : LevelPairing ℓ M N Ω) (f : N' →* N) (gM : M →* M) (gN : N →* N)
    (gμ : Ωˣ →* Ωˣ)
    (hcov : ∀ (k : ℕ) (x : M) (y : N), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      P.e k (gM x) (gN y) = gμ (P.e k x y))
    (gN' : N' →* N') (hf : ∀ y, f (gN' y) = gN (f y)) :
    ∀ (k : ℕ) (x : M) (y : N'), x ^ (ℓ ^ k) = 1 → y ^ (ℓ ^ k) = 1 →
      (P.compRight f).e k (gM x) (gN' y) = gμ ((P.compRight f).e k x y) := by
  intro k x y hx hy
  change P.e k (gM x) (f (gN' y)) = gμ (P.e k x (f y))
  rw [hf]
  exact hcov k x (f y) hx (tors_map f hy)

end CompRight

section Count

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- Lagrange through the first isomorphism theorem. -/
theorem card_eq_range_mul_ker {S T : Type*} [Group S] [Group T] (f : S →* T) :
    Nat.card S = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

/-- **The `n`-torsion of the image of `φ`.** For `G` `n`-divisible and `ker φ` finite,
`#(φ(G) ∩ H[n]) = #G[n]`. -/
theorem card_range_torsion_eq (n : ℕ) (hdiv : ∀ g : G, ∃ h : G, h ^ n = g) (φ : G →* H)
    [Finite φ.ker] :
    Nat.card ((powMonoidHom n : H →* H).ker ⊓ φ.range : Subgroup H) =
      Nat.card (powMonoidHom n : G →* G).ker := by
  set S : Subgroup G := (φ.comp (powMonoidHom n)).ker with hS
  let p : S →* G := (powMonoidHom n : G →* G).comp S.subtype
  let q : S →* H := φ.comp S.subtype
  have hpr : p.range = φ.ker := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hc
      obtain ⟨h, rfl⟩ := hdiv c
      exact ⟨⟨h, hc⟩, rfl⟩
  have hqr : q.range = (powMonoidHom n : H →* H).ker ⊓ φ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ⟨(x : G), rfl⟩⟩
      change (φ (x : G)) ^ n = 1
      rw [← map_pow]
      exact x.2
    · rintro ⟨hy, ⟨x, rfl⟩⟩
      have hx : x ∈ S := by
        change φ (x ^ n) = 1
        rw [map_pow]
        exact hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have hpk : p.ker = ((powMonoidHom n : G →* G).ker).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hqk : q.ker = φ.ker.subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hle1 : (powMonoidHom n : G →* G).ker ≤ S := by
    intro x hx
    change φ (x ^ n) = 1
    have hx' : x ^ n = 1 := hx
    rw [hx', map_one]
  have hle2 : φ.ker ≤ S := by
    intro x hx
    change φ (x ^ n) = 1
    rw [map_pow, hx, one_pow]
  have h1 := card_eq_range_mul_ker p
  have h2 := card_eq_range_mul_ker q
  rw [hpr, hpk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv] at h1
  rw [hqr, hqk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle2).toEquiv] at h2
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have h3 : Nat.card ((powMonoidHom n : H →* H).ker ⊓ φ.range : Subgroup H) * Nat.card φ.ker =
      Nat.card (powMonoidHom n : G →* G).ker * Nat.card φ.ker := by
    rw [← h2, h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos h3

/-- **Left nondegeneracy by counting.** -/
theorem eq_one_of_count {M D μ : Type*} [CommGroup M] [CommGroup D] [CommGroup μ]
    [Finite (M →* μ)] (Φ : D → (M →* μ)) (hΦ : Function.Injective Φ)
    (hcard : Nat.card (M →* μ) ≤ Nat.card D)
    (hsep : ∀ x : M, x ≠ 1 → ∃ χ : M →* μ, χ x ≠ 1) (x : M) (hx : ∀ d : D, Φ d x = 1) : x = 1 := by
  by_contra hne
  obtain ⟨χ, hχ⟩ := hsep x hne
  obtain ⟨d, rfl⟩ := (hΦ.bijective_of_nat_card_le hcard).2 χ
  exact hχ (hx d)

end Count

end WeilTate

#check @WeilTate.LevelPairing.compRight
#check @WeilTate.LevelPairing.compRight_cov
#check @WeilTate.card_range_torsion_eq
#check @WeilTate.eq_one_of_count
#print axioms WeilTate.LevelPairing.compRight
#print axioms WeilTate.LevelPairing.compRight_cov
#print axioms WeilTate.card_range_torsion_eq
#print axioms WeilTate.eq_one_of_count
