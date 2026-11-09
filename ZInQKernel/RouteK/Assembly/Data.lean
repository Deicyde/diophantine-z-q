import ZInQKernel.RouteK.Assembly.Realize

/-!
# Route K, L5: the slot data on abstract index types

The data of slot-k §2.4: `β`, `θ`, `p₀ ∈ P` and slots `D : Slots β θ p₀`, with the properties of
`β` and `θ` that the proof of DL uses (`Inputs`: `β` odd squarefree with `|β| ≡ 7 (mod 8)`;
`θ > 0` squarefree with `θ ≡ 1 (mod 8)`; `β`, `θ` coprime; (θ3) and (θ4) in bits).

The primes of the two curves are indexed by the abstract types of Lemmas 1 and 2
(`ZInQKernel/RouteK/System/`), with `G = P ∖ {p₀}` and `T` the primes of `θ`:

* `Option G` stands for `P` (`none ↦ p₀`, `some p ↦ p`; `D.pP`);
* `𝒞_Σ`, on `P ∪ {q₀} ∪ R_P`, is indexed by `Unit ⊕ (Option G ⊕ G)` (`D.fS`): `q₀`, `P`, `r_p`;
* `𝒞₁`, on `P ∪ {q₀} ∪ R_P ∪ R_T`, by `(Unit ⊕ (Option G ⊕ G)) ⊕ T` (`D.f₁`), the partners
  `r_ℓ` on the right;
* `𝒞₂`, on `P ∪ R_P ∪ {q₀} ∪ T ∪ R_T`, by `(Option G ⊕ G) ⊕ (Option T ⊕ T)` (`D.f₂`), in the
  shape `S' ⊕ (Option G' ⊕ G')` of Lemma 2 with `g = q₀`, `G' = T` and glue primes `r_ℓ`.

This file proves that these maps are injective families of odd primes.
-/

namespace ZInQ.RouteK

open scoped BigOperators

/-- The properties of `β` and `θ` used by the proof of DL (slot-k §2.4, §2.5): `β` odd, squarefree,
`|β| ≡ 7 (mod 8)`, `p₀ ∈ P`; (θ1) `θ > 0`, `θ ≡ 1 (mod 8)`, and `θ` squarefree; (θ2) `β`, `θ`
coprime; (θ3) `[β/ℓ] = 0` for `ℓ ∣ θ`; (θ4) `[θ/p] = 0` for `p ∣ β`. -/
structure Inputs (β θ : ℤ) (p₀ : ℕ) : Prop where
  sqf_β : Squarefree β
  odd_β : Odd β
  mod_β : β.natAbs % 8 = 7
  p₀_mem : p₀ ∈ primesOf β
  pos_θ : 0 < θ
  mod_θ : θ % 8 = 1
  sqf_θ : Squarefree θ
  coprime : IsCoprime β θ
  θ3 : ∀ ℓ ∈ primesOf θ, legBit ℓ β = 0
  θ4 : ∀ p ∈ primesOf β, legBit p θ = 0

/-- `G = P ∖ {p₀}`, as a type. -/
abbrev GP (β : ℤ) (p₀ : ℕ) := {p // p ∈ primesOf β \ {p₀}}

/-- The primes `T` of `θ`, as a type. -/
abbrev TP (θ : ℤ) := {ℓ // ℓ ∈ primesOf θ}

namespace Inputs

variable {β θ : ℤ} {p₀ : ℕ} (hI : Inputs β θ p₀)
include hI

theorem β_ne_zero : β ≠ 0 := hI.sqf_β.ne_zero

theorem θ_ne_zero : θ ≠ 0 := hI.pos_θ.ne'

theorem odd_θ : Odd θ := Int.odd_iff.mpr (by have := hI.mod_θ; omega)

theorem mem_P {p : ℕ} (hp : p ∈ primesOf β) : p.Prime ∧ p ≠ 2 := odd_of_mem_primesOf hI.odd_β hp

theorem mem_T {ℓ : ℕ} (hℓ : ℓ ∈ primesOf θ) : ℓ.Prime ∧ ℓ ≠ 2 := odd_of_mem_primesOf hI.odd_θ hℓ

theorem disjoint {p : ℕ} (hp : p ∈ primesOf β) (hpT : p ∈ primesOf θ) : False := by
  obtain ⟨hpp, hd1, -⟩ := mem_primesOf.mp hp
  obtain ⟨-, hd2, -⟩ := mem_primesOf.mp hpT
  exact (Nat.prime_iff_prime_int.mp hpp).not_isUnit (hI.coprime.isUnit_of_dvd' hd1 hd2)

omit hI in
/-- A prime not dividing `2βθ` lies neither in `P` nor in `T`. -/
theorem not_mem_of_not_dvd {q : ℕ} (h : ¬ (q : ℤ) ∣ 2 * β * θ) :
    q ∉ primesOf β ∧ q ∉ primesOf θ := by
  constructor
  · intro hq
    exact h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (mem_primesOf.mp hq).2.1 _) _)
  · intro hq
    exact h (dvd_mul_of_dvd_right (mem_primesOf.mp hq).2.1 _)

theorem prod_P : ∏ p ∈ primesOf β, p = β.natAbs :=
  Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hI.sqf_β)

theorem prod_T : ∏ ℓ ∈ primesOf θ, ℓ = θ.natAbs :=
  Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hI.sqf_θ)

theorem θ_natAbs_mod : θ.natAbs % 8 = 1 := by
  have := hI.mod_θ; have := hI.pos_θ; omega

end Inputs

namespace Slots

variable {β θ : ℤ} {p₀ : ℕ} (D : Slots β θ p₀)

/-- `Option G` stands for `P`: `none ↦ p₀`, `some p ↦ p`. -/
def pP : Option (GP β p₀) → ℕ := fun o => o.elim p₀ Subtype.val

/-- The glue slots `r_p`, on `G`. -/
def rPv : GP β p₀ → ℕ := fun p => D.rP p.1

/-- The glue slots `r_ℓ`, on `T`. -/
def rTv : TP θ → ℕ := fun ℓ => D.rT ℓ.1

/-- `Option T` stands for `{q₀} ∪ T`: `none ↦ q₀`, `some ℓ ↦ ℓ`. -/
def qT : Option (TP θ) → ℕ := fun o => o.elim D.q₀ Subtype.val

/-- The primes of `𝒞_Σ` on `P ∪ {q₀} ∪ R_P`. -/
def fS : Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀) → ℕ :=
  Sum.elim (fun _ => D.q₀) (Sum.elim pP D.rPv)

/-- The primes of `𝒞₁` on `P ∪ {q₀} ∪ R_P ∪ R_T`. -/
def f₁ : (Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) ⊕ TP θ → ℕ := Sum.elim D.fS D.rTv

/-- The primes of `𝒞₂` on `P ∪ R_P ∪ {q₀} ∪ T ∪ R_T`. -/
def f₂ : (Option (GP β p₀) ⊕ GP β p₀) ⊕ (Option (TP θ) ⊕ TP θ) → ℕ :=
  Sum.elim (Sum.elim pP D.rPv) (Sum.elim D.qT D.rTv)

theorem q₀_not_mem : D.q₀ ∉ primesOf β ∧ D.q₀ ∉ primesOf θ :=
  Inputs.not_mem_of_not_dvd D.q₀_not_dvd

theorem rPv_not_mem (p : GP β p₀) : D.rPv p ∉ primesOf β ∧ D.rPv p ∉ primesOf θ :=
  Inputs.not_mem_of_not_dvd (D.rP_not_dvd p.1 p.2)

theorem rTv_not_mem (ℓ : TP θ) : D.rTv ℓ ∉ primesOf β ∧ D.rTv ℓ ∉ primesOf θ :=
  Inputs.not_mem_of_not_dvd (D.rT_not_dvd ℓ.1 ℓ.2)

variable {D}
variable (hI : Inputs β θ p₀)
include hI

theorem pP_mem (o : Option (GP β p₀)) : pP o ∈ primesOf β := by
  cases o with
  | none => exact hI.p₀_mem
  | some p => exact (Finset.mem_sdiff.mp p.2).1

omit hI in
theorem pP_injective : Function.Injective (pP (β := β) (p₀ := p₀)) := by
  rintro (_ | ⟨p, hp⟩) (_ | ⟨p', hp'⟩) h <;> simp only [pP, Option.elim_none, Option.elim_some] at h
  · rfl
  · exact absurd (Finset.mem_singleton.mpr h.symm) (Finset.mem_sdiff.mp hp').2
  · exact absurd (Finset.mem_singleton.mpr h) (Finset.mem_sdiff.mp hp).2
  · subst h; rfl

theorem qT_prime (o : Option (TP θ)) : (D.qT o).Prime ∧ D.qT o ≠ 2 := by
  cases o with
  | none => exact ⟨D.q₀_prime, by show D.q₀ ≠ 2; have := D.q₀_mod_eight; omega⟩
  | some ℓ => exact hI.mem_T ℓ.2

omit hI in
theorem rPv_prime (p : GP β p₀) : (D.rPv p).Prime ∧ D.rPv p ≠ 2 :=
  ⟨D.rP_prime p.1 p.2, by have := D.rP_mod_eight p.1 p.2; simp only [rPv]; omega⟩

omit hI in
theorem rTv_prime (ℓ : TP θ) : (D.rTv ℓ).Prime ∧ D.rTv ℓ ≠ 2 :=
  ⟨D.rT_prime ℓ.1 ℓ.2, by have := D.rT_mod_eight ℓ.1 ℓ.2; simp only [rTv]; omega⟩

theorem fS_prime (k : Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) : (D.fS k).Prime ∧ D.fS k ≠ 2 := by
  rcases k with _ | o | p
  · exact ⟨D.q₀_prime, by have := D.q₀_mod_eight; simp only [fS, Sum.elim_inl]; omega⟩
  · exact hI.mem_P (pP_mem hI o)
  · exact rPv_prime p

theorem f₁_prime (k : (Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) ⊕ TP θ) :
    (D.f₁ k).Prime ∧ D.f₁ k ≠ 2 := by
  rcases k with k | ℓ
  · exact fS_prime hI k
  · exact rTv_prime ℓ

theorem f₂_prime (k : (Option (GP β p₀) ⊕ GP β p₀) ⊕ (Option (TP θ) ⊕ TP θ)) :
    (D.f₂ k).Prime ∧ D.f₂ k ≠ 2 := by
  rcases k with (o | p) | (o | ℓ)
  · exact hI.mem_P (pP_mem hI o)
  · exact rPv_prime p
  · exact qT_prime hI o
  · exact rTv_prime ℓ

/-! ### Distinctness -/


omit hI in
theorem rPv_injective : Function.Injective D.rPv := fun p p' h =>
  Subtype.ext (D.rP_injOn p.2 p'.2 h)

omit hI in
theorem rTv_injective : Function.Injective D.rTv := fun ℓ ℓ' h =>
  Subtype.ext (D.rT_injOn ℓ.2 ℓ'.2 h)

omit hI in
theorem qT_injective : Function.Injective D.qT := by
  rintro (_ | ⟨ℓ, hℓ⟩) (_ | ⟨ℓ', hℓ'⟩) h <;> simp only [qT, Option.elim_none, Option.elim_some] at h
  · rfl
  · exact absurd (h ▸ hℓ') D.q₀_not_mem.2
  · exact absurd (h ▸ hℓ) D.q₀_not_mem.2
  · subst h; rfl

theorem fS_injective : Function.Injective D.fS := by
  refine Function.Injective.sumElim (fun _ _ _ => rfl) ?_ ?_
  · refine Function.Injective.sumElim pP_injective rPv_injective fun o p h => ?_
    exact (D.rPv_not_mem p).1 (h ▸ pP_mem hI o)
  · rintro _ (o | p) h
    · change D.q₀ = pP o at h
      exact D.q₀_not_mem.1 (h ▸ pP_mem hI o)
    · exact D.rP_ne_q₀ p.1 p.2 h.symm

theorem f₁_injective : Function.Injective D.f₁ := by
  refine Function.Injective.sumElim (fS_injective hI) rTv_injective ?_
  rintro (_ | o | p) ℓ h
  · exact D.rT_ne_q₀ ℓ.1 ℓ.2 h.symm
  · change pP o = D.rTv ℓ at h
    exact (D.rTv_not_mem ℓ).1 (h ▸ pP_mem hI o)
  · exact D.rT_ne_rP ℓ.1 ℓ.2 p.1 p.2 h.symm

theorem f₂_injective : Function.Injective D.f₂ := by
  refine Function.Injective.sumElim ?_ ?_ ?_
  · refine Function.Injective.sumElim pP_injective rPv_injective fun o p h => ?_
    exact (D.rPv_not_mem p).1 (h ▸ pP_mem hI o)
  · refine Function.Injective.sumElim qT_injective rTv_injective ?_
    rintro (_ | ℓ) ℓ' h
    · exact D.rT_ne_q₀ ℓ'.1 ℓ'.2 h.symm
    · change ℓ.1 = D.rTv ℓ' at h
      exact (D.rTv_not_mem ℓ').2 (h ▸ ℓ.2)
  · rintro (o | p) (o' | ℓ) h
    · cases o' with
      | none =>
        change pP o = D.q₀ at h
        exact D.q₀_not_mem.1 (h ▸ pP_mem hI o)
      | some ℓ =>
        change pP o = ℓ.1 at h
        exact hI.disjoint (pP_mem hI o) (h ▸ ℓ.2)
    · change pP o = D.rTv ℓ at h
      exact (D.rTv_not_mem ℓ).1 (h ▸ pP_mem hI o)
    · cases o' with
      | none => exact D.rP_ne_q₀ p.1 p.2 h
      | some ℓ =>
        change D.rPv p = ℓ.1 at h
        exact (D.rPv_not_mem p).2 (h ▸ ℓ.2)
    · exact D.rT_ne_rP ℓ.1 ℓ.2 p.1 p.2 h.symm

end Slots

end ZInQ.RouteK
