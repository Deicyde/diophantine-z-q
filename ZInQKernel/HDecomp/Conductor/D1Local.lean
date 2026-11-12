import ZInQKernel.HDecomp.Conductor.Breaks

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-d1-local/Local.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-! # glue-d1-local: the local form of D1's degree bound `e ≤ a!`

Glazer bounds only the local degree `[F:ℚ_p] ≤ a` and uses the Galois closure `F̃` of `F/ℚ_p`.
For a finite Galois `L/ℚ` and a prime `P` of `𝓞 L` over `p`, the local Galois group
`Gal(L_P/ℚ_p)` is the decomposition group `D_P = Stab(P) ≤ Gal(L/ℚ)`, and for an intermediate
field `K` with `w = P ∩ 𝓞 K` the subgroup `Gal(L_P/K_w)` is `D_P ∩ Gal(L/K)`
(Serre, *Corps locaux*, II §3, UNVERIFIED locator). So "`L_P` is the Galois closure of
`K_w/ℚ_p`" is the group condition that `D_P ∩ Gal(L/K)` has trivial normal core in `D_P`, and
`[K_w:ℚ_p]` is the index `[D_P : D_P ∩ Gal(L/K)]`. Everything below is stated over Mathlib's
`Gal(L/ℚ)`, `MulAction.stabilizer`, `Ideal.inertia` and `Ideal.ramificationIdx`; no completion
is needed. -/

namespace GlueD1Local

open NumberField GlueConductor
open scoped Pointwise

/-- A subgroup with trivial normal core: the group embeds in the permutations of the cosets,
so `|D| ≤ [D:H]!`. -/
theorem card_le_factorial_index_of_normalCore_eq_bot {D : Type*} [Group D] [Finite D]
    (H : Subgroup D) (hcore : H.normalCore = ⊥) : Nat.card D ≤ H.index.factorial := by
  have h := H.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot] at h
  exact Nat.le_of_dvd (Nat.factorial_pos _) h

/-- Without the core hypothesis: `|D / core_D(H)| ≤ [D:H]!`. -/
theorem index_normalCore_le_factorial_index {D : Type*} [Group D] [Finite D]
    (H : Subgroup D) : H.normalCore.index ≤ H.index.factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) H.index_normalCore_dvd_factorial_index

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

/-- The decomposition group `D_P = Stab(P) ≤ Gal(L/ℚ)`. -/
abbrev decompGroup (P : Ideal (𝓞 L)) : Subgroup Gal(L/ℚ) := MulAction.stabilizer Gal(L/ℚ) P

/-- `Gal(L/K) ∩ D_P`, as a subgroup of `D_P` (the local group `Gal(L_P/K_w)`). -/
abbrev localSub (K : IntermediateField ℚ L) (P : Ideal (𝓞 L)) : Subgroup (decompGroup L P) :=
  K.fixingSubgroup.subgroupOf (decompGroup L P)

/-- `e(P|p) = |I_P| ≤ |D_P|`. -/
theorem ramificationIdx_le_card_decompGroup (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ ≤ Nat.card (decompGroup L P) := by
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (Ideal.span {(p : ℤ)}) P]
  exact Subgroup.card_le_of_le (Ideal.inertia_le_stabilizer P)

/-- **The local degree bound (decomposition-group form).** Let `L/ℚ` be finite Galois, `P` a
prime of `𝓞 L` over `p`, and `K` an intermediate field such that `D_P ∩ Gal(L/K)` has trivial
normal core in `D_P` (i.e. `L_P` is the Galois closure of `K_w` over `ℚ_p`) and index
`[D_P : D_P ∩ Gal(L/K)] ≤ a` (i.e. `[K_w : ℚ_p] ≤ a`). Then `e(P|p) ≤ |D_P| ≤ a!`. -/
theorem ramificationIdx_le_factorial_local (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (hdeg : (localSub L K P).index ≤ a) :
    P.ramificationIdx ℤ ≤ a.factorial :=
  (ramificationIdx_le_card_decompGroup L p P).trans
    ((card_le_factorial_index_of_normalCore_eq_bot _ hcore).trans (Nat.factorial_le hdeg))

/-- **D1, local form.** The hypothesis `e ≤ a!` of `D1_genuine` is replaced by the local data:
`L_P` is the Galois closure of `K_w/ℚ_p` and `[K_w:ℚ_p] ≤ a`. -/
theorem D1_local (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : (localSub L K P).index ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine hH hS L p P a ha (ramificationIdx_le_factorial_local L p P K hcore a hdeg) b hb

/-- `|D_P| = e(P|p)·f(P|p)` (Mathlib's `Ideal.card_stabilizer_eq`). -/
theorem card_decompGroup (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (decompGroup L P) = P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  rw [Ideal.card_stabilizer_eq (G := Gal(L/ℚ)) (Ideal.span {(p : ℤ)}) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]

/-- `D_P ∩ Gal(L/K)` is the stabilizer of `P` in `Gal(L/K)`. -/
def localSubEquiv (K : IntermediateField ℚ L) (P : Ideal (𝓞 L)) :
    localSub L K P ≃ MulAction.stabilizer K.fixingSubgroup P where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The local degree as an index.** For `w = P ∩ 𝓞 K`,
`[D_P : D_P ∩ Gal(L/K)] = e(w|p)·f(w|p)` (the local degree `[K_w : ℚ_p]`). -/
theorem index_localSub (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) :
    (localSub L K P).index =
      (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ := by
  have hD := card_decompGroup L p P
  have : IsGaloisGroup K.fixingSubgroup K L :=
    IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L K
  have : IsGaloisGroup K.fixingSubgroup (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ (𝓞 K) (𝓞 L) K L
  have hH : Nat.card (MulAction.stabilizer K.fixingSubgroup P) =
      P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) := by
    have h1 := Ideal.card_stabilizer_eq (G := K.fixingSubgroup) (P.under (𝓞 K)) P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P K.fixingSubgroup,
      Ideal.inertiaDegIn_eq_inertiaDeg (P.under (𝓞 K)) P K.fixingSubgroup] at h1
    exact h1
  have hS : Nat.card (localSub L K P) = P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) := by
    rw [← hH]; exact Nat.card_congr (localSubEquiv L K P)
  have he := Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 K)) P
  have hf := Ideal.inertiaDeg_tower (R := ℤ) (P.under (𝓞 K)) P
  have hmul := (localSub L K P).card_mul_index
  rw [hS, hD, he, hf] at hmul
  have hpos : 0 < P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) := by
    rw [← hS]; exact Nat.card_pos
  have : P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) * (localSub L K P).index =
      P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) *
        ((P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ) := by
    rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

/-- **D1, local form, with the local degree as `e(w|p)·f(w|p)`.** -/
theorem D1_local' (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hcore : (localSub L K P).normalCore = ⊥)
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_local L hH hS p P K hcore a ha ((index_localSub L p P K).trans_le hdeg) b hb

/-! ## The Krasner-type situation: `K` has a single prime over `p`

If `L` is the Galois closure of `K` over `ℚ` (`core_G(Gal(L/K)) = ⊥`) and `K` has only one prime
`w` over `p`, then the core hypothesis of `D1_local'` holds: `L_P` is then the Galois closure of
`K_w`. Krasner's lemma gives such a `K` for any finite `F/ℚ_p` (`K = ℚ(α)` with the minimal
polynomial of `α` close to that of a generator of `F`; then `K_w ≅ F` and `[K:ℚ] = [F:ℚ_p]`). -/

/-- Group theory: if `G = H·D` and `core_G(H) = ⊥`, then `core_D(H ∩ D) = ⊥`. -/
theorem normalCore_subgroupOf_eq_bot {G : Type*} [Group G] (D H : Subgroup G)
    (hHD : ∀ g : G, ∃ h ∈ H, ∃ d ∈ D, g = h * d) (hcore : H.normalCore = ⊥) :
    (H.subgroupOf D).normalCore = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx : ∀ b : D, b * x * b⁻¹ ∈ H.subgroupOf D := hx
  have hxG : (x : G) ∈ H.normalCore := by
    show ∀ g : G, g * x * g⁻¹ ∈ H
    intro g
    obtain ⟨h, hh, d, hd, rfl⟩ := hHD g
    have h1 := hx ⟨d, hd⟩
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : h * (d * x * d⁻¹) * h⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hh (by simpa using h1)) (H.inv_mem hh)
    simpa [mul_assoc] using h2
  rw [hcore, Subgroup.mem_bot] at hxG
  exact (Subgroup.mem_bot).mpr (Subtype.ext hxG)

/-- If `K` has a single prime `w` over `p`, then `Gal(L/ℚ) = Gal(L/K)·D_P`. -/
theorem fixingSubgroup_mul_decompGroup (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K)) (g : Gal(L/ℚ)) :
    ∃ h ∈ K.fixingSubgroup, ∃ d ∈ decompGroup L P, g = h * d := by
  have : IsGaloisGroup K.fixingSubgroup K L :=
    IsGaloisGroup.intermediateField Gal(L/ℚ) ℚ L K
  have : IsGaloisGroup K.fixingSubgroup (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ (𝓞 K) (𝓞 L) K L
  have hQ : (g • P).IsPrime := Ideal.IsPrime.smul g
  have hv : (g • P).under (𝓞 K) = P.under (𝓞 K) := by
    apply hunique _ (Ideal.IsPrime.under _ _)
    refine ⟨?_⟩
    have h1 : (g • P).under ℤ = Ideal.span {(p : ℤ)} := by
      rw [Ideal.under_smul, ← Ideal.over_def P (Ideal.span {(p : ℤ)})]
    rw [← h1, Ideal.under_under]
  obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) K.fixingSubgroup
    P (g • P) hv.symm
  refine ⟨h, h.2, h⁻¹ * g, ?_, by simp⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, hh]
  exact inv_smul_smul (h : Gal(L/ℚ)) P

/-- **The Krasner-type form.** If `L` is the Galois closure of `K` (`core_G(Gal(L/K)) = ⊥`), `K`
has a single prime `w` over `p`, and `e(w|p)·f(w|p) ≤ a`, then `e(P|p) ≤ a!`. -/
theorem ramificationIdx_le_factorial_of_unique (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : K.fixingSubgroup.normalCore = ⊥)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a) :
    P.ramificationIdx ℤ ≤ a.factorial :=
  ramificationIdx_le_factorial_local L p P K
    (normalCore_subgroupOf_eq_bot _ _ (fixingSubgroup_mul_decompGroup L p P K hunique) hclos)
    a ((index_localSub L p P K).trans_le hdeg)

/-- **D1 in the Krasner-type situation.** -/
theorem D1_krasner (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : K.fixingSubgroup.normalCore = ⊥)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_genuine hH hS L p P a ha (ramificationIdx_le_factorial_of_unique L p P K hclos hunique a hdeg)
    b hb

/-- Galois correspondence: if `L` is the normal closure of `K` over `ℚ`, then
`core_G(Gal(L/K)) = ⊥`. -/
theorem normalCore_fixingSubgroup_eq_bot (K : IntermediateField ℚ L)
    (h : IntermediateField.normalClosure ℚ K L = ⊤) : K.fixingSubgroup.normalCore = ⊥ := by
  set N := K.fixingSubgroup.normalCore
  have : N.Normal := Subgroup.normalCore_normal _
  have hK : K ≤ IntermediateField.fixedField N := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact (IntermediateField.mem_fixingSubgroup_iff K σ).mp
      (Subgroup.normalCore_le _ hσ) x hx
  have htop : IntermediateField.fixedField N = ⊤ := by
    rw [eq_top_iff, ← h]
    exact (IntermediateField.normalClosure_le_iff_of_normal).mpr hK
  rw [← IntermediateField.fixingSubgroup_fixedField N, htop, IntermediateField.fixingSubgroup_top]

/-- `D1_krasner` with "`L` is the normal closure of `K`" as a field-theoretic hypothesis. -/
theorem D1_krasner' (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (K : IntermediateField ℚ L) (hclos : IntermediateField.normalClosure ℚ K L = ⊤)
    (hunique : ∀ v : Ideal (𝓞 K), v.IsPrime → v.LiesOver (Ideal.span {(p : ℤ)}) →
      v = P.under (𝓞 K))
    (a : ℕ) (ha : 1 ≤ a)
    (hdeg : (P.under (𝓞 K)).ramificationIdx ℤ * (P.under (𝓞 K)).inertiaDeg ℤ ≤ a)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 :=
  D1_krasner L hH hS p P K (normalCore_fixingSubgroup_eq_bot L K hclos) hunique a ha hdeg b hb

end GlueD1Local

