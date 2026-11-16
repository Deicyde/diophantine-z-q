import ZInQKernel.Contrib.OneProof.H.TailZ22

/-!
# gt-grcount: González–Rotger's count on `X₆` without the bundled model

`ShimuraSplit.GonzalezRotgerCountX6Ab` (field `gonzalezRotgerCountX6Ab` of the open research bundle,
`ZInQKernel/Contrib/OneProof/H/TailZ17.lean`) says: *some* witness `(Y, Φ, X, Ψ, fY)` of the moduli clause lists
`R1fpPropsAb`, `X6Props` (the canonical `Y₃`, `X₆ = X₀(6,1)` with the moduli bijection `Ψ`) has exactly
`2^{inertCount6 k} · #Pic(R)` points with CM by `R`. The integrator ruled it a composite: the existential bundles
the canonical models with González–Rotger's count.

This file separates the two.

* `GonzalezRotgerProp56X6` (new LEAF, printed form): González–Rotger Prop. 5.6 at `(D, N) = (6, 1)` on `X₀(6,1)`,
  stated for **every** witness of the moduli description (no existence claim).
* The model comes from the open LEAF `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (González–Rotger Thm 5.12 on the
  canonical `X₆`), already a field of the same bundle; the theorem only uses its witness.
* `gonzalezRotgerCountX6Ab_of_printed : GonzalezRotgerProp56X6 → GonzalezRotgerX6Ab → GonzalezRotgerCountX6Ab`.

The count on points depends on the witness only through the bijection `Ψ` (`card_points_eq`), so the new leaf is
implied outright by the kernel's model-free count `LeafQM.AV.R5fpCount` (`prop56X6_of_r5fpCount`), and is equivalent
to it given any witness (`r5fpCount_of_prop56X6`). The chain's only consumer of the field is
`ShimuraSplit.r5fpCount_of_points` (`TailZ9`, field `r5count`), i.e. the chain uses only `R5fpCount`.

§2 splits the count itself into its two published ingredients, with the arithmetic glue proved:
* `EichlerOptEmbCount6` (LEAF, pure algebra over Mathlib's `ℍ[ℚ, 2, 0, -3]` and the kernel's maximal order
  `LeafQM.O`): Eichler's count of `𝒪^×`-classes of optimal embeddings, `h(R) · ∏_{p ∣ 6} (1 − (k/p))`;
* `CMPointsOptEmb6` (consequence of Shimura 1967 / González–Rotger 2006 §5): CM points by `R` on `X₀(6,1)`, i.e.
  classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R`, are in bijection with those classes;
* `r5fpCount_of_eichler : EichlerOptEmbCount6 → CMPointsOptEmb6 → R5fpCount`, through
  `eichlerFactor6_eq : ∏_{p ∣ 6} (1 − (k/p)) ≠ 0 → ∏_{p ∣ 6} (1 − (k/p)) = 2^{inertCount6 k}` (the only finite
  computation in the count: the local factors at `2` and `3`).

No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

noncomputable section

namespace GRCountX6

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-! ## 1. The printed count, model-free, and the field from it -/

/-- **LEAF (González–Rotger, J. Math. Soc. Japan 58 (2006), Prop. 5.6, p. 943 (read by the locator audit), at
`(D, N) = (6, 1)`, on `X₀(6,1)`; printed form, without the existence of the model).**

*Published statement*: for an order `R` of conductor prime to `DN` in an imaginary quadratic field `k` that embeds
optimally in the Eichler order of level `N` of the quaternion algebra of discriminant `D`, the number of CM points
by `R` on `X₀(D,N)` is `#CM(R) = 2^{#{p ∣ D(R)N(R)}} h(R)`. At `D = 6`, `N = 1`, `D(R)` is the product of the primes
`p ∣ 6` inert in `k`, so `#CM(R) = 2^{inertCount6 k} · #Pic(R)`.

*Lean form*: for every witness `(Y, Φ, X, Ψ, fY)` of the moduli description of `X₀(6,1)` on abelian schemes
(`R1fpPropsAb`, `X6Props`: the fine `Y₃`, the coarse `X₆` proper smooth of relative dimension one over `ℚ` with
`Ψ : X(ℚ̄) ≃` QM pairs over `ℚ̄` up to isomorphism), and every such `R` occurring as some `End_𝒪(A)`, the points
`x ∈ X(ℚ̄)` whose QM pair has `End_𝒪(A) ≅ R` (the CM points by `R`) number `2^{inertCount6 k} · #Pic(R)`.

*Why faithful, not stronger*: it is `ShimuraSplit.GonzalezRotgerCountX6Ab` with the existential over the witness
replaced by a universal: it asserts nothing about the existence of the model, only the printed count on it. It
follows outright from the kernel's model-free form `LeafQM.AV.R5fpCount` (`prop56X6_of_r5fpCount`), the count of
CM points read through the moduli interpretation of `X₀(6,1)`. The occurrence hypothesis ("`R` occurs as some
`End_𝒪(A)`") is the moduli form of the printed optimal-embedding hypothesis (Shimura 1967), and excludes the orders
where some `p ∣ 6` splits; conductor prime to 6 then follows. Given any witness, the statement is equivalent to
`R5fpCount` (`prop56X6_of_r5fpCount`, `r5fpCount_of_prop56X6`); it carries no information about the model, which
comes from the field `gonzalezRotgerX6Ab`. The passage from the printed points over `ℂ` to classes of
polarization-free QM pairs over `ℚ̄` (the type-`μ` polarization lemma, then descent of CM pairs) is standard glue.
The statement review could not check Prop. 5.6's wording against the paper (the locator audit read it): a reader
with the paper should confirm that `D(R)` is the product of the `p ∣ D` with `(R/p) = −1`. Statement review 2026-11-14 (two lenses, AI, from memory): faithful. -/
def GonzalezRotgerProp56X6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
        (∃ P : QMPair Qbar, Nonempty (com P.q ≃+* R)) →
          Nat.card {x : fieldPt Qbar ⟶ X //
              ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R)} =
            2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

/-- The CM points by `R` on a coarse witness are counted through the moduli bijection `Ψ`. -/
theorem card_points_eq {X : Over (Spec (CommRingCat.of ℚ))}
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) {k : Type} [Field k] (R : Subring k) :
    Nat.card {x : fieldPt Qbar ⟶ X //
        ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R)} =
      Nat.card {c : Quotient (pairSetoid Qbar) //
        ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} :=
  Nat.card_congr (Equiv.subtypeEquiv Ψ (fun x => by
    constructor
    · rintro ⟨P, hP, hR'⟩; exact ⟨P, hP.symm, hR'⟩
    · rintro ⟨P, hP, hR'⟩; exact ⟨P, hP.symm, hR'⟩))

/-- The new leaf is implied by the kernel's model-free count (so it is never stronger than `R5fpCount`). -/
theorem prop56X6_of_r5fpCount (h : R5fpCount) : GonzalezRotgerProp56X6 := by
  intro Y Φ X Ψ fY _ _ k _ _ _ hk R hR hc ho
  rw [card_points_eq Ψ R]
  exact h k hk R hR hc ho

/-- Conversely, the new leaf and any witness (here González–Rotger Thm 5.12's) give the model-free count. -/
theorem r5fpCount_of_prop56X6 (h : GonzalezRotgerProp56X6)
    (hX : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab) : R5fpCount := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := hX
  intro k _ _ _ hk R hR hc ho
  rw [← card_points_eq Ψ R]
  exact h Y Φ X Ψ fY h1 h6 k hk R hR hc ho

/-- **The field from the printed count and the model of the open LEAF `GonzalezRotgerX6Ab`.** -/
theorem gonzalezRotgerCountX6Ab_of_printed (h : GonzalezRotgerProp56X6)
    (hX : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab) : ShimuraSplit.GonzalezRotgerCountX6Ab := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := hX
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, h Y Φ X Ψ fY h1 h6⟩

/-- The same with the model of the open LEAF `DeligneComponentsX6PrintedAb` (Deligne's `π₀` on the canonical `X₆`). -/
theorem gonzalezRotgerCountX6Ab_of_printed' (h : GonzalezRotgerProp56X6)
    (hX : ShimuraGlue.DeligneComponentsX6PrintedAb) : ShimuraSplit.GonzalezRotgerCountX6Ab := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := hX
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, h Y Φ X Ψ fY h1 h6⟩

/-- The field from the kernel's model-free count `R5fpCount` and the model of `GonzalezRotgerX6Ab`. -/
theorem gonzalezRotgerCountX6Ab_of_r5fpCount (h : R5fpCount)
    (hX : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab) : ShimuraSplit.GonzalezRotgerCountX6Ab :=
  gonzalezRotgerCountX6Ab_of_printed (prop56X6_of_r5fpCount h) hX

/-! ## 2. The count from Eichler's optimal-embedding theorem and the CM-point correspondence -/

section Eichler

/-- Optimal embeddings of the order `R ⊆ k` in the maximal order `𝒪 ⊂ B = (2, −3 | ℚ)`: `ℚ`-algebra maps
`Φ : k → B` with `Φ⁻¹(𝒪) = R` (the convention of the kernel's `QMCentralizerCMC`, `TailU`). -/
def OptEmb (k : Type) [Field k] [NumberField k] (R : Subring k) : Type :=
  {Φ : k →ₐ[ℚ] LeafQM.B // LeafQM.O.comap Φ.toRingHom = R}

/-- Conjugacy by `𝒪^×`: `Ψ = u Φ u⁻¹` for a unit `u` of `𝒪`. -/
def ConjRel {k : Type} [Field k] [NumberField k] (R : Subring k) (Φ Ψ : OptEmb k R) : Prop :=
  ∃ u : (↥LeafQM.O)ˣ, ∀ x : k,
    Ψ.1 x = ((u : LeafQM.O) : LeafQM.B) * Φ.1 x * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B)

theorem unit_mul_inv (u : (↥LeafQM.O)ˣ) :
    ((u : LeafQM.O) : LeafQM.B) * (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B) = 1 := by
  rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]

theorem unit_inv_mul (u : (↥LeafQM.O)ˣ) :
    (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B) * ((u : LeafQM.O) : LeafQM.B) = 1 := by
  rw [← Subring.coe_mul, Units.inv_mul, Subring.coe_one]

/-- Sanity: `ConjRel` is an equivalence relation (so `Quot (ConjRel R)` is the set of `𝒪^×`-conjugacy classes). -/
theorem conjRel_equivalence {k : Type} [Field k] [NumberField k] (R : Subring k) :
    Equivalence (ConjRel R) where
  refl Φ := ⟨1, fun x => by simp⟩
  symm := by
    rintro Φ Ψ ⟨u, hu⟩
    refine ⟨u⁻¹, fun x => ?_⟩
    rw [hu x, inv_inv]
    calc Φ.1 x = (((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B) * ((u : LeafQM.O) : LeafQM.B) * Φ.1 x *
          ((((u⁻¹ : (↥LeafQM.O)ˣ) : LeafQM.O) : LeafQM.B) * ((u : LeafQM.O) : LeafQM.B)) := by
          rw [unit_inv_mul, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  trans := by
    rintro Φ Ψ Χ ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨v * u, fun x => ?_⟩
    rw [hv x, hu x, mul_inv_rev]
    simp only [Units.val_mul, Subring.coe_mul, mul_assoc]

/-- The norm `−1` unit `1 + i ∈ 𝒪` (inverse `−1 + i`): the input that identifies `𝒪^1`-classes of normalized
optimal embeddings with `𝒪^×`-classes of all optimal embeddings in `CMPointsOptEmb6`. -/
theorem one_add_i_mem_units :
    LeafQM.ofInt ![1, 1, 0, 0] * LeafQM.ofInt ![-1, 1, 0, 0] = 1 ∧
      LeafQM.ofInt ![-1, 1, 0, 0] * LeafQM.ofInt ![1, 1, 0, 0] = 1 ∧
      LeafQM.ofInt ![1, 1, 0, 0] * star (LeafQM.ofInt ![1, 1, 0, 0]) = -1 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp [LeafQM.ofInt] <;> norm_num

open Classical in
/-- The local optimal-embedding number at `p ∣ 6` of the maximal order of `k` in the maximal order of the local
division algebra: `1 − (k/p)`, i.e. `2` if `p` is inert in `k` (`p𝒪_k` prime), `1` if `p` ramifies
(`p𝒪_k = 𝔓²`), `0` if `p` splits. For an order of conductor prime to `p` this is Eichler's `1 − (R/p)`. -/
def eichlerLocal (k : Type) [Field k] [NumberField k] (p : NumberField.RingOfIntegers k) : ℕ :=
  if (Ideal.span {p}).IsPrime then 2
  else if ∃ P : Ideal (NumberField.RingOfIntegers k), P.IsPrime ∧ Ideal.span {p} = P ^ 2 then 1 else 0

/-- `∏_{p ∣ 6} (1 − (k/p))`. -/
def eichlerFactor6 (k : Type) [Field k] [NumberField k] : ℕ :=
  eichlerLocal k 2 * eichlerLocal k 3

/-- **The finite computation in the count**: when no `p ∣ 6` splits (`∏_{p ∣ 6} (1 − (k/p)) ≠ 0`), the local
factors multiply to `2^{inertCount6 k}`. -/
theorem eichlerFactor6_eq {k : Type} [Field k] [NumberField k] (h : eichlerFactor6 k ≠ 0) :
    eichlerFactor6 k = 2 ^ inertCount6 k := by
  unfold eichlerFactor6 eichlerLocal inertCount6 at *
  split_ifs at * <;> simp_all

/-- **LEAF (Eichler's theorem on optimal embeddings, for the maximal order of the quaternion algebra of
discriminant 6).** Eichler, J. reine angew. Math. 195 (1955); Vignéras, *Arithmétique des algèbres de
quaternions*, LNM 800 (1980), Ch. III Thm 5.11 and Cor. 5.12; Voight, *Quaternion Algebras* (2021), Thm 30.7.3
(theorem numbers UNVERIFIED). For an order `R` of conductor prime to `6` in an imaginary quadratic field `k`, the
optimal embeddings `R ↪ 𝒪` fall into finitely many `𝒪^×`-conjugacy classes, and their number is
`h(R) · ∏_{p ∣ 6} (1 − (R/p))` (the class number of the indefinite algebra `B` is one, so the sum over the left
ideal classes of `𝒪` has one term). Pure algebra, over Mathlib's `QuaternionAlgebra ℚ 2 0 (-3)`, the kernel's
maximal order `LeafQM.O`, Mathlib's `CommRing.Pic` and prime ideals of `𝓞 k`. -/
def EichlerOptEmbCount6 : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Finite (Quot (ConjRel R)) ∧
        Nat.card (Quot (ConjRel R)) = Nat.card (CommRing.Pic R) * eichlerFactor6 k

/-- **Consequence (CM points by `R` on `X₀(6,1)` ↔ optimal embeddings).** Shimura, Ann. of Math. 85 (1967)
§§1-3; Jordan, Harvard thesis (1981) §3; González–Rotger, J. Math. Soc. Japan 58 (2006) §5 (locators
UNVERIFIED): the CM points by `R` on `𝒪^1∖ℍ` correspond bijectively to the `𝒪^1`-conjugacy classes of normalized
optimal embeddings `R ↪ 𝒪` (`End_𝒪(A_τ) ≅ Φ_τ⁻¹(𝒪)`). Since `𝒪` has a unit of norm `−1` (`one_add_i_mem_units`)
and an element normalizing `Φ(k)` non-trivially has negative norm in the indefinite `B`, these classes are the
`𝒪^×`-classes of all optimal embeddings; and isomorphism classes of CM QM pairs over `ℚ̄` and over `ℂ` agree. Lean
form: a bijection between the isomorphism classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R` and `Quot (ConjRel R)`. -/
def CMPointsOptEmb6 : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Nonempty ({c : Quotient (pairSetoid Qbar) //
          ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ≃ Quot (ConjRel R))

/-- **The model-free count from Eichler and the CM-point correspondence** (glue: occurrence makes the class set
nonempty, finiteness makes its cardinality positive, so no `p ∣ 6` splits and `eichlerFactor6_eq` applies). -/
theorem r5fpCount_of_eichler (hE : EichlerOptEmbCount6) (hM : CMPointsOptEmb6) : R5fpCount := by
  intro k _ _ _ hk R hR hc ho
  obtain ⟨e⟩ := hM k hk R hR hc
  obtain ⟨hfin, hcard⟩ := hE k hk R hR hc
  obtain ⟨P, hP⟩ := ho
  have hpos : Nat.card (Quot (ConjRel R)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨e ⟨Quotient.mk _ P, P, rfl, hP⟩⟩, hfin⟩
  have hf : eichlerFactor6 k ≠ 0 := by
    intro h0
    rw [hcard, h0, mul_zero] at hpos
    exact hpos rfl
  rw [Nat.card_congr e, hcard, eichlerFactor6_eq hf, mul_comm]

/-- **The field from Eichler, the CM-point correspondence and the model of `GonzalezRotgerX6Ab`.** -/
theorem gonzalezRotgerCountX6Ab_of_eichler (hE : EichlerOptEmbCount6) (hM : CMPointsOptEmb6)
    (hX : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab) : ShimuraSplit.GonzalezRotgerCountX6Ab :=
  gonzalezRotgerCountX6Ab_of_r5fpCount (r5fpCount_of_eichler hE hM) hX

end Eichler

end GRCountX6
