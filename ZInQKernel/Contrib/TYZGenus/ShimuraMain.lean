import ZInQKernel.Contrib.TYZGenus.ShimuraCusp

/-!
# tyz-cm: main results — the CM leaf from the field-of-definition theorem for `ℚ(X₀(N))`

Task tyz-cm (2026-11-13). Report: `docs/research/tyz-cm.md`; log: `scratch/tyz-cm/log.md`.
Owner of this file: tyz-cm.

* Leaf `CMValueRingClass` (Shimura): the values at Heegner points of discriminant `D` of the
  functions of `ℚ(X₀(N))` that are regular on `ℍ` lie in the ring class field of discriminant `D`.
* `cmFieldOfDefinition_of_cmValue (hV : CMValueRingClass) (hI : X0.EtaModelInvariant) :
  CM.CMFieldOfDefinition ringClassFieldD` — **the main result of tyz-cm**.
* `cmValueRingClass_of_modFn : ShimuraReciprocityModFn → CMValueRingClass` (the trivial-class
  case of Gross's form of the main theorem of CM), so the main result also holds with
  `ShimuraReciprocityModFn` in place of `CMValueRingClass` (`cmFieldOfDefinition_of_modFn_inv`,
  `ShimuraCusp.lean`).
* `shimuraReciprocityPic_of_modFn : ShimuraReciprocityModFn → X0.EtaModelInvariant →
  ShimuraReciprocityPic` (the leaf of `ShimuraRecip.lean`, used by `ShimuraZn.lean`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex

/-- **Leaf CM-VALUE (field of definition of Heegner points of `X₀(N)`; Shimura).** For every
`g ∈ ℚ(X₀(N))` regular on `ℍ` (`IsRatModFn N g`) and every Heegner form `Q` of level `N` and
discriminant `D` (a primitive positive definite `[A, B, C]`, `N ∣ A`, `B² − 4AC = D`), the value
`g(τ_Q)` is algebraic and lies in the ring class field `H_D` of the order of discriminant `D`
(`ringClassFieldD D ⊂ ℚ̄`, through cm-points' embedding `ιC : ℚ̄ → ℂ`).

Content: `τ_Q` is the point `(ℂ/L, L_N/L)` of `X₀(N)`, `L = ⟨1, τ_Q⟩` a proper `O_D`-lattice and
`L_N = ⟨1/N, τ_Q⟩` a lattice for an order `O' ⊇ O_D`; by the main theorem of complex
multiplication every `σ ∈ Aut(ℂ/H_D)` fixes the isomorphism class of the pair (its idele lies in
`K^× Ô_D^×`), and since `X₀(N)_ℚ` is the coarse moduli space of such pairs, `σ` fixes
`g(τ_Q)`; so `g(τ_Q) ∈ H_D`.
Sources (refereed, textbook; numbers UNVERIFIED, from memory): Shimura, *Introduction to the
arithmetic theory of automorphic functions* (1971), Thm. 5.7 (`K(j(𝔞)) = H_O`), Prop. 6.9 /
Thm. 6.23 (`ℚ(X₀(N)) = ℚ(j, j_N)`, rational structure) and §6.8 (values at CM points); Gross,
*Heegner points on `X₀(N)`* (Durham 1983), 1984, §1–§3; Cox, *Primes of the form x² + ny²*,
Thm. 11.1 and §11.C (`j(τ), j(Nτ)` at CM points). No Heegner condition `(f, N) = 1` is needed
(`H_{O'} ⊆ H_D`). This statement is weaker than `ShimuraReciprocityModFn`
(`cmValueRingClass_of_modFn`). -/
def CMValueRingClass : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (D : ℤ) (Q : HeegnerForm N D), ∃ a ∈ ringClassFieldD D, ιC a = g Q.tauH

/-! ## The main result -/

/-- **The CM leaf `CM.CMFieldOfDefinition ringClassFieldD` from the field-of-definition theorem
for `ℚ(X₀(N))` and x0-32's `Γ₀(32)`-invariance leaf.** -/
theorem cmFieldOfDefinition_of_cmValue (hV : CMValueRingClass) (hI : X0.EtaModelInvariant) :
    CMFieldOfDefinition ringClassFieldD := by
  intro D Q
  obtain ⟨a, haH, ha⟩ := hV 32 _ (isRatModFn_xC_of hI etaCuspGrowth xQExpRational) D Q
  obtain ⟨b, hbH, hb⟩ := hV 32 _ (isRatModFn_yC_of hI etaCuspGrowth yQExpRational) D Q
  rw [heegnerPt_of_alg Q ha hb]
  split_ifs with h
  · rw [mem_ptsOver_iff]
    exact ⟨haH, hbH⟩
  · exact AddSubgroup.zero_mem _

/-- **The TYZ package leaf `Package.CMFieldOfDefinitionTYZ`** from the same two leaves. -/
theorem cmFieldTYZ_of_cmValue (hV : CMValueRingClass) (hI : X0.EtaModelInvariant) :
    ZInQ.Contrib.TYZGenus.Package.CMFieldOfDefinitionTYZ :=
  RingClassBridge.cmFieldTYZ_of_ringClassD (cmFieldOfDefinition_of_cmValue hV hI)

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **Reading A of TYZ Theorem 3.5 with the CM field-of-definition leaf discharged** by
`CMValueRingClass` and `X0.EtaModelInvariant` (ring-class's
`tyzThm35ReadingA_of_cmLeaves_ringClassD`; `TYZSigmaFixesZn` stays a hypothesis: task
cm-numeric). -/
theorem tyzThm35ReadingA_of_cmValue (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hV : CMValueRingClass) (hI : X0.EtaModelInvariant)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29
    (cmFieldOfDefinition_of_cmValue hV hI) hs h318 hG

/-! ## `CMValueRingClass` from Gross's form of the main theorem of CM -/

section General
variable {m f : ℕ} [NeZero m] [NeZero f]

/-- **`κ(O)·⟨1/N, τ_Q⟩ ⊆ ⟨1/N, τ_Q⟩`** for a Heegner form of level `N` (uses `N ∣ A`). -/
theorem kappa_mul_mem_latN_gen (hsq : Squarefree m) {D : ℤ} (hD : D = discOf m f) {N : ℕ}
    (Q : HeegnerForm N D) {o : QNeg m} (ho : o ∈ (conductorOrder (QNeg m) f).toSubalgebra) :
    ∀ x ∈ Q.latN, kappa m o * x ∈ Q.latN := by
  obtain ⟨u, v, huv⟩ := kappa_order hsq hD Q ho
  obtain ⟨A', hA'⟩ := Q.N_dvd
  have hN0 : (N : ℂ) ≠ 0 := by
    have hA := Q.A_pos
    intro h
    have : (N : ℤ) = 0 := by exact_mod_cast h
    rw [this, zero_mul] at hA'
    omega
  have hA'C : (Q.A : ℂ) = N * A' := by exact_mod_cast hA'
  have h1 : kappa m o * (1 / (N : ℂ)) ∈ Q.latN := by
    rw [huv, HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨u, v * A', ?_⟩
    simp only [zsmul_eq_mul]
    rw [hA'C]
    push_cast
    field_simp
  have hτ : kappa m o * Q.tau ∈ Q.latN := by
    have hq := heegner_tau_quad Q
    rw [HeegnerForm.latN]
    refine Submodule.mem_span_pair.2 ⟨-(N * v * Q.C), u - v * Q.B, ?_⟩
    rw [huv]
    simp only [zsmul_eq_mul]
    push_cast
    field_simp
    linear_combination (-(v : ℂ)) * hq
  intro x hx
  rw [HeegnerForm.latN] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact h1
    · exact hτ
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
  | smul r z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hz

end General

/-- **`CMValueRingClass` from `ShimuraReciprocityModFn`** (the trivial class `J = 𝓞_K`). -/
theorem cmValueRingClass_of_modFn (hS : ShimuraReciprocityModFn) : CMValueRingClass := by
  intro N g hg D Q
  have hDneg := Q.D_neg
  have h4 := disc_mod_four Q
  obtain ⟨b, hb, hsq⟩ := sqfPart_spec D.natAbs
  have hspec := condD_spec h4 hDneg
  have hDa : (D.natAbs : ℤ) = -D := by omega
  have hm0 : sqfPart D.natAbs ≠ 0 := fun h => by rw [h, mul_zero] at hb; omega
  have hf0 : condD D ≠ 0 := by
    intro h; rw [h] at hspec; split_ifs at hspec <;> simp at hspec <;> omega
  have : NeZero (sqfPart D.natAbs) := ⟨hm0⟩
  have : NeZero (condD D) := ⟨hf0⟩
  set m := sqfPart D.natAbs with hm
  set f := condD D with hf
  have hD : D = discOf m f := by
    unfold discOf
    split_ifs at hspec ⊢ with h3
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
    · have := congrArg (fun k : ℕ => (k : ℤ)) hspec
      rw [hDa] at this; push_cast at this; linarith
  have hK : ringClassFieldD D = ringClassFieldBar m f := by rw [ringClassFieldD, if_pos hDneg]
  obtain ⟨e, he⟩ := exists_normalized_embed_any m
  set J1 : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus := 1 with hJ1
  have hone : (J1 : Ideal (𝓞 (QNeg m))) = ⊤ := by
    rw [hJ1, OneMemClass.coe_one, Ideal.one_eq_top]
  have hmul : LinearMap.mulLeft ℤ (1 : ℂ) = LinearMap.id := by ext; simp
  have hL : idealLat m f J1 * Q.lat = Q.lat.map (LinearMap.mulLeft ℤ 1) := by
    rw [hone, hmul, Submodule.map_id]
    exact idealLat_top_mul (fun o ho => kappa_mul_mem_lat hsq hD Q ho)
  have hLN : idealLat m f J1 * Q.latN = Q.latN.map (LinearMap.mulLeft ℤ 1) := by
    rw [hone, hmul, Submodule.map_id]
    exact idealLat_top_mul (fun o ho => kappa_mul_mem_latN_gen hsq hD Q ho)
  -- the action hypothesis for `ρ` fixing `H`
  have hρe : ∀ ρ ∈ (ringClassFieldD D).fixingSubgroup,
      ∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J1) x) := by
    intro ρ hρ x
    rw [hJ1, map_one, map_one, AlgEquiv.one_apply]
    have hx : e x ∈ ringClassFieldD D := by
      rw [hK, ← ringClassFieldBar_eq_map m f e]
      exact ⟨x, x.2, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ _ hx
  obtain ⟨a, -, ha, -, -⟩ := hS N g hg m f hsq e he J1 1 (hρe 1 (Subgroup.one_mem _)) D hD Q Q 1
    hL hLN
  refine ⟨a, ?_, ha⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (ringClassFieldD D)]
  intro ρ
  obtain ⟨a1, a2, h1, h2, h12⟩ := hS N g hg m f hsq e he J1 ρ (hρe ρ.1 ρ.2) D hD Q Q 1 hL hLN
  have e1 : a1 = a := ιCA.injective (h1.trans ha.symm)
  have e2 : a2 = a := ιCA.injective (h2.trans ha.symm)
  rw [← e1]
  conv_rhs => rw [e1, ← e2]
  exact h12

/-- **`ShimuraReciprocityPic` from `ShimuraReciprocityModFn` and x0-32's invariance leaf.** -/
theorem shimuraReciprocityPic_of_modFn (hS : ShimuraReciprocityModFn)
    (hI : X0.EtaModelInvariant) : ShimuraReciprocityPic :=
  shimuraReciprocityPic_of hS (isRatModFn_xC_of hI etaCuspGrowth xQExpRational)
    (isRatModFn_yC_of hI etaCuspGrowth yQExpRational)

end ZInQ.Contrib.TYZGenus.Shimura
