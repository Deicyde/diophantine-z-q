import ZInQKernel.Contrib.G15.Transport

/-!
# G15: Glazer's D1 bound stated at the completions

`GlueD1Local.D1_local` takes its local hypotheses in decomposition-group form (`D_P ∩ Gal(L/K)`
has trivial normal core in `D_P`, index `≤ a`). With the transport of `Transport.lean` these are
the completion statements "`L_w` is the Galois closure of `K_u/ℚ_v`" and "`[K_u : ℚ_v] ≤ a`".
With T20/T21 discharged by `ZInQ.Contrib.Different` the bound is closed: no hypotheses besides
the local ones.

No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain
open scoped AdicCompletionExtension

noncomputable section

namespace ZInQ.Contrib.G15

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
/-- Every finite place `w` of a number field lies over a rational prime `p`. -/
theorem exists_prime_liesOver (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hprime : (w.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ w.asIdeal
  have hne : w.asIdeal.under ℤ ≠ ⊥ := Ideal.under_ne_bot ℤ w.ne_bot
  obtain h | ⟨p, hp, hpeq⟩ := Ideal.isPrime_int_iff.mp hprime
  · exact absurd h hne
  · exact ⟨p, hp, ⟨hpeq.symm⟩⟩

variable [IsGalois ℚ L]
  (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (K : IntermediateField ℚ L) (u : HeightOneSpectrum (𝓞 K))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]

/-- **`e ≤ a!` from the completions.** If `L_w` is the Galois closure of (the image of) `K_u`
over `ℚ_v` and `[K_u : ℚ_v] ≤ a`, then `e(w | p) ≤ |D_w| ≤ a!`. -/
theorem ramificationIdx_le_factorial_completion
    (hclos : IntermediateField.normalClosure (v.adicCompletion ℚ) (localField v w K u)
      (w.adicCompletion L) = ⊤)
    (a : ℕ) (hdeg : Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K) ≤ a) :
    w.asIdeal.ramificationIdx ℤ ≤ a.factorial := by
  obtain ⟨p, hp, hlo⟩ := exists_prime_liesOver w
  have : Fact p.Prime := ⟨hp⟩
  exact GlueD1Local.ramificationIdx_le_factorial_local L p w.asIdeal K
    (normalCore_localSub_eq_bot v w K u hclos) a
    ((index_localSub_eq_finrank v w K u).trans_le hdeg)

/-- **D1 at the completions, kernel filtration.** If `L_w` is the Galois closure of `K_u/ℚ_v`,
`1 ≤ a`, `[K_u : ℚ_v] ≤ a` and `G_b(w) ≠ 1`, then `φ(b) ≤ 4a²` for the kernel's Herbrand sum
`GlueConductor.phi (ramCard L P)`. Closed (T20, T21 proved). -/
theorem D1_completion_ramGroup
    (hclos : IntermediateField.normalClosure (v.adicCompletion ℚ) (localField v w K u)
      (w.adicCompletion L) = ⊤)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K) ≤ a)
    (b : ℕ) (hb : GlueConductor.ramGroup L w.asIdeal b ≠ ⊥) :
    GlueConductor.phi (GlueConductor.ramCard L w.asIdeal) b ≤ 4 * a ^ 2 := by
  obtain ⟨p, hp, hlo⟩ := exists_prime_liesOver w
  have : Fact p.Prime := ⟨hp⟩
  exact ZInQ.Contrib.Different.D1_genuine_closed L p w.asIdeal a ha
    (ramificationIdx_le_factorial_completion v w K u hclos a hdeg) b hb

/-- **D1 at the completions, local filtration.** As `D1_completion_ramGroup`, with everything
read in `Gal(L_w/ℚ_v)`: if `G_b(L_w/ℚ_v) ≠ 1` then
`φ_{L_w/ℚ_v}(b) = ∑_{1 ≤ i ≤ b} |G_i(L_w/ℚ_v)| / |G_0(L_w/ℚ_v)| ≤ 4a²`. Closed. -/
theorem D1_completion
    (hclos : IntermediateField.normalClosure (v.adicCompletion ℚ) (localField v w K u)
      (w.adicCompletion L) = ⊤)
    (a : ℕ) (ha : 1 ≤ a) (hdeg : Module.finrank (v.adicCompletion ℚ) (u.adicCompletion K) ≤ a)
    (b : ℕ) (hb : localRam v w b ≠ ⊥) :
    GlueConductor.phi (fun i => Nat.card (localRam v w i)) b ≤ 4 * a ^ 2 := by
  rw [← ramCard_eq_card_localRam_fun v w]
  exact D1_completion_ramGroup v w K u hclos a ha hdeg b ((ramGroup_ne_bot_iff v w b).mpr hb)

end ZInQ.Contrib.G15

end
