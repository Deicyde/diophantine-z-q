import ZInQKernel.Contrib.TYZGenus.RingClassGenus

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section Lifts

variable {K : Type} [Field K] [NumberField K]

/-- **Lifts of `2Cl` into the squares of `Pic O`**: there is a set `R ⊆ Pic(O)²` mapped bijectively
onto `Cl(K)² = Pic(𝓞_K)²` by `Pic O → Cl(K)`; it has `#Cl(K)²` elements. (For `O = O_{n,4}` these are
the candidates for TYZ's `Φ₀` up to the factor `⟨σ_{1+2ϖ}⟩`; TYZ's exact choice is not recorded on this
host.) -/
theorem exists_lift_picSquares (O : NumberFieldOrder K) :
    ∃ R : Finset (Pic O), (∀ c ∈ R, c ∈ picSquares O) ∧
      Set.BijOn (picToMax O) (R : Set (Pic O)) (picSquares (maximalNumberFieldOrder K)) ∧
      R.card = Nat.card (picSquares (maximalNumberFieldOrder K)) := by
  classical
  have hlift : ∀ s : picSquares (maximalNumberFieldOrder K),
      ∃ c, c ∈ picSquares O ∧ picToMax O c = s := by
    rintro ⟨s, ⟨c, rfl⟩⟩
    obtain ⟨c', hc'⟩ := picToMax_surjective O c
    exact ⟨c' ^ 2, ⟨c', rfl⟩, by simp [hc']⟩
  choose f hf1 hf2 using hlift
  have hinj : Function.Injective f := fun s t h => Subtype.ext (by rw [← hf2 s, ← hf2 t, h])
  haveI : Fintype (picSquares (maximalNumberFieldOrder K)) := Fintype.ofFinite _
  refine ⟨Finset.univ.image f, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
    exact hf1 s
  · intro c hc
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    rw [hf2]; exact s.2
  · intro c hc c' hc' h
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc')
    rw [hf2, hf2] at h
    rw [Subtype.ext h]
  · intro s hs
    exact ⟨f ⟨s, hs⟩, Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ _)), hf2 _⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]

open ZInQ.RouteK.Rank5b in
/-- For TYZ's order `O_{n,4}`: such a lift has `g(n) = gCl n` elements. -/
theorem exists_lift_picSquares_O4 (n : ℕ) [NeZero n] :
    ∃ R : Finset (Pic (O4 n)), (∀ c ∈ R, c ∈ picSquares (O4 n)) ∧
      Set.BijOn (picToMax (O4 n)) (R : Set (Pic (O4 n)))
        (picSquares (maximalNumberFieldOrder (QNeg n))) ∧ R.card = gCl n := by
  obtain ⟨R, h1, h2, h3⟩ := exists_lift_picSquares (O4 n)
  exact ⟨R, h1, h2, by rw [h3, gCl_eq_card_picSquares]⟩

end Lifts

section ClassSeven

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp.CurveA

/-- **The ring class field of discriminant `−d`, `d ≡ 3 (mod 4)` squarefree, is the Hilbert class
field `H_d`** (TYZ's class-7 CM points have discriminant `−d`). -/
theorem ringClassFieldD_neg {d : ℕ} (hd : d % 4 = 3) (hsq : Squarefree d) :
    haveI : NeZero d := ⟨by omega⟩
    ringClassFieldD (-d) = ((hilbertField d).restrictScalars ℚ).map (embed d) := by
  haveI : NeZero d := ⟨by omega⟩
  have hab : (-(d : ℤ)).natAbs = d := by omega
  have hs : sqfPart d = d := by
    obtain ⟨b, hb, hs⟩ := sqfPart_spec d
    exact squarefree_eq_of_sq_mul_eq (e := 1) (by rw [hb]; ring) (by rw [hb]; omega) hs hsq
  have hc : condD (-d) = 1 := by
    rw [condD, hab, hs, if_pos hd, Nat.div_self (by omega)]
    rfl
  rw [ringClassFieldD, if_pos (by omega), hc, hab, hs, ringClassFieldBar_eq, conductorOrder_one]

end ClassSeven

end ZInQ.Contrib.TYZGenus.RingClass
