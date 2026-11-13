import ZInQKernel.Contrib.TYZGenus.Package
import ZInQKernel.Contrib.TYZGenus.RingClass
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
example (hH : ∀ d : ℕ, d % 8 = 5 → Squarefree d → Normal ℚ (Hprimebar d)) (n : ℕ) (hsq : Squarefree n) :
    Normal ℚ (HHprime n) := by
  have h1 : Normal ℚ (Lni n) := sorry
  have e : (⨆ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), Hprimebar d₀ : IntermediateField ℚ Qbar) =
      ⨆ d : (n.divisors.filter (fun d => d % 8 = 5) : Set ℕ), Hprimebar d := iSup_subtype'
  have h2 : ∀ d : (n.divisors.filter (fun d => d % 8 = 5) : Set ℕ), Normal ℚ (Hprimebar d) := by
    rintro ⟨d₀, hd⟩
    obtain ⟨hdn, hd5⟩ := Finset.mem_filter.mp hd
    exact hH d₀ hd5 (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hdn))
  have h3 := IntermediateField.normal_iSup (F := ℚ) (K := Qbar) _ (h := h2)
  rw [← e] at h3
  unfold HHprime
  exact IntermediateField.normal_sup (F := ℚ) (K := Qbar) (Lni n) _
