import ZInQKernel.RouteK.RankVariants
import ZInQKernel.RouteK.Assembly.PoleCompleteness

/-!
# CR₃ restricted to the two curves the proof uses

The only consumer of CR₃ is pole completeness (`poleCompleteness_of_certifiedRank`), and it applies
CR₃ at two curves only: `C_{d₁}` and `C_{d₁ |θ|}`, where `d₁ = D.d₁` comes from a slot choice
`D : RouteK.Slots β θ p₀` made inside the descent lemma (`RouteK.descent_lemma`). This module states
the positive-rank hypothesis for exactly these curves, `RouteK.Rank.CertifiedRankDLRk`, and derives:

* `RouteK.Rank.sel_of_selmerCertified`: a certificate of Selmer type (`SelmerCertified d a`) gives
  `#Sel₂(C_d) = 8` and a Selmer class `(a, b)` (Proposition 0);
* `RouteK.Rank.certifiedRankDLRk_of_certifiedRankTYZRk` and
  `RouteK.Rank.certifiedRankDLRk_of_certifiedRankRk`: CR₃^TYZ,Rk and CR₃^Rk imply CR₃^DL,Rk;
* `RouteK.Rank.poleCompleteness_of_certifiedRankDLRk`: CR₃^DL,Rk implies pole completeness, by RK9
  (`loc_of_mem_sel2_of_infinite_order`) with Mordell–Weil (`fg_points`);
* `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk`:
  Theorem 1.1 from 6C_min and CR₃^DL,Rk;
* `RouteK.Rank.CertifiedRankDLAdmRk`: the same over the proof's actual inputs (admissible `B` with
  the multiplier, `p₀` and slots of `exists_multiplier_and_slots`), implied by CR₃^DL,Rk and implying
  pole completeness.
-/

namespace ZInQ

namespace RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.RouteK.Selmer ZInQ.RouteK.Rank5b

/-- **Proposition 0 at one certificate.** If `d ≡ 5 (mod 8)` is squarefree and `a` is a squarefree
divisor of `d` such that `Σ(𝒞_d)` has exactly 8 solutions, one of them with first coordinate the
class of `a` (`SelmerCertified d a`), then `#Sel₂(C_d) = 8` and `(a, b) ∈ Sel₂(C_d)` for some `b`.
This is the pointwise content of the proof of `Selmer.certifiedRank_of_sel`. -/
theorem sel_of_selmerCertified {d : ℕ} (hd : d % 8 = 5) (hsqd : Squarefree d) {a : ℤ}
    (hsqa : Squarefree a) (had : a ∣ (d : ℤ)) (hc : SelmerCertified d a) :
    (Sel2 d).ncard = 8 ∧ ∃ b : ℤ, (a, b) ∈ Sel2 d := by
  obtain ⟨_, hcard, σ, hσ, hfirst⟩ := hc
  have hd0 : d ≠ 0 := by omega
  have hodd := odd_of_mod_eight_eq_five hd
  obtain ⟨hiff, hsurj⟩ := prop0Statement d hd hsqd
  have hmem : selPair d σ ∈ Sel2 d := (hiff σ).1 ((Config.mem_sols _).mp hσ)
  have hA : (selPair d σ).1 = a := by
    have h1 : σ.a0 = (natClass d a).1 := congrArg Prod.fst hfirst
    have h2 : σ.a1 = (natClass d a).2.1 := congrArg (fun t => t.2.1) hfirst
    have h3 : σ.u = (natClass d a).2.2 := congrArg (fun t => t.2.2) hfirst
    simp only [selPair, h1, h2, h3]
    exact classInt_natClass hd0 hsqa had
  have hS : Sel2 d = selPair d '' ((natConfig d hodd).sols : Set (Unknowns d.primeFactors)) := by
    ext ab
    constructor
    · intro hab
      obtain ⟨τ, rfl⟩ := hsurj hab
      exact ⟨τ, (Config.mem_sols _).mpr ((hiff τ).2 hab), rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (hiff τ).1 ((Config.mem_sols _).mp hτ)
  refine ⟨?_, (selPair d σ).2, ?_⟩
  · rw [hS, Set.ncard_image_of_injective _ (selPair_injective hodd), Set.ncard_coe_finset]
    exact hcard
  · rw [← hA]; exact hmem

/-- **CR₃^DL,Rk** (the positive-rank hypothesis restricted to the two curves the proof chooses).
For all `β`, `θ`, `p₀` satisfying the slot inputs `RouteK.Inputs β θ p₀` there is a slot choice
`D : RouteK.Slots β θ p₀` such that both `C_{D.d₁}` and `C_{D.d₁ |θ|}` (`C_d : y² = x³ − d²x`,
`shortCurve (−d²)` over `ℚ`) have a rational point of infinite order.

These are the two curves to which pole completeness applies CR₃ (`d₂ = D.d₂ = D.d₁ |θ|`,
`Slots.d₂_eq`). The slot choice is existential, so a family of explicit points on the curves of some
slot choice suffices. CR₃^DL,Rk is implied in Lean by CR₃^Rk
(`certifiedRankDLRk_of_certifiedRankRk`) and by CR₃^TYZ,Rk
(`certifiedRankDLRk_of_certifiedRankTYZRk`), and so rests on the same literature (Tian–Yuan–Zhang
with Proposition N, and Gross–Zagier with an auxiliary field; `docs/research/cr3-trust.md`); any
statement Lean derives from these
hypotheses, down to `PoleCompleteness` itself, is equally justified by that literature. What this
form adds is a smaller target for partial results.

The statement depends on the internal definitions `RouteK.Inputs` and `RouteK.Slots` (and on
`Slots.d₁`), so a change to the slot construction changes its meaning. -/
def CertifiedRankDLRk : Prop :=
  ∀ (β θ : ℤ) (p₀ : ℕ), Inputs β θ p₀ → ∃ D : Slots β θ p₀,
    (∃ P : (shortCurve (-((D.d₁ : ℕ) : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P) ∧
    (∃ P : (shortCurve (-((D.d₁ * θ.natAbs : ℕ) : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P)

/-- `C_{D.d₁ |θ|} = C_{D.d₂}` is a curve with `d ≡ 5 (mod 8)`, `d` squarefree, `β ∣ d` and a
certificate of Selmer type for `β`. -/
theorem slots_d₂_facts {β θ : ℤ} {p₀ : ℕ} (D : Slots β θ p₀) (hI : Inputs β θ p₀) :
    (D.d₁ * θ.natAbs) % 8 = 5 ∧ Squarefree (D.d₁ * θ.natAbs) ∧ β ∣ ((D.d₁ * θ.natAbs : ℕ) : ℤ) ∧
      SelmerCertified (D.d₁ * θ.natAbs) β := by
  rw [← D.d₂_eq hI]
  refine ⟨?_, D.squarefree_d₂ hI, ?_, D.selmerCertified_d₂ hI⟩
  · rw [D.d₂_eq hI, Nat.mul_mod, D.d₁_mod hI, hI.θ_natAbs_mod]
  · rw [D.d₂_eq hI, Nat.cast_mul]
    exact dvd_mul_of_dvd_left (D.β_dvd_d₁ hI) _

/-- CR₃^TYZ,Rk at a curve carrying a certificate of Selmer type for some `a` with `|a| ≡ 7 (mod 8)`:
the genus sum `T5b d` is odd by Corollary 4.4 (`det_M5b_eq_one`) and Theorem 3.6
(`det_M5b_eq_T5b`). -/
theorem exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified (h : CertifiedRankTYZRk)
    {d : ℕ} (hd : d % 8 = 5) (hsqd : Squarefree d) {a : ℤ} (hsqa : Squarefree a)
    (had : a ∣ (d : ℤ)) (h7 : a.natAbs % 8 = 7) (hc : SelmerCertified d a) :
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P := by
  obtain ⟨h8, b, hb⟩ := sel_of_selmerCertified hd hsqd hsqa had hc
  refine h d hd hsqd ?_
  rw [← det_M5b_eq_T5b hd hsqd]
  exact det_M5b_eq_one hd hsqd h8 hb h7

/-- **CR₃^DL,Rk from CR₃^TYZ,Rk**: take any slot choice (`exists_slots`); both curves have odd genus
sum `T5b`. -/
theorem certifiedRankDLRk_of_certifiedRankTYZRk (h : CertifiedRankTYZRk) : CertifiedRankDLRk := by
  intro β θ p₀ hI
  obtain ⟨D⟩ := exists_slots hI.odd_β hI.odd_θ hI.coprime hI.p₀_mem
  obtain ⟨h₂5, h₂sq, h₂β, h₂c⟩ := slots_d₂_facts D hI
  exact ⟨D, exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified h (D.d₁_mod hI)
      (D.squarefree_d₁ hI) hI.sqf_β (D.β_dvd_d₁ hI) hI.mod_β (D.selmerCertified_d₁ hI),
    exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified h h₂5 h₂sq hI.sqf_β h₂β
      hI.mod_β h₂c⟩

/-- **CR₃^DL,Rk from CR₃^Rk**: take any slot choice (`exists_slots`); on both curves Proposition 0
(`sel_of_selmerCertified`) gives `#Sel₂ = 8` and a Selmer class `(β, b)` with `|β| ≡ 7 (mod 8)`. -/
theorem certifiedRankDLRk_of_certifiedRankRk (h : CertifiedRankRk) : CertifiedRankDLRk := by
  intro β θ p₀ hI
  obtain ⟨D⟩ := exists_slots hI.odd_β hI.odd_θ hI.coprime hI.p₀_mem
  obtain ⟨h₂5, h₂sq, h₂β, h₂c⟩ := slots_d₂_facts D hI
  refine ⟨D, ?_, ?_⟩
  · obtain ⟨h8, b, hb⟩ := sel_of_selmerCertified (D.d₁_mod hI) (D.squarefree_d₁ hI) hI.sqf_β
      (D.β_dvd_d₁ hI) (D.selmerCertified_d₁ hI)
    exact h _ (D.d₁_mod hI) (D.squarefree_d₁ hI) h8 ⟨(β, b), hb, hI.mod_β⟩
  · obtain ⟨h8, b, hb⟩ := sel_of_selmerCertified h₂5 h₂sq hI.sqf_β h₂β h₂c
    exact h _ h₂5 h₂sq h8 ⟨(β, b), hb, hI.mod_β⟩

/-- The conclusion of CR₃ at one curve, from a certificate of Selmer type and a point of infinite
order: Proposition 0 (`sel_of_selmerCertified`), RK9 (`loc_of_mem_sel2_of_infinite_order`) with
Mordell–Weil (`fg_points`), and `exists_point_of_loc`. -/
theorem exists_point_of_selmerCertified_of_infinite_order {d : ℕ} (hd : d % 8 = 5)
    (hsqd : Squarefree d) {a : ℤ} (hsqa : Squarefree a) (had : a ∣ (d : ℤ))
    (h7 : a.natAbs % 8 = 7) (hc : SelmerCertified d a)
    (hinf : ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P) :
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - (d : ℚ) ^ 2 * x ∧ x ≠ 0 ∧ IsSquare (x / a) := by
  obtain ⟨h8, b, hb⟩ := sel_of_selmerCertified hd hsqd hsqa had hc
  have hd0 : d ≠ 0 := by omega
  have hloc := loc_of_mem_sel2_of_infinite_order hd0 (fg_points d hd0) hinf h8 _ hb
  exact exists_point_of_loc hd0 hsqa h7 hb.2.1.ne_zero hloc

/-- The core of pole completeness for one admissible `B`: from a multiplier `m`, slot inputs and a
slot choice `D` whose two curves have points of infinite order, `B` is pole-soluble. Each use of CR₃
in `poleCompleteness_of_certifiedRank` is replaced by
`exists_point_of_selmerCertified_of_infinite_order`. -/
theorem poleSoluble_of_slots_infinite_order {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730)
    {p₀ : ℕ} (hI : Inputs (betaOf B m) (thetaOf B m) p₀) (D : Slots (betaOf B m) (thetaOf B m) p₀)
    (hP₁ : ∃ P : (shortCurve (-((D.d₁ : ℕ) : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P)
    (hP₂ : ∃ P : (shortCurve (-((D.d₁ * (thetaOf B m).natAbs : ℕ) : ℚ) ^ 2)).toAffine.Point,
      ¬IsOfFinAddOrder P) : PoleSoluble B := by
  obtain ⟨h₂5, h₂sq, h₂β, h₂c⟩ := slots_d₂_facts D hI
  have hmB' : (m : ℚ) ≠ B := by
    intro h
    have h1 : (0 : ℚ) < m := h ▸ hB.2.1
    have h2 : (m : ℚ) < 1 := by linarith [hB.2.2.1, h ▸ le_refl (m : ℚ)]
    have : (0 : ℤ) < m := by exact_mod_cast h1
    have : m < 1 := by exact_mod_cast h2
    omega
  obtain ⟨x₁, y₁, h₁, hx₁, hs₁⟩ := exists_point_of_selmerCertified_of_infinite_order
    (D.d₁_mod hI) (D.squarefree_d₁ hI) hI.sqf_β (D.β_dvd_d₁ hI) hI.mod_β (D.selmerCertified_d₁ hI)
    hP₁
  obtain ⟨x₂, y₂, h₂, hx₂, hs₂⟩ := exists_point_of_selmerCertified_of_infinite_order h₂5 h₂sq
    hI.sqf_β h₂β hI.mod_β h₂c hP₂
  have hn0 : ((D.d₁ : ℕ) : ℚ) ≠ 0 := by
    have : D.d₁ ≠ 0 := by have := D.d₁_mod hI; omega
    exact_mod_cast this
  refine poleSoluble_of_points (y₂ := y₂) hB.ne_zero hm hmB' hn0 h₁ hx₁ hs₁ ?_ hx₂ hs₂
  rw [h₂, Nat.cast_mul, mul_pow, natAbs_cast_sq, mul_pow]

/-- **PC from CR₃^DL,Rk.** The proof of `poleCompleteness_of_certifiedRank`, with the slot choice
taken from the hypothesis instead of from `descent_lemma`, and each use of CR₃ replaced by
`exists_point_of_selmerCertified_of_infinite_order` (`poleSoluble_of_slots_infinite_order`). -/
theorem poleCompleteness_of_certifiedRankDLRk (hDL : CertifiedRankDLRk) : PoleCompleteness := by
  rw [poleCompleteness_iff_admissible]
  intro B hB
  obtain ⟨m, hm, hβ, h7, ⟨p₀, hp₀⟩, -⟩ := exists_multiplier_and_slots hB
  have hI := inputs_of_admissible hB hm hβ h7 hp₀
  obtain ⟨D, hP₁, hP₂⟩ := hDL _ _ _ hI
  exact poleSoluble_of_slots_infinite_order hB hm hI D hP₁ hP₂

/-- **CR₃^DL,Adm,Rk** (CR₃^DL,Rk over the proof's actual inputs). For every admissible `B` there are
a signed divisor `m` of 2730 with `β = betaOf B m` odd and `|β| ≡ 7 (mod 8)`, a prime `p₀ ∣ β` and a
slot choice `D : RouteK.Slots β θ p₀` (`θ = thetaOf B m`) such that `C_{D.d₁}` and `C_{D.d₁ |θ|}`
have rational points of infinite order. These are the data produced by
`exists_multiplier_and_slots`; the statement is implied by CR₃^DL,Rk
(`certifiedRankDLAdmRk_of_certifiedRankDLRk`) and implies pole completeness
(`poleCompleteness_of_certifiedRankDLAdmRk`). Like CR₃^DL,Rk it depends on the internal definitions
`betaOf`, `thetaOf`, `Admissible` and `RouteK.Slots`. -/
def CertifiedRankDLAdmRk : Prop :=
  ∀ B : ℚ, Admissible B → ∃ m : ℤ, m ∣ 2730 ∧ Odd (betaOf B m) ∧ (betaOf B m).natAbs % 8 = 7 ∧
    ∃ p₀ ∈ primesOf (betaOf B m), ∃ D : Slots (betaOf B m) (thetaOf B m) p₀,
      (∃ P : (shortCurve (-((D.d₁ : ℕ) : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P) ∧
      (∃ P : (shortCurve (-((D.d₁ * (thetaOf B m).natAbs : ℕ) : ℚ) ^ 2)).toAffine.Point,
        ¬IsOfFinAddOrder P)

/-- **CR₃^DL,Adm,Rk from CR₃^DL,Rk.** -/
theorem certifiedRankDLAdmRk_of_certifiedRankDLRk (hDL : CertifiedRankDLRk) :
    CertifiedRankDLAdmRk := by
  intro B hB
  obtain ⟨m, hm, hβ, h7, ⟨p₀, hp₀⟩, -⟩ := exists_multiplier_and_slots hB
  obtain ⟨D, hP₁, hP₂⟩ := hDL _ _ _ (inputs_of_admissible hB hm hβ h7 hp₀)
  exact ⟨m, hm, hβ, h7, p₀, hp₀, D, hP₁, hP₂⟩

/-- **PC from CR₃^DL,Adm,Rk.** -/
theorem poleCompleteness_of_certifiedRankDLAdmRk (h : CertifiedRankDLAdmRk) : PoleCompleteness := by
  rw [poleCompleteness_iff_admissible]
  intro B hB
  obtain ⟨m, hm, hβ, h7, p₀, hp₀, D, hP₁, hP₂⟩ := h B hB
  exact poleSoluble_of_slots_infinite_order hB hm (inputs_of_admissible hB hm hβ h7 hp₀) D hP₁ hP₂

end RouteK.Rank

/-- **Theorem 1.1** from 6C_min and CR₃^DL,Rk (`RouteK.Rank.CertifiedRankDLRk`: for the slot inputs
of the proof there is a slot choice whose two curves `C_{d₁}`, `C_{d₁ |θ|}` have points of infinite
order). Pole completeness comes from `RouteK.Rank.poleCompleteness_of_certifiedRankDLRk`; the rest
of the assembly is that of
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank` (route AP, with
Szemerédi's theorem in the primes and Proposition D proved). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankDLRk) : FrozenTarget :=
  Assembly.assembly_AP Compiler.NodeCheck.haltingAddMulBound hH
    (RouteK.Rank.poleCompleteness_of_certifiedRankDLRk hCR)
    (Mult.slopeRepresentationAP_of_goodPrimeAP
      (goodPrimeAP_of_greenTaoDense greenTaoDense Density.goodPrimeDensity))

/-- **Theorem 1.1** from 6C_min and CR₃^DL,Adm,Rk (`RouteK.Rank.CertifiedRankDLAdmRk`: for every
admissible `B`, a multiplier and a slot choice whose two curves have points of infinite order).
Pole completeness comes from `RouteK.Rank.poleCompleteness_of_certifiedRankDLAdmRk`; the rest of
the assembly is that of
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLRk`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLAdmRk
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankDLAdmRk) : FrozenTarget :=
  Assembly.assembly_AP Compiler.NodeCheck.haltingAddMulBound hH
    (RouteK.Rank.poleCompleteness_of_certifiedRankDLAdmRk hCR)
    (Mult.slopeRepresentationAP_of_goodPrimeAP
      (goodPrimeAP_of_greenTaoDense greenTaoDense Density.goodPrimeDensity))

end ZInQ
