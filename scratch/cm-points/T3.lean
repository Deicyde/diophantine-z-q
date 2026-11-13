import ZInQKernel.Contrib.TYZGenus.Package

noncomputable section
namespace ZInQ.Contrib.TYZGenus.Package
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.PropN WeierstrassCurve.Affine

/-- `A(K)` as a `ℤ[i]`-submodule of `A(ℚ̄)`, for `i ∈ K`. -/
def ptsOverMod (K : IntermediateField ℚ Qbar) (hi : iQ ∈ K) : Submodule GaussianInt PtA where
  carrier := ptsOver K
  add_mem' ha hb := (ptsOver K).add_mem ha hb
  zero_mem' := (ptsOver K).zero_mem
  smul_mem' z P hP := by
    show z.re • P + z.im • iPt P ∈ ptsOver K
    exact (ptsOver K).add_mem ((ptsOver K).zsmul_mem hP _) ((ptsOver K).zsmul_mem (iPt_mem hi hP) _)

theorem ptT_mem (K : IntermediateField ℚ Qbar) : ptT ∈ ptsOver K := by
  rw [mem_ptsOver_iff]
  refine ⟨ofNat_mem K 2, ?_⟩
  exact K.neg_mem (ofNat_mem K 4)

theorem tauG_mem (K : IntermediateField ℚ Qbar) (hi : iQ ∈ K) (y : GaussianInt) :
    tauG y ∈ ptsOverMod K hi :=
  (ptsOverMod K hi).smul_mem y (ptT_mem K)

theorem galPt_ptT (σ : GalQ) : galPt σ ptT = ptT := by
  obtain ⟨h', e⟩ := galPt_some σ nonsingular_T
  rw [ptT, e, Point.some.injEq]
  exact ⟨map_ofNat σ 2, by rw [map_neg, map_ofNat]⟩

theorem galPt_tauG (σ : GalQ) (hσ : σ iQ = iQ) (y : GaussianInt) : galPt σ (tauG y) = tauG y := by
  rw [tauG_apply, gsmul_def, map_add, map_zsmul, map_zsmul, galPt_iPt σ hσ, galPt_ptT]

theorem betaOneSign_neg_one : betaOneSign (-1) = 1 := by decide

theorem fixes_i_of_isBetaOneLift {σ : GalQ} (hσ : IsBetaOneLift σ) : σ iQ = iQ := by
  have h := hσ (-1) (isUnit_one.neg).squarefree iQ (by rw [iQ_sq]; push_cast; ring)
  rw [h, betaOneSign_neg_one, Int.cast_one, one_mul]

theorem Pseq_eq (ℓ : ℕ → ℤ) (ε : ℕ → ℕ → GaussianInt) (Z : ℕ → PtA) (d : ℕ) :
    Pseq ℓ ε Z d = Z d - ∑ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
      (ε (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Pseq ℓ ε Z (d / d₁) := by
  rw [Pseq]
  congr 1
  exact Finset.sum_attach _ (fun d₁ => (ε (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Pseq ℓ ε Z (d / d₁))

/-- For `d ∣ n` of class `5, 7` and `d₁ ∣ d` of class `1, 3`, `d / d₁ ∣ n` has class `5, 7`. -/
theorem div_class {n d d₁ : ℕ} (hd : d ∈ n.divisors) (hdc : d % 8 = 5 ∨ d % 8 = 7)
    (hd₁ : d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3))) :
    d / d₁ ∈ n.divisors ∧ (d / d₁ % 8 = 5 ∨ d / d₁ % 8 = 7) := by
  obtain ⟨hd₁d, -, hc⟩ := Finset.mem_filter.mp hd₁
  have hdd : d₁ ∣ d := Nat.dvd_of_mem_divisors hd₁d
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
  refine ⟨Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hdd).trans hdn, hn0⟩, ?_⟩
  rcases hdc with h | h <;> rcases hc with h' | h'
  · rw [div_mod8_of hdd h h' (Or.inl rfl)]; left; rfl
  · rw [div_mod8_of hdd h h' (Or.inr (Or.inl rfl))]; right; rfl
  · rw [div_mod8_of hdd h h' (Or.inl rfl)]; right; rfl
  · rw [div_mod8_of hdd h h' (Or.inr (Or.inl rfl))]; left; rfl

theorem Pseq_mem {ℓ : ℕ → ℤ} {ε : ℕ → ℕ → GaussianInt} {Z : ℕ → PtA} {n : ℕ}
    {S : Submodule GaussianInt PtA}
    (hZ : ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ S) :
    ∀ d, d ∈ n.divisors → (d % 8 = 5 ∨ d % 8 = 7) → Pseq ℓ ε Z d ∈ S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hdc
    rw [Pseq_eq]
    refine S.sub_mem (hZ d hd hdc) (S.sum_mem fun d₁ hd₁ => S.smul_mem _ ?_)
    obtain ⟨h1, h2⟩ := div_class hd hdc hd₁
    obtain ⟨-, hlt, -⟩ := Finset.mem_filter.mp hd₁
    exact ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2.symm.symm |>
      fun h => Nat.pos_of_mem_divisors hd) hlt) h1 h2

open Classical in
/-- **Core glue**: the pinned objects give `PropN.GenusData ℓ n`. -/
theorem genusData_of {ℓ : ℕ → ℤ} {n : ℕ} (hn : n % 8 = 5) (K : IntermediateField ℚ Qbar)
    (hi : iQ ∈ K) (hN : Normal ℚ K)
    (h318 : ∀ P ∈ ptsOver K, IsOfFinAddOrder P → ∃ y : GaussianInt, tauG y = P)
    (Z : ℕ → PtA) (hZ : ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver K)
    (ε : ℕ → ℕ → GaussianInt) (hε : EpsClasses n ε)
    (htors : ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))
    (σ : GalQ) (hσ : IsBetaOneLift σ)
    (h5 : ∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2)
    (h7 : ∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1) :
    Nonempty (GenusData ℓ n) := by
  set S := ptsOverMod K hi with hS
  have hZS : ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ S := hZ
  have hPS := Pseq_mem (ℓ := ℓ) (ε := ε) hZS
  have hσK : ∀ x ∈ K, σ x ∈ K := fun x hx =>
    (IntermediateField.normal_iff_forall_map_le.mp hN) σ.toAlgHom ⟨x, hx, rfl⟩
  have hσi := fixes_i_of_isBetaOneLift hσ
  have hn0 : n ≠ 0 := by omega
  have hnd : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  let ZM : ℕ → S := fun e =>
    if h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7) then ⟨Z e, hZS e h.1 h.2⟩ else 0
  let PM : ℕ → S := fun e =>
    if h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7) then ⟨Pseq ℓ ε Z e, hPS e h.1 h.2⟩ else 0
  let τM : GaussianInt →+ S :=
    AddMonoidHom.mk' (fun y => ⟨tauG y, tauG_mem K hi y⟩) (fun a b => by ext; simp)
  let βM : S →+ S :=
    AddMonoidHom.mk' (fun x => ⟨galPt σ x, galPt_mem σ hσK x.2⟩) (fun a b => by ext; simp)
  have hZM : ∀ e (h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7)), (ZM e : PtA) = Z e :=
    fun e h => by simp only [ZM, dite_eq_left_of_eq_true (eq_true h)]
  have hPM : ∀ e (h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7)), (PM e : PtA) = Pseq ℓ ε Z e :=
    fun e h => by simp only [PM, dite_eq_left_of_eq_true (eq_true h)]
  refine ⟨{
      M := S
      Z := ZM
      P := PM
      ε := ε
      eps_53 := And.left hε
      eps_pm1 := And.right hε
      recursion := ?_
      torsion_of_zero := ?_
      τ := τM
      τ_eq_zero := ?_
      tors_mem_range := ?_
      β := βM
      β_τ := ?_
      beta_five := ?_
      beta_seven := ?_ }⟩
  · intro d hd hdc
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_sum, hPM d ⟨hd, hdc⟩, hZM d ⟨hd, hdc⟩, Pseq_eq]
    congr 1
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    rw [Submodule.coe_smul, hPM _ (div_class hd hdc hd₁)]
  · intro h0
    have ht := htors h0
    rw [← hPM n ⟨hnd, Or.inl hn⟩] at ht
    exact (AddSubmonoid.isOfFinAddOrder_coe (H := S.toAddSubmonoid)).mp ht
  · intro y
    rw [← tauG_eq_zero]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  · intro x hx
    obtain ⟨y, hy⟩ := h318 x x.2 ((AddSubmonoid.isOfFinAddOrder_coe (H := S.toAddSubmonoid)).mpr hx)
    exact ⟨y, Subtype.ext hy⟩
  · intro y
    exact Subtype.ext (galPt_tauG σ hσi y)
  · intro e he he5
    obtain ⟨k, hk⟩ := h5 e he he5
    refine ⟨k, Subtype.ext ?_⟩
    have h := hZM e ⟨he, Or.inl he5⟩
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, AddMonoidHom.mk'_apply, h, βM, τM]
    exact hk
  · intro e he he7
    apply Subtype.ext
    have h := hZM e ⟨he, Or.inr he7⟩
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, AddMonoidHom.mk'_apply, h, βM, τM]
    exact h7 e he he7

open ZInQ.Contrib.TYZDecomp in
/-- **Glue, level 1**: `i ∈ ℍ'_n`, normality of `ℍ'_n`, Lemma 3.18 and the genus-point leaf
(with existential `Z`) give `TYZGenusPackage`; here `M`, `τ`, `β` are pinned. -/
theorem genusPackage_of_genusPointLeaf (Hn : ℕ → IntermediateField ℚ Qbar) (hI : IContained Hn)
    (hN : NormalFields Hn) (h318 : Lemma318 Hn)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeaf ℓ Hn) : TYZGenusPackage := by
  intro ℓ hℓ n hn hsq
  obtain ⟨Z, hZ, ⟨ε, hε, ht⟩, ⟨σ, hσ, h5, h7⟩⟩ := hG ℓ hℓ n hn hsq
  exact genusData_of hn (Hn n) (hI n hn hsq) (hN n hn hsq) (h318 n hn hsq) Z hZ ε hε ht σ hσ h5 h7

/-- **Glue, level 2**: with the genus points `Z` pinned, the three genus-point leaves give the
bundled leaf. -/
theorem genusPointLeaf_of_split {ℓ : ℕ → ℤ} {Hn : ℕ → IntermediateField ℚ Qbar} {Z : ℕ → PtA}
    (hZ : GenusPtsDefined Hn Z) (h35 : Thm35First ℓ Z) (h321 : Lemma321 Z) :
    GenusPointLeaf ℓ Hn :=
  fun n hn hsq => ⟨Z, hZ n hn hsq, h35 n hn hsq, h321 n hn hsq⟩

open ZInQ.Contrib.TYZDecomp in
/-- **Main glue**: the split leaves give `TYZGenusPackage`. -/
theorem genusPackage_of_split (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA)
    (hI : IContained Hn) (hN : NormalFields Hn) (h318 : Lemma318 Hn)
    (hZ : GenusPtsDefined Hn Z) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ Z)
    (h321 : Lemma321 Z) : TYZGenusPackage :=
  genusPackage_of_genusPointLeaf Hn hI hN h318 fun ℓ hℓ =>
    genusPointLeaf_of_split hZ (h35 ℓ hℓ) h321

open ZInQ.Contrib.TYZDecomp ZInQ.Literature in
/-- **The premise `TYZThm35ReadingA` from the split leaves** (with the three genuine TYZ leaves on
`𝓛` of `TYZDecomp.Leaves`, through Proposition N). -/
theorem tyzThm35ReadingA_of_split (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA)
    (hI : IContained Hn) (hN : NormalFields Hn) (h318 : Lemma318 Hn)
    (hZ : GenusPtsDefined Hn Z) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ Z)
    (h321 : Lemma321 Z) : TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 h1 h29 (genusPackage_of_split Hn Z hI hN h318 hZ h35 h321)

end ZInQ.Contrib.TYZGenus.Package
#print axioms ZInQ.Contrib.TYZGenus.Package.tyzThm35ReadingA_of_split
