import ZInQKernel.OneProof.H.TailZ22

/-! # gt-x6facts: `BabaGranathRationalAb` from Elkies' leaf and the existence of the three CM pairs

Task gt-x6facts (docs/research/gt-x6facts.md). The open research field `babaGranathRationalAb`
(`HDec.QMSplit.Moduli.BabaGranathRationalAb`, TailZ22) is proved from
* the open research field `elkiesEquationsX6Ab` (`HDec.QMSplit.Moduli.ElkiesEquationsX6Ab`, TailZ22, already a
  field of `OpenResearchLeaves16`), and
* one new witness-free statement, `QMPairsCMExist`: over `ℚ̄` there are QM pairs with CM by `ℤ[i]`, `ℤ[ζ₃]`
  and `ℤ[√−6]` (the existence of the three elliptic CM points of `X₆`).

The witness of Baba–Granath is Elkies' witness, with `π = t` and `(t₄, t₃, t₂₄) = (1, ∞, 0)`. The forward CM
clauses are Elkies' value clauses; the converse clauses (a point over `t₄` has CM by `ℤ[i]`, etc.) follow from
Elkies' fibre clause, one CM pair of each kind (`Ψ` is onto the classes), and the invariance of the CM
predicates under twists and isomorphisms (the argument of the chain's `LeafQM.AV.cm_of_val`).

The second field of the task, `gonzalezRotgerX6Ab`, is not reduced here (docs/research/gt-x6facts.md §3). -/

namespace HDec.QMSplit.Moduli.X6Facts

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

/-- **The three elliptic CM pairs exist over `ℚ̄`** (step: the CM points of discriminants `−4, −3, −24` on
`X₆ = X₀(6, 1)`, Baba–Granath Lemma 3.1's distinguished points, h-b1 M9): there are QM pairs `(A, ι)` over `ℚ̄`
(abelian surfaces with `ι : 𝒪 ↪ End A`, `𝒪` the maximal order of `B = (2, −3)`) whose commutant `End_𝒪(A)`
contains an element `φ` with `φ² = −1`, resp. `φ² − φ + 1 = 0`, resp. `φ² = −6`.

LEAF (published, classical; locators UNVERIFIED, no network): the orders `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` embed
(optimally) in `𝒪` (`i + j`, `(1 + j)/2`, `2j + k` in the chain's basis; Eichler's embedding theorem
in the form of Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800, Ch. III §5), and an optimal
embedding of `R` gives a QM abelian surface with `End_𝒪 ≅ R` (Shimura, Ann. of Math. 85 (1967) §§1-3:
`A_τ = ℂ²/ι(𝒪)(τ, 1)ᵀ` at the fixed point `τ` of `R^×`; descended to `ℚ̄` by Shimura–Taniyama); in the same
words González–Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6 gives `#CM(R) = 2^b h(R) > 0` on `X₀(6, 1)`
for these three orders. A consequence of each of these, never stronger: it asserts one pair of each kind. -/
def QMPairsCMExist : Prop :=
  (∃ P : QMPair Qbar, HasCM4 P.q) ∧ (∃ P : QMPair Qbar, HasCM3 P.q) ∧ (∃ P : QMPair Qbar, HasCM24 P.q)

/-- `QMPairsCMExist` is the witness-free form of the chain's clause `CMExists X Ψ` (on any coarse witness, since
`Ψ` is onto the classes). -/
theorem cmExists_iff (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : CMExists X Ψ ↔ QMPairsCMExist := by
  constructor
  · rintro ⟨⟨_, P₄, -, c₄⟩, ⟨_, P₃, -, c₃⟩, ⟨_, P₂, -, c₂⟩⟩
    exact ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩
  · rintro ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩
    exact ⟨⟨_, P₄, Ψ.apply_symm_apply _, c₄⟩, ⟨_, P₃, Ψ.apply_symm_apply _, c₃⟩,
      ⟨_, P₂, Ψ.apply_symm_apply _, c₂⟩⟩

/-- **`BabaGranathRationalAb` from Elkies' leaf and the three CM pairs** (gt-x6facts). -/
theorem babaGranathRationalAb_of_elkies (hE : ElkiesEquationsX6Ab) (hC : QMPairsCMExist) :
    BabaGranathRationalAb := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, -⟩ := hE
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hC
  have hs : ∀ P : QMPair Qbar, Ψ (Ψ.symm (Quotient.mk _ P)) = Quotient.mk _ P :=
    fun P => Ψ.apply_symm_apply _
  refine ⟨Y, Φ, X, Ψ, fY, t, OnePoint.some 1, OnePoint.infty, OnePoint.some 0, h1, h6,
    OnePoint.coe_ne_infty _, fun h => one_ne_zero (OnePoint.coe_injective h),
    (OnePoint.coe_ne_infty _).symm, fun x x' P Q hP hQ => ?_⟩
  obtain ⟨hf, h24, h4, h3⟩ := hcl x x' P Q hP hQ
  refine ⟨hf, ⟨fun c => by rw [h4 c]; simp, fun hx => ?_⟩, ⟨fun c => by rw [h3 c]; simp, fun hx => ?_⟩,
    ⟨fun c => by rw [h24 c]; simp, fun hx => ?_⟩⟩
  · -- a point over `t = 1` is `W`-conjugate to the `ℤ[i]` point
    have e := (hcl _ _ P₄ P₄ (hs P₄) (hs P₄)).2.2.1 c₄
    obtain ⟨α, ⟨g⟩⟩ := (hcl _ x P₄ P (hs P₄) hP).1.1 (e.trans (by rw [hx]; simp))
    exact HasCM4.of_iso g ((hasCM4_twist P₄.q α).2 c₄)
  · have e := (hcl _ _ P₃ P₃ (hs P₃) (hs P₃)).2.2.2 c₃
    obtain ⟨α, ⟨g⟩⟩ := (hcl _ x P₃ P (hs P₃) hP).1.1 (e.trans (by rw [hx]; simp))
    exact HasCM3.of_iso g ((hasCM3_twist P₃.q α).2 c₃)
  · have e := (hcl _ _ P₂ P₂ (hs P₂) (hs P₂)).2.1 c₂
    obtain ⟨α, ⟨g⟩⟩ := (hcl _ x P₂ P (hs P₂) hP).1.1 (e.trans (by rw [hx]; simp))
    exact HasCM24.of_iso g ((hasCM24_twist P₂.q α).2 c₂)

/-- **`QMPairsCMExist` is a consequence of `BabaGranathRationalAb`** (proved, no other input): `π` is onto
`P¹(ℚ̄)` by the fibre clause (the chain's `ShimuraSplit.surj_of_fibre`: finite twist classes and `CurveSurj`), and
a point over `t₄` (resp. `t₃`, `t₂₄`) carries a pair with CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) by the converse CM
clauses. So the new leaf is strictly weaker than the field it replaces. -/
theorem qmPairsCMExist_of_babaGranath (h : BabaGranathRationalAb) : QMPairsCMExist := by
  obtain ⟨Y, Φ, X, Ψ, fY, π, t₄, t₃, t₂₄, -, h6, -, -, -, hcl⟩ := h
  have hsurj := ShimuraSplit.surj_of_fibre h6 π fun x x' P Q hP hQ => (hcl x x' P Q hP hQ).1
  have pt : ∀ t : OnePoint ℚ, ∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧
      π.val (K := Qbar) x.left = t.map (algebraMap ℚ Qbar) := by
    intro t
    obtain ⟨x, hx⟩ := hsurj (t.map (algebraMap ℚ Qbar))
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Ψ x)
    exact ⟨x, P, hP.symm, hx⟩
  obtain ⟨x₄, P₄, h₄, v₄⟩ := pt t₄
  obtain ⟨x₃, P₃, h₃, v₃⟩ := pt t₃
  obtain ⟨x₂, P₂, h₂, v₂⟩ := pt t₂₄
  exact ⟨⟨P₄, ((hcl x₄ x₄ P₄ P₄ h₄ h₄).2.1).2 v₄⟩, ⟨P₃, ((hcl x₃ x₃ P₃ P₃ h₃ h₃).2.2.1).2 v₃⟩,
    ⟨P₂, ((hcl x₂ x₂ P₂ P₂ h₂ h₂).2.2.2).2 v₂⟩⟩

/-- **Under Elkies' leaf, `BabaGranathRationalAb` is equivalent to `QMPairsCMExist`.** -/
theorem babaGranathRationalAb_iff (hE : ElkiesEquationsX6Ab) : BabaGranathRationalAb ↔ QMPairsCMExist :=
  ⟨qmPairsCMExist_of_babaGranath, babaGranathRationalAb_of_elkies hE⟩

/-! ## `QMPairsCMExist` from its printed setting over `ℂ` and Shimura–Taniyama -/

/-- **The three elliptic CM pairs exist over `ℂ`** (the printed setting of `QMPairsCMExist`): there are QM
pairs `(A, ι)` over `ℂ` whose commutant `End_𝒪(A)` contains `φ` with `φ² = −1`, resp. `φ² − φ + 1 = 0`, resp.
`φ² = −6`.

LEAF (published, classical; locators UNVERIFIED, no network): Shimura, Ann. of Math. 85 (1967) §§1-3: for
`τ ∈ ℍ`, `A_τ = ℂ²/ι(𝒪)(τ, 1)ᵀ` is an abelian surface with QM by `𝒪` and `End_𝒪(A_τ) = Φ_τ(k) ∩ 𝒪`
(the same source as the bundle's `QMCentralizerCMC`); at the fixed point `τ` of `ι(i + j)`, `ι((1 + j)/2)`,
`ι(2j + k)` (elements of `𝒪` with reduced characteristic polynomials `x² + 1`, `x² − x + 1`, `x² + 6`; Eichler,
Vignéras LNM 800 Ch. III §5) the commutant contains the corresponding element. A consequence, never stronger:
one pair of each kind. -/
def QMPairsCMExistC : Prop :=
  (∃ P : QMPair ℂ, HasCM4 P.q) ∧ (∃ P : QMPair ℂ, HasCM3 P.q) ∧ (∃ P : QMPair ℂ, HasCM24 P.q)

open HDec.HSyn.G0Split.FibreQM.PeriodMapH in
/-- **Descent of a CM QM pair from `ℂ` to `ℚ̄`** (glue, proved): by Shimura–Taniyama (the bundle field
`shimuraTaniyamaQbar`, through the chain's `stQM_lf7`) `A ≅ A₀ ×_{ℚ̄, ιe} ℂ`; by T11(b) (proved,
`t11b_of_exists t11bExists_lf8`) every endomorphism of the base change comes from `A₀`, so conjugating by the isomorphism
gives a ring map `κ : End A → End A₀` with `κ ∘ ι` a QM structure on `A₀`. -/
theorem descend_pair (hST : QMSplitSTQM.ShimuraTaniyamaQbar) (P : QMPair ℂ)
    (hcm : HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) :
    ∃ (P₀ : QMPair Qbar) (κ : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End P₀.A),
      ∀ a, κ (P.q.iota a) = P₀.q.iota a := by
  have hR := HDec.AVB2.t11b_of_exists HDec.HSyn.t11bExists_lf8
  obtain ⟨ιe, A₀, e, e', h1, h2⟩ := HDec.HSyn.stQM_lf7 hST P.A P.q P.surface hcm
  let β := RingEquiv.ofBijective (LeafQCheck.endBCe ιe A₀) (LeafQCheck.endBCe_bijective ιe A₀ hR)
  let κ : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End A₀ :=
    β.symm.toRingHom.comp (LeafQCheck.conjE e e' h1 h2)
  have κinj : Function.Injective κ := β.symm.injective.comp (LeafQCheck.conjE_injective e e' h1 h2)
  have hdim : A₀.dim = 2 := by
    have := LeafQCheck.dim_eq_of_iso e e' h1 h2
    rw [← P.surface, ← this]
    exact (@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).symm
  exact ⟨⟨A₀, hdim, ⟨κ.comp P.q.iota, κinj.comp P.q.injective⟩⟩, κ, fun a => rfl⟩

/-- A ring map compatible with the QM structures maps the commutant into the commutant. -/
theorem map_mem_com {K L : Type} [Field K] [Field L] {A : PkgI3.AbVar K} {B : PkgI3.AbVar L}
    {q : QMStr A} {q' : QMStr B} (κ : PkgI3.AbVar.End A →+* PkgI3.AbVar.End B)
    (hκ : ∀ a, κ (q.iota a) = q'.iota a) {φ : PkgI3.AbVar.End A} (hφ : φ ∈ com q) : κ φ ∈ com q' := by
  rw [com, Subring.mem_centralizer_iff] at hφ ⊢
  rintro _ ⟨a, rfl⟩
  rw [← hκ, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]

/-- **`QMPairsCMExist` from `QMPairsCMExistC` and Shimura–Taniyama** (glue, proved). -/
theorem qmPairsCMExist_of_C (hC : QMPairsCMExistC) (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar) :
    QMPairsCMExist := by
  obtain ⟨⟨P₄, φ₄, m₄, e₄⟩, ⟨P₃, φ₃, m₃, e₃⟩, ⟨P₂, φ₂, m₂, e₂⟩⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨P, κ, hκ⟩ := descend_pair hST P₄ (Or.inl ⟨φ₄, m₄, e₄⟩)
    exact ⟨P, κ φ₄, map_mem_com κ hκ m₄, by rw [← map_mul, e₄, map_neg, map_one]⟩
  · obtain ⟨P, κ, hκ⟩ := descend_pair hST P₃ (Or.inr (Or.inl ⟨φ₃, m₃, e₃⟩))
    exact ⟨P, κ φ₃, map_mem_com κ hκ m₃, by
      rw [← map_mul, ← map_sub, ← map_one κ, ← map_add, e₃, map_zero]⟩
  · obtain ⟨P, κ, hκ⟩ := descend_pair hST P₂ (Or.inr (Or.inr ⟨φ₂, m₂, e₂⟩))
    exact ⟨P, κ φ₂, map_mem_com κ hκ m₂, by rw [← map_mul, e₂, map_neg, map_ofNat]⟩

/-- **`BabaGranathRationalAb` from Elkies' leaf, Shimura–Taniyama (both bundle fields) and the printed-setting
CM existence `QMPairsCMExistC`** (gt-x6facts; the form for the fold). -/
theorem babaGranathRationalAb_of_printed (hE : ElkiesEquationsX6Ab)
    (hST : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar) (hC : QMPairsCMExistC) :
    BabaGranathRationalAb :=
  babaGranathRationalAb_of_elkies hE (qmPairsCMExist_of_C hC hST)

end HDec.QMSplit.Moduli.X6Facts

#print axioms HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_of_elkies
#print axioms HDec.QMSplit.Moduli.X6Facts.qmPairsCMExist_of_C
#print axioms HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_iff
#print axioms HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_of_printed
