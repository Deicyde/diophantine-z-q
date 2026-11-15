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

end HDec.QMSplit.Moduli.X6Facts

#print axioms HDec.QMSplit.Moduli.X6Facts.babaGranathRationalAb_of_elkies
