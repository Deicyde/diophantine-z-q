import ZInQKernel.HDecomp.QM.Leaves

/-!
# mobius-glue: the `π`-half of qm-pin's comparison of two triples

Task mobius-glue (2026-11-13). See `docs/research/mobius-glue.md`.

`LeafQM.AV.Pin.MobiusGlue` (qm-pin §3.2, copied verbatim from `scratch/qm-pin/QMPin.lean`
together with the definitions it uses) is proved here from three named facts:

* `CurveRatFactor` (curves): on a proper smooth curve over `ℚ`, a morphism `ρ` to `P¹` that is
  constant on the fibres of a morphism `σ` to `P¹` is a rational function of `σ` on `ℚ̄`-points;
* `CurveSurj` (curves): a morphism to `P¹` with finite fibres on `ℚ̄`-points, from a proper
  smooth curve over `ℚ` with a `ℚ̄`-point, is onto `P¹(ℚ̄)`;
* `TwistClassFinite` (moduli): a twist class of level-3 objects over `ℚ̄` contains only
  finitely many isomorphism classes.

Compiled here: an injective rational function on an algebraically closed field of
characteristic 0 has degree at most one (`natDegree_le_one_of_injective`, Wronskian argument); a
rational function of degree at most one without finite pole fixing `0` and `c ≠ 0` is the
identity (`ratEval_eq_self`; together: a Möbius map fixing `0, ∞, c` is the identity); and the
reduction `mobiusGlue_of_curveFacts`. No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ## §0 The definitions of qm-pin (copied verbatim from `scratch/qm-pin/QMPin.lean`) -/


/-- **A family of level-3 QM abelian surfaces over a scheme `S`** (the data of an object of the
moduli problem over `S`, without the group law, which rigidity recovers): a scheme `𝒜 → S`,
proper and smooth of relative dimension 2, with endomorphisms `ι(a)` over `S` (`a ∈ 𝒪`) and
sections `η(a) : S → 𝒜` (`a ∈ 𝒪`; for the universal object, the images of the constant sections
under the level structure `(𝒪/3𝒪)_S ≅ 𝒜[3]`). -/
structure QMFamily (S : Scheme.{0}) where
  F : Over S
  proper : IsProper F.hom
  smooth : SmoothOfRelativeDimension 2 F.hom
  iota : O → (F.left ⟶ F.left)
  iota_over : ∀ a : O, iota a ≫ F.hom = F.hom
  eta : O → (S ⟶ F.left)
  eta_sec : ∀ a : O, eta a ≫ F.hom = 𝟙 S

/-- **`P` is the fibre of the family `𝒜` at the field point `y : Spec K → S`**: a morphism
`g : P.A → 𝒜` making `P.A → Spec K` the pullback of `𝒜 → S` along `y`, carrying `ι_P` to `ι_𝒜`
and the level points `η_P(a)` to the sections `η_𝒜(a)` (same shape as `IsBaseChangeOf`). -/
def IsFibreOf {S : Scheme.{0}} (𝒜 : QMFamily S) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) (P : QML3 K) : Prop :=
  ∃ g : P.A.X.left ⟶ 𝒜.F.left,
    IsPullback g P.A.X.hom 𝒜.F.hom y ∧
    (∀ a : O, (P.q.iota a).hom.left ≫ g = g ≫ 𝒜.iota a) ∧
    (∀ a : O, (Additive.toMul (P.e.eta a)).left ≫ g = y ≫ 𝒜.eta a)

/-- **R1fam, clause**: `Φ` is induced by a family: there is a family `𝒜` over `Y` (the universal
object of R1(a), polarization forgotten) such that the class `Φ_K(y)` of every field point is
the class of the fibre `y*𝒜`. -/
def R1famProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∃ 𝒜 : QMFamily Y.left, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
    Φ K y = M3.mk P → IsFibreOf 𝒜 y.left P

/-- **R1fp, repaired clause list** (to replace `LeafQM.AV.R1fpProps`): the four old clauses and
`R1famProps`. -/
def R1fpPropsPin (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ

/-- **R1univ, clause** (the existence half of R1(a)'s universal property, on families over proper
smooth curves `S/ℚ`): every family over `S` all of whose field fibres are objects is classified by
a morphism `g : S → Y`: the class of the object at `s ≫ g` is the fibre at `s`. -/
def R1univProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ 𝒜' : QMFamily S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜' s.left P) →
      ∃ g : S ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S) (P : QML3 K),
        IsFibreOf 𝒜' s.left P → Φ K (s ≫ g) = M3.mk P

/-- The fully repaired clause list: family and universal property. -/
def R1fpPropsU (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  R1fpPropsPin Y Φ ∧ R1univProps Y Φ

/-- **Glue (not compiled; argued in the report §3.4).** Given a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g`, and CM objects of the three kinds, the two morphisms `π'` and `π ∘ g` to `P¹`
agree on `ℚ̄`-points: they have the same fibres (both `R2fpProps`), so `π' = h ∘ π ∘ g` with `h`
a bijection of `P¹(ℚ̄)` which is a morphism (graph argument on each geometric component of
`Y'`), hence a Möbius map, and `h` fixes `0, ∞, −16/27`. Algebraic geometry of curves. -/
def MobiusGlue : Prop :=
  ∀ (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) (g : Y' ⟶ Y),
    R1fpPropsU Y Φ → R2fpProps Y Φ π → R1fpPropsU Y' Φ' → R2fpProps Y' Φ' π' →
    ((∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) →
    (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g)) →
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

/-! ## §1 Rational functions on `P¹`: an injective one is a Möbius map -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]


open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

theorem eval_ne_zero_of_coprime {F G : K[X]} (h : IsCoprime F G) {a : K} (hG : G.eval a = 0) :
    F.eval a ≠ 0 := by
  intro hF
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Polynomial.eval a) huv
  simp [eval_add, eval_mul, hF, hG] at this

/-- The Wronskian `F' G - F G'` of a coprime pair of which one has positive degree is nonzero
(characteristic 0). -/
theorem wronskian_ne_zero [CharZero K] {F G : K[X]} (h : IsCoprime F G)
    (hdeg : F.natDegree ≠ 0 ∨ G.natDegree ≠ 0) :
    derivative F * G - F * derivative G ≠ 0 := by
  intro hW
  have hW' : derivative F * G = F * derivative G := sub_eq_zero.mp hW
  have key : ∀ {P Q : K[X]}, IsCoprime P Q → P ∣ derivative P * Q → P.natDegree = 0 := by
    intro P Q hPQ hd
    have hd' : P ∣ derivative P := hPQ.dvd_of_dvd_mul_right hd
    by_contra hP
    have hne : derivative P ≠ 0 := derivative_ne_zero.mpr hP
    have h1 := natDegree_le_of_dvd hd' hne
    have h2 := natDegree_derivative_lt hP
    omega
  have hF : F.natDegree = 0 := key h ⟨derivative G, hW'⟩
  have hG : G.natDegree = 0 := key h.symm ⟨derivative F, by rw [mul_comm, ← hW', mul_comm]⟩
  rcases hdeg with hdeg | hdeg <;> contradiction

/-- **An injective rational function has degree at most one** (algebraically closed field of
characteristic 0). -/
theorem natDegree_le_one_of_injective [IsAlgClosed K] [CharZero K] {F G : K[X]}
    (hcop : IsCoprime F G) (hinj : ∀ s t : K, ratEval F G s = ratEval F G t → s = t) :
    F.natDegree ≤ 1 ∧ G.natDegree ≤ 1 := by
  classical
  by_contra hcon
  set n := max F.natDegree G.natDegree with hn_def
  have hn : 2 ≤ n := by
    rw [not_and_or] at hcon
    rcases hcon with h | h <;> omega
  set W := derivative F * G - F * derivative G with hW_def
  have hW : W ≠ 0 := wronskian_ne_zero hcop (by omega)
  -- the good values of `c`
  set S : Set K := {c | F.coeff n - c * G.coeff n ≠ 0} with hS_def
  have hS : S.Infinite := by
    have hsub : Sᶜ.Subsingleton := by
      intro c hc d hd
      simp only [hS_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hc hd
      by_cases hG : G.coeff n = 0
      · have hF : F.coeff n ≠ 0 := by
          rcases le_total F.natDegree G.natDegree with h | h
          · have hnG : n = G.natDegree := by omega
            have : G.natDegree ≠ 0 := by omega
            rw [hnG] at hG
            exact absurd (leadingCoeff_eq_zero.mp hG) (by rintro rfl; simp at this)
          · have hnF : n = F.natDegree := by omega
            have : F.natDegree ≠ 0 := by omega
            rw [hnF]
            intro h0
            exact absurd (leadingCoeff_eq_zero.mp h0) (by rintro rfl; simp at this)
        rw [hG, mul_zero, sub_zero] at hc
        exact absurd hc hF
      · have e1 : c = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hc
        have e2 : d = F.coeff n / G.coeff n := by rw [eq_div_iff hG]; linear_combination -hd
        rw [e1, e2]
    have := hsub.finite.infinite_compl
    rwa [compl_compl] at this
  -- every good `c` is the value at a root of `W`
  have hgood : ∀ c ∈ S, ∃ a, W.IsRoot a ∧ F.eval a / G.eval a = c := by
    intro c hc
    set H := F - C c * G with hH_def
    have hHn : H.natDegree = n := by
      apply natDegree_eq_of_le_of_coeff_ne_zero
      · refine (natDegree_sub_le _ _).trans (max_le (le_max_left _ _) ?_)
        exact (natDegree_C_mul_le _ _).trans (le_max_right _ _)
      · have hc' : F.coeff n - c * G.coeff n ≠ 0 := hc
        simpa [hH_def, coeff_sub, coeff_C_mul] using hc'
    have hH0 : H ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hHn; omega
    -- a root of `H` has value `c`
    have hval : ∀ b, H.IsRoot b → G.eval b ≠ 0 ∧ F.eval b / G.eval b = c := by
      intro b hb
      have hb' : F.eval b = c * G.eval b := by
        have := hb; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
        linear_combination this
      have hGb : G.eval b ≠ 0 := by
        intro h0
        exact eval_ne_zero_of_coprime hcop h0 (by rw [hb', h0, mul_zero])
      exact ⟨hGb, by rw [hb']; field_simp⟩
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root H (by
      rw [degree_eq_natDegree hH0]; exact_mod_cast (by omega : H.natDegree ≠ 0))
    obtain ⟨hGa, hFa⟩ := hval a ha
    -- all roots of `H` are `a`
    have hall : ∀ b ∈ H.roots, a = b := by
      intro b hb
      have hb' := (mem_roots hH0).mp hb
      obtain ⟨hGb, hFb⟩ := hval b hb'
      apply hinj
      simp only [ratEval, hGa, hGb, ite_false, hFa, hFb]
    have hcount : H.roots.count a = n := by
      rw [Multiset.count_eq_card.mpr hall, IsAlgClosed.card_roots_eq_natDegree, hHn]
    have hmult : 1 < H.rootMultiplicity a := by
      rw [← count_roots]; convert (show 1 < n by omega) using 2
    obtain ⟨-, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot hH0).mp hmult
    refine ⟨a, ?_, hFa⟩
    have hd' : (derivative F).eval a = c * (derivative G).eval a := by
      have := hd
      simp only [IsRoot, hH_def, derivative_sub, derivative_mul, derivative_C, zero_mul,
        zero_add, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    have ha' : F.eval a = c * G.eval a := by
      have := ha; simp only [IsRoot, hH_def, eval_sub, eval_mul, eval_C] at this
      linear_combination this
    simp only [IsRoot, hW_def, eval_sub, eval_mul, hd', ha']
    ring
  -- so the good values lie in a finite set
  have hfin : S.Finite := by
    refine ((W.roots.toFinset.finite_toSet).image (fun a => F.eval a / G.eval a)).subset ?_
    intro c hc
    obtain ⟨a, ha, rfl⟩ := hgood c hc
    exact ⟨a, by simpa [Multiset.mem_toFinset, mem_roots hW] using ha, rfl⟩
  exact hS hfin


/-- **A rational function of degree at most one with no finite pole, fixing `0` and some
`c ≠ 0`, is the identity on `K`.** (With `∞ ↦ ∞`, which "no finite pole" encodes: a Möbius map
fixing `0, ∞, c` is the identity.) -/
theorem ratEval_eq_self [IsAlgClosed K] {F G : K[X]} (hF1 : F.natDegree ≤ 1)
    (hpole : ∀ t, ratEval F G t ≠ OnePoint.infty) (h0 : ratEval F G 0 = OnePoint.some 0)
    {c : K} (hc : c ≠ 0) (hcc : ratEval F G c = OnePoint.some c) :
    ∀ t, ratEval F G t = OnePoint.some t := by
  classical
  have hGne : ∀ t, G.eval t ≠ 0 := fun t ht => hpole t (by simp [ratEval, ht])
  have hG0 : G.natDegree = 0 := by
    by_contra h
    have hG : G ≠ 0 := by rintro rfl; simp at h
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root G (by
      rw [degree_eq_natDegree hG]; exact_mod_cast h)
    exact hGne a ha
  have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero hG0
  have hFX : F = C (F.coeff 1) * X + C (F.coeff 0) := eq_X_add_C_of_natDegree_le_one hF1
  have hd : G.coeff 0 ≠ 0 := by
    have := hGne 0; rwa [hGC, eval_C] at this
  have hval : ∀ t, ratEval F G t =
      OnePoint.some ((F.coeff 1 * t + F.coeff 0) / G.coeff 0) := by
    intro t
    simp only [ratEval, hGne t, ite_false]
    congr 1
    conv_lhs => rw [hFX, hGC]
    simp
  have hb : F.coeff 0 = 0 := by
    have := h0; rw [hval, OnePoint.coe_eq_coe] at this
    simpa [hd] using this
  have ha : F.coeff 1 = G.coeff 0 := by
    have := hcc; rw [hval, OnePoint.coe_eq_coe, hb, add_zero, div_eq_iff hd] at this
    exact mul_right_cancel₀ hc (by rw [this, mul_comm])
  intro t
  rw [hval, hb, ha, add_zero, mul_div_cancel_left₀ _ hd]

end Mob

/-! ## §2 The named facts -/

open Polynomial in
/-- **Curve fact 1 (factorization through a rational function).** On a proper smooth curve
`S/ℚ`, if `ρ : S → P¹` is constant on the fibres of `σ : S → P¹` (on `ℚ̄`-points), then
`ρ = R ∘ σ` on `ℚ̄`-points with finite `σ`-value, for a rational function `R = [F : G]`,
`F, G ∈ ℚ̄[t]` coprime. (On a geometric component `C` where `σ` is nonconstant: the image of
`(σ, ρ) : C → P¹ × P¹` projects bijectively, hence birationally (char. 0), onto the normal
curve `P¹`, so its inverse is a morphism and `R = pr₂ ∘ pr₁⁻¹`; components where `σ` is
constant are absorbed by the fibre condition, or by Lagrange interpolation if every component
is. STANDARD; not in Mathlib.) -/
def CurveRatFactor : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    ∀ σ ρ : ToP1 S.left,
      (∀ y₁ y₂ : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left →
        ρ.val (K := Qbar) y₁.left = ρ.val (K := Qbar) y₂.left) →
      ∃ F G : Qbar[X], IsCoprime F G ∧ ∀ (y : fieldPt Qbar ⟶ S) (t : Qbar),
        σ.val (K := Qbar) y.left = OnePoint.some t → ρ.val (K := Qbar) y.left = Mob.ratEval F G t

/-- **Curve fact 2 (surjectivity).** A morphism `σ : S → P¹` from a proper smooth curve `S/ℚ`
with a `ℚ̄`-point, whose fibres on `ℚ̄`-points are finite, is onto `P¹(ℚ̄)`. (The geometric
component through the given point has infinitely many `ℚ̄`-points, so `σ` is nonconstant on
it; its image is closed and irreducible, hence `P¹`; closed points of `P¹_ℚ̄` lift to
`ℚ̄`-points. STANDARD, e.g. Hartshorne II.6.8; not in Mathlib.) -/
def CurveSurj : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    Nonempty (fieldPt Qbar ⟶ S) → ∀ σ : ToP1 S.left,
      (∀ y : fieldPt Qbar ⟶ S, {y' : fieldPt Qbar ⟶ S |
        σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite) →
      ∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ S, σ.val (K := Qbar) y.left = t

/-- **Moduli fact (finite twist classes).** For a level-3 object `P` over `ℚ̄`, only finitely
many isomorphism classes `[Q]` have `(Q.A, Q.ι)` isomorphic to an `Aut(𝒪)`-twist of
`(P.A, P.ι)`. (The twists of a pair by `α` and by `α ∘ (conjugation by a unit)` are isomorphic
through `ι(u)`, and `Aut(𝒪)` modulo these is the finite group `N(𝒪)/ℚ^×𝒪^×` (Skolem–Noether);
for a fixed pair, `η` is determined by `η(1) ∈ A[3](ℚ̄)`, a finite group. STANDARD; not in
Mathlib.) -/
def TwistClassFinite : Prop :=
  ∀ P : QML3 Qbar, {m : M3 Qbar | ∃ Q : QML3 Qbar, m = M3.mk Q ∧
    ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}.Finite

/-! ## §3 The reduction -/

/-- **`MobiusGlue` from the two curve facts and the moduli fact.** -/
theorem mobiusGlue_of_curveFacts (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : TwistClassFinite) : MobiusGlue := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg y
  set σ : ToP1 Y'.left := π.comp g.left with hσ_def
  have hσ : ∀ y : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y.left =
      π.val (K := Qbar) (y ≫ g).left := by
    intro y; exact ToP1.val_comp_right π g.left y.left
  rw [← hσ]
  -- representatives
  have hout : ∀ y : fieldPt Qbar ⟶ Y', Φ' Qbar y = M3.mk (Quotient.out (Φ' Qbar y)) :=
    fun y => (Quotient.out_eq _).symm
  -- the two maps have the same fibres
  have hrel : ∀ y₁ y₂ : fieldPt Qbar ⟶ Y', σ.val (K := Qbar) y₁.left = σ.val (K := Qbar) y₂.left
      ↔ π'.val (K := Qbar) y₁.left = π'.val (K := Qbar) y₂.left := by
    intro y₁ y₂
    rw [hσ, hσ, (h2 (y₁ ≫ g) (y₂ ≫ g) _ _ ((hg Qbar y₁).symm.trans (hout y₁))
      ((hg Qbar y₂).symm.trans (hout y₂))).1, (h2' y₁ y₂ _ _ (hout y₁) (hout y₂)).1]
  -- CM points of `Y'` and the values there
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂, c₂⟩⟩ := hCM
  have hpt : ∀ P : QML3 Qbar, Φ' Qbar ((Φ' Qbar).symm (M3.mk P)) = M3.mk P :=
    fun P => (Φ' Qbar).apply_symm_apply _
  set y₄ := (Φ' Qbar).symm (M3.mk P₄)
  set y₃ := (Φ' Qbar).symm (M3.mk P₃)
  set y₂ := (Φ' Qbar).symm (M3.mk P₂)
  have hY : ∀ y : fieldPt Qbar ⟶ Y', ∀ P : QML3 Qbar, Φ' Qbar y = M3.mk P →
      Φ Qbar (y ≫ g) = M3.mk P := fun y P hP => (hg Qbar y).symm.trans hP
  have σ₄ : σ.val (K := Qbar) y₄.left = OnePoint.some 0 := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₄)) (hY _ _ (hpt P₄))).2.1 c₄
  have π₄ : π'.val (K := Qbar) y₄.left = OnePoint.some 0 :=
    (h2' _ _ _ _ (hpt P₄) (hpt P₄)).2.1 c₄
  have σ₃ : σ.val (K := Qbar) y₃.left = OnePoint.infty := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₃)) (hY _ _ (hpt P₃))).2.2.1 c₃
  have π₃ : π'.val (K := Qbar) y₃.left = OnePoint.infty :=
    (h2' _ _ _ _ (hpt P₃) (hpt P₃)).2.2.1 c₃
  have σ₂ : σ.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) := by
    rw [hσ]; exact (h2 _ _ _ _ (hY _ _ (hpt P₂)) (hY _ _ (hpt P₂))).2.2.2 c₂
  have π₂ : π'.val (K := Qbar) y₂.left = OnePoint.some (-16 / 27) :=
    (h2' _ _ _ _ (hpt P₂) (hpt P₂)).2.2.2 c₂
  -- finite fibres
  have hfin : ∀ y : fieldPt Qbar ⟶ Y', {y' : fieldPt Qbar ⟶ Y' |
      σ.val (K := Qbar) y'.left = σ.val (K := Qbar) y.left}.Finite := by
    intro y
    refine ((hT (Quotient.out (Φ' Qbar y))).preimage
      (Set.injOn_of_injective (Φ' Qbar).injective)).subset ?_
    intro y' hy'
    have e : π'.val (K := Qbar) y.left = π'.val (K := Qbar) y'.left :=
      ((hrel y' y).1 hy').symm
    exact ⟨_, hout y', ((h2' y y' _ _ (hout y) (hout y')).1).1 e⟩
  obtain ⟨⟨hprop', hsmooth', hne', -, -⟩, -⟩ := h1'
  have hsurj := hSu Y' hprop' hsmooth' hne' σ hfin
  obtain ⟨F, G, hcop, hFG⟩ := hRF Y' hprop' hsmooth' σ π' (fun y₁ y₂ h => (hrel y₁ y₂).1 h)
  -- the rational function is injective, has no finite pole, and fixes `0` and `-16/27`
  have hinj : ∀ s t : Qbar, Mob.ratEval F G s = Mob.ratEval F G t → s = t := by
    intro s t hst
    obtain ⟨ys, hys⟩ := hsurj (OnePoint.some s)
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) ys.left = π'.val (K := Qbar) yt.left := by
      rw [hFG ys s hys, hFG yt t hyt, hst]
    have := (hrel ys yt).2 e
    rw [hys, hyt] at this
    exact OnePoint.coe_injective this
  have hdeg := Mob.natDegree_le_one_of_injective hcop hinj
  have hpole : ∀ t, Mob.ratEval F G t ≠ OnePoint.infty := by
    intro t ht
    obtain ⟨yt, hyt⟩ := hsurj (OnePoint.some t)
    have e : π'.val (K := Qbar) yt.left = π'.val (K := Qbar) y₃.left := by
      rw [hFG yt t hyt, ht, π₃]
    have := (hrel yt y₃).2 e
    rw [hyt, σ₃] at this
    exact OnePoint.coe_ne_infty t this
  have h0 : Mob.ratEval F G 0 = OnePoint.some 0 := by rw [← hFG y₄ 0 σ₄, π₄]
  have hc : Mob.ratEval F G (-16 / 27) = OnePoint.some (-16 / 27) := by
    rw [← hFG y₂ _ σ₂, π₂]
  have hid := Mob.ratEval_eq_self hdeg.1 hpole h0 (by norm_num) hc
  -- conclusion
  by_cases hinf : σ.val (K := Qbar) y.left = OnePoint.infty
  · rw [hinf]
    rw [← π₃]
    exact (hrel y y₃).1 (by rw [hinf, σ₃])
  · obtain ⟨t, ht⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← ht, hFG y t ht.symm, hid t]

/-! ## §4 `TwistClassFinite` from the textbook leaf `TorsionStructure` (T5) and an algebra fact -/

/-- **Algebra fact (finiteness of `Aut(𝒪)` modulo inner automorphisms by units).** Every ring
automorphism of `𝒪` is, up to conjugation by a unit of `𝒪`, one of finitely many. (Every
automorphism of `𝒪` extends to `B = 𝒪 ⊗ ℚ`, hence is conjugation by some `x ∈ N(𝒪)`
(Skolem–Noether), and `N(𝒪)/ℚ^×𝒪^×` is finite: for the maximal order of the quaternion algebra
of discriminant 6 it is the Atkin–Lehner group `W ≅ (ℤ/2)²`. STANDARD (Vignéras, *Arithmétique
des algèbres de quaternions*; locator UNVERIFIED); not in Mathlib.) A statement about the concrete
order `O` of the kernel only. -/
def AutOInnerFinite : Prop :=
  ∃ T : Set (O ≃+* O), T.Finite ∧ ∀ α : O ≃+* O, ∃ t ∈ T, ∃ v : Oˣ,
    ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)

section FiniteTwist

variable {K : Type} [Field K]

/-- Every element of `𝒪` is congruent modulo `3𝒪` to some `liftO c`, `c ∈ (ℤ/3)⁴`. -/
theorem exists_liftO_congr (u : O) : ∃ c : Fin 4 → ZMod 3, ∃ k : O, u - liftO c = 3 * k := by
  obtain ⟨n, hn⟩ := u.2
  refine ⟨fun i => (n i : ZMod 3), ⟨ofInt (fun i => n i / 3), ⟨_, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33, liftO]
  rw [hn, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast, Nat.cast_ofNat]
  omega

/-- **Finitely many level structures on one `(A, ι)`** (characteristic 0, given the leaf
`TorsionStructure`): by the kernel's torsor glue `Level3.torsor`, a level structure is
`a ↦ η₀(a u₀)`, which depends only on `u₀ mod 3𝒪`. -/
theorem level3_finite (hT : ObjBridge.TorsionStructure) [CharZero K] {A : AbVar K}
    (s : A.dim = 2) (q : QMStr A) : Finite (Level3 q) := by
  rcases isEmpty_or_nonempty (Level3 q) with h | h
  · infer_instance
  · obtain ⟨e₀⟩ := h
    have key : ∀ e : Level3 q, ∃ c : Fin 4 → ZMod 3, ∀ a : O,
        e.eta a = e₀.eta (a * liftO c) := by
      intro e
      obtain ⟨u₀, -, -, hu⟩ := Level3.torsor hT ⟨A, s, q, e₀⟩ e
      obtain ⟨c, k, hk⟩ := exists_liftO_congr u₀
      refine ⟨c, fun a => (hu a).trans ((e₀.eq_iff _ _).2 ⟨a * k, ?_⟩)⟩
      calc a * u₀ - a * liftO c = a * (u₀ - liftO c) := by noncomm_ring
        _ = a * (3 * k) := by rw [hk]
        _ = 3 * (a * k) := by noncomm_ring
    choose f hf using key
    refine Finite.of_injective f fun e e' h => Level3.ext' ?_
    ext a
    rw [hf e a, hf e' a, h]

/-- Transport of a level structure along an isomorphism of QM pairs. -/
def transportLevel {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (e : Level3 q) : Level3 q' where
  eta := (AbVar.ptMap (L := K) f.φ).toAdditive.comp e.eta
  linear a b := by
    change Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ f.φ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ f.φ.hom) ≫ (q'.iota a).hom)
    rw [e.linear]
    change Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q.iota a).hom) ≫ f.φ.hom) = _
    rw [Category.assoc, f.equivariant a, Category.assoc]
  ker a := by
    rw [← e.ker]
    constructor
    · intro h
      have h' : Additive.toMul (e.eta a) ≫ f.φ.hom = 1 := congrArg Additive.toMul h
      have : Additive.toMul (e.eta a) = 1 := by
        calc Additive.toMul (e.eta a) = Additive.toMul (e.eta a) ≫ f.φ.hom ≫ f.ψ.hom := by
              rw [f.left, Category.comp_id]
          _ = 1 := by rw [← Category.assoc, h', MonObj.one_comp]
      exact congrArg Additive.ofMul this
    · intro h
      change Additive.ofMul (Additive.toMul (e.eta a) ≫ f.φ.hom) = 0
      rw [h]
      change Additive.ofMul ((1 : _ ⟶ _) ≫ f.φ.hom) = 0
      rw [MonObj.one_comp]
      rfl

/-- An object is isomorphic to the transport of its level structure. -/
def QML3.isoTransport (Q : QML3 K) {A' : AbVar K} (s' : A'.dim = 2) {q' : QMStr A'}
    (f : QMIso Q.q q') : Q.Iso ⟨A', s', q', transportLevel f Q.e⟩ where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant := f.equivariant
  level _ := rfl

/-- Twists by `t` and by `v t v⁻¹` (`v ∈ 𝒪^×`) are isomorphic through `ι(v)`. -/
def conjUnitIso {A : AbVar K} (q : QMStr A) (t α : O ≃+* O) (v : Oˣ)
    (hv : ∀ a, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)) : QMIso (q.twist t) (q.twist α) where
  φ := q.iota v
  ψ := q.iota ↑v⁻¹
  left := by
    have : q.iota ↑v⁻¹ * q.iota ↑v = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    exact congrArg AbVar.Hom.hom this
  right := by
    have : q.iota ↑v * q.iota ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    exact congrArg AbVar.Hom.hom this
  equivariant a := by
    have : q.iota (v : O) * q.iota (t a) = q.iota (α a) * q.iota v := by
      rw [← map_mul, ← map_mul, hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    exact congrArg AbVar.Hom.hom this

/-- **`TwistClassFinite` from the leaf `TorsionStructure` and `AutOInnerFinite`.** -/
theorem twistClassFinite_of (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) :
    TwistClassFinite := by
  obtain ⟨T, hTfin, hTα⟩ := hA
  intro P
  let R : (O ≃+* O) → Set (M3 Qbar) := fun t =>
    Set.range (fun e : Level3 (P.q.twist t) => M3.mk ⟨P.A, P.surface, P.q.twist t, e⟩)
  have hR : ∀ t, (R t).Finite := fun t => by
    have := level3_finite hT P.surface (P.q.twist t)
    exact Set.finite_range _
  refine (hTfin.biUnion fun t _ => hR t).subset ?_
  rintro m ⟨Q, rfl, α, ⟨f⟩⟩
  obtain ⟨t, ht, v, hv⟩ := hTα α
  let h : QMIso Q.q (P.q.twist t) := ((conjUnitIso P.q t α v hv).trans f).symm
  refine Set.mem_biUnion ht ⟨transportLevel h Q.e, ?_⟩
  exact Quotient.sound ⟨(QML3.isoTransport Q P.surface h).symm⟩

end FiniteTwist

/-! ## §5 The result -/

/-- **`MobiusGlue` from two curve facts, the textbook leaf `TorsionStructure` (T5, Mumford §4)
and the algebra fact `AutOInnerFinite`.** -/
theorem mobiusGlue_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) : MobiusGlue :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite_of hT hA)

/-! ## §6 Downstream: the comparison and the transfer of fibre statements, now from named facts

The next five declarations are copied verbatim from `scratch/qm-pin/QMPin.lean` §4. -/

/-- **The `Φ`-half of the comparison (compiled).** If `(Y, Φ)` has the universal property and
`(Y', Φ')` satisfies the repaired clause list, then `Φ' = Φ ∘ g` for a morphism `g : Y' → Y`. -/
theorem phi_part {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univProps Y Φ) (h1' : R1fpPropsPin Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜' s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm


/-- `SameTriple` with a morphism in place of an isomorphism (all the transfer needs). -/
def SameTripleMor (Y Y' : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Φ' : PtEquiv Y')
    (π : ToP1 Y.left) (π' : ToP1 Y'.left) : Prop :=
  ∃ g : Y' ⟶ Y, (∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g)) ∧
    ∀ y : fieldPt Qbar ⟶ Y', π'.val (K := Qbar) y.left = π.val (K := Qbar) (y ≫ g).left

theorem transfer_pointwise_mor {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (hS : SameTripleMor Y Y' Φ Φ' π π') (t : OnePoint Qbar) (R : QML3 Qbar → Prop)
    (h : ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = t → R P) :
    ∀ (y' : fieldPt Qbar ⟶ Y') (P : QML3 Qbar), Φ' Qbar y' = M3.mk P →
      π'.val (K := Qbar) y'.left = t → R P := by
  obtain ⟨g, hΦ, hπ⟩ := hS
  intro y' P hP ht
  exact h (y' ≫ g) P ((hΦ Qbar y').symm.trans hP) ((hπ y').symm.trans ht)

/-- **The comparison from `R1univProps` and `MobiusGlue` (compiled).** -/
theorem sameTripleMor_of_mobius (hM : MobiusGlue)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (h1 : R1fpPropsU Y Φ) (h2 : R2fpProps Y Φ π) (h1' : R1fpPropsU Y' Φ')
    (h2' : R2fpProps Y' Φ' π') : SameTripleMor Y Y' Φ Φ' π π' := by
  obtain ⟨g, hg⟩ := phi_part h1.2 h1'.1
  exact ⟨g, hg, hM Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hg⟩

/-- **Pieces from the witness, with `R1univProps` (compiled).** A fibre statement proved for one
triple satisfying the fully repaired list holds for every such triple, given `MobiusGlue` and CM
objects (the latter from the leaves: `CMExists` and `X6Surj`). -/
theorem pointwise_of_witness_mor (hM : MobiusGlue)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpPropsU Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
    (R : OnePoint Qbar → QML3 Qbar → Prop)
    (h : ∀ t (y : fieldPt Qbar ⟶ Y₀) (P : QML3 Qbar), Φ₀ Qbar y = M3.mk P →
      π₀.val (K := Qbar) y.left = t → R t P) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsU Y Φ → R2fpProps Y Φ π →
      ∀ t (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        π.val (K := Qbar) y.left = t → R t P :=
  fun _ _ _ h1' h2' t =>
    transfer_pointwise_mor (sameTripleMor_of_mobius hM hCM h1 h2 h1' h2') t (R t) (h t)


/-- **The comparison of two triples from the named facts.** -/
theorem sameTripleMor_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    {π : ToP1 Y.left} {π' : ToP1 Y'.left}
    (h1 : R1fpPropsU Y Φ) (h2 : R2fpProps Y Φ π) (h1' : R1fpPropsU Y' Φ')
    (h2' : R2fpProps Y' Φ' π') : SameTripleMor Y Y' Φ Φ' π π' :=
  sameTripleMor_of_mobius (mobiusGlue_of_named hRF hSu hT hA) hCM h1 h2 h1' h2'

/-- **Pieces from the witness, from the named facts.** -/
theorem pointwise_of_witness_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q))
    {Y₀ : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀} {π₀ : ToP1 Y₀.left}
    (h1 : R1fpPropsU Y₀ Φ₀) (h2 : R2fpProps Y₀ Φ₀ π₀)
    (R : OnePoint Qbar → QML3 Qbar → Prop)
    (h : ∀ t (y : fieldPt Qbar ⟶ Y₀) (P : QML3 Qbar), Φ₀ Qbar y = M3.mk P →
      π₀.val (K := Qbar) y.left = t → R t P) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpPropsU Y Φ → R2fpProps Y Φ π →
      ∀ t (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
        π.val (K := Qbar) y.left = t → R t P :=
  pointwise_of_witness_mor (mobiusGlue_of_named hRF hSu hT hA) hCM h1 h2 R h

end Pin

end AV

end LeafQM

#print axioms LeafQM.AV.Pin.Mob.natDegree_le_one_of_injective
#print axioms LeafQM.AV.Pin.Mob.ratEval_eq_self
#print axioms LeafQM.AV.Pin.mobiusGlue_of_curveFacts
#print axioms LeafQM.AV.Pin.level3_finite
#print axioms LeafQM.AV.Pin.twistClassFinite_of
#print axioms LeafQM.AV.Pin.mobiusGlue_of_named
#print axioms LeafQM.AV.Pin.sameTripleMor_of_named
#print axioms LeafQM.AV.Pin.pointwise_of_witness_named
