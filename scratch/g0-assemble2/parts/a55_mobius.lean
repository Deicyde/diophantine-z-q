/-! ## g0-assemble2: mobius-glue (scratch/mobius-glue/MobiusGlue.lean), adapted to Leaves.lean after pin-apply

Changes (all mechanical): (1) its §0 copies of `QMFamily`, `IsFibreOf`, `R1famProps`,
`R1univProps` (lines 47-79, 89-100) are not repeated: pin-apply put the same text into Leaves.lean
(`LeafQM.AV.*`), which the names resolve to; (2) its copy of `MobiusGlue` (stated with
`R1fpPropsU`) is renamed `MobiusGlueU` throughout, because Leaves.lean's `LeafQM.AV.Pin.MobiusGlue`
is stated with the repaired `R1fpProps` (the same six clauses, associated differently);
`mobiusGlue_of_U` below converts; (3) §6 (lines 549-643, qm-pin's comparison lemmas, already in
Leaves.lean) and the two downstream corollaries at lines 1409-1434 are not repeated. -/

/-!
# mobius-glue: the `π`-half of qm-pin's comparison of two triples

Task mobius-glue (2026-11-13). See `docs/research/mobius-glue.md`.

**Main result** (`mobiusGlue_of_curves`): `LeafQM.AV.Pin.MobiusGlueU` (qm-pin §3.2, copied
verbatim from `scratch/qm-pin/QMPin.lean` together with the definitions it uses) follows from

* `CurveRatFactor` (curves): on a proper smooth curve over `ℚ`, a morphism `ρ` to `P¹` that is
  constant on the fibres of a morphism `σ` to `P¹` is a rational function of `σ` on `ℚ̄`-points;
* `CurveSurj` (curves): a morphism to `P¹` with finite fibres on `ℚ̄`-points, from a proper
  smooth curve over `ℚ` with a `ℚ̄`-point, is onto `P¹(ℚ̄)`;
* `ObjBridge.TorsionStructure` (the decomposition's textbook leaf T5, `A(K̄)[n] ≅ (ℤ/n)^{2g}`).

Contents.
* §0 the qm-pin definitions (verbatim).
* §1 an injective rational function on an algebraically closed field of characteristic 0 has
  degree at most one (`Mob.natDegree_le_one_of_injective`, Wronskian argument); one of degree at
  most one without finite pole fixing `0` and `c ≠ 0` is the identity (`Mob.ratEval_eq_self`).
* §2 the named facts; §3 `mobiusGlue_of_curveFacts` (from the curve facts and
  `TwistClassFinite`).
* §4 `TwistClassFinite` from T5 and `AutOInnerFinite` (finitely many level structures per pair via
  the kernel's `Level3.torsor`; transport of level structures; twists by conjugate automorphisms).
* §5-§6 the combined statements and the downstream comparison/transfer (qm-pin §4 copied).
* §7 `AutOInnerFinite` from Skolem–Noether (the kernel's `TSkolemKW.leafSkolemNoether`, through
  an explicit extension of `α ∈ Aut 𝒪` to `B`) and `NormalizerFinite`.
* §8 `NormalizerFinite` proved (`N(𝒪)/ℚ^×𝒪^× = {1, i, j, ij}`, descent on the reduced norm), hence
  `autOInnerFinite`, `twistClassFinite`, `mobiusGlue_of_curves`, `sameTripleMor_of_curves`,
  `pointwise_of_witness_curves`.
No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3


/-- **R1fp, repaired clause list** (to replace `LeafQM.AV.R1fpProps`): the four old clauses and
`R1famProps`. -/
def R1fpPropsPin (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧
  (∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q) ∧
  R1famProps Y Φ
/-- The fully repaired clause list: family and universal property. -/
def R1fpPropsU (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  R1fpPropsPin Y Φ ∧ R1univProps Y Φ

/-- **Glue (not compiled; argued in the report §3.4).** Given a morphism `g : Y' → Y` with
`Φ' = Φ ∘ g`, and CM objects of the three kinds, the two morphisms `π'` and `π ∘ g` to `P¹`
agree on `ℚ̄`-points: they have the same fibres (both `R2fpProps`), so `π' = h ∘ π ∘ g` with `h`
a bijection of `P¹(ℚ̄)` which is a morphism (graph argument on each geometric component of
`Y'`), hence a Möbius map, and `h` fixes `0, ∞, −16/27`. Algebraic geometry of curves. -/
def MobiusGlueU : Prop :=
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

/-- **`MobiusGlueU` from the two curve facts and the moduli fact.** -/
theorem mobiusGlue_of_curveFacts (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : TwistClassFinite) : MobiusGlueU := by
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

/-- **`MobiusGlueU` from two curve facts, the textbook leaf `TorsionStructure` (T5, Mumford §4)
and the algebra fact `AutOInnerFinite`.** -/
theorem mobiusGlue_of_named (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hA : AutOInnerFinite) : MobiusGlueU :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite_of hT hA)

end Pin

end AV

end LeafQM


/-! ## §7 `AutOInnerFinite` from Skolem–Noether (proved in the kernel) and `NormalizerFinite`

(Outside the `open MonObj` scope of §0-§6.) -/

namespace LeafQM

namespace AV

namespace Pin

namespace AutOExt

/-! ### Extension of a ring automorphism of `𝒪` to `B` -/

theorem mem_O_of_int (z0 z1 z2 z3 : ℤ) : (⟨z0, z1, z2, z3⟩ : B) ∈ O := by
  refine ⟨![z0 - z2, z1 - z3, 2 * z2, 2 * z3], ?_⟩
  ext <;> simp [ofInt]

theorem nat_smul_mem (n : ℕ) {x : B} (hx : x ∈ O) : (n : ℚ) • x ∈ O := by
  rw [Algebra.smul_def, map_natCast]
  exact O.mul_mem (natCast_mem O n) hx

theorem den_mul_int (q : ℚ) (k : ℕ) : ∃ z : ℤ, ((k * q.den : ℕ) : ℚ) * q = z :=
  ⟨k * q.num, by push_cast; rw [mul_assoc, Rat.den_mul_eq_num]⟩

/-- Every element of `B` has a positive integer multiple in `𝒪`. -/
theorem exists_nat_smul_mem (b : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O := by
  set m := b.re.den * b.imI.den * b.imJ.den * b.imK.den with hm
  refine ⟨m, by positivity, ?_⟩
  obtain ⟨z0, h0⟩ := den_mul_int b.re (b.imI.den * b.imJ.den * b.imK.den)
  obtain ⟨z1, h1⟩ := den_mul_int b.imI (b.re.den * b.imJ.den * b.imK.den)
  obtain ⟨z2, h2⟩ := den_mul_int b.imJ (b.re.den * b.imI.den * b.imK.den)
  obtain ⟨z3, h3⟩ := den_mul_int b.imK (b.re.den * b.imI.den * b.imJ.den)
  have e : (m : ℚ) • b = ⟨z0, z1, z2, z3⟩ := by
    ext
    · rw [QuaternionAlgebra.re_smul, ← h0, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imI_smul, ← h1, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imJ_smul, ← h2, smul_eq_mul, hm]; push_cast; ring
    · rw [QuaternionAlgebra.imK_smul, ← h3, smul_eq_mul, hm]
  rw [e]
  exact mem_O_of_int z0 z1 z2 z3

variable (α : O ≃+* O)

/-- A chosen positive integer `m` with `m b ∈ 𝒪`. -/
def extDen (b : B) : ℕ := Classical.choose (exists_nat_smul_mem b)

theorem extDen_pos (b : B) : 0 < extDen b := (Classical.choose_spec (exists_nat_smul_mem b)).1

theorem extDen_mem (b : B) : ((extDen b : ℕ) : ℚ) • b ∈ O :=
  (Classical.choose_spec (exists_nat_smul_mem b)).2

/-- `α̃(b) = m⁻¹ α(m b)`. -/
def extFun (b : B) : B := ((extDen b : ℚ)⁻¹) • (α ⟨_, extDen_mem b⟩ : B)

theorem natCast_mul_eq_smul (n : ℕ) (x : B) : (n : B) * x = (n : ℚ) • x := by
  rw [Algebra.smul_def, map_natCast]

theorem alpha_nat_smul (n : ℕ) (x : B) (hx : x ∈ O) (hnx : (n : ℚ) • x ∈ O) :
    (α ⟨_, hnx⟩ : B) = (n : ℚ) • (α ⟨x, hx⟩ : B) := by
  have : (⟨_, hnx⟩ : O) = (n : O) * ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [natCast_mul_eq_smul]
  rw [this, map_mul, map_natCast, MulMemClass.coe_mul, SubringClass.coe_natCast,
    natCast_mul_eq_smul]

/-- Independence of the choice of `m`. -/
theorem extFun_eq (b : B) (m : ℕ) (hm : 0 < m) (hb : (m : ℚ) • b ∈ O) :
    extFun α b = ((m : ℚ)⁻¹) • (α ⟨_, hb⟩ : B) := by
  have hd : 0 < extDen b := extDen_pos b
  have hdm : (m : ℚ) • ((extDen b : ℚ) • b) ∈ O := nat_smul_mem m (extDen_mem b)
  have hmd : (extDen b : ℚ) • ((m : ℚ) • b) ∈ O := nat_smul_mem (extDen b) hb
  have e1 := alpha_nat_smul α m _ (extDen_mem b) hdm
  have e2 := alpha_nat_smul α (extDen b) _ hb hmd
  have e3 : (⟨_, hdm⟩ : O) = ⟨_, hmd⟩ := Subtype.ext (smul_comm _ _ _)
  rw [e3, e2] at e1
  -- e1 : d • α(m b) = m • α(d b)
  unfold extFun
  have hX : (α ⟨_, extDen_mem b⟩ : B) = ((m : ℚ)⁻¹ * extDen b) • (α ⟨_, hb⟩ : B) := by
    rw [mul_smul, e1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
  rw [hX, smul_smul]
  congr 1
  have : (extDen b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem extFun_coe (a : O) : extFun α a = α a := by
  have h1 : ((1 : ℕ) : ℚ) • (a : B) ∈ O := by simp
  rw [extFun_eq α a 1 one_pos h1]
  have : (⟨_, h1⟩ : O) = a := Subtype.ext (by simp)
  rw [this]; simp

/-- A common multiplier for two elements. -/
theorem common_den (b c : B) : ∃ m : ℕ, 0 < m ∧ (m : ℚ) • b ∈ O ∧ (m : ℚ) • c ∈ O := by
  refine ⟨extDen b * extDen c, Nat.mul_pos (extDen_pos b) (extDen_pos c), ?_, ?_⟩
  · have := nat_smul_mem (extDen c) (extDen_mem b)
    rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  · have := nat_smul_mem (extDen b) (extDen_mem c)
    rwa [smul_smul, ← Nat.cast_mul] at this

theorem extFun_add (b c : B) : extFun α (b + c) = extFun α b + extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc : (m : ℚ) • (b + c) ∈ O := by rw [smul_add]; exact O.add_mem hb hc
  rw [extFun_eq α _ m hm hbc, extFun_eq α _ m hm hb, extFun_eq α _ m hm hc, ← smul_add]
  congr 1
  have : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ + ⟨_, hc⟩ := Subtype.ext (by simp [smul_add])
  rw [this, map_add]; rfl

theorem smul_mul_smul' (r s : ℚ) (x y : B) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem extFun_mul (b c : B) : extFun α (b * c) = extFun α b * extFun α c := by
  obtain ⟨m, hm, hb, hc⟩ := common_den b c
  have hbc0 : ((m : ℚ) * m) • (b * c) ∈ O := by
    rw [← smul_mul_smul']; exact O.mul_mem hb hc
  have hbc : ((m * m : ℕ) : ℚ) • (b * c) ∈ O := by rw [Nat.cast_mul]; exact hbc0
  have hprod : (⟨_, hbc⟩ : O) = ⟨_, hb⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((m * m : ℕ) : ℚ) • (b * c) = ((m : ℚ) • b) * ((m : ℚ) • c)
    rw [smul_mul_smul', Nat.cast_mul]
  have e1 : (α ⟨_, hbc⟩ : B) = (α ⟨_, hb⟩ : B) * (α ⟨_, hc⟩ : B) := by
    rw [hprod, map_mul, MulMemClass.coe_mul]
  rw [extFun_eq α _ (m * m) (Nat.mul_pos hm hm) hbc, extFun_eq α _ m hm hb,
    extFun_eq α _ m hm hc, smul_mul_smul', e1, Nat.cast_mul, mul_inv]

theorem extFun_algebraMap (q : ℚ) : extFun α (algebraMap ℚ B q) = algebraMap ℚ B q := by
  have hq : ((q.den : ℕ) : ℚ) • algebraMap ℚ B q ∈ O := by
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast]
    exact intCast_mem O q.num
  rw [extFun_eq α _ q.den q.den_pos hq]
  have : (⟨_, hq⟩ : O) = (q.num : O) := Subtype.ext (by
    simp only [SubringClass.coe_intCast]
    rw [Algebra.smul_def, ← map_mul, Rat.den_mul_eq_num, map_intCast])
  rw [this, map_intCast, SubringClass.coe_intCast, ← map_intCast (algebraMap ℚ B),
    Algebra.smul_def, ← map_mul]
  congr 1
  rw [inv_mul_eq_div, Rat.num_div_den]

/-- The extension `α̃ : B → B` as a `ℚ`-algebra map. -/
def extAlgHom : B →ₐ[ℚ] B where
  toFun := extFun α
  map_one' := by simpa using extFun_coe α 1
  map_zero' := by simpa using extFun_coe α 0
  map_add' := extFun_add α
  map_mul' := extFun_mul α
  commutes' := extFun_algebraMap α

theorem extAlgHom_apply (b : B) : extAlgHom α b = extFun α b := rfl

theorem extAlgHom_coe (a : O) : extAlgHom α a = α a := extFun_coe α a

theorem extAlgHom_symm_comp : (extAlgHom α.symm).comp (extAlgHom α) = AlgHom.id ℚ B := by
  refine AlgHom.ext fun b => ?_
  change extAlgHom α.symm (extFun α b) = b
  rw [extFun_eq α b (extDen b) (extDen_pos b) (extDen_mem b), map_smul, extAlgHom_coe,
    RingEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (extDen_pos b).ne'),
    one_smul]

/-- The extension as a `ℚ`-algebra automorphism of `B`. -/
def extAlgEquiv : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofAlgHom (extAlgHom α) (extAlgHom α.symm)
    (by simpa using extAlgHom_symm_comp α.symm) (extAlgHom_symm_comp α)

theorem extAlgEquiv_apply (b : B) : extAlgEquiv α b = extFun α b := rfl

/-! ### `AutOInnerFinite` from Skolem–Noether and the normalizer -/

/-- **Normalizer fact (N(𝒪)/ℚ^×𝒪^× finite).** Every `u ∈ B^×` normalizing `𝒪` is
`q · v · t` with `q ∈ ℚ^×`, `v ∈ 𝒪^×` and `t` in a fixed finite set. -/
def NormalizerFinite : Prop :=
  ∃ T : Set Bˣ, T.Finite ∧ ∀ u : Bˣ, (∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O) →
    ∃ t ∈ T, ∃ v : Oˣ, ∃ q : ℚ, q ≠ 0 ∧ (u : B) = algebraMap ℚ B q * ((v : O) : B) * (t : B)

/-- Skolem–Noether (proved in the kernel, `TSkolemKW.leafSkolemNoether`) applied to `α̃`. -/
theorem conj_of_skolem : ∃ u : Bˣ, ∀ b : B, extFun α b = u * b * ((u⁻¹ : Bˣ) : B) := by
  obtain ⟨u, hu⟩ := GlueDescent.B6_inner TSkolemKW.leafSkolemNoether (extAlgEquiv α)
  exact ⟨u, fun b => hu b⟩

/-- Conjugation by a unit of `𝒪`, `a ↦ v⁻¹ a v`. -/
def conjUnit (v : Oˣ) : O ≃+* O where
  toFun a := ((v⁻¹ : Oˣ) : O) * a * v
  invFun a := (v : O) * a * ((v⁻¹ : Oˣ) : O)
  left_inv a := by
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
  right_inv a := by
    simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
  map_mul' a b := by
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' a b := by
    simp only [mul_add, add_mul]

theorem key_conj {R : Type*} [Ring R] (x y w w' c c' t : R) (hvv : w' * w = 1) (hcc : c' * c = 1)
    (hc : c * x = x * c) (h : x * (c * w * t) = c * w * t * y) : w' * x * w * t = t * y := by
  have h1 : x * w * t = w * t * y := by
    calc x * w * t = c' * (c * x) * w * t := by rw [← mul_assoc, hcc, one_mul]
      _ = c' * (x * (c * w * t)) := by rw [hc]; simp only [mul_assoc]
      _ = c' * (c * w * t * y) := by rw [h]
      _ = w * t * y := by simp only [← mul_assoc]; rw [hcc, one_mul]
  calc w' * x * w * t = w' * (x * w * t) := by simp only [mul_assoc]
    _ = w' * (w * t * y) := by rw [h1]
    _ = t * y := by simp only [← mul_assoc]; rw [hvv, one_mul]

/-- **`AutOInnerFinite` from the normalizer fact** (with Skolem–Noether from the kernel). -/
theorem autOInnerFinite_of_normalizer (hN : NormalizerFinite) : AutOInnerFinite := by
  classical
  obtain ⟨T, hT, hTu⟩ := hN
  let P : (O ≃+* O) → Bˣ → Prop := fun β t => ∀ a : O, ((β a : O) : B) * t = t * a
  let T' : Set (O ≃+* O) := {β | ∃ t ∈ T, P β t}
  let f : (O ≃+* O) → Bˣ := fun β => if h : ∃ t ∈ T, P β t then Classical.choose h else 1
  have hf : ∀ β ∈ T', f β ∈ T ∧ P β (f β) := by
    intro β hβ
    have hβ' : ∃ t ∈ T, P β t := hβ
    simp only [f, hβ', dite_true]
    exact Classical.choose_spec hβ'
  have hT' : T'.Finite := by
    refine Set.Finite.of_finite_image (f := f) (hT.subset (t := f '' T') ?_) ?_
    · rintro _ ⟨β, hβ, rfl⟩; exact (hf β hβ).1
    · intro β₁ h₁ β₂ h₂ heq
      apply RingEquiv.ext; intro a
      apply Subtype.ext
      have e1 := (hf β₁ h₁).2 a
      have e2 := (hf β₂ h₂).2 a
      rw [heq] at e1
      exact (Units.mul_left_inj (f β₂)).1 (e1.trans e2.symm)
  refine ⟨T', hT', fun α => ?_⟩
  obtain ⟨u, hu⟩ := conj_of_skolem α
  have hback : ∀ b : B, extFun α.symm (extFun α b) = b := fun b =>
    congrArg (fun φ : B →ₐ[ℚ] B => φ b) (extAlgHom_symm_comp α)
  have hnorm : ∀ a : B, a ∈ O ↔ (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O := by
    intro a
    rw [← hu]
    constructor
    · intro ha
      rw [show a = ((⟨a, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α _).2
    · intro ha
      rw [← hback a, show extFun α a = ((⟨_, ha⟩ : O) : B) from rfl, extFun_coe]
      exact (α.symm _).2
  obtain ⟨t, ht, v, q, hq, huq⟩ := hTu u hnorm
  have hrel : ∀ a : O, ((α a : O) : B) * u = u * a := by
    intro a
    rw [← extFun_coe, hu, Units.inv_mul_cancel_right]
  let β : O ≃+* O := α.trans (conjUnit v)
  have hβ : ∀ a : O, β a = ((v⁻¹ : Oˣ) : O) * α a * v := fun a => rfl
  refine ⟨β, ⟨t, ht, fun a => ?_⟩, v, fun a => ?_⟩
  · have hvv : (((v⁻¹ : Oˣ) : O) : B) * ((v : O) : B) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul]; rfl
    have hcc : algebraMap ℚ B q⁻¹ * algebraMap ℚ B q = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hq, map_one]
    have h := hrel a
    rw [huq] at h
    rw [hβ, MulMemClass.coe_mul, MulMemClass.coe_mul]
    exact key_conj _ _ _ _ _ _ _ hvv hcc (Algebra.commutes q _) h
  · rw [hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]

end AutOExt

/-- **`MobiusGlueU` from the two curve facts, the leaf `TorsionStructure` (T5) and
`NormalizerFinite` (`N(𝒪)/ℚ^×𝒪^×` finite).** Skolem–Noether enters through the kernel's proof
`TSkolemKW.leafSkolemNoether`. -/
theorem mobiusGlue_of_normalizer (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) (hN : AutOExt.NormalizerFinite) : MobiusGlueU :=
  mobiusGlue_of_named hRF hSu hT (AutOExt.autOInnerFinite_of_normalizer hN)

end Pin

end AV

end LeafQM


/-! ## §8 `NormalizerFinite`, proved: `N(𝒪)/ℚ^×𝒪^×` is represented by `{1, i, j, ij}`

Descent on `|nrd|`. A prime `p ∤ 6` dividing `nrd(u)` of a normalizing `u ∈ 𝒪` divides `u`: an
explicit identity `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`,
`scratch/mobius-glue/py/normalizer_identity.py`). If `2 | nrd(u)` then `u i⁻¹ ∈ 𝒪`, and if
`3 | nrd(u)` then `u j⁻¹ ∈ 𝒪` (checks modulo 2 and 3 by `decide`). -/

namespace LeafQM

namespace AV

namespace Pin

namespace NormO

/-! ### Integer coordinates -/

/-- The reduced norm in the coordinates of `ofInt`. -/
def nrdZ (n : Fin 4 → ℤ) : ℤ :=
  n 0 ^ 2 + n 0 * n 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 + n 2 ^ 2 - 2 * n 3 ^ 2

/-- The conjugate in the coordinates of `ofInt`. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem mulCoord_conjC (n : Fin 4 → ℤ) : mulCoord n (conjC n) = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem mulCoord_conjC' (n : Fin 4 → ℤ) : mulCoord (conjC n) n = ![nrdZ n, 0, 0, 0] := by
  funext l; fin_cases l <;> simp [mulCoord, conjC, nrdZ] <;> ring

theorem nrdZ_mul (n m : Fin 4 → ℤ) : nrdZ (mulCoord n m) = nrdZ n * nrdZ m := by
  simp [mulCoord, nrdZ]; ring

theorem ofInt_scalar (z : ℤ) : ofInt ![z, 0, 0, 0] = algebraMap ℚ B (z : ℚ) := by
  ext <;> simp [ofInt]

theorem smul_ofInt (z : ℤ) (n : Fin 4 → ℤ) : (z : ℚ) • ofInt n = ofInt (fun l => z * n l) := by
  ext <;> simp [ofInt] <;> ring

theorem mem_O_iff (x : B) : x ∈ O ↔ ∃ n, x = ofInt n := Iff.rfl

/-- `(1/z) • ofInt m ∈ 𝒪` forces `z ∣ m`. -/
theorem dvd_of_smul_mem {z : ℤ} (hz : z ≠ 0) {m : Fin 4 → ℤ}
    (h : ((z : ℚ)⁻¹) • ofInt m ∈ O) : ∀ l, z ∣ m l := by
  obtain ⟨w, hw⟩ := h
  have : ofInt m = ofInt (fun l => z * w l) := by
    rw [← smul_ofInt, ← hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hz), one_smul]
  have e := AV.ofInt_injective this
  intro l
  exact ⟨w l, congrFun e l⟩

/-! ### The units `i`, `j` of `B` -/

def ei : Fin 4 → ℤ := ![0, 1, 0, 0]
def ej : Fin 4 → ℤ := ![-1, 0, 2, 0]

theorem nrdZ_ei : nrdZ ei = -2 := by simp [nrdZ, ei]
theorem nrdZ_ej : nrdZ ej = 3 := by simp [nrdZ, ej]

def ui : Bˣ where
  val := ofInt ei
  inv := ((2 : ℚ)⁻¹) • ofInt ei
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei]

def uj : Bˣ where
  val := ofInt ej
  inv := ((-3 : ℚ)⁻¹) • ofInt ej
  val_inv := by
    rw [mul_smul_comm, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]
  inv_val := by
    rw [smul_mul_assoc, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej]

/-- The representatives `{1, i, j, ij}` of `N(𝒪)/ℚ^×𝒪^×`. -/
def T : Set Bˣ := {1, ui, uj, ui * uj}

theorem T_finite : T.Finite := by
  simp only [T]
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-! ### Normalizing units -/

/-- `u` normalizes `𝒪`. -/
def IsNorm (u : Bˣ) : Prop :=
  ∀ a ∈ O, (u : B) * a * ((u⁻¹ : Bˣ) : B) ∈ O ∧ ((u⁻¹ : Bˣ) : B) * a * u ∈ O

theorem IsNorm.mul {u w : Bˣ} (hu : IsNorm u) (hw : IsNorm w) : IsNorm (u * w) := by
  intro a ha
  refine ⟨?_, ?_⟩
  · have := (hu _ (hw a ha).1).1
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this
  · have := (hw _ (hu a ha).2).2
    simpa [mul_inv_rev, Units.val_mul, mul_assoc] using this

theorem IsNorm.inv {u : Bˣ} (hu : IsNorm u) : IsNorm u⁻¹ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hu a ha
  exact ⟨h2, by simpa using h1⟩

/-- The unit `c ∈ ℚ^×` of `B`. -/
def sc (c : ℚ) (hc : c ≠ 0) : Bˣ where
  val := algebraMap ℚ B c
  inv := algebraMap ℚ B c⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]

theorem isNorm_sc (c : ℚ) (hc : c ≠ 0) : IsNorm (sc c hc) := by
  intro a ha
  have e1 : ((sc c hc : Bˣ) : B) * a * (((sc c hc)⁻¹ : Bˣ) : B) = a := by
    change algebraMap ℚ B c * a * algebraMap ℚ B c⁻¹ = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
  have e2 : (((sc c hc)⁻¹ : Bˣ) : B) * a * ((sc c hc : Bˣ) : B) = a := by
    change algebraMap ℚ B c⁻¹ * a * algebraMap ℚ B c = a
    rw [Algebra.commutes, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one]
  exact ⟨by rw [e1]; exact ha, by rw [e2]; exact ha⟩

theorem isNorm_ui : IsNorm ui := by
  rintro a ⟨n, rfl⟩
  have e : ((ui : Bˣ) : B) * ofInt n * ((ui⁻¹ : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change ofInt ei * ofInt n * (((2 : ℚ)⁻¹) • ofInt ei) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  have e' : ((ui⁻¹ : Bˣ) : B) * ofInt n * ((ui : Bˣ) : B) =
      ofInt ![n 0 + n 2, n 1 + n 3, -n 2, -n 3] := by
    change (((2 : ℚ)⁻¹) • ofInt ei) * ofInt n * ofInt ei = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

theorem isNorm_uj : IsNorm uj := by
  rintro a ⟨n, rfl⟩
  have e : ((uj : Bˣ) : B) * ofInt n * ((uj⁻¹ : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change ofInt ej * ofInt n * (((-3 : ℚ)⁻¹) • ofInt ej) = _
    rw [mul_smul_comm, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  have e' : ((uj⁻¹ : Bˣ) : B) * ofInt n * ((uj : Bˣ) : B) = ofInt ![n 0, -n 1, n 2, -n 3] := by
    change (((-3 : ℚ)⁻¹) • ofInt ej) * ofInt n * ofInt ej = _
    rw [smul_mul_assoc, smul_mul_assoc, ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ej] <;> ring
  exact ⟨⟨_, e⟩, ⟨_, e'⟩⟩

/-! ### The norm of a unit in `𝒪` and its inverse -/

theorem nrdZ_ne_zero (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) : nrdZ n ≠ 0 := by
  intro h0
  have h1 : (u : B) * ofInt (conjC n) = 0 := by
    rw [hu, ofInt_mul, mulCoord_conjC, h0, ofInt_scalar]; simp
  have h2 : ofInt (conjC n) = 0 := by
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) * x) h1
    simpa [← mul_assoc] using this
  have h3 : conjC n = 0 := AV.ofInt_injective (h2.trans ofInt_zero.symm)
  have h4 : n = 0 := by
    funext l
    have e0 := congrFun h3 0; have e1 := congrFun h3 1
    have e2 := congrFun h3 2; have e3 := congrFun h3 3
    simp [conjC] at e0 e1 e2 e3
    fin_cases l <;> simp <;> omega
  have : (u : B) = 0 := by rw [hu, h4, ofInt_zero]
  exact u.ne_zero this

theorem inv_eq (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) :
    ((u⁻¹ : Bˣ) : B) = ((nrdZ n : ℚ)⁻¹) • ofInt (conjC n) := by
  have hN : (nrdZ n : ℚ) ≠ 0 := by exact_mod_cast nrdZ_ne_zero u n hu
  apply Units.inv_eq_of_mul_eq_one_right
  rw [mul_smul_comm, hu, ofInt_mul, mulCoord_conjC, ofInt_scalar, Algebra.smul_def, ← map_mul,
    inv_mul_cancel₀ hN, map_one]

def bas : Fin 4 → (Fin 4 → ℤ) := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- For a normalizing `u = ofInt n`, `nrd(u)` divides every coordinate of `u e_k ū`. -/
theorem nrd_dvd_coords (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (k l : Fin 4) : nrdZ n ∣ mulCoord (mulCoord n (bas k)) (conjC n) l := by
  have h := (hN (ofInt (bas k)) ⟨_, rfl⟩).1
  rw [inv_eq u n hu, mul_smul_comm, hu, ofInt_mul, ofInt_mul] at h
  exact dvd_of_smul_mem (nrdZ_ne_zero u n hu) h l

/-- The identities `6 x_l² = Σ λ · coord(u e_k ū)` (coefficients from PARI's `matsolvemod`). -/
theorem six_sq_identities (n : Fin 4 → ℤ) :
    let F := fun k l => mulCoord (mulCoord n (bas k)) (conjC n) l
    6 * n 0 ^ 2 = 2 * F 0 0 + 2 * F 1 1 + 2 * F 1 3 + 2 * F 2 2 - 2 * F 3 1 ∧
    6 * n 1 ^ 2 = -F 1 1 - 2 * F 2 0 + F 3 1 + F 3 3 ∧
    6 * n 2 ^ 2 = 2 * F 0 0 - 2 * F 1 1 + 2 * F 2 2 - 2 * F 3 3 ∧
    6 * n 3 ^ 2 = F 1 1 + F 1 3 - 2 * F 2 0 - F 3 3 := by
  intro F
  simp only [F, mulCoord, bas, conjC]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> ring

/-- A prime `p ≠ 2, 3` dividing `nrd(u)` of a normalizing `u = ofInt n` divides `n`. -/
theorem dvd_of_prime_dvd_nrd (u : Bˣ) (n : Fin 4 → ℤ) (hu : (u : B) = ofInt n) (hN : IsNorm u)
    (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (hpd : (p : ℤ) ∣ nrdZ n) :
    ∀ l, (p : ℤ) ∣ n l := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hF : ∀ k l, (p : ℤ) ∣ mulCoord (mulCoord n (bas k)) (conjC n) l :=
    fun k l => hpd.trans (nrd_dvd_coords u n hu hN k l)
  have h6 : ¬ (p : ℤ) ∣ 6 := by
    intro h
    have h' : p ∣ 6 := by exact_mod_cast h
    have : p ∣ 2 * 3 := h'
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  obtain ⟨i0, i1, i2, i3⟩ := six_sq_identities n
  have k0 : (p : ℤ) ∣ 6 * n 0 ^ 2 := by
    rw [i0]
    exact dvd_sub (dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 1 3) _))
      (dvd_mul_of_dvd_right (hF 2 2) _)) (dvd_mul_of_dvd_right (hF 3 1) _)
  have k1 : (p : ℤ) ∣ 6 * n 1 ^ 2 := by
    rw [i1]
    exact dvd_add (dvd_add (dvd_sub (dvd_neg.mpr (hF 1 1)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 1)) (hF 3 3)
  have k2 : (p : ℤ) ∣ 6 * n 2 ^ 2 := by
    rw [i2]
    exact dvd_sub (dvd_add (dvd_sub (dvd_mul_of_dvd_right (hF 0 0) _)
      (dvd_mul_of_dvd_right (hF 1 1) _)) (dvd_mul_of_dvd_right (hF 2 2) _))
      (dvd_mul_of_dvd_right (hF 3 3) _)
  have k3 : (p : ℤ) ∣ 6 * n 3 ^ 2 := by
    rw [i3]
    exact dvd_sub (dvd_sub (dvd_add (hF 1 1) (hF 1 3)) (dvd_mul_of_dvd_right (hF 2 0) _))
      (hF 3 3)
  have key : ∀ l, (p : ℤ) ∣ 6 * n l ^ 2 := by
    intro l; fin_cases l
    exacts [k0, k1, k2, k3]
  intro l
  rcases hpZ.dvd_or_dvd (key l) with h | h
  · exact absurd h h6
  · exact hpZ.dvd_of_dvd_pow h

/-! ### The primes 2 and 3 -/

theorem two_dvd_mulCoord_ei (n : Fin 4 → ℤ) (h : (2 : ℤ) ∣ nrdZ n) :
    ∀ l, (2 : ℤ) ∣ mulCoord n ei l := by
  have hz : ((nrdZ n : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 2,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a = 0 ∧ c = 0 := by
    decide
  obtain ⟨h0, h2⟩ := key _ _ _ _ hz
  have d0 : (2 : ℤ) ∣ n 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0
  have d2 : (2 : ℤ) ∣ n 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
  intro l
  fin_cases l <;> simp [mulCoord, ei] <;> omega

theorem three_dvd_mulCoord_ej (n : Fin 4 → ℤ) (h : (3 : ℤ) ∣ nrdZ n) :
    ∀ l, (3 : ℤ) ∣ mulCoord n ej l := by
  have hz : ((nrdZ n : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  simp only [nrdZ] at hz
  push_cast at hz
  have key : ∀ a b c d : ZMod 3,
      a ^ 2 + a * c - 2 * b ^ 2 - 2 * b * d + c ^ 2 - 2 * d ^ 2 = 0 → a - c = 0 ∧ b - d = 0 := by
    decide
  obtain ⟨h0, h1⟩ := key _ _ _ _ hz
  have d0 : (3 : ℤ) ∣ n 0 - n 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h0)
  have d1 : (3 : ℤ) ∣ n 1 - n 3 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast; exact h1)
  intro l
  fin_cases l <;> simp [mulCoord, ej] <;> omega

/-! ### Closure of `T` under right multiplication by `i` and `j` -/

theorem T_mem_iff (t : Bˣ) : t ∈ T ↔ t = 1 ∨ t = ui ∨ t = uj ∨ t = ui * uj := Iff.rfl

theorem T_mul_ui : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (ui : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, ui, by simp [T], by simp⟩
  · refine ⟨2, two_ne_zero, 1, by simp [T], ?_⟩
    change ofInt ei * ofInt ei = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ei, QuaternionAlgebra.algebraMap_eq]
  · refine ⟨-1, by norm_num, ui * uj, by simp [T], ?_⟩
    change ofInt ej * ofInt ei = _ * (ofInt ei * ofInt ej)
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-2, by norm_num, uj, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ei = _ * ofInt ej
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

theorem T_mul_uj : ∀ t ∈ T, ∃ c : ℚ, c ≠ 0 ∧ ∃ t' ∈ T,
    (t : B) * (uj : B) = algebraMap ℚ B c * (t' : B) := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact ⟨1, one_ne_zero, uj, by simp [T], by simp⟩
  · exact ⟨1, one_ne_zero, ui * uj, by simp [T], by simp⟩
  · refine ⟨-3, by norm_num, 1, by simp [T], ?_⟩
    change ofInt ej * ofInt ej = _
    rw [ofInt_mul]; ext <;> simp [ofInt, mulCoord, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num
  · refine ⟨-3, by norm_num, ui, by simp [T], ?_⟩
    change ofInt ei * ofInt ej * ofInt ej = _ * ofInt ei
    rw [ofInt_mul, ofInt_mul]
    ext <;> simp [ofInt, mulCoord, ei, ej, QuaternionAlgebra.algebraMap_eq] <;> norm_num

/-- Rearranging `q v t i = (q c) v t'` for central `c`. -/
theorem rearrange (q c : ℚ) (V Tt I T' : B) (h : Tt * I = algebraMap ℚ B c * T') :
    algebraMap ℚ B q * V * Tt * I = algebraMap ℚ B (q * c) * V * T' := by
  rw [mul_assoc (algebraMap ℚ B q * V), h, ← mul_assoc, mul_assoc (algebraMap ℚ B q),
    ← Algebra.commutes c V, ← mul_assoc, ← map_mul]

theorem mulCoord_smul_right (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord n (fun l => z * m l) = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem mulCoord_smul_left (n m : Fin 4 → ℤ) (z : ℤ) :
    mulCoord (fun l => z * n l) m = fun l => z * mulCoord n m l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem nrdZ_smul (n : Fin 4 → ℤ) (z : ℤ) : nrdZ (fun l => z * n l) = z ^ 2 * nrdZ n := by
  simp [nrdZ]; ring

/-! ### The descent -/

theorem descent (m : ℕ) : ∀ (u : Bˣ) (n : Fin 4 → ℤ), (u : B) = ofInt n →
    (nrdZ n).natAbs = m → IsNorm u →
    ∃ q : ℚ, q ≠ 0 ∧ ∃ v : Oˣ, ∃ t ∈ T, (u : B) = algebraMap ℚ B q * ((v : O) : B) * t := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u n hu hm hN
  have hN0 := nrdZ_ne_zero u n hu
  by_cases h1 : m = 1
  · have hsq : nrdZ n * nrdZ n = 1 := by
      have : (nrdZ n).natAbs = 1 := hm.trans h1
      rcases Int.natAbs_eq_iff.mp this with h | h <;> rw [h] <;> norm_num
    set w : Fin 4 → ℤ := fun l => nrdZ n * conjC n l with hw_def
    have hw1 : mulCoord n w = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_right, mulCoord_conjC]
      funext l; fin_cases l <;> simp [hsq]
    have hw2 : mulCoord w n = ![1, 0, 0, 0] := by
      rw [hw_def, mulCoord_smul_left, mulCoord_conjC']
      funext l; fin_cases l <;> simp [hsq]
    let v : Oˣ :=
      ⟨⟨ofInt n, n, rfl⟩, ⟨ofInt w, w, rfl⟩,
        Subtype.ext (by
          change ofInt n * ofInt w = 1
          rw [ofInt_mul, hw1, ofInt_one]),
        Subtype.ext (by
          change ofInt w * ofInt n = 1
          rw [ofInt_mul, hw2, ofInt_one])⟩
    refine ⟨1, one_ne_zero, v, 1, by simp [T], ?_⟩
    rw [map_one, one_mul, Units.val_one, mul_one]
    exact hu
  · have hm0 : m ≠ 0 := by
      rintro rfl; exact hN0 (Int.natAbs_eq_zero.mp hm)
    set p := m.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime h1
    have hpd : (p : ℤ) ∣ nrdZ n := by
      rw [Int.natCast_dvd, hm]; exact Nat.minFac_dvd m
    have hp1 : 2 ≤ p := hp.two_le
    by_cases hp2 : p = 2
    · have h2 : (2 : ℤ) ∣ nrdZ n := by rw [hp2] at hpd; exact_mod_cast hpd
      have hc := two_dvd_mulCoord_ei n h2
      set n' : Fin 4 → ℤ := fun l => mulCoord n ei l / 2 with hn'_def
      have hn' : mulCoord n ei = fun l => 2 * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hc l)).symm
      have hu' : ((u * ui⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((2 : ℚ)⁻¹) • ofInt ei) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ei = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * ui⁻¹ : Bˣ) : B) * ((ui : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ei
        rw [hmul, nrdZ_ei] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h2' : (-2 : ℤ).natAbs = 2 := rfl
        rw [← hm, e, Int.natAbs_mul, h2']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * ui⁻¹) n' hu' rfl (hN.mul isNorm_ui.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_ui t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * ui⁻¹ : Bˣ) : B) * ui := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    by_cases hp3 : p = 3
    · have h3 : (3 : ℤ) ∣ nrdZ n := by rw [hp3] at hpd; exact_mod_cast hpd
      have hc := three_dvd_mulCoord_ej n h3
      set n' : Fin 4 → ℤ := fun l => -(mulCoord n ej l / 3) with hn'_def
      have hn' : mulCoord n ej = fun l => (-3) * n' l := by
        funext l
        simp only [hn'_def]
        rw [mul_neg, neg_mul, neg_neg, Int.mul_ediv_cancel' (hc l)]
      have hu' : ((u * uj⁻¹ : Bˣ) : B) = ofInt n' := by
        change (u : B) * (((-3 : ℚ)⁻¹) • ofInt ej) = _
        rw [mul_smul_comm, hu, ofInt_mul, hn', ← smul_ofInt, smul_smul]
        norm_num
      have hmul : mulCoord n' ej = n := by
        apply AV.ofInt_injective
        rw [← ofInt_mul, ← hu', ← hu]
        change ((u * uj⁻¹ : Bˣ) : B) * ((uj : Bˣ) : B) = u
        rw [← Units.val_mul, inv_mul_cancel_right]
      have hlt : (nrdZ n').natAbs < m := by
        have e := nrdZ_mul n' ej
        rw [hmul, nrdZ_ej] at e
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        have h3' : (3 : ℤ).natAbs = 3 := rfl
        rw [← hm, e, Int.natAbs_mul, h3']
        omega
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (u * uj⁻¹) n' hu' rfl (hN.mul isNorm_uj.inv)
      obtain ⟨c, hc0, t', ht', htc⟩ := T_mul_uj t ht
      refine ⟨q * c, mul_ne_zero hq hc0, v, t', ht', ?_⟩
      have : (u : B) = ((u * uj⁻¹ : Bˣ) : B) * uj := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [this, he, rearrange q c _ _ _ _ htc]
    · have hdiv := dvd_of_prime_dvd_nrd u n hu hN p hp hp2 hp3 hpd
      set n' : Fin 4 → ℤ := fun l => n l / p with hn'_def
      have hn' : n = fun l => (p : ℤ) * n' l :=
        funext fun l => (Int.mul_ediv_cancel' (hdiv l)).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpi : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero hp0
      have hu' : ((sc _ hpi * u : Bˣ) : B) = ofInt n' := by
        change algebraMap ℚ B ((p : ℚ)⁻¹) * u = _
        rw [← Algebra.smul_def, hu, hn', ← smul_ofInt, smul_smul]
        push_cast
        rw [inv_mul_cancel₀ hp0, one_smul]
      have hlt : (nrdZ n').natAbs < m := by
        have e : nrdZ n = (p : ℤ) ^ 2 * nrdZ n' := by rw [hn', nrdZ_smul]
        have hne : (nrdZ n').natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (nrdZ_ne_zero _ _ hu')
        rw [← hm, e, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        have : 4 ≤ p ^ 2 := by nlinarith
        have : (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs := by
          have : 1 * (nrdZ n').natAbs < p ^ 2 * (nrdZ n').natAbs :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
          simpa using this
        exact this
      obtain ⟨q, hq, v, t, ht, he⟩ :=
        ih _ hlt (sc _ hpi * u) n' hu' rfl ((isNorm_sc _ hpi).mul hN)
      refine ⟨p * q, mul_ne_zero hp0 hq, v, t, ht, ?_⟩
      have : (u : B) = algebraMap ℚ B (p : ℚ) * ((sc _ hpi * u : Bˣ) : B) := by
        change _ = _ * (algebraMap ℚ B ((p : ℚ)⁻¹) * u)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]
      rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

/-! ### `NormalizerFinite` -/

/-- **`N(𝒪)/ℚ^×𝒪^×` is finite** (represented by `{1, i, j, ij}`). -/
theorem normalizerFinite : AutOExt.NormalizerFinite := by
  refine ⟨T, T_finite, fun u hu => ?_⟩
  obtain ⟨m, hm, ⟨n, hn⟩⟩ := AutOExt.exists_nat_smul_mem (u : B)
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu0 : ((sc _ hm0 * u : Bˣ) : B) = ofInt n := by
    change algebraMap ℚ B m * u = _
    rw [← Algebra.smul_def]; exact hn
  have hN : IsNorm u := by
    intro a ha
    refine ⟨(hu a).1 ha, (hu _).2 ?_⟩
    simpa [mul_assoc] using ha
  obtain ⟨q, hq, v, t, ht, he⟩ := descent _ (sc _ hm0 * u) n hu0 rfl ((isNorm_sc _ hm0).mul hN)
  refine ⟨t, ht, v, (m : ℚ)⁻¹ * q, mul_ne_zero (inv_ne_zero hm0) hq, ?_⟩
  have : (u : B) = algebraMap ℚ B ((m : ℚ)⁻¹) * ((sc _ hm0 * u : Bˣ) : B) := by
    change _ = _ * (algebraMap ℚ B m * u)
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hm0, map_one, one_mul]
  rw [this, he, ← mul_assoc, ← mul_assoc, ← map_mul]

end NormO

open CategoryTheory AlgebraicGeometry

/-- **`AutOInnerFinite`, proved** (Skolem–Noether from the kernel, the normalizer from §8). -/
theorem autOInnerFinite : AutOInnerFinite :=
  AutOExt.autOInnerFinite_of_normalizer NormO.normalizerFinite

/-- **`TwistClassFinite` from the leaf `TorsionStructure` alone.** -/
theorem twistClassFinite (hT : ObjBridge.TorsionStructure) : TwistClassFinite :=
  twistClassFinite_of hT autOInnerFinite

/-- **Main result: `MobiusGlueU` from the two curve facts and the textbook leaf
`TorsionStructure` (T5).** -/
theorem mobiusGlue_of_curves (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlueU :=
  mobiusGlue_of_curveFacts hRF hSu (twistClassFinite hT)

/-- **The comparison of two triples from the curve facts and T5.** -/

/-- (g0-assemble2) the repaired `R1fpProps` of Leaves.lean gives mobius-glue's `R1fpPropsU`. -/
theorem r1fpPropsU_of {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1fpProps Y Φ) : R1fpPropsU Y Φ :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩

/-- (g0-assemble2) mobius-glue's `MobiusGlueU` gives Leaves.lean's `MobiusGlue`. -/
theorem mobiusGlue_of_U (h : MobiusGlueU) : MobiusGlue := by
  intro Y Y' Φ Φ' π π' g h1 h2 h1' h2' hCM hΦ y
  exact h Y Y' Φ Φ' π π' g (r1fpPropsU_of h1) h2 (r1fpPropsU_of h1') h2' hCM hΦ y

/-- **`MobiusGlue` (Leaves.lean's) from the two curve facts and T5** (mobius-glue). -/
theorem mobiusGlue_of_curves' (hRF : CurveRatFactor) (hSu : CurveSurj)
    (hT : ObjBridge.TorsionStructure) : MobiusGlue :=
  mobiusGlue_of_U (mobiusGlue_of_curves hRF hSu hT)

end Pin

end AV

end LeafQM
