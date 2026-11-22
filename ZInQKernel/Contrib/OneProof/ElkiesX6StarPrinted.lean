import ZInQKernel.Contrib.OneProof.ElkiesX6Star

/-! # elkies-coord: `ElkiesX6StarPrinted` from Elkies' theorem in his own (function-field) form

Task elkies-coord (docs/research/elkies-coord.md). The research field `elkiesX6StarPrinted`
(`HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted`, gt-elkies) was rated a *consequence*, not printed form,
because its fibre clause is the `ℚ̄`-point form "`t(x) = t(x')` iff `x' ∈ W x`" of Elkies' "`t` is a coordinate on
`X*(6) = X₆/W`". Here:

1. `ffPullback g : ℚ(Z) →+* ℚ(Z)` is the comorphism of an automorphism `g` of an integral scheme on Mathlib's function
   field (the stalk at the generic point), and `fixedByW Ψ ⊆ ℚ(X₆)` the rational functions fixed by every `g ∈ W`
   (`W = atkinLehnerW X Ψ`, gt-elkies' moduli definition of `{1, w₂, w₃, w₆}`).
2. `ElkiesX6StarFunctionField` is Elkies' statement in function-field form: `ℚ(X₆)^W = ℚ(t)` (`t` generates the
   function field of `X₆/W`), with the CM values and the charts `s² = −t`, `r² = 3(t − 1)` (`X6Glue.ElkiesCharts`),
   unchanged from `ElkiesX6StarPrinted`.
3. `elkiesX6StarPrinted_of_functionField : ElkiesX6StarFunctionField → ElkiesX6StarPrinted` (proved). The proof:
   * the charts make `X₆` integral (`ℚ[s, r]/(r² + 3s² + 3)` is a domain, `t.U ∩ t.V ≠ ∅`), so `ℚ(X₆)` is a field;
   * every `g ∈ W` fixes `t ∈ ℚ(X₆)`, hence maps `{t ≠ ∞}` to itself and acts on Elkies' coordinates by signs
     `(s, r) ↦ (c s, d r)` (`conicMapL_comp_of_signs`; the germ calculus of `ffPullback` against the charts);
   * the sign automorphisms `s ↦ −s`, `r ↦ −r` of `ℚ(X₆) = Frac ℚ[t, s, r]/(s² + t, r² − 3(t − 1))` fix `ℚ(t)`
     pointwise, so `ℚ(X₆)^W = ℚ(t)` forces elements of `W` negating `s`, `r` and `s r` (`exists_neg`);
   * the `W`-orbit relation is transitive (gt-elkies' moduli step `orbit_iff_twist` and the composition of twists),
     so `W` realizes all four sign changes, which are exactly the fibres of `t = −s²` on the conic model
     (x6-glue's bijection `conicMapL`).
-/

namespace HDec.QMSplit.Moduli.ElkiesCoord

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

section FF

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem gen_specializes (g : Z ≅ Z) : g.hom (genericPoint Z) ⤳ genericPoint Z := by
  rw [genericPoint_eq_of_isOpenImmersion g.hom]

/-- The comorphism `g^* : ℚ(Z) → ℚ(Z)`, `φ ↦ φ ∘ g`, of an automorphism `g` of an integral scheme on
its function field (the stalk at the generic point; `g` fixes the generic point). -/
noncomputable def ffPullback (g : Z ≅ Z) : Z.functionField →+* Z.functionField :=
  (Z.presheaf.stalkSpecializes (gen_specializes g) ≫ g.hom.stalkMap (genericPoint Z)).hom

theorem ffPullback_germ (g : Z ≅ Z) (A : Z.Opens) (hA : genericPoint Z ∈ A)
    (hA' : genericPoint Z ∈ g.hom ⁻¹ᵁ A) (s : Γ(Z, A)) :
    ffPullback g (Z.presheaf.germ A _ hA s) = Z.presheaf.germ (g.hom ⁻¹ᵁ A) _ hA' (g.hom.app A s) := by
  unfold ffPullback
  rw [CommRingCat.comp_apply, ← ConcreteCategory.comp_apply (Z.presheaf.germ A _ hA),
    TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap_apply]

/-- Sections over two opens with the same germ at the generic point agree on the intersection. -/
theorem res_eq_of_germ_eq {A B : Z.Opens} (hA : genericPoint Z ∈ A) (hB : genericPoint Z ∈ B)
    (a : Γ(Z, A)) (b : Γ(Z, B)) (h : Z.presheaf.germ A _ hA a = Z.presheaf.germ B _ hB b) :
    Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a =
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b := by
  have hAB : genericPoint Z ∈ A ⊓ B := ⟨hA, hB⟩
  apply germ_injective_of_isIntegral Z (genericPoint Z) hAB
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact h

end FF

/-! ## Values of sections at field points -/

section Ev

variable {Z : Scheme.{0}} {K : Type} [Field K]

theorem pt_comp {Z' : Scheme.{0}} (h : Z ⟶ Z') (y : Spec (CommRingCat.of K) ⟶ Z) :
    (Scheme.SpecToEquivOfField K Z' (y ≫ h)).1 = h (Scheme.SpecToEquivOfField K Z y).1 := by
  rw [_root_.LeafQM.AV.specToEquivOfField_comp_right]

theorem ev_comp_hom {Z' : Scheme.{0}} (h : Z ⟶ Z') (A : Z'.Opens) (y : Spec (CommRingCat.of K) ⟶ Z)
    (hA : (Scheme.SpecToEquivOfField K Z' (y ≫ h)).1 ∈ A)
    (hA' : (Scheme.SpecToEquivOfField K Z y).1 ∈ h ⁻¹ᵁ A) (s : Γ(Z', A)) :
    X6Glue.ev A (y ≫ h) hA s = X6Glue.ev (h ⁻¹ᵁ A) y hA' (h.app A s) := by
  rw [X6Glue.ev_apply, X6Glue.ev_apply]
  generalize hp : Scheme.SpecToEquivOfField K Z' (y ≫ h) = p at hA
  rw [_root_.LeafQM.AV.specToEquivOfField_comp_right] at hp
  subst hp
  rw [ConcreteCategory.comp_apply, Scheme.evaluation_naturality_apply]

theorem ev_res {A A' : Z.Opens} (i : A' ⟶ A) (y : Spec (CommRingCat.of K) ⟶ Z)
    (h' : (Scheme.SpecToEquivOfField K Z y).1 ∈ A') (s : Γ(Z, A)) :
    X6Glue.ev A' y h' (Z.presheaf.map i.op s) = X6Glue.ev A y (i.le h') s := by
  rw [X6Glue.ev_apply, X6Glue.ev_apply]
  congr 1
  simp only [Scheme.evaluation, ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res_apply]

theorem ev_eq_of_germ_eq [IsIntegral Z] {A B : Z.Opens} (hA : genericPoint Z ∈ A)
    (hB : genericPoint Z ∈ B) (a : Γ(Z, A)) (b : Γ(Z, B))
    (h : Z.presheaf.germ A _ hA a = Z.presheaf.germ B _ hB b)
    (y : Spec (CommRingCat.of K) ⟶ Z) (hyA : (Scheme.SpecToEquivOfField K Z y).1 ∈ A)
    (hyB : (Scheme.SpecToEquivOfField K Z y).1 ∈ B) :
    X6Glue.ev A y hyA a = X6Glue.ev B y hyB b := by
  have hAB : (Scheme.SpecToEquivOfField K Z y).1 ∈ A ⊓ B := ⟨hyA, hyB⟩
  have e1 := ev_res (homOfLE (inf_le_left : A ⊓ B ≤ A)) y hAB a
  have e2 := ev_res (homOfLE (inf_le_right : A ⊓ B ≤ B)) y hAB b
  rw [res_eq_of_germ_eq hA hB a b h] at e1
  exact e1.symm.trans e2

theorem ev_mul_eq_one_of_germ [IsIntegral Z] {A B : Z.Opens} (hA : genericPoint Z ∈ A)
    (hB : genericPoint Z ∈ B) (a : Γ(Z, A)) (b : Γ(Z, B))
    (h : Z.presheaf.germ A _ hA a * Z.presheaf.germ B _ hB b = 1)
    (y : Spec (CommRingCat.of K) ⟶ Z) (hyA : (Scheme.SpecToEquivOfField K Z y).1 ∈ A)
    (hyB : (Scheme.SpecToEquivOfField K Z y).1 ∈ B) :
    X6Glue.ev A y hyA a * X6Glue.ev B y hyB b = 1 := by
  have hAB : (Scheme.SpecToEquivOfField K Z y).1 ∈ A ⊓ B := ⟨hyA, hyB⟩
  have hη : genericPoint Z ∈ A ⊓ B := ⟨hA, hB⟩
  have e : Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a *
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b = 1 := by
    apply germ_injective_of_isIntegral Z _ hη
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact h
  have := congrArg (X6Glue.ev (A ⊓ B) y hAB) e
  rw [map_mul, map_one, ev_res, ev_res] at this
  exact this

end Ev

/-! ## Elkies' ring: points and sign automorphisms -/

section Ring

open X6Glue

theorem exists_sq_eq (a : Qbar) : ∃ b : Qbar, b ^ 2 = a :=
  IsAlgClosed.exists_pow_nat_eq a two_pos

theorem eS_ne_zero : (eS : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  intro h
  have := congrArg (elkiesLift (K := Qbar) (-1) 1 b (by ring) (by linear_combination hb)) h
  rw [elkiesLift_S, map_zero] at this
  exact one_ne_zero this

theorem eT_ne_zero : (eT : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  intro h
  have := congrArg (elkiesLift (K := Qbar) (-1) 1 b (by ring) (by linear_combination hb)) h
  rw [elkiesLift_T, map_zero] at this
  exact neg_ne_zero.mpr one_ne_zero this

theorem eR_ne_zero : (eR : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-3)
  intro h
  have := congrArg (elkiesLift (K := Qbar) 0 0 b (by ring) (by linear_combination hb)) h
  rw [elkiesLift_R, map_zero] at this
  subst this
  norm_num at hb

theorem two_ne_zero' : (2 : ElkiesRing) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-3)
  intro h
  have := congrArg (elkiesLift (K := Qbar) 0 0 b (by ring) (by linear_combination hb)) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

/-- `s ↦ −s` on Elkies' ring. -/
noncomputable def negSHom : ElkiesRing →+* ElkiesRing :=
  elkiesLift (K := ElkiesRing) eT (-eS) eR (by linear_combination rel1) (by linear_combination rel2)

/-- `r ↦ −r` on Elkies' ring. -/
noncomputable def negRHom : ElkiesRing →+* ElkiesRing :=
  elkiesLift (K := ElkiesRing) eT eS (-eR) (by linear_combination rel1) (by linear_combination rel2)

theorem negSHom_invol : negSHom.comp negSHom = RingHom.id _ := by
  apply elkies_hom_ext
  · simp [negSHom, elkiesLift_S]
  · simp [negSHom, elkiesLift_R]

theorem negRHom_invol : negRHom.comp negRHom = RingHom.id _ := by
  apply elkies_hom_ext
  · simp [negRHom, elkiesLift_S]
  · simp [negRHom, elkiesLift_R]

noncomputable def negS : ElkiesRing ≃+* ElkiesRing :=
  RingEquiv.ofRingHom negSHom negSHom negSHom_invol negSHom_invol

noncomputable def negR : ElkiesRing ≃+* ElkiesRing :=
  RingEquiv.ofRingHom negRHom negRHom negRHom_invol negRHom_invol

theorem negS_T : negS eT = eT := by
  show negSHom eT = _; simp [negSHom, elkiesLift_T]
theorem negS_S : negS eS = -eS := by
  show negSHom eS = _; simp [negSHom, elkiesLift_S]
theorem negS_R : negS eR = eR := by
  show negSHom eR = _; simp [negSHom, elkiesLift_R]
theorem negR_T : negR eT = eT := by
  show negRHom eT = _; simp [negRHom, elkiesLift_T]
theorem negR_S : negR eS = eS := by
  show negRHom eS = _; simp [negRHom, elkiesLift_S]
theorem negR_R : negR eR = -eR := by
  show negRHom eR = _; simp [negRHom, elkiesLift_R]

end Ring

theorem unit_cast_sq {R : Type*} [Ring R] (c : ℤˣ) : ((c : ℤ) : R) ^ 2 = 1 := by
  rcases Int.units_eq_one_or c with rfl | rfl <;> simp

/-- Sign changes `(s, r) ↦ (c s, d r)` on the conic's `ℚ̄`-points (on the points at infinity
`b ↦ c d b`, since `b = r/s`). -/
noncomputable def signAct (c d : ℤˣ) : HDec.X6Kummer.ConicPt → HDec.X6Kummer.ConicPt
  | Sum.inl p => Sum.inl ⟨(((c : ℤ) : Qbar) * p.1.1, ((d : ℤ) : Qbar) * p.1.2), by
      have hc : ((c : ℤ) : Qbar) ^ 2 = 1 := by
        exact unit_cast_sq _
      have hd : ((d : ℤ) : Qbar) ^ 2 = 1 := by
        exact unit_cast_sq _
      have := p.2
      simp only at this ⊢
      linear_combination (p.1.2 ^ 2) * hd + 3 * p.1.1 ^ 2 * hc + this⟩
  | Sum.inr b => Sum.inr ⟨((((c * d : ℤˣ)) : ℤ) : Qbar) * b.1, by
      have hc : ((((c * d : ℤˣ)) : ℤ) : Qbar) ^ 2 = 1 := by
        exact unit_cast_sq _
      have := b.2
      linear_combination (b.1 ^ 2) * hc + this⟩


/-! ## The charts: rational functions `t, s, r` and the action of a `t`-preserving automorphism -/

section Charts

open X6Glue

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left} [IsIntegral X.left]

/-- `ElkiesRing → Γ(t.U) → ℚ(X)`. -/
noncomputable abbrev jU (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (hηU : genericPoint X.left ∈ t.U) :
    ElkiesRing →+* X.left.functionField :=
  (X.left.presheaf.germ t.U _ hηU).hom.comp (φU : ElkiesRing →+* Γ(X.left, t.U))

/-- `ElkiesRing → Γ(t.V) → ℚ(X)`. -/
noncomputable abbrev jV (φV : ElkiesRing ≃+* Γ(X.left, t.V)) (hηV : genericPoint X.left ∈ t.V) :
    ElkiesRing →+* X.left.functionField :=
  (X.left.presheaf.germ t.V _ hηV).hom.comp (φV : ElkiesRing →+* Γ(X.left, t.V))

variable (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V))
  (hηU : genericPoint X.left ∈ t.U) (hηV : genericPoint X.left ∈ t.V)

theorem jU_injective : Function.Injective (jU φU hηU) :=
  (germ_injective_of_isIntegral X.left _ hηU).comp φU.injective

theorem germ_inv_rel (hT : φU eT = t.f) (hTg : φV eT = t.g) : jU φU hηU eT * jV φV hηV eT = 1 := by
  have hη : genericPoint X.left ∈ t.U ⊓ t.V := ⟨hηU, hηV⟩
  have := congrArg (X.left.presheaf.germ (t.U ⊓ t.V) _ hη) t.inv
  rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
  simpa [jU, jV, hT, hTg] using this

theorem germ_glue1
    (hg1 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eS) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) = 1) :
    jU φU hηU eS * jV φV hηV eS = 1 := by
  have hη : genericPoint X.left ∈ t.U ⊓ t.V := ⟨hηU, hηV⟩
  have := congrArg (X.left.presheaf.germ (t.U ⊓ t.V) _ hη) hg1
  rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this
  simpa [jU, jV] using this

theorem germ_glue2
    (hg2 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eR) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) =
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eR)) :
    jU φU hηU eR * jV φV hηV eS = jV φV hηV eR := by
  have hη : genericPoint X.left ∈ t.U ⊓ t.V := ⟨hηU, hηV⟩
  have := congrArg (X.left.presheaf.germ (t.U ⊓ t.V) _ hη) hg2
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply] at this
  simpa [jU, jV] using this

theorem sigma_inv_of {F : Type*} [Field F] (σ : F →+* F) (a b : F) (c : ℤˣ)
    (hS : σ a = ((c : ℤ) : F) * a) (h1 : a * b = 1) : σ b = ((c : ℤ) : F) * b := by
  have e := congrArg σ h1
  rw [map_mul, map_one, hS] at e
  have hc := unit_cast_sq (R := F) c
  linear_combination (((c : ℤ) : F) * b) * e - σ b * ((c : ℤ) : F) ^ 2 * h1 - σ b * hc

theorem mem_preimage_gen (g : X.left ≅ X.left) {A : X.left.Opens} (h : genericPoint X.left ∈ A) :
    genericPoint X.left ∈ g.hom ⁻¹ᵁ A := by
  show g.hom (genericPoint X.left) ∈ A
  rw [genericPoint_eq_of_isOpenImmersion g.hom]
  exact h

omit [IsIntegral X.left] in
theorem mem_preimage_pt (g : X.left ≅ X.left) {A : X.left.Opens} (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (h : (Scheme.SpecToEquivOfField Qbar X.left (y ≫ g.hom)).1 ∈ A) :
    (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ g.hom ⁻¹ᵁ A := by
  show g.hom _ ∈ A
  rw [← pt_comp]
  exact h

theorem pullback_jU (g : X.left ≅ X.left) (a : ElkiesRing) :
    ffPullback g (jU φU hηU a) =
      X.left.presheaf.germ (g.hom ⁻¹ᵁ t.U) _ (mem_preimage_gen g hηU) (g.hom.app t.U (φU a)) := by
  simp only [jU, RingHom.comp_apply, RingHom.coe_coe]
  exact ffPullback_germ g t.U hηU _ _

theorem pullback_jV (g : X.left ≅ X.left) (a : ElkiesRing) :
    ffPullback g (jV φV hηV a) =
      X.left.presheaf.germ (g.hom ⁻¹ᵁ t.V) _ (mem_preimage_gen g hηV) (g.hom.app t.V (φV a)) := by
  simp only [jV, RingHom.comp_apply, RingHom.coe_coe]
  exact ffPullback_germ g t.V hηV _ _

variable {φU φV}

include hηV in
/-- A `t`-preserving automorphism maps `t.U = {t ≠ ∞}` onto itself (on `ℚ̄`-points). -/
theorem memU_comp_iff (hT : φU eT = t.f) (hTg : φV eT = t.g) (g : X.left ≅ X.left)
    (hτ : ffPullback g (jU φU hηU eT) = jU φU hηU eT) (y : Spec (CommRingCat.of Qbar) ⟶ X.left) :
    pt (X := X) (y ≫ g.hom) ∈ t.U ↔ pt (X := X) y ∈ t.U := by
  have hinv := germ_inv_rel φU φV hηU hηV hT hTg
  have hτ' : ffPullback g (jV φV hηV eT) = jV φV hηV eT := by
    have e := congrArg (ffPullback g) hinv
    rw [map_mul, map_one, hτ] at e
    rw [eq_inv_of_mul_eq_one_right e, eq_inv_of_mul_eq_one_right hinv]
  have gf : X.left.presheaf.germ t.U _ hηU t.f = jU φU hηU eT := by simp [jU, hT]
  have gg : X.left.presheaf.germ t.V _ hηV t.g = jV φV hηV eT := by simp [jV, hTg]
  constructor
  · intro h'
    by_contra h
    have hv := memV_of_not_memU (X := X) (t := t) y h
    have h0 := ev_g_eq_zero (X := X) (t := t) y h hv
    have hm := mem_preimage_pt g y h'
    have key := ev_mul_eq_one_of_germ (mem_preimage_gen g hηU) hηV (g.hom.app t.U t.f) t.g
      (by rw [← ffPullback_germ g t.U hηU, gf, gg, hτ, hinv]) y hm hv
    rw [h0, mul_zero] at key
    exact zero_ne_one key
  · intro h
    by_contra h'
    have hv := memV_of_not_memU (X := X) (t := t) (y ≫ g.hom) h'
    have h0 := ev_g_eq_zero (X := X) (t := t) (y ≫ g.hom) h' hv
    have hm := mem_preimage_pt g y hv
    rw [ev_comp_hom g.hom t.V y hv hm] at h0
    have key := ev_mul_eq_one_of_germ (mem_preimage_gen g hηV) hηU (g.hom.app t.V t.g) t.f
      (by rw [← ffPullback_germ g t.V hηV, gf, gg, hτ', mul_comm, hinv]) y hm h
    rw [h0, zero_mul] at key
    exact zero_ne_one key

include hηV in
/-- **A `t`-preserving automorphism acts on Elkies' coordinates by signs.** If `g^*t = t`,
`g^*s = c s` and `g^*r = d r` in `ℚ(X)`, then on `ℚ̄`-points `g` is `(s, r) ↦ (c s, d r)` (and
`b ↦ c d b` at `t = ∞`). -/
theorem conicMapL_comp_of_signs (hT : φU eT = t.f) (hTg : φV eT = t.g)
    (hg1 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eS) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) = 1)
    (hg2 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eR) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) =
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eR))
    (g : X.left ≅ X.left) (c d : ℤˣ)
    (hτ : ffPullback g (jU φU hηU eT) = jU φU hηU eT)
    (hS : ffPullback g (jU φU hηU eS) = ((c : ℤ) : X.left.functionField) * jU φU hηU eS)
    (hR : ffPullback g (jU φU hηU eR) = ((d : ℤ) : X.left.functionField) * jU φU hηU eR)
    (y : Spec (CommRingCat.of Qbar) ⟶ X.left) :
    conicMapL φU φV hTg (y ≫ g.hom) = signAct c d (conicMapL φU φV hTg y) := by
  have hmem := memU_comp_iff hηU hηV hT hTg g hτ y
  by_cases h : pt (X := X) y ∈ t.U
  · have h' := hmem.mpr h
    have hm := mem_preimage_pt g y h'
    rw [conicMapL, dif_pos h', conicMapL, dif_pos h]
    simp only [signAct]
    congr 1
    apply Subtype.ext
    -- each coordinate
    have coord : ∀ (a : ElkiesRing) (e : ℤˣ),
        ffPullback g (jU φU hηU a) = ((e : ℤ) : X.left.functionField) * jU φU hηU a →
        psiU φU (y ≫ g.hom) h' a = ((e : ℤ) : Qbar) * psiU φU y h a := by
      intro a e he
      simp only [psiU, RingHom.comp_apply, RingHom.coe_coe]
      rw [ev_comp_hom g.hom t.U y h' hm]
      rw [ev_eq_of_germ_eq (mem_preimage_gen g hηU) hηU _ (((e : ℤ) : Γ(X.left, t.U)) * φU a) _ y hm h]
      · rw [map_mul, map_intCast]
      · rw [← pullback_jU φU hηU g a, he, map_mul, map_intCast]
        rfl
    simp only
    rw [coord eS c hS, coord eR d hR]
  · have h' : ¬ pt (X := X) (y ≫ g.hom) ∈ t.U := fun hh => h (hmem.mp hh)
    have hv' := memV_of_not_memU (X := X) (t := t) (y ≫ g.hom) h'
    have hv := memV_of_not_memU (X := X) (t := t) y h
    have hm := mem_preimage_pt g y hv'
    rw [conicMapL, dif_neg h', conicMapL, dif_neg h]
    simp only [signAct]
    congr 1
    apply Subtype.ext
    simp only
    have e1 := germ_glue1 φU φV hηU hηV hg1
    have e2 := germ_glue2 φU φV hηU hηV hg2
    have hS' := sigma_inv_of (ffPullback g) _ _ c hS e1
    have hR' : ffPullback g (jV φV hηV eR) =
        ((((c * d : ℤˣ)) : ℤ) : X.left.functionField) * jV φV hηV eR := by
      rw [← e2, map_mul, hR, hS']
      push_cast
      ring
    simp only [psiV, RingHom.comp_apply, RingHom.coe_coe]
    rw [ev_comp_hom g.hom t.V y hv' hm]
    rw [ev_eq_of_germ_eq (mem_preimage_gen g hηV) hηV _
      (((((c * d : ℤˣ)) : ℤ) : Γ(X.left, t.V)) * φV eR) _ y hm hv]
    · rw [map_mul, map_intCast]
    · rw [← pullback_jV φV hηV g eR, hR', map_mul, map_intCast]
      rfl

end Charts

/-! ## Sign changes from `ℚ(X)^W = ℚ(t)` -/

section Fixed

theorem not_mem_closure {F : Type*} [Field F] (θ : F ≃+* F) (τ x : F) (hθτ : θ τ = τ)
    (hx : θ x = -x) (hx0 : x ≠ 0) (h2 : (2 : F) ≠ 0) : x ∉ Subfield.closure {τ} := by
  intro hmem
  have hle : Subfield.closure {τ} ≤ RingHom.eqLocusField (θ : F →+* F) (RingHom.id F) := by
    rw [Subfield.closure_le, Set.singleton_subset_iff]
    exact hθτ
  have h' : θ x = x := hle hmem
  rw [hx] at h'
  have : (2 : F) * x = 0 := by linear_combination -h'
  exact hx0 ((mul_eq_zero.mp this).resolve_left h2)

/-- If the fixed field of a family of field endomorphisms is `closure {τ}` and an automorphism `θ`
fixing `τ` negates `x ≠ 0`, while each member of the family sends `x` to `±x`, then some member
sends `x` to `−x`. -/
theorem exists_neg {F : Type*} [Field F] {ι : Type*} (W : Set ι) (σ : ι → F →+* F) (τ x : F)
    (hfix : {φ : F | ∀ g ∈ W, σ g φ = φ} = Subfield.closure {τ})
    (hpm : ∀ g ∈ W, σ g x = x ∨ σ g x = -x) (θ : F ≃+* F) (hθτ : θ τ = τ) (hx : θ x = -x)
    (hx0 : x ≠ 0) (h2 : (2 : F) ≠ 0) : ∃ g ∈ W, σ g x = -x := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hm : x ∈ {φ : F | ∀ g ∈ W, σ g φ = φ} := fun g hg => (hpm g hg).resolve_right (hne g hg)
  rw [hfix] at hm
  exact not_mem_closure θ τ x hθτ hx hx0 h2 hm

theorem sq_pm {F : Type*} [Field F] (σ : F →+* F) (x y : F) (hy : σ y = y) (h : x ^ 2 = y) :
    σ x = x ∨ σ x = -x := by
  have : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, h, hy]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem pm_unit {F : Type*} [Field F] (a b : F) (h : a = b ∨ a = -b) :
    ∃ c : ℤˣ, a = ((c : ℤ) : F) * b := by
  rcases h with h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

/-- The four sign pairs from three generators, in a set closed under products. -/
theorem all_signs (P : ℤˣ → ℤˣ → Prop) (hmul : ∀ c d c' d', P c d → P c' d' → P (c * c') (d * d'))
    (h1 : ∃ d, P (-1) d) (h2 : ∃ c, P c (-1)) (h3 : ∃ c d, c * d = -1 ∧ P c d) : ∀ c d, P c d := by
  obtain ⟨d1, p1⟩ := h1
  obtain ⟨c2, p2⟩ := h2
  obtain ⟨c3, d3, hcd, p3⟩ := h3
  have key : P (-1) 1 ∧ P 1 (-1) := by
    rcases Int.units_eq_one_or c3 with rfl | rfl <;> rcases Int.units_eq_one_or d3 with rfl | rfl
    · exact absurd hcd (by decide)
    · refine ⟨?_, p3⟩
      rcases Int.units_eq_one_or d1 with rfl | rfl
      · exact p1
      · simpa using hmul _ _ _ _ p1 p3
    · refine ⟨p3, ?_⟩
      rcases Int.units_eq_one_or c2 with rfl | rfl
      · exact p2
      · simpa using hmul _ _ _ _ p2 p3
    · exact absurd hcd (by decide)
  obtain ⟨pa, pb⟩ := key
  intro c d
  rcases Int.units_eq_one_or c with rfl | rfl <;> rcases Int.units_eq_one_or d with rfl | rfl
  · simpa using hmul _ _ _ _ pa pa
  · exact pb
  · exact pa
  · simpa using hmul _ _ _ _ pa pb

theorem signAct_signAct (c d c' d' : ℤˣ) (p : HDec.X6Kummer.ConicPt) :
    signAct c' d' (signAct c d p) = signAct (c * c') (d * d') p := by
  rcases p with p | b
  · simp only [signAct]
    congr 1
    apply Subtype.ext
    simp only [Units.val_mul, Int.cast_mul]
    ext <;> simp only <;> ring
  · simp only [signAct]
    congr 1
    apply Subtype.ext
    simp only [Units.val_mul, Int.cast_mul]
    ring

end Fixed

/-! ## The automorphism of `ℚ(X)` induced by a sign automorphism of Elkies' ring -/

section Theta

open X6Glue

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left} [IsIntegral X.left]
  (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (hU : IsAffineOpen t.U) (hηU : genericPoint X.left ∈ t.U)

/-- The automorphism of `ℚ(X) = Frac Γ(t.U)` induced by an automorphism of `Γ(t.U) ≅ ElkiesRing`. -/
noncomputable def thetaOf (e : ElkiesRing ≃+* ElkiesRing) :
    X.left.functionField ≃+* X.left.functionField :=
  haveI : Nonempty t.U := ⟨⟨_, hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X.left t.U hU
  IsFractionRing.ringEquivOfRingEquiv (A := Γ(X.left, t.U)) (B := Γ(X.left, t.U))
    (φU.symm.trans (e.trans φU))

theorem thetaOf_jU (e : ElkiesRing ≃+* ElkiesRing) (a : ElkiesRing) :
    thetaOf φU hU hηU e (jU φU hηU a) = jU φU hηU (e a) := by
  have : Nonempty t.U := ⟨⟨_, hηU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X.left t.U hU
  have := IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := X.left.functionField)
    (L := X.left.functionField) (φU.symm.trans (e.trans φU)) (φU a)
  have h2 : (φU.symm.trans (e.trans φU)) (φU a) = φU (e a) := by simp
  rw [h2] at this
  exact this

end Theta

/-! ## Values of `t` and sign changes -/

section Values

open X6Glue

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}
  {φU : ElkiesRing ≃+* Γ(X.left, t.U)} {φV : ElkiesRing ≃+* Γ(X.left, t.V)}

theorem val_eq_of_signAct (hT : φU eT = t.f) (hTg : φV eT = t.g) (y y' : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (c d : ℤˣ) (h : conicMapL φU φV hTg y' = signAct c d (conicMapL φU φV hTg y)) :
    t.val y = t.val y' := by
  rcases hy : conicMapL φU φV hTg y with p | b
  · rw [hy] at h
    simp only [signAct] at h
    rw [val_of_inl φU φV hTg hT y p hy, val_of_inl φU φV hTg hT y' _ h]
    congr 1
    simp only
    have hc := unit_cast_sq (R := Qbar) c
    linear_combination (p.1.1 ^ 2) * hc
  · rw [hy] at h
    simp only [signAct] at h
    rw [val_of_inr φU φV hTg y b hy, val_of_inr φU φV hTg y' _ h]

theorem signAct_of_val (hT : φU eT = t.f) (hTg : φV eT = t.g) (y y' : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (h : t.val y = t.val y') :
    ∃ c d : ℤˣ, conicMapL φU φV hTg y' = signAct c d (conicMapL φU φV hTg y) := by
  rcases hy : conicMapL φU φV hTg y with p | b <;> rcases hy' : conicMapL φU φV hTg y' with p' | b'
  · rw [val_of_inl φU φV hTg hT y p hy, val_of_inl φU φV hTg hT y' p' hy'] at h
    have h1 : p'.1.1 ^ 2 = p.1.1 ^ 2 := by
      have := Option.some_injective _ h
      linear_combination this
    have h2 : p'.1.2 ^ 2 = p.1.2 ^ 2 := by
      linear_combination p'.2 - p.2 - 3 * h1
    obtain ⟨c, hc⟩ := pm_unit _ _ (sq_eq_sq_iff_eq_or_eq_neg.mp h1)
    obtain ⟨d, hd⟩ := pm_unit _ _ (sq_eq_sq_iff_eq_or_eq_neg.mp h2)
    refine ⟨c, d, ?_⟩
    simp only [signAct]
    congr 1
    apply Subtype.ext
    ext
    · exact hc
    · exact hd
  · rw [val_of_inl φU φV hTg hT y p hy, val_of_inr φU φV hTg y' b' hy'] at h
    exact absurd h (OnePoint.coe_ne_infty _)
  · rw [val_of_inr φU φV hTg y b hy, val_of_inl φU φV hTg hT y' p' hy'] at h
    exact absurd h.symm (OnePoint.coe_ne_infty _)
  · have h1 : b'.1 ^ 2 = b.1 ^ 2 := by rw [b.2, b'.2]
    obtain ⟨d, hd⟩ := pm_unit _ _ (sq_eq_sq_iff_eq_or_eq_neg.mp h1)
    refine ⟨1, d, ?_⟩
    simp only [signAct]
    congr 1
    apply Subtype.ext
    simpa using hd

end Values

/-! ## Twists compose -/

section Twist

variable {K : Type} [Field K]

/-- Twisting both sides of an isomorphism of QM pairs by the same `β`. -/
def twistIso {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (e : QMIso q q')
    (β : _root_.LeafQM.O ≃+* _root_.LeafQM.O) : QMIso (q.twist β) (q'.twist β) where
  φ := e.φ
  ψ := e.ψ
  left := e.left
  right := e.right
  equivariant a := e.equivariant (β a)

/-- `(ι ∘ α) ∘ β = ι ∘ (α ∘ β)`. -/
def twistComp {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'}
    (α β : _root_.LeafQM.O ≃+* _root_.LeafQM.O) (e : QMIso ((q.twist α).twist β) q') :
    QMIso (q.twist (β.trans α)) q' where
  φ := e.φ
  ψ := e.ψ
  left := e.left
  right := e.right
  equivariant a := e.equivariant a

end Twist

section Orbit

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {X : Over (Spec (CommRingCat.of ℚ))}
  {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}

/-- The `W`-orbit relation on `X₆(ℚ̄)` is transitive (through the moduli step `orbit_iff_twist`). -/
theorem orbit_trans (h6 : X6Props Y Φ X Ψ fY) {x x₁ x₂ : fieldPt Qbar ⟶ X}
    (h01 : ∃ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, x ≫ g.hom = x₁)
    (h12 : ∃ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, x₁ ≫ g.hom = x₂) :
    ∃ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, x ≫ g.hom = x₂ := by
  have hP : Ψ x = Quotient.mk _ (Ψ x).out := (Quotient.out_eq _).symm
  have hQ1 : Ψ x₁ = Quotient.mk _ (Ψ x₁).out := (Quotient.out_eq _).symm
  have hQ2 : Ψ x₂ = Quotient.mk _ (Ψ x₂).out := (Quotient.out_eq _).symm
  obtain ⟨α, ⟨e1⟩⟩ := (ElkiesX6Star.orbit_iff_twist h6 x x₁ _ _ hP hQ1).mp h01
  obtain ⟨β, ⟨e2⟩⟩ := (ElkiesX6Star.orbit_iff_twist h6 x₁ x₂ _ _ hQ1 hQ2).mp h12
  exact (ElkiesX6Star.orbit_iff_twist h6 x x₂ _ _ hP hQ2).mpr
    ⟨β.trans α, ⟨twistComp α β ((twistIso e1 β).trans e2)⟩⟩

end Orbit

/-! ## Elkies' ring is a domain -/

section Domain

open X6Glue Polynomial

/-- `r² + 3(s² + 1)` over `ℚ[s]` (Elkies' ring with `t = −s²` eliminated). -/
noncomputable def conicPoly : (Polynomial ℚ)[X] := X ^ 2 + C (3 * (X ^ 2 + 1))

theorem conicPoly_monic : conicPoly.Monic := monic_X_pow_add_C _ two_ne_zero

theorem conicPoly_natDegree : conicPoly.natDegree = 2 := natDegree_X_pow_add_C

theorem conicPoly_not_isRoot (b : Polynomial ℚ) : ¬ conicPoly.IsRoot b := by
  intro h
  simp only [conicPoly, IsRoot, eval_add, eval_pow, eval_X, eval_C] at h
  have hm : (X ^ 2 + C 1 : Polynomial ℚ).Monic := monic_X_pow_add_C _ two_ne_zero
  have h' : b ^ 2 = C (-3) * (X ^ 2 + C 1) := by
    rw [map_neg, map_one]
    have : (C 3 : Polynomial ℚ) = 3 := rfl
    linear_combination h + (X ^ 2 + 1) * this
  have := congrArg leadingCoeff h'
  rw [leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_C, hm.leadingCoeff] at this
  nlinarith [sq_nonneg (leadingCoeff b)]

theorem conicPoly_irreducible : Irreducible conicPoly := by
  rw [conicPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [conicPoly_natDegree])
    (by rw [conicPoly_natDegree]; norm_num)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro b hb
  rw [mem_roots conicPoly_monic.ne_zero] at hb
  exact conicPoly_not_isRoot b hb

theorem conicPoly_prime : Prime conicPoly :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp conicPoly_irreducible

instance : IsDomain (AdjoinRoot conicPoly) := AdjoinRoot.isDomain_of_prime conicPoly_prime

/-- `ElkiesRing → ℚ[s][r]/(r² + 3(s² + 1))`, `t ↦ −s²`. -/
noncomputable def toAdj : ElkiesRing →+* AdjoinRoot conicPoly :=
  elkiesLift (K := AdjoinRoot conicPoly) (-(AdjoinRoot.of conicPoly X) ^ 2) (AdjoinRoot.of conicPoly X)
    (AdjoinRoot.root conicPoly) (by ring) (by
      have h : AdjoinRoot.mk conicPoly (X ^ 2 + C (3 * (X ^ 2 + 1))) = 0 := AdjoinRoot.mk_self
      rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_mul, map_add, map_pow, map_one,
        map_ofNat] at h
      linear_combination h)

/-- The inverse direction. -/
noncomputable def fromAdj : AdjoinRoot conicPoly →+* ElkiesRing :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap ℚ ElkiesRing) eS) eR (by
    have e1 := rel1
    have e2 := rel2
    simp only [conicPoly, eval₂_add, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom, eval₂_mul,
      eval₂_ofNat, eval₂_one]
    linear_combination e2 + 3 * e1)

theorem fromAdj_toAdj : fromAdj.comp toAdj = RingHom.id _ := by
  apply elkies_hom_ext
  · simp [toAdj, fromAdj, elkiesLift_S]
  · simp [toAdj, fromAdj, elkiesLift_R]

instance elkiesRing_isDomain : IsDomain ElkiesRing := by
  have hinj : Function.Injective toAdj := by
    intro a b h
    have := congrArg fromAdj h
    simpa [← RingHom.comp_apply, fromAdj_toAdj] using this
  exact hinj.isDomain toAdj

end Domain

/-! ## `X₆` is integral, from the charts -/

section Integral

open X6Glue

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}

theorem isIntegral_open {A : X.left.Opens} (hA : IsAffineOpen A) (φ : ElkiesRing ≃+* Γ(X.left, A))
    (hne : (A : Set X.left).Nonempty) : IsIntegral A.toScheme := by
  have : IsAffine A.toScheme := hA
  have : Nonempty A.toScheme := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : IsDomain Γ(X.left, A) := φ.symm.injective.isDomain (φ.symm : Γ(X.left, A) →+* ElkiesRing)
  have : IsDomain Γ(A.toScheme, ⊤) :=
    (A.topIso.commRingCatIsoToRingEquiv).injective.isDomain
      (A.topIso.commRingCatIsoToRingEquiv : Γ(A.toScheme, ⊤) →+* Γ(X.left, A))
  exact isIntegral_of_isAffine_of_isDomain A.toScheme

theorem isIrreducible_open {A : X.left.Opens} (h : IsIntegral A.toScheme) :
    IsIrreducible (A : Set X.left) := by
  have := (IrreducibleSpace.isIrreducible_univ A.toScheme).image A.ι A.ι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.Opens.range_ι] at this

/-- A `ℚ̄`-point of `t.U ∩ t.V` (where `s = 1`, `r = √−6`, `t = −1`). -/
theorem exists_pt_inter (hU : IsAffineOpen t.U) (hV : IsAffineOpen t.V)
    (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V))
    (hT : φU eT = t.f) (hTg : φV eT = t.g) :
    ∃ p : X.left, p ∈ t.U ∧ p ∈ t.V := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  obtain ⟨y, hy⟩ := conicMapL_surjective φU φV hTg hU hV
    (Sum.inl ⟨(1, b), by simp only; linear_combination hb⟩)
  have hyU : pt (X := X) y ∈ t.U := by
    by_contra h
    rw [conicMapL, dif_neg h] at hy
    exact absurd hy (by simp)
  refine ⟨_, hyU, ?_⟩
  rw [conicMapL, dif_pos hyU] at hy
  have hs : psiU φU y hyU eS = 1 := by
    have := congrArg (fun c => match c with | Sum.inl q => q.1.1 | Sum.inr _ => 0) hy
    simpa using this
  have ht : ev t.U y hyU t.f ≠ 0 := by
    rw [← hT]
    change psiU φU y hyU eT ≠ 0
    have e1 := congrArg (psiU φU y hyU) rel1
    simp only [map_add, map_pow, map_zero, hs] at e1
    intro h0
    rw [h0] at e1
    norm_num at e1
  have hb' : pt (X := X) y ∈ X.left.basicOpen t.f := by
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hyU]
    intro h0
    apply ht
    rw [ev_apply, h0, map_zero]
  rw [t.basicOpen_f] at hb'
  exact hb'.2

theorem irreducibleSpace_of_charts (hc : ElkiesCharts X t) : IrreducibleSpace X.left := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := hc
  obtain ⟨p, hpU, hpV⟩ := exists_pt_inter hU hV φU φV hT hTg
  have iU := isIrreducible_open (isIntegral_open hU φU ⟨p, hpU⟩)
  have iV := isIrreducible_open (isIntegral_open hV φV ⟨p, hpV⟩)
  have hcl : (Set.univ : Set X.left) ⊆ closure (t.U : Set X.left) := by
    intro x _
    have hx : x ∈ (t.U ⊔ t.V : X.left.Opens) := by rw [t.cover]; trivial
    rcases hx with h | h
    · exact subset_closure h
    · have := subset_closure_inter_of_isPreirreducible_of_isOpen iV.isPreirreducible t.U.isOpen
        ⟨p, hpV, hpU⟩ h
      exact closure_mono Set.inter_subset_right this
  have heq : closure (t.U : Set X.left) = Set.univ := Set.eq_univ_of_univ_subset hcl
  have hirr : IsIrreducible (Set.univ : Set X.left) := heq ▸ iU.closure
  exact { isPreirreducible_univ := hirr.2, toNonempty := ⟨p⟩ }

theorem isReduced_of_charts (hc : ElkiesCharts X t) : IsReduced X.left := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := hc
  obtain ⟨p, hpU, hpV⟩ := exists_pt_inter hU hV φU φV hT hTg
  have key : ∀ (A : X.left.Opens), IsIntegral A.toScheme → ∀ x ∈ A,
      _root_.IsReduced (X.left.presheaf.stalk x) := by
    intro A hA x hx
    let q : A.toScheme := ⟨x, hx⟩
    have hinj : Function.Injective (A.ι.stalkMap q) :=
      (asIso (A.ι.stalkMap q)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_injective (A.ι.stalkMap q).hom hinj
  have : ∀ x : X.left, _root_.IsReduced (X.left.presheaf.stalk x) := by
    intro x
    have hx : x ∈ (t.U ⊔ t.V : X.left.Opens) := by rw [t.cover]; trivial
    rcases hx with h | h
    · exact key t.U (isIntegral_open hU φU ⟨p, hpU⟩) x h
    · exact key t.V (isIntegral_open hV φV ⟨p, hpV⟩) x h
  exact isReduced_of_isReduced_stalk X.left

/-- **Elkies' charts make `X₆` an integral scheme.** -/
theorem isIntegral_of_charts (hc : ElkiesCharts X t) : IsIntegral X.left := by
  have := irreducibleSpace_of_charts hc
  have := isReduced_of_charts hc
  exact isIntegral_of_irreducibleSpace_of_isReduced X.left

/-- **The generic point lies in `t.U = {t ≠ ∞}`** (`t` is not identically `∞`). -/
theorem genericPoint_mem_of_charts (hc : ElkiesCharts X t) [IrreducibleSpace X.left] :
    genericPoint X.left ∈ t.U := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := hc
  obtain ⟨p, hpU, -⟩ := exists_pt_inter hU hV φU φV hT hTg
  exact ((genericPoint_spec X.left).mem_open_set_iff t.U.isOpen).mpr ⟨p, trivial, hpU⟩

end Integral

/-- `ℚ(X₆)^W`: the rational functions on `X₆` fixed by every `g ∈ W` (`g^*φ = φ`). -/
def fixedByW {X : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left]
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Set X.left.functionField :=
  {φ | ∀ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, ffPullback (Z := X.left) ((Over.forget _).mapIso g) φ = φ}

/-- **LEAF (Elkies, *Shimura curve computations*, Algorithmic Number Theory (ANTS-III, Portland 1998), LNCS 1423,
pp. 1–47, §3 on `X*(6)`; section number, display and the `0/∞` orientation UNVERIFIED, recalled without a
source), in Elkies' function-field form.** On some witness of the moduli clause lists (the canonical `Y₃` with
`R1fpPropsAb`, and `X₆ = X₀(6, 1)` with its moduli bijection `Ψ`, `X6Props`), Elkies' coordinate `t` satisfies:
* **`t` is a coordinate on `X*(6) = X₆/W`**, read in function fields: whenever `X₆` is an integral scheme and `t`
  is regular at its generic point (both follow from the charts: `isIntegral_of_charts`,
  `genericPoint_mem_of_charts`), `ℚ(X₆)^W = ℚ(t)`: the rational
  functions fixed by every `w ∈ W = {1, w₂, w₃, w₆}` (`fixedByW`, `W = atkinLehnerW`, acting by pullback
  `ffPullback`) form the subfield generated by `t` (which contains the prime field `ℚ`). `ℚ(X/W) = ℚ(X)^W` for the
  quotient of a curve by a finite group is the definition of the quotient's function field (STANDARD; Serre,
  *Groupes algébriques et corps de classes* III §12; Mumford, *Abelian varieties* §7; locators UNVERIFIED), and
  "`t` is a coordinate on the genus-0 curve `X*(6)`" is `ℚ(X*(6)) = ℚ(t)`;
* **the CM values** `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3` (as in `ElkiesX6StarPrinted`);
* **the equations** `X₆ = X*(6)(√−t, √(3(t − 1)))` as the curve over the `t`-line in its two charts
  (`X6Glue.ElkiesCharts X t`, as in `ElkiesX6StarPrinted`).
Never stronger than the printed statement: the first clause is the printed coordinate statement in function-field
form, stated under the integrality that the charts already give (so it asserts no existence beyond the charts), the
other two are `ElkiesX6StarPrinted`'s. -/
def ElkiesX6StarFunctionField : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
      fixedByW Ψ = (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P →
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

/-! ## The fibre clause from the function-field form -/

section Main

open X6Glue

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {X : Over (Spec (CommRingCat.of ℚ))}
  {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}

/-- **`ℚ(X₆)^W = ℚ(t)` and Elkies' charts give the `ℚ̄`-point form**: the fibres of `t` on `X₆(ℚ̄)` are the
`W`-orbits. -/
theorem fibre_of_ff (h6 : X6Props Y Φ X Ψ fY) [IsIntegral X.left] {t : ToP1 X.left}
    (hη : genericPoint X.left ∈ t.U)
    (hfix : fixedByW Ψ = (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField))
    (hc : ElkiesCharts X t) (x x' : fieldPt Qbar ⟶ X) :
    t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
      ∃ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, x ≫ g.hom = x' := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, hg1, hg2⟩ := hc
  -- the generic point lies in `t.V`
  obtain ⟨b, hb⟩ := exists_sq_eq (-3)
  obtain ⟨y0, hy0⟩ := conicMapL_surjective φU φV hTg hU hV (Sum.inr ⟨b, hb⟩)
  have hy0U : ¬ pt (X := X) y0 ∈ t.U := by
    intro h
    rw [conicMapL, dif_pos h] at hy0
    exact absurd hy0 (by simp)
  have hηV : genericPoint X.left ∈ t.V :=
    ((genericPoint_spec X.left).mem_open_set_iff t.V.isOpen).mpr
      ⟨_, trivial, memV_of_not_memU (X := X) (t := t) y0 hy0U⟩
  -- notation
  set W := ElkiesX6Star.atkinLehnerW X Ψ with hW
  let σ : (X ≅ X) → X.left.functionField →+* X.left.functionField :=
    fun g => ffPullback (Z := X.left) ((Over.forget _).mapIso g)
  set τ := jU φU hη eT with hτdef
  set S := jU φU hη eS with hSdef
  set R := jU φU hη eR with hRdef
  have hgerm : X.left.presheaf.germ t.U _ hη t.f = τ := by simp [τ, hT]
  rw [hgerm] at hfix
  have hfix' : {φ | ∀ g ∈ W, σ g φ = φ} = (Subfield.closure {τ} : Set X.left.functionField) := hfix
  have hτ : ∀ g ∈ W, σ g τ = τ := by
    have hm : τ ∈ {φ | ∀ g ∈ W, σ g φ = φ} := by
      rw [hfix']
      exact Subfield.subset_closure rfl
    exact hm
  -- relations
  have r1 : S ^ 2 = -τ := by
    have := congrArg (jU φU hη) rel1
    simp only [map_add, map_pow, map_zero] at this
    linear_combination this
  have r2 : R ^ 2 = 3 * (τ - 1) := by
    have := congrArg (jU φU hη) rel2
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_one, map_zero] at this
    linear_combination this
  have hSpm : ∀ g ∈ W, σ g S = S ∨ σ g S = -S := fun g hg =>
    sq_pm (σ g) _ _ (by rw [map_neg, hτ g hg]) r1
  have hRpm : ∀ g ∈ W, σ g R = R ∨ σ g R = -R := fun g hg =>
    sq_pm (σ g) _ _ (by rw [map_mul, map_sub, map_ofNat, map_one, hτ g hg]) r2
  have hSRpm : ∀ g ∈ W, σ g (S * R) = S * R ∨ σ g (S * R) = -(S * R) := by
    intro g hg
    rw [map_mul]
    rcases hSpm g hg with h | h <;> rcases hRpm g hg with h' | h' <;> rw [h, h'] <;>
      first | (left; ring1) | (right; ring1)
  -- nonvanishing
  have hinj := jU_injective φU hη
  have hS0 : S ≠ 0 := (map_ne_zero_iff _ hinj).mpr eS_ne_zero
  have hR0 : R ≠ 0 := (map_ne_zero_iff _ hinj).mpr eR_ne_zero
  have h2 : (2 : X.left.functionField) ≠ 0 := by
    have := (map_ne_zero_iff _ hinj).mpr two_ne_zero'
    rwa [map_ofNat] at this
  -- the sign automorphisms of `ℚ(X)`
  have hθsτ : thetaOf φU hU hη negS τ = τ := by rw [hτdef, thetaOf_jU, negS_T]
  have hθsS : thetaOf φU hU hη negS S = -S := by rw [hSdef, thetaOf_jU, negS_S, map_neg]
  have hθsR : thetaOf φU hU hη negS R = R := by rw [hRdef, thetaOf_jU, negS_R]
  have hθrτ : thetaOf φU hU hη negR τ = τ := by rw [hτdef, thetaOf_jU, negR_T]
  have hθrR : thetaOf φU hU hη negR R = -R := by rw [hRdef, thetaOf_jU, negR_R, map_neg]
  have hθsSR : thetaOf φU hU hη negS (S * R) = -(S * R) := by rw [map_mul, hθsS, hθsR]; ring
  obtain ⟨g1, hg1W, hg1S⟩ := exists_neg W σ τ S hfix' hSpm _ hθsτ hθsS hS0 h2
  obtain ⟨g2, hg2W, hg2R⟩ := exists_neg W σ τ R hfix' hRpm _ hθrτ hθrR hR0 h2
  obtain ⟨g3, hg3W, hg3SR⟩ := exists_neg W σ τ (S * R) hfix' hSRpm _ hθsτ hθsSR
    (mul_ne_zero hS0 hR0) h2
  -- the action of `W` on `ℚ̄`-points
  let F : (fieldPt Qbar ⟶ X) → HDec.X6Kummer.ConicPt := fun x => conicMapL φU φV hTg x.left
  have act : ∀ g ∈ W, ∀ c d : ℤˣ, σ g S = ((c : ℤ) : X.left.functionField) * S →
      σ g R = ((d : ℤ) : X.left.functionField) * R → ∀ x, F (x ≫ g.hom) = signAct c d (F x) :=
    fun g hg c d hS hR x =>
      conicMapL_comp_of_signs hη hηV hT hTg hg1 hg2 ((Over.forget _).mapIso g) c d (hτ g hg) hS hR x.left
  have Finj : ∀ x x', F x = F x' → x = x' := fun x x' e =>
    Over.OverMorphism.ext (conicMapL_injective φU φV hTg hU hV _ _ e)
  have Fsurj : ∀ c, ∃ x, F x = c := fun c => by
    obtain ⟨y, hy⟩ := conicMapL_surjective φU φV hTg hU hV c
    exact ⟨Over.homMk y (specQ_hom_ext _ _), hy⟩
  -- every sign pair is realized by the orbit relation
  let P : ℤˣ → ℤˣ → Prop := fun c d =>
    ∀ x x', F x' = signAct c d (F x) → ∃ g ∈ W, x ≫ g.hom = x'
  have hPg : ∀ g ∈ W, ∀ c d : ℤˣ, σ g S = ((c : ℤ) : X.left.functionField) * S →
      σ g R = ((d : ℤ) : X.left.functionField) * R → P c d :=
    fun g hg c d hS hR x x' e => ⟨g, hg, Finj _ _ (by rw [act g hg c d hS hR x, e])⟩
  have hmul : ∀ c d c' d', P c d → P c' d' → P (c * c') (d * d') := by
    intro c d c' d' p p' x x' e
    obtain ⟨x₁, hx₁⟩ := Fsurj (signAct c d (F x))
    exact orbit_trans h6 (p x x₁ hx₁) (p' x₁ x' (by rw [e, hx₁, signAct_signAct]))
  have hall : ∀ c d, P c d := by
    apply all_signs P hmul
    · obtain ⟨d, hd⟩ := pm_unit _ _ (hRpm g1 hg1W)
      exact ⟨d, hPg g1 hg1W (-1) d (by rw [hg1S]; simp) hd⟩
    · obtain ⟨c, hc⟩ := pm_unit _ _ (hSpm g2 hg2W)
      exact ⟨c, hPg g2 hg2W c (-1) hc (by rw [hg2R]; simp)⟩
    · obtain ⟨c, hc⟩ := pm_unit _ _ (hSpm g3 hg3W)
      obtain ⟨d, hd⟩ := pm_unit _ _ (hRpm g3 hg3W)
      refine ⟨c, d, ?_, hPg g3 hg3W c d hc hd⟩
      rcases Int.units_eq_one_or (c * d) with h | h
      · exfalso
        have e : σ g3 (S * R) = S * R := by
          rw [map_mul, hc, hd]
          have : ((c : ℤ) : X.left.functionField) * ((d : ℤ) : X.left.functionField) = 1 := by
            rw [← Int.cast_mul, ← Units.val_mul, h]; simp
          linear_combination (S * R) * this
        rw [hg3SR] at e
        have : (2 : X.left.functionField) * (S * R) = 0 := by linear_combination -e
        exact mul_ne_zero h2 (mul_ne_zero hS0 hR0) this
      · exact h
  constructor
  · intro hval
    obtain ⟨c, d, hcd⟩ := signAct_of_val hT hTg x.left x'.left hval
    exact hall c d x x' hcd
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := pm_unit _ _ (hSpm g hg)
    obtain ⟨d, hd⟩ := pm_unit _ _ (hRpm g hg)
    exact val_eq_of_signAct hT hTg x.left (x ≫ g.hom).left c d (act g hg c d hc hd x)

end Main

/-- **`ElkiesX6StarPrinted` from Elkies' function-field form** (elkies-coord): the fibre clause is `fibre_of_ff`;
the witness, the CM clause and the charts are the leaf's. -/
theorem elkiesX6StarPrinted_of_functionField (h : ElkiesX6StarFunctionField) : ElkiesX6Star.ElkiesX6StarPrinted := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hff, hcm, hc⟩ := h
  have hI := isIntegral_of_charts hc
  have hη := genericPoint_mem_of_charts hc
  exact ⟨Y, Φ, X, Ψ, fY, t, h1, h6, fun x x' => fibre_of_ff h6 hη (hff hI hη) hc x x', hcm, hc⟩

end HDec.QMSplit.Moduli.ElkiesCoord
