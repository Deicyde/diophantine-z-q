import ZInQKernel.RouteK.System.Partner

/-!
# Route K: Lemma 2 (gluing)

`docs/research/slot-k.md` §2.2, Lemma 2. The symbol set is `S = S' ⊔ {g} ⊔ G ⊔ R` with glue primes
`R = {r_ℓ : ℓ ∈ G}` such that `[r_ℓ/ℓ] = [r_ℓ/g] = 1` and `[r_ℓ/x] = 0` for every other `x`. The
glued configuration `𝒞*` lives on `S' ⊔ {g*}`, with `c_{g*} = c_g Π_ℓ c_ℓ` and symbols
`[y/g*] = Σ_{x ∈ G ∪ {g}} [y/x]`, `[g*/y] = Σ_{x ∈ G ∪ {g}} [x/y]`. The map `Φ` that keeps
`a, b`, `u|_{S'}, v|_{S'}` and sends `u_g, v_g` to `u_{g*}, v_{g*}` is a bijection of solution sets.

As suggested in §4.3 of the note, we index `S` by the abstract type `S' ⊕ (Option G ⊕ G)`:

* `.inl s` is `s ∈ S'`;
* `.inr (.inl none)` is `g` and `.inr (.inl (some ℓ))` is `ℓ ∈ G`, so `Option G` is `X = G ∪ {g}`;
* `.inr (.inr ℓ)` is the glue prime `r_ℓ`.

The glued configuration lives on `Option S'`, with `none` the glued symbol `g*`. A configuration on
another index type is brought to this form by `Config.reindex` (`Config.solsReindexEquiv`).
-/

namespace ZInQ.RouteK

namespace Config

variable {S' G : Type*} [Fintype S'] [DecidableEq S'] [Fintype G] [DecidableEq G]

/-- The glued configuration `𝒞*` on `S' ⊔ {g*}` (`g* = none`). -/
def glue (𝒞 : Config (S' ⊕ (Option G ⊕ G))) : Config (Option S') where
  cls := fun
    | none => ∏ o, 𝒞.cls (.inr (.inl o))
    | some s => 𝒞.cls (.inl s)
  cls_mem := fun
    | none => prod_mem_oddClasses _ _ fun _ _ => 𝒞.cls_mem _
    | some _ => 𝒞.cls_mem _
  bit := fun
    | some y, some y' => 𝒞.bit (.inl y) (.inl y')
    | some y, none => ∑ o, 𝒞.bit (.inl y) (.inr (.inl o))
    | none, some y => ∑ o, 𝒞.bit (.inr (.inl o)) (.inl y)
    | none, none => 0
  recip := by
    rintro (_ | x) (_ | y) h
    · exact absurd rfl h
    · show ∑ o, 𝒞.bit (.inr (.inl o)) (.inl y) + ∑ o, 𝒞.bit (.inl y) (.inr (.inl o)) =
        lam8 (∏ o, 𝒞.cls (.inr (.inl o))) * lam8 (𝒞.cls (.inl y))
      rw [← Finset.sum_add_distrib, lam8_prod _ _ fun _ _ => 𝒞.cls_mem _, Finset.sum_mul]
      exact Finset.sum_congr rfl fun o _ => 𝒞.recip _ _ Sum.inr_ne_inl
    · show ∑ o, 𝒞.bit (.inl x) (.inr (.inl o)) + ∑ o, 𝒞.bit (.inr (.inl o)) (.inl x) =
        lam8 (𝒞.cls (.inl x)) * lam8 (∏ o, 𝒞.cls (.inr (.inl o)))
      rw [← Finset.sum_add_distrib, lam8_prod _ _ fun _ _ => 𝒞.cls_mem _, Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => 𝒞.recip _ _ Sum.inl_ne_inr
    · exact 𝒞.recip _ _ fun e => h (congrArg some (Sum.inl_injective e))

section glueSimp

variable (𝒞 : Config (S' ⊕ (Option G ⊕ G)))

omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_cls_none : 𝒞.glue.cls none = ∏ o, 𝒞.cls (.inr (.inl o)) := rfl
omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_cls_some (s : S') : 𝒞.glue.cls (some s) = 𝒞.cls (.inl s) := rfl
omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_bit_some_some (y y' : S') :
    𝒞.glue.bit (some y) (some y') = 𝒞.bit (.inl y) (.inl y') := rfl
omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_bit_some_none (y : S') :
    𝒞.glue.bit (some y) none = ∑ o, 𝒞.bit (.inl y) (.inr (.inl o)) := rfl
omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_bit_none_some (y : S') :
    𝒞.glue.bit none (some y) = ∑ o, 𝒞.bit (.inr (.inl o)) (.inl y) := rfl
omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_lam_some (s : S') : 𝒞.glue.lam (some s) = 𝒞.lam (.inl s) := rfl
omit [Fintype S'] [DecidableEq S'] in
@[simp] theorem glue_mu_some (s : S') : 𝒞.glue.mu (some s) = 𝒞.mu (.inl s) := rfl

omit [Fintype S'] [DecidableEq S'] in
/-- `λ_{g*} = Σ_{x ∈ G ∪ {g}} λ_x`. -/
theorem glue_lam_none : 𝒞.glue.lam none = ∑ o, 𝒞.lam (.inr (.inl o)) :=
  lam8_prod _ _ fun _ _ => 𝒞.cls_mem _

omit [Fintype S'] [DecidableEq S'] in
/-- `μ_{g*} = Σ_{x ∈ G ∪ {g}} μ_x`. -/
theorem glue_mu_none : 𝒞.glue.mu none = ∑ o, 𝒞.mu (.inr (.inl o)) :=
  mu8_prod _ _ fun _ _ => 𝒞.cls_mem _

omit [DecidableEq S'] in
/-- `c(𝒞*) = c(𝒞)` when the glue primes have class 1 (in general it differs by `Π c_{r_ℓ}`). -/
theorem glue_prodClass (h : ∀ ℓ, 𝒞.cls (.inr (.inr ℓ)) = 1) : 𝒞.glue.prodClass = 𝒞.prodClass := by
  simp only [prodClass, Fintype.prod_option, Fintype.prod_sum_type, glue_cls_none, glue_cls_some,
    h, Finset.prod_const_one, mul_one]
  exact mul_comm _ _

end glueSimp

/-- The gluing of a vector: `w*_{g*} = w_g` and `w*|_{S'} = w|_{S'}`. -/
def glueVec (w : S' ⊕ (Option G ⊕ G) → ZMod 2) : Option S' → ZMod 2
  | none => w (.inr (.inl none))
  | some s => w (.inl s)

/-- The map `Φ` of Lemma 2: keep `a, b` and `u|_{S'}, v|_{S'}`; send `u_g, v_g` to `u_{g*}, v_{g*}`. -/
def glueMap (σ : Unknowns (S' ⊕ (Option G ⊕ G))) : Unknowns (Option S') :=
  ⟨σ.a0, σ.a1, σ.b0, σ.b1, glueVec σ.u, glueVec σ.v⟩

omit [Fintype S'] [DecidableEq S'] [Fintype G] [DecidableEq G] in
theorem glueMap_first (σ : Unknowns (S' ⊕ (Option G ⊕ G))) :
    (glueMap σ).first = (σ.a0, σ.a1, glueVec σ.u) := rfl

/-- The inverse of `Φ`: `u_x = u_{g*}`, `v_x = v_{g*}` on `X = G ∪ {g}`, and on the glue primes
the formulas (2.1) and (2.2) of the note:
```
u_{r_ℓ} = Σ_{y∈S'} [y/ℓ](u_y + u_g) + u_g + λ_ℓ(v_g + a₀),
v_{r_ℓ} = Σ_{y∈S'} [y/ℓ](v_y + v_g) + v_g + μ_ℓu_g + λ_ℓ(v_g + b₀) + b₁μ_ℓ.
``` -/
def glueLift (𝒞 : Config (S' ⊕ (Option G ⊕ G))) (τ : Unknowns (Option S')) :
    Unknowns (S' ⊕ (Option G ⊕ G)) where
  a0 := τ.a0
  a1 := τ.a1
  b0 := τ.b0
  b1 := τ.b1
  u := fun
    | .inl s => τ.u (some s)
    | .inr (.inl _) => τ.u none
    | .inr (.inr ℓ) => ∑ y, 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) * (τ.u (some y) + τ.u none) +
        τ.u none + 𝒞.lam (.inr (.inl (some ℓ))) * (τ.v none + τ.a0)
  v := fun
    | .inl s => τ.v (some s)
    | .inr (.inl _) => τ.v none
    | .inr (.inr ℓ) => ∑ y, 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) * (τ.v (some y) + τ.v none) +
        τ.v none + 𝒞.mu (.inr (.inl (some ℓ))) * τ.u none +
        𝒞.lam (.inr (.inl (some ℓ))) * (τ.v none + τ.b0) + τ.b1 * 𝒞.mu (.inr (.inl (some ℓ)))

omit [DecidableEq S'] [Fintype G] [DecidableEq G] in
@[simp] theorem glueMap_glueLift (𝒞 : Config (S' ⊕ (Option G ⊕ G))) (τ : Unknowns (Option S')) :
    glueMap (𝒞.glueLift τ) = τ := by
  ext o
  · rfl
  · rfl
  · rfl
  · rfl
  · cases o <;> rfl
  · cases o <;> rfl

/-- The hypotheses of Lemma 2: the glue primes `r_ℓ` have class 1, `[r_ℓ/ℓ] = [r_ℓ/g] = 1`, and
`[r_ℓ/x] = 0` for every other symbol `x`. -/
structure Gluing (𝒞 : Config (S' ⊕ (Option G ⊕ G))) : Prop where
  cls_eq_one : ∀ ℓ, 𝒞.cls (.inr (.inr ℓ)) = 1
  bit_ell : ∀ ℓ, 𝒞.bit (.inr (.inr ℓ)) (.inr (.inl (some ℓ))) = 1
  bit_g : ∀ ℓ, 𝒞.bit (.inr (.inr ℓ)) (.inr (.inl none)) = 1
  bit_other : ∀ ℓ z, z ≠ .inr (.inr ℓ) → z ≠ .inr (.inl (some ℓ)) → z ≠ .inr (.inl none) →
    𝒞.bit (.inr (.inr ℓ)) z = 0

/-- `w` is constant on `X = G ∪ {g}`. -/
def GlueConst (w : S' ⊕ (Option G ⊕ G) → ZMod 2) : Prop :=
  ∀ o : Option G, w (.inr (.inl o)) = w (.inr (.inl none))

omit [Fintype S'] [DecidableEq S'] [DecidableEq G] in
theorem GlueConst.sum_mul {w : S' ⊕ (Option G ⊕ G) → ZMod 2} (hw : GlueConst w)
    (f : Option G → ZMod 2) :
    ∑ o, f o * w (.inr (.inl o)) = (∑ o, f o) * w (.inr (.inl none)) := by
  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun o _ => by rw [hw o]

omit [DecidableEq S'] [Fintype G] [DecidableEq G] in
theorem glueLift_u_const (𝒞 : Config (S' ⊕ (Option G ⊕ G))) (τ : Unknowns (Option S')) :
    GlueConst (𝒞.glueLift τ).u := fun _ => rfl

omit [DecidableEq S'] [Fintype G] [DecidableEq G] in
theorem glueLift_v_const (𝒞 : Config (S' ⊕ (Option G ⊕ G))) (τ : Unknowns (Option S')) :
    GlueConst (𝒞.glueLift τ).v := fun _ => rfl

variable {𝒞 : Config (S' ⊕ (Option G ⊕ G))}

namespace Gluing

omit [Fintype S'] [DecidableEq S'] [Fintype G] [DecidableEq G] in
theorem lam_r (h : 𝒞.Gluing) (ℓ : G) : 𝒞.lam (.inr (.inr ℓ)) = 0 := by
  simp [lam, h.cls_eq_one]

omit [Fintype S'] [DecidableEq S'] [Fintype G] [DecidableEq G] in
theorem mu_r (h : 𝒞.Gluing) (ℓ : G) : 𝒞.mu (.inr (.inr ℓ)) = 0 := by
  simp [mu, h.cls_eq_one]

/-- Step 1: the row at `r_ℓ` is `(Ku)_{r_ℓ} = u_ℓ + u_g`. -/
theorem monsky_r (h : 𝒞.Gluing) (u : S' ⊕ (Option G ⊕ G) → ZMod 2) (ℓ : G) :
    𝒞.monsky u (.inr (.inr ℓ)) = u (.inr (.inl (some ℓ))) + u (.inr (.inl none)) := by
  have hs := fun {z : S' ⊕ (Option G ⊕ G)} (hz : z ≠ .inr (.inr ℓ)) => 𝒞.bit_symm_of_cls_one (h.cls_eq_one ℓ) hz
  rw [monsky_eq_sum, Fintype.sum_eq_add (.inr (.inl (some ℓ))) (.inr (.inl none)) (by simp)]
  · rw [hs (by simp), hs (by simp), h.bit_ell, h.bit_g]
    ring_nf; reduce_mod_char
  · rintro z ⟨hz1, hz2⟩
    by_cases hz : z = .inr (.inr ℓ)
    · subst hz; rw [CharTwo.add_self_eq_zero, mul_zero]
    · rw [hs hz, h.bit_other ℓ z hz hz1 hz2, zero_mul]

/-- Step 2: the rows at `y ∈ S'` are those of `Σ(𝒞*)`. -/
theorem monsky_inl (h : 𝒞.Gluing) {u : S' ⊕ (Option G ⊕ G) → ZMod 2} (hu : GlueConst u) (y : S') :
    𝒞.monsky u (.inl y) = 𝒞.glue.monsky (glueVec u) (some y) := by
  rw [monsky_eq_sum, monsky_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hR : ∑ ℓ : G, 𝒞.bit (.inr (.inr ℓ)) (.inl y) * (u (.inr (.inr ℓ)) + u (.inl y)) = 0 :=
    Finset.sum_eq_zero fun ℓ _ => by
      rw [h.bit_other ℓ _ Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr, zero_mul]
  have hX : ∑ o : Option G, 𝒞.bit (.inr (.inl o)) (.inl y) * (u (.inr (.inl o)) + u (.inl y)) =
      (∑ o : Option G, 𝒞.bit (.inr (.inl o)) (.inl y)) * (u (.inr (.inl none)) + u (.inl y)) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun o _ => by rw [hu o]
  rw [hR, hX, add_zero, add_comm]
  conv_rhs => rw [Fintype.sum_option]
  rfl

/-- The row at `ℓ ∈ G`: `(Ku)_ℓ = Σ_{y ∈ S'} [y/ℓ](u_y + u_g) + (u_{r_ℓ} + u_g)`. -/
theorem monsky_ell (h : 𝒞.Gluing) {u : S' ⊕ (Option G ⊕ G) → ZMod 2} (hu : GlueConst u) (ℓ : G) :
    𝒞.monsky u (.inr (.inl (some ℓ))) =
      ∑ y : S', 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) * (u (.inl y) + u (.inr (.inl none))) +
        (u (.inr (.inr ℓ)) + u (.inr (.inl none))) := by
  rw [monsky_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, hu (some ℓ)]
  have hX : ∑ o : Option G, 𝒞.bit (.inr (.inl o)) (.inr (.inl (some ℓ))) *
      (u (.inr (.inl o)) + u (.inr (.inl none))) = 0 :=
    Finset.sum_eq_zero fun o _ => by rw [hu o, CharTwo.add_self_eq_zero, mul_zero]
  have hR : ∑ ℓ' : G, 𝒞.bit (.inr (.inr ℓ')) (.inr (.inl (some ℓ))) *
      (u (.inr (.inr ℓ')) + u (.inr (.inl none))) = u (.inr (.inr ℓ)) + u (.inr (.inl none)) := by
    rw [Fintype.sum_eq_single ℓ, h.bit_ell, one_mul]
    intro ℓ' hℓ'
    rw [h.bit_other ℓ' _ (by simp) (by simpa [eq_comm] using hℓ') (by simp), zero_mul]
  rw [hX, hR, zero_add]

/-- Step 3: the sum of the rows over `X = G ∪ {g}` is the row of `Σ(𝒞*)` at `g*`; the glue
unknowns `u_{r_ℓ}` cancel. -/
theorem sum_monsky_X (h : 𝒞.Gluing) {u : S' ⊕ (Option G ⊕ G) → ZMod 2} (hu : GlueConst u) :
    ∑ o : Option G, 𝒞.monsky u (.inr (.inl o)) = 𝒞.glue.monsky (glueVec u) none := by
  have e1 : ∑ o : Option G, 𝒞.monsky u (.inr (.inl o)) =
      ∑ z, (∑ o : Option G, 𝒞.bit z (.inr (.inl o))) * (u z + u (.inr (.inl none))) := by
    simp only [monsky_eq_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun o _ => by rw [hu o]
  have hR : ∀ ℓ : G, ∑ o : Option G, 𝒞.bit (.inr (.inr ℓ)) (.inr (.inl o)) = 0 := fun ℓ => by
    rw [Fintype.sum_option, h.bit_g, Fintype.sum_eq_single ℓ, h.bit_ell]
    · decide
    · intro ℓ' hℓ'
      exact h.bit_other ℓ _ (by simp) (by simpa using hℓ') (by simp)
  have hX0 : ∑ o' : Option G, (∑ o : Option G, 𝒞.bit (.inr (.inl o')) (.inr (.inl o))) *
      (u (.inr (.inl o')) + u (.inr (.inl none))) = 0 :=
    Finset.sum_eq_zero fun o' _ => by rw [hu o', CharTwo.add_self_eq_zero, mul_zero]
  have hR0 : ∑ ℓ : G, (∑ o : Option G, 𝒞.bit (.inr (.inr ℓ)) (.inr (.inl o))) *
      (u (.inr (.inr ℓ)) + u (.inr (.inl none))) = 0 :=
    Finset.sum_eq_zero fun ℓ _ => by rw [hR ℓ, zero_mul]
  rw [e1, Fintype.sum_sum_type, Fintype.sum_sum_type, hX0, hR0, add_zero, add_zero]
  conv_rhs => rw [monsky_eq_sum, Fintype.sum_option]
  rw [CharTwo.add_self_eq_zero, mul_zero, zero_add]
  rfl

omit [DecidableEq S'] in
theorem dot_lam (h : 𝒞.Gluing) {w : S' ⊕ (Option G ⊕ G) → ZMod 2} (hw : GlueConst w) :
    dot 𝒞.lam w = dot 𝒞.glue.lam (glueVec w) := by
  rw [dot, dot, Fintype.sum_sum_type, Fintype.sum_sum_type, hw.sum_mul]
  conv_rhs => rw [Fintype.sum_option, glue_lam_none]
  simp only [h.lam_r, zero_mul, Finset.sum_const_zero, add_zero]
  rw [add_comm]; rfl

omit [DecidableEq S'] in
theorem dot_mu (h : 𝒞.Gluing) {w : S' ⊕ (Option G ⊕ G) → ZMod 2} (hw : GlueConst w) :
    dot 𝒞.mu w = dot 𝒞.glue.mu (glueVec w) := by
  rw [dot, dot, Fintype.sum_sum_type, Fintype.sum_sum_type, hw.sum_mul]
  conv_rhs => rw [Fintype.sum_option, glue_mu_none]
  simp only [h.mu_r, zero_mul, Finset.sum_const_zero, add_zero]
  rw [add_comm]; rfl

omit [DecidableEq S'] in
theorem D_iff (h : 𝒞.Gluing) {σ : Unknowns (S' ⊕ (Option G ⊕ G))} (hu : GlueConst σ.u)
    (hv : GlueConst σ.v) : 𝒞.D σ ↔ 𝒞.glue.D (glueMap σ) := by
  rw [D, D, glue_prodClass 𝒞 h.cls_eq_one, h.dot_lam hu, h.dot_mu hu, h.dot_lam hv]
  rfl

/-- Step 1: a solution is constant on `X` (`u_ℓ = u_g`, `v_ℓ = v_g`). -/
theorem const_of_isSol (h : 𝒞.Gluing) {σ : Unknowns (S' ⊕ (Option G ⊕ G))} (hσ : 𝒞.IsSol σ) :
    GlueConst σ.u ∧ GlueConst σ.v := by
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  constructor
  · rintro (_ | ℓ)
    · rfl
    · have := hσ.1 (.inr (.inr ℓ))
      rw [E1, h.monsky_r, h.lam_r, h.mu_r] at this
      simp only [zero_mul, mul_zero, add_zero] at this
      exact key _ _ this
  · rintro (_ | ℓ)
    · rfl
    · have := hσ.2.1 (.inr (.inr ℓ))
      rw [E2, h.monsky_r, h.lam_r, h.mu_r] at this
      simp only [zero_mul, mul_zero, add_zero, zero_add] at this
      exact key _ _ this

/-- `Φ` maps solutions of `Σ(𝒞)` to solutions of `Σ(𝒞*)`. -/
theorem glueMap_isSol (h : 𝒞.Gluing) {σ : Unknowns (S' ⊕ (Option G ⊕ G))} (hσ : 𝒞.IsSol σ) :
    𝒞.glue.IsSol (glueMap σ) := by
  obtain ⟨hu, hv⟩ := h.const_of_isSol hσ
  obtain ⟨h1, h2, h3, h4⟩ := hσ
  refine ⟨?_, ?_, h3, (h.D_iff hu hv).1 h4⟩
  · rintro (_ | y)
    · -- the sum of the rows `E1_x`, `x ∈ X`
      have hs := Finset.sum_congr rfl fun (o : Option G) (_ : o ∈ Finset.univ) => h1 (.inr (.inl o))
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
      rw [h.sum_monsky_X hu, hv.sum_mul, ← glue_lam_none, ← glue_mu_none] at hs
      exact hs
    · have := h1 (.inl y)
      rwa [E1, h.monsky_inl hu] at this
  · rintro (_ | y)
    · have hs := Finset.sum_congr rfl fun (o : Option G) (_ : o ∈ Finset.univ) => h2 (.inr (.inl o))
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
      rw [h.sum_monsky_X hv, hu.sum_mul, hv.sum_mul, ← glue_lam_none, ← glue_mu_none] at hs
      exact hs
    · have := h2 (.inl y)
      rwa [E2, h.monsky_inl hv] at this

omit [DecidableEq S'] [Fintype G] [DecidableEq G] in
@[simp] theorem glueVec_glueLift_u (τ : Unknowns (Option S')) : glueVec (𝒞.glueLift τ).u = τ.u :=
  funext fun o => by cases o <;> rfl

omit [DecidableEq S'] [Fintype G] [DecidableEq G] in
@[simp] theorem glueVec_glueLift_v (τ : Unknowns (Option S')) : glueVec (𝒞.glueLift τ).v = τ.v :=
  funext fun o => by cases o <;> rfl

/-- The lift of a solution of `Σ(𝒞*)` solves `Σ(𝒞)`. -/
theorem glueLift_isSol (h : 𝒞.Gluing) {τ : Unknowns (Option S')} (hτ : 𝒞.glue.IsSol τ) :
    𝒞.IsSol (𝒞.glueLift τ) := by
  set σ := 𝒞.glueLift τ with hσ
  have hu : GlueConst σ.u := glueLift_u_const 𝒞 τ
  have hv : GlueConst σ.v := glueLift_v_const 𝒞 τ
  have ha1 : τ.a1 = 0 := hτ.a1_eq_zero
  obtain ⟨h1, h2, h3, h4⟩ := hτ
  -- the rows at `ℓ ∈ G`, by the choice (2.1), (2.2) of `u_{r_ℓ}`, `v_{r_ℓ}`
  have hE1ℓ : ∀ ℓ : G, 𝒞.E1 σ (.inr (.inl (some ℓ))) := fun ℓ => by
    rw [E1, h.monsky_ell hu]
    simp only [hσ, glueLift, ha1]
    generalize (∑ y : S', 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) * (τ.u (some y) + τ.u none)) = A
    ring_nf; reduce_mod_char
  have hE2ℓ : ∀ ℓ : G, 𝒞.E2 σ (.inr (.inl (some ℓ))) := fun ℓ => by
    rw [E2, h.monsky_ell hv]
    simp only [hσ, glueLift]
    generalize (∑ y : S', 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) * (τ.v (some y) + τ.v none)) = A
    ring_nf; reduce_mod_char
  -- the row at `g`: the sum of the rows over `X` is the row at `g*`
  have hE1g : 𝒞.E1 σ (.inr (.inl none)) := by
    have hs : ∑ o : Option G, (𝒞.monsky σ.u (.inr (.inl o)) + 𝒞.lam (.inr (.inl o)) * σ.v (.inr (.inl o))) =
        ∑ o : Option G, (σ.a0 * 𝒞.lam (.inr (.inl o)) + σ.a1 * 𝒞.mu (.inr (.inl o))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        h.sum_monsky_X hu, hv.sum_mul, ← glue_lam_none, ← glue_mu_none]
      have := h1 none
      rw [E1, ← glueVec_glueLift_u (𝒞 := 𝒞) τ] at this
      exact this
    rw [Fintype.sum_option, Fintype.sum_option,
      Finset.sum_congr rfl fun ℓ _ => hE1ℓ ℓ] at hs
    exact add_right_cancel hs
  have hE2g : 𝒞.E2 σ (.inr (.inl none)) := by
    have hs : ∑ o : Option G, (𝒞.mu (.inr (.inl o)) * σ.u (.inr (.inl o)) +
        𝒞.monsky σ.v (.inr (.inl o)) + 𝒞.lam (.inr (.inl o)) * σ.v (.inr (.inl o))) =
        ∑ o : Option G, (σ.b0 * 𝒞.lam (.inr (.inl o)) + σ.b1 * 𝒞.mu (.inr (.inl o))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, h.sum_monsky_X hv, hu.sum_mul, hv.sum_mul, ← glue_lam_none,
        ← glue_mu_none]
      have := h2 none
      rw [E2, ← glueVec_glueLift_v (𝒞 := 𝒞) τ] at this
      exact this
    rw [Fintype.sum_option, Fintype.sum_option,
      Finset.sum_congr rfl fun ℓ _ => hE2ℓ ℓ] at hs
    exact add_right_cancel hs
  refine ⟨?_, ?_, h3, ?_⟩
  · rintro (y | (_ | ℓ) | ℓ)
    · have := h1 (some y)
      rw [E1, ← glueVec_glueLift_u (𝒞 := 𝒞) τ, ← h.monsky_inl hu] at this
      exact this
    · exact hE1g
    · exact hE1ℓ ℓ
    · rw [E1, h.monsky_r, h.lam_r, h.mu_r]
      simp only [hσ, glueLift, CharTwo.add_self_eq_zero, mul_zero, zero_mul]
  · rintro (y | (_ | ℓ) | ℓ)
    · have := h2 (some y)
      rw [E2, ← glueVec_glueLift_v (𝒞 := 𝒞) τ, ← h.monsky_inl hv] at this
      exact this
    · exact hE2g
    · exact hE2ℓ ℓ
    · rw [E2, h.monsky_r, h.lam_r, h.mu_r]
      simp only [hσ, glueLift, CharTwo.add_self_eq_zero, mul_zero, zero_mul]
  · rw [h.D_iff hu hv, hσ, glueMap_glueLift]; exact h4

/-- The lift inverts `Φ` on solutions: a solution is determined by its image, through step 1 and
the formulas (2.1), (2.2). -/
theorem glueLift_glueMap (h : 𝒞.Gluing) {σ : Unknowns (S' ⊕ (Option G ⊕ G))} (hσ : 𝒞.IsSol σ) :
    𝒞.glueLift (glueMap σ) = σ := by
  obtain ⟨hu, hv⟩ := h.const_of_isSol hσ
  have ha1 : σ.a1 = 0 := hσ.a1_eq_zero
  ext z
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases z with y | (_ | ℓ) | ℓ
    · rfl
    · rfl
    · exact (hu (some ℓ)).symm
    · have := hσ.1 (.inr (.inl (some ℓ)))
      rw [E1, h.monsky_ell hu, hv (some ℓ), ha1] at this
      simp only [glueLift, glueMap, glueVec]
      generalize (∑ y : S', 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) *
        (σ.u (.inl y) + σ.u (.inr (.inl none)))) = A at this ⊢
      linear_combination (norm := (ring_nf; reduce_mod_char)) this
  · rcases z with y | (_ | ℓ) | ℓ
    · rfl
    · rfl
    · exact (hv (some ℓ)).symm
    · have := hσ.2.1 (.inr (.inl (some ℓ)))
      rw [E2, h.monsky_ell hv, hu (some ℓ), hv (some ℓ)] at this
      simp only [glueLift, glueMap, glueVec]
      generalize (∑ y : S', 𝒞.bit (.inl y) (.inr (.inl (some ℓ))) *
        (σ.v (.inl y) + σ.v (.inr (.inl none)))) = A at this ⊢
      linear_combination (norm := (ring_nf; reduce_mod_char)) this

/-- **Lemma 2** (gluing): `Φ` is a bijection from the solutions of `Σ(𝒞)` onto those of `Σ(𝒞*)`,
with inverse `glueLift`. -/
def solsEquiv (h : 𝒞.Gluing) : 𝒞.sols ≃ 𝒞.glue.sols where
  toFun σ := ⟨glueMap σ.1, (mem_sols _).2 (h.glueMap_isSol ((mem_sols _).1 σ.2))⟩
  invFun τ := ⟨𝒞.glueLift τ.1, (mem_sols _).2 (h.glueLift_isSol ((mem_sols _).1 τ.2))⟩
  left_inv σ := Subtype.ext (h.glueLift_glueMap ((mem_sols _).1 σ.2))
  right_inv τ := Subtype.ext (glueMap_glueLift 𝒞 τ.1)

@[simp] theorem solsEquiv_apply (h : 𝒞.Gluing) (σ : 𝒞.sols) : (h.solsEquiv σ).1 = glueMap σ.1 :=
  rfl

@[simp] theorem solsEquiv_symm_apply (h : 𝒞.Gluing) (τ : 𝒞.glue.sols) :
    (h.solsEquiv.symm τ).1 = 𝒞.glueLift τ.1 := rfl

theorem bijOn (h : 𝒞.Gluing) :
    Set.BijOn glueMap (𝒞.sols : Set (Unknowns (S' ⊕ (Option G ⊕ G))))
      (𝒞.glue.sols : Set (Unknowns (Option S'))) :=
  bijOn_of_equiv_coe h.solsEquiv fun _ => rfl

theorem card_sols (h : 𝒞.Gluing) : 𝒞.sols.card = 𝒞.glue.sols.card :=
  Finset.card_eq_of_equiv h.solsEquiv

end Gluing

end Config

end ZInQ.RouteK
