import Mathlib

/-!
# Lane RC23-visibility: the Weil-index calculus and the operator relations of App F

Manuscript, Appendix F, subsection "Transformation law and recurrence" (tex 8623–8868), the
paragraphs "The normalized diagonal factor" (tex 8701–8724), "An operator construction of the common
double cover" (tex 8726–8815) and "The metaplectic comparison at two and the extracted character"
(tex 8817–8867), with the multiplicativity remark on (O.5b) (tex 8869–8887).

Elliot derives every identity below from three printed properties of Weil's index
(A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211; the
manuscript's locators I.13, I.14 Théorème 2, II.25, II.28 Proposition 4) and the laws of the Hilbert
symbol. They are formalized here abstractly over the index:

* `k` is a field (the text's `ℚ_p` or `ℝ`; nothing else about `k` is used), `R` a commutative
  ring (the coefficients `ℂ`), `γ : kˣ → Rˣ` the one-dimensional index `γ(a) = γ(⟨a⟩)`,
  `hs : kˣ → kˣ → Rˣ` the Hilbert symbol `(·,·)_k`;
* a diagonal form `⟨a₁, …, aₙ⟩` is a list of units; its index is `gammaDiag γ l`, the product of
  the one-dimensional indices (multiplicativity under orthogonal sums), `scaleForm u l` is `uQ`
  and `detForm l` the determinant of the diagonal matrix `A` of `Q(x) = xᵀAx`;
* the printed inputs are the fields of `WeilIndexAxioms γ hs` (hypotheses, not proved);
* the operators `U_Q(b)`, `D(a)`, `𝓕_Q` are elements of an `R`-algebra `A` subject to the
  relations of `OperatorAxioms` (hypotheses: the elementary relations and Weil's Fourier formula);
  `W_Q = γ_Q 𝓕_Q` is `weylOp` and `M_Q(a) = r_Q(a) D(a)` is `diagOp`, both units of `A`.

PROVED here: the index of the quaternion norm form and the ratio identity (tex 8688–8716), (O.5a)
in general and for ternary forms (tex 8717–8722, 8849–8853), the change of diagonalization and the
extracted determinant (tex 8719–8722), `γ(1)⁴ = (−1,−1)` and `γ(Q)² = (det Q,−1) γ(1)⁶`
(tex 8762–8770), the cocycle of `r_Q` (tex 8765), `r_Q/r_{Q₀} = (a, det Q)` (tex 8809–8812), the two
convention remarks (tex 8854–8856, 8862–8867), and the six operator relations (tex 8772–8787),
plus `M_Q(−1)² = (−1,−1)` (tex 8806). The multiplicativity of the (O.5b) characters
(tex 8879–8882) is proved in its algebraic form. A model of `WeilIndexAxioms` at the real place
(`weilIndexAxioms_real`, `real_place_nontrivial`: `k = ℝ`, `R = ℂ`, `γ(a) = e^{±πi/4}`) shows
the hypotheses hold for nontrivial data, with `γ(1)⁴ = (−1,−1)_∞ = −1`.
-/

namespace ZInQ.Manuscript.RC.Visibility

variable {k R : Type*} [Field k] [CommRing R]

/-! ### Diagonal forms -/

/-- **Definition (tex 8694–8695, 8704–8705).** The Weil index of the diagonal form
`⟨a₁, …, aₙ⟩`: the product of the one-dimensional indices `γ(aᵢ)` ("multiplication under orthogonal
sums"). -/
def gammaDiag (γ : kˣ → Rˣ) (l : List kˣ) : Rˣ := (l.map γ).prod

/-- **Definition (tex 8731–8738).** The scaled form `uQ = ⟨u a₁, …, u aₙ⟩`. -/
def scaleForm (u : kˣ) (l : List kˣ) : List kˣ := l.map (u * ·)

/-- **Definition (tex 8862–8863).** `det Q`, the determinant of the diagonal matrix `A` of
`Q(x) = xᵀAx`, i.e. `a₁ ⋯ aₙ`. -/
def detForm (l : List kˣ) : kˣ := l.prod

/-- **PROVED.** The empty form has index one. -/
@[simp] theorem gammaDiag_nil (γ : kˣ → Rˣ) : gammaDiag γ [] = 1 := rfl

/-- **PROVED (tex 8694–8695).** `γ(⟨a⟩ ⊕ Q) = γ(a) γ(Q)`. -/
@[simp] theorem gammaDiag_cons (γ : kˣ → Rˣ) (a : kˣ) (l : List kˣ) :
    gammaDiag γ (a :: l) = γ a * gammaDiag γ l := by simp [gammaDiag]

/-- **PROVED.** Scaling the empty form. -/
@[simp] theorem scaleForm_nil (u : kˣ) : scaleForm u [] = [] := rfl

/-- **PROVED.** `u(⟨a⟩ ⊕ Q) = ⟨ua⟩ ⊕ uQ`. -/
@[simp] theorem scaleForm_cons (u a : kˣ) (l : List kˣ) :
    scaleForm u (a :: l) = (u * a) :: scaleForm u l := rfl

/-- **PROVED.** Scaling keeps the rank. -/
@[simp] theorem length_scaleForm (u : kˣ) (l : List kˣ) : (scaleForm u l).length = l.length := by
  simp [scaleForm]

/-- **PROVED.** The empty determinant is one. -/
@[simp] theorem detForm_nil : detForm ([] : List kˣ) = 1 := rfl

/-- **PROVED.** `det(⟨a⟩ ⊕ Q) = a det Q`. -/
@[simp] theorem detForm_cons (a : kˣ) (l : List kˣ) : detForm (a :: l) = a * detForm l := by
  simp [detForm]

/-- **PROVED (tex 8694–8695, 8704–8705).** Multiplicativity under orthogonal sums:
`γ(Q ⊕ Q') = γ(Q) γ(Q')`. -/
theorem gammaDiag_append (γ : kˣ → Rˣ) (l₁ l₂ : List kˣ) :
    gammaDiag γ (l₁ ++ l₂) = gammaDiag γ l₁ * gammaDiag γ l₂ := by
  simp [gammaDiag]

/-- **PROVED (tex 8721, 8785–8786).** `det(uQ) = uⁿ det Q` for a form of rank `n`. -/
theorem detForm_scaleForm (u : kˣ) (l : List kˣ) :
    detForm (scaleForm u l) = u ^ l.length * detForm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [scaleForm_cons, detForm_cons, detForm_cons, ih, List.length_cons, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel

/-- **PROVED.** `1 · Q = Q`. -/
theorem scaleForm_one (l : List kˣ) : scaleForm 1 l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [scaleForm_cons, one_mul, ih]

/-! ### The printed inputs -/

/-- **The printed properties of the Weil index and the Hilbert-symbol laws (hypotheses).**
Kinds and sources field by field below. Consistency with nontrivial values:
`weilIndexAxioms_real`. -/
structure WeilIndexAxioms (γ : kˣ → Rˣ) (hs : kˣ → kˣ → Rˣ) : Prop where
  /-- **PRINT (Weil 1964, Ch. II; locator not given by the manuscript, UNVERIFIED).**
  `γ(−q) = γ(q)⁻¹` (tex 8705). -/
  neg : ∀ a, γ (-a) = (γ a)⁻¹
  /-- **GLUE/PRINT (Weil 1964: the index is an invariant of the isomorphism class of the form;
  UNVERIFIED locator).** Isometric forms have the same index: `⟨a⟩ ≅ ⟨a s²⟩` by `x ↦ s x`
  (used at tex 8719–8720 and for `γ(b⁻¹Q) = γ(bQ)`). -/
  sq : ∀ a s, γ (a * s ^ 2) = γ a
  /-- **PRINT + GLUE (tex 8703–8712).** The norm form of the quaternion algebra `(u,a)` is
  `⟨1,−u,−a,ua⟩` (GLUE); its index is `1` when the algebra splits (the form is hyperbolic) and
  `−1` for the division algebra (Weil 1964, II.28, Proposition 4: "Let 𝔨 be the algebra of
  quaternions over the local field k, and let n be the norm on 𝔨: n(z) = z z̄. Then γ(n) = −1";
  read in the English translation by E. Peterson, the French print UNVERIFIED); "these are exactly
  the two values of `(u,a)_p`" (GLUE: the Hilbert symbol is `1` iff `(u,a)` splits). -/
  norm_form : ∀ u a, gammaDiag γ [1, -u, -a, u * a] = hs u a
  /-- **GLUE (Serre, *A Course in Arithmetic*, Ch. III §1.1, Prop. 2; UNVERIFIED locator).**
  `(a,b) = (b,a)`. -/
  hs_symm : ∀ a b, hs a b = hs b a
  /-- **GLUE (Serre, *A Course in Arithmetic*, Ch. III §1.2, Thm. 2 (bilinearity); UNVERIFIED
  locator).** `(a,bc) = (a,b)(a,c)`. -/
  hs_mul : ∀ a b c, hs a (b * c) = hs a b * hs a c
  /-- **GLUE (Serre, Ch. III §1.1: the symbol takes the values `±1`).** `(a,b)² = 1`. -/
  hs_sq : ∀ a b, hs a b * hs a b = 1

namespace WeilIndexAxioms

variable {γ : kˣ → Rˣ} {hs : kˣ → kˣ → Rˣ}

/-- **PROVED.** `(a,1) = 1`. -/
theorem hs_one_right (hW : WeilIndexAxioms γ hs) (a : kˣ) : hs a 1 = 1 := by
  have h := hW.hs_mul a 1 1
  rw [mul_one] at h
  exact (mul_left_cancel (h.symm.trans (mul_one (hs a 1)).symm))

/-- **PROVED.** `(ab,c) = (a,c)(b,c)`. -/
theorem hs_mul_left (hW : WeilIndexAxioms γ hs) (a b c : kˣ) :
    hs (a * b) c = hs a c * hs b c := by
  rw [hW.hs_symm, hW.hs_mul, hW.hs_symm c a, hW.hs_symm c b]

/-- **PROVED (tex 8856: "the Hilbert symbol has order two").** `(a,b)⁻¹ = (a,b)`. -/
theorem hs_inv (hW : WeilIndexAxioms γ hs) (a b : kˣ) : (hs a b)⁻¹ = hs a b :=
  inv_eq_of_mul_eq_one_right (hW.hs_sq a b)

/-- **PROVED.** `(a,b)³ = (a,b)`. -/
theorem hs_pow_three (hW : WeilIndexAxioms γ hs) (a b : kˣ) : hs a b ^ 3 = hs a b := by
  rw [pow_succ, pow_two, hW.hs_sq, one_mul]

/-- **PROVED.** `(u,s²) = 1`. -/
theorem hs_sq_right (hW : WeilIndexAxioms γ hs) (u s : kˣ) : hs u (s ^ 2) = 1 := by
  rw [pow_two, hW.hs_mul, hW.hs_sq]

/-- **PROVED.** `(s²,u) = 1`. -/
theorem hs_sq_left (hW : WeilIndexAxioms γ hs) (s u : kˣ) : hs (s ^ 2) u = 1 := by
  rw [hW.hs_symm, hW.hs_sq_right]

/-- **PROVED.** `(b³,c) = (b,c)`. -/
theorem hs_pow_three_left (hW : WeilIndexAxioms γ hs) (b c : kˣ) : hs (b ^ 3) c = hs b c := by
  rw [pow_succ, hW.hs_mul_left, hW.hs_sq_left, one_mul]

/-- **PROVED (tex 8705, 8787).** `γ(−uQ) = γ(uQ)⁻¹`. -/
theorem gammaDiag_scaleForm_neg (hW : WeilIndexAxioms γ hs) (u : kˣ) (l : List kˣ) :
    gammaDiag γ (scaleForm (-u) l) = (gammaDiag γ (scaleForm u l))⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [scaleForm_cons, scaleForm_cons, gammaDiag_cons, gammaDiag_cons, ih, neg_mul, hW.neg,
      mul_inv]

/-- **PROVED (the step `γ(b⁻¹Q) = γ(bQ)` of tex 8785–8787).** `u⁻¹Q ≅ uQ` (each entry
`u⁻¹aᵢ = (u aᵢ)(u⁻¹)²`), so `γ(u⁻¹Q) = γ(uQ)`. -/
theorem gammaDiag_scaleForm_inv (hW : WeilIndexAxioms γ hs) (u : kˣ) (l : List kˣ) :
    gammaDiag γ (scaleForm u⁻¹ l) = gammaDiag γ (scaleForm u l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [scaleForm_cons, scaleForm_cons, gammaDiag_cons, gammaDiag_cons, ih]
    congr 1
    rw [← hW.sq (u * a) u⁻¹]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

end WeilIndexAxioms

variable {γ : kˣ → Rˣ} {hs : kˣ → kˣ → Rˣ}

/-! ### The normalized diagonal factor (tex 8688–8724) -/

/-- **PROVED (tex 8703–8707).** "By multiplicativity under orthogonal sums and
`γ(−q) = γ(q)⁻¹`, its index is `γ(1)γ(ua)/(γ(u)γ(a))`." -/
theorem index_norm_form (hW : WeilIndexAxioms γ hs) (u a : kˣ) :
    gammaDiag γ [1, -u, -a, u * a] = γ 1 * γ (u * a) * (γ u)⁻¹ * (γ a)⁻¹ := by
  simp only [gammaDiag_cons, gammaDiag_nil, hW.neg, mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- **PROVED (tex 8688–8693, 8712–8716).** "Solving this equality gives
`γ(ua)/γ(a) = (γ(u)/γ(1)) (u,a)_p`." -/
theorem weil_index_ratio (hW : WeilIndexAxioms γ hs) (u a : kˣ) :
    γ (u * a) * (γ a)⁻¹ = γ u * (γ 1)⁻¹ * hs u a := by
  rw [← hW.norm_form, index_norm_form hW]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- **PROVED (tex 8712–8716).** The ratio identity solved for `γ(ua)`. -/
theorem gamma_scale_one_dim (hW : WeilIndexAxioms γ hs) (u a : kˣ) :
    γ (u * a) = γ u * (γ 1)⁻¹ * hs u a * γ a := by
  rw [← weil_index_ratio hW, inv_mul_cancel_right]

/-- **PROVED (tex 8717–8718).** Applying the ratio identity entry by entry:
`γ(uQ) = (γ(u)/γ(1))ⁿ (u, det Q) γ(Q)` for a diagonal form of rank `n`. -/
theorem gammaDiag_scaleForm (hW : WeilIndexAxioms γ hs) (u : kˣ) (Q : List kˣ) :
    gammaDiag γ (scaleForm u Q) =
      (γ u * (γ 1)⁻¹) ^ Q.length * hs u (detForm Q) * gammaDiag γ Q := by
  induction Q with
  | nil => simp [hW.hs_one_right]
  | cons a Q ih =>
    rw [scaleForm_cons, gammaDiag_cons, ih, gamma_scale_one_dim hW, detForm_cons, hW.hs_mul,
      gammaDiag_cons, List.length_cons, pow_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

/-- **PROVED ((O.5a), general rank; tex 8717–8718, 8849–8853).**
`γ(uQ)/γ(Q) = (γ(u)/γ(1))ⁿ (u, det Q)`. -/
theorem O5a (hW : WeilIndexAxioms γ hs) (u : kˣ) (Q : List kˣ) :
    gammaDiag γ (scaleForm u Q) * (gammaDiag γ Q)⁻¹ =
      (γ u * (γ 1)⁻¹) ^ Q.length * hs u (detForm Q) := by
  rw [gammaDiag_scaleForm hW, mul_inv_cancel_right]

/-- **PROVED ((O.5a), tex 8849–8853).** For `Q_B = ⟨a₁,a₂,a₃⟩`:
`(γ(uQ_B)/γ(Q_B)) / (γ(u)/γ(1))³ = (u, det Q_B)_p` with `det Q_B = a₁a₂a₃`. -/
theorem O5a_ternary (hW : WeilIndexAxioms γ hs) (u a₁ a₂ a₃ : kˣ) :
    gammaDiag γ (scaleForm u [a₁, a₂, a₃]) * (gammaDiag γ [a₁, a₂, a₃])⁻¹ *
        ((γ u * (γ 1)⁻¹) ^ 3)⁻¹ = hs u (a₁ * a₂ * a₃) := by
  rw [O5a hW, show [a₁, a₂, a₃].length = 3 from rfl, mul_comm ((γ u * (γ 1)⁻¹) ^ 3),
    mul_inv_cancel_right]
  simp only [detForm_cons, detForm_nil, mul_one, mul_assoc]

/-- **PROVED (tex 8719–8720).** "A change of diagonalization changes the determinant only by a
square, so it changes no symbol": `(u, s²δ) = (u, δ)`. -/
theorem hs_det_change (hW : WeilIndexAxioms γ hs) (u s δ : kˣ) :
    hs u (s ^ 2 * δ) = hs u δ := by
  rw [hW.hs_mul, hW.hs_sq_right, one_mul]

/-- **PROVED (GLUE fact behind tex 8719–8720).** A change of basis `P` changes the determinant
of the matrix of the form by the square `(det P)²`. -/
theorem det_change_of_basis {n : Type*} [Fintype n] [DecidableEq n] (P A : Matrix n n k) :
    (P.transpose * A * P).det = P.det ^ 2 * A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- **PROVED (tex 8721–8722, 8888–8890).** The determinant of `Q_B/m` is `m⁻³ det Q_B`, whose
class is `m det Q_B`: `(u, m⁻³δ) = (u,m)(u,δ)`. -/
theorem hs_extracted (hW : WeilIndexAxioms γ hs) (u m δ : kˣ) :
    hs u (m⁻¹ ^ 3 * δ) = hs u m * hs u δ := by
  have h : m⁻¹ ^ 3 * δ = (m⁻¹) ^ 2 * ((m⁻¹) ^ 2 * (m * δ)) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  rw [h, hs_det_change hW, hs_det_change hW, hW.hs_mul]

/-- **PROVED (tex 8698–8699).** For `B = (−a,−b)` the norm on `B⁰` is `aX² + bY² + abZ²`,
whose determinant is `(ab)²`. -/
theorem detForm_QB (a b : kˣ) : detForm [a, b, a * b] = (a * b) ^ 2 := by
  simp only [detForm_cons, detForm_nil, mul_one]
  rw [pow_two, mul_assoc]

/-- **PROVED (tex 8699–8700).** "There is therefore no additional determinant character for
`Q_B`": `(u, det Q_B) = 1`. -/
theorem hs_det_QB (hW : WeilIndexAxioms γ hs) (u a b : kˣ) : hs u (detForm [a, b, a * b]) = 1 := by
  rw [detForm_QB, hW.hs_sq_right]

/-- **PROVED (tex 8721–8722).** "Thus the extra factor is precisely `(u,m)_p`":
`(u, m⁻³ det Q_B) = (u,m)`. -/
theorem hs_extracted_QB (hW : WeilIndexAxioms γ hs) (u m a b : kˣ) :
    hs u (m⁻¹ ^ 3 * detForm [a, b, a * b]) = hs u m := by
  rw [hs_extracted hW, hs_det_QB hW, mul_one]

/-! ### `γ(1)⁴`, `γ(Q)²` and the diagonal factor `r_Q` (tex 8761–8770, 8809–8812) -/

/-- **PROVED (tex 8764, 8767–8768).** "For the middle equality apply the quaternion-norm formula
to `⟨1,1,1,1⟩`": `γ(1)⁴ = (−1,−1)_k`. -/
theorem gamma_one_pow_four (hW : WeilIndexAxioms γ hs) : γ 1 ^ 4 = hs (-1) (-1) := by
  have h := hW.norm_form (-1) (-1)
  simp only [neg_neg, mul_neg, mul_one, gammaDiag_cons, gammaDiag_nil] at h
  rw [← h]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-- **PROVED (tex 8768–8770).** The quaternion-norm formula applied to `⟨1,−a,1,−a⟩`:
`γ(a)² = (a,−1) γ(1)²`. -/
theorem gamma_sq_one (hW : WeilIndexAxioms γ hs) (a : kˣ) : γ a ^ 2 = hs a (-1) * γ 1 ^ 2 := by
  have h := hW.norm_form a (-1)
  simp only [neg_neg, mul_neg, mul_one, gammaDiag_cons, gammaDiag_nil, hW.neg] at h
  rw [← hW.hs_inv, ← h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

/-- **PROVED (tex 8763, 8768–8770), any rank.** `γ(Q)² = (det Q,−1) γ(1)^{2n}`. -/
theorem gamma_sq_general (hW : WeilIndexAxioms γ hs) (Q : List kˣ) :
    (gammaDiag γ Q) ^ 2 = hs (detForm Q) (-1) * γ 1 ^ (2 * Q.length) := by
  induction Q with
  | nil => simp [hW.hs_symm 1, hW.hs_one_right]
  | cons a Q ih =>
    rw [gammaDiag_cons, mul_pow, ih, gamma_sq_one hW, detForm_cons, hW.hs_mul_left,
      List.length_cons, mul_add, mul_one, pow_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel

/-- **PROVED (tex 8763, 8768–8770).** For `Q = ⟨a₁,a₂,a₃⟩`: `γ(Q)² = (det Q,−1)_k γ(1)⁶`. -/
theorem gamma_sq (hW : WeilIndexAxioms γ hs) (a₁ a₂ a₃ : kˣ) :
    (gammaDiag γ [a₁, a₂, a₃]) ^ 2 = hs (detForm [a₁, a₂, a₃]) (-1) * γ 1 ^ 6 := by
  rw [gamma_sq_general hW]
  rfl

/-- **PROVED (from tex 8763–8764).** For ternary `Q`: `γ(Q)⁴ = (−1,−1)_k`. -/
theorem gamma_pow_four (hW : WeilIndexAxioms γ hs) {Q : List kˣ} (hQ : Q.length = 3) :
    (gammaDiag γ Q) ^ 4 = hs (-1) (-1) := by
  have h4 : (gammaDiag γ Q) ^ 4 = ((gammaDiag γ Q) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, gamma_sq_general hW, hQ, mul_pow, ← pow_mul, show 2 * 3 * 2 = 4 * 3 by rfl, pow_mul,
    gamma_one_pow_four hW, pow_two (hs _ _), hW.hs_sq, one_mul, hW.hs_pow_three]

/-- **Definition (tex 8738).** `r_Q(a) = γ(aQ)/γ(Q)`. -/
def rQ (γ : kˣ → Rˣ) (Q : List kˣ) (a : kˣ) : Rˣ :=
  gammaDiag γ (scaleForm a Q) * (gammaDiag γ Q)⁻¹

/-- **PROVED ((O.5a) for `r_Q`).** `r_Q(a) = (γ(a)/γ(1))ⁿ (a, det Q)`. -/
theorem rQ_eq (hW : WeilIndexAxioms γ hs) (Q : List kˣ) (a : kˣ) :
    rQ γ Q a = (γ a * (γ 1)⁻¹) ^ Q.length * hs a (detForm Q) :=
  O5a hW a Q

/-- **PROVED (tex 8712–8716).** `γ(ab)/γ(1) = (γ(a)/γ(1)) (γ(b)/γ(1)) (a,b)`. -/
theorem gamma_ratio_mul (hW : WeilIndexAxioms γ hs) (a b : kˣ) :
    γ (a * b) * (γ 1)⁻¹ = γ a * (γ 1)⁻¹ * (γ b * (γ 1)⁻¹) * hs a b := by
  rw [gamma_scale_one_dim hW]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- **PROVED (tex 8765), any rank.** `r_Q(a) r_Q(b) = (a,b)ⁿ r_Q(ab)`. -/
theorem rQ_mul_general (hW : WeilIndexAxioms γ hs) (Q : List kˣ) (a b : kˣ) :
    rQ γ Q a * rQ γ Q b = hs a b ^ Q.length * rQ γ Q (a * b) := by
  rw [rQ_eq hW, rQ_eq hW, rQ_eq hW, gamma_ratio_mul hW, hW.hs_mul_left]
  simp only [mul_pow]
  have h1 : (hs a b ^ Q.length) * (hs a b ^ Q.length) = 1 := by
    rw [← mul_pow, hW.hs_sq, one_pow]
  refine (mul_one _).symm.trans ?_
  rw [← h1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul]
  abel

/-- **PROVED (tex 8765).** For ternary `Q`: `r_Q(a) r_Q(b) = (a,b)_k r_Q(ab)`. -/
theorem rQ_mul (hW : WeilIndexAxioms γ hs) {Q : List kˣ} (hQ : Q.length = 3) (a b : kˣ) :
    rQ γ Q a * rQ γ Q b = hs a b * rQ γ Q (a * b) := by
  rw [rQ_mul_general hW, hQ, hW.hs_pow_three]

/-- **PROVED (used at tex 8778).** `r_Q(a⁻¹) = r_Q(a)`, since `a⁻¹Q ≅ aQ`. -/
theorem rQ_inv (hW : WeilIndexAxioms γ hs) (Q : List kˣ) (a : kˣ) : rQ γ Q a⁻¹ = rQ γ Q a := by
  rw [rQ, rQ, hW.gammaDiag_scaleForm_inv]

/-- **PROVED.** `r_Q(1) = 1`. -/
theorem rQ_one (γ : kˣ → Rˣ) (Q : List kˣ) : rQ γ Q 1 = 1 := by
  rw [rQ, scaleForm_one, mul_inv_cancel]

/-- **PROVED (tex 8705).** `r_Q(−1) = γ(−Q)/γ(Q) = γ(Q)⁻²`. -/
theorem rQ_neg_one (hW : WeilIndexAxioms γ hs) (Q : List kˣ) :
    rQ γ Q (-1) = (gammaDiag γ Q)⁻¹ * (gammaDiag γ Q)⁻¹ := by
  rw [rQ, hW.gammaDiag_scaleForm_neg, scaleForm_one]

/-- **PROVED (tex 8809–8812).** For ternary `Q` and `Q₀ = ⟨1,1,1⟩`:
`r_Q(a)/r_{Q₀}(a) = (a, det Q)_k`. -/
theorem rQ_div_rQ0 (hW : WeilIndexAxioms γ hs) {Q : List kˣ} (hQ : Q.length = 3) (a : kˣ) :
    rQ γ Q a * (rQ γ [1, 1, 1] a)⁻¹ = hs a (detForm Q) := by
  rw [rQ_eq hW, rQ_eq hW, hQ, show ([1, 1, 1] : List kˣ).length = 3 from rfl,
    show detForm ([1, 1, 1] : List kˣ) = 1 by simp, hW.hs_one_right, mul_one,
    mul_comm ((γ a * (γ 1)⁻¹) ^ 3), mul_inv_cancel_right]

/-- **PROVED (tex 8785–8787).** For ternary `Q`: "the index-square formula reduces
`γ(Q)²γ(bQ)²` to `(−b,−1)_k`". -/
theorem scalar_WUW (hW : WeilIndexAxioms γ hs) {Q : List kˣ} (hQ : Q.length = 3) (b : kˣ) :
    (gammaDiag γ Q) ^ 2 * (gammaDiag γ (scaleForm b Q)) ^ 2 = hs (-b) (-1) := by
  rw [gamma_sq_general hW, gamma_sq_general hW, detForm_scaleForm, length_scaleForm, hQ,
    hW.hs_mul_left, hW.hs_pow_three_left, show (-b : kˣ) = -1 * b by simp, hW.hs_mul_left,
    ← hW.hs_pow_three (-1) (-1), ← gamma_one_pow_four hW]
  rw [← mul_one ((γ 1 ^ 4) ^ 3 * hs b (-1)), ← hW.hs_sq (detForm Q) (-1)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow]
  abel

/-! ### The two convention remarks (tex 8854–8856, 8862–8867) -/

/-- **PROVED (tex 8854–8856).** With the inverse convention `γ'(a) = γ(a)⁻¹` "both numerator and
denominator are inverted; the quotient is unchanged because the Hilbert symbol has order two":
the quotient (O.5a) computed with `γ'` is again `(u, a₁a₂a₃)`. -/
theorem inverse_convention (hW : WeilIndexAxioms γ hs) (u a₁ a₂ a₃ : kˣ) :
    gammaDiag (fun a => (γ a)⁻¹) (scaleForm u [a₁, a₂, a₃]) *
        (gammaDiag (fun a => (γ a)⁻¹) [a₁, a₂, a₃])⁻¹ *
        (((γ u)⁻¹ * ((γ 1)⁻¹)⁻¹) ^ 3)⁻¹ = hs u (a₁ * a₂ * a₃) := by
  have hinv : ∀ l : List kˣ, gammaDiag (fun a => (γ a)⁻¹) l = (gammaDiag γ l)⁻¹ := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => rw [gammaDiag_cons, gammaDiag_cons, ih, mul_inv]
  have h := O5a_ternary hW u a₁ a₂ a₃
  rw [hinv, hinv, ← hW.hs_inv, ← h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

/-- **PROVED (GLUE fact behind tex 8863–8866).** The Gram matrix `2A` of a ternary form has
determinant `2³ det A`. -/
theorem gram_det (A : Matrix (Fin 3) (Fin 3) k) : ((2 : k) • A).det = 8 * A.det := by
  rw [Matrix.det_smul, Fintype.card_fin]
  norm_num

/-- **PROVED (tex 8862–8867).** With the Gram convention both `Q` and `Q₀ = ⟨1,1,1⟩` acquire the
factor `2³` in their determinants, which cancels in the comparison:
`(u, 8δ)/(u, 8·1) = (u, δ)`. -/
theorem gram_convention (hW : WeilIndexAxioms γ hs) (h8 : (8 : k) ≠ 0) (u δ : kˣ) :
    hs u (Units.mk0 8 h8 * δ) * (hs u (Units.mk0 8 h8))⁻¹ = hs u δ := by
  rw [hW.hs_mul, mul_comm, inv_mul_cancel_left]

/-! ### The operators of the double cover (tex 8726–8807) -/

section Operators

variable {A : Type*} [Ring A] [Algebra R A]

/-- **Definition.** A scalar `c ∈ Rˣ` as the invertible operator `c · id` (through
`algebraMap R A`). -/
def scalarOp : Rˣ →* Aˣ := Units.map (algebraMap R A : R →* A)

/-- **PROVED.** The underlying operator of `scalarOp c` is `algebraMap R A c`. -/
theorem coe_scalarOp (c : Rˣ) : ((scalarOp c : Aˣ) : A) = algebraMap R A c := rfl

/-- **PROVED.** Scalars are central. -/
theorem coe_scalarOp_comm (c : Rˣ) (x : A) :
    ((scalarOp c : Aˣ) : A) * x = x * ((scalarOp c : Aˣ) : A) := by
  rw [coe_scalarOp, Algebra.commutes]

/-- **PROVED.** Scalars are central in `Aˣ`. -/
theorem scalarOp_comm (c : Rˣ) (X : Aˣ) : scalarOp c * X = X * scalarOp c := by
  ext
  rw [Units.val_mul, Units.val_mul, coe_scalarOp_comm]

/-- **PROVED.** `c • x = (c · id) x` for `c ∈ Rˣ`. -/
theorem smul_eq_scalarOp_mul (c : Rˣ) (x : A) : c • x = ((scalarOp c : Aˣ) : A) * x := by
  rw [Units.smul_def, Algebra.smul_def, coe_scalarOp]

/-- **PROVED.** `↑(scalarOp c * X) = c • ↑X`. -/
theorem coe_scalarOp_mul (c : Rˣ) (X : Aˣ) : ((scalarOp c * X : Aˣ) : A) = c • (X : A) := by
  rw [Units.val_mul, smul_eq_scalarOp_mul]

/-- **PROVED.** `(c x)(d y) = (cd)(xy)` for scalars `c`, `d`. -/
theorem scalar_mul_scalar_mul (c d : Rˣ) (x y : A) :
    ((scalarOp c : Aˣ) : A) * x * (((scalarOp d : Aˣ) : A) * y) =
      ((scalarOp (c * d) : Aˣ) : A) * (x * y) := by
  rw [map_mul, Units.val_mul, mul_assoc, ← mul_assoc x, ← coe_scalarOp_comm d x, mul_assoc,
    mul_assoc]

/-- **PROVED (tex 8662–8663: "a scalar used to normalize the Weyl operator cancels with its
inverse in this conjugation").** Conjugation by `cX` is conjugation by `X`. -/
theorem conj_scalarOp_mul (c : Rˣ) (X Y : Aˣ) :
    (scalarOp c * X) * Y * (scalarOp c * X)⁻¹ = X * Y * X⁻¹ := by
  rw [scalarOp_comm c X, mul_inv_rev, mul_assoc X, scalarOp_comm c Y]
  group

/-- **The operator relations taken as hypotheses (tex 8731–8758).** `U b` is `U_Q(b)`
(multiplication by `e(bQ(x))`), `D a` is `D(a)φ(x) = |a|^{3/2} φ(ax)` (a homomorphism
`kˣ → Aˣ`, by the change of variables; GLUE), `F` is `𝓕_Q`. -/
structure OperatorAxioms (γ : kˣ → Rˣ) (Q : List kˣ) (U : k → A) (D : kˣ →* Aˣ) (F : Aˣ) :
    Prop where
  /-- **GLUE (tex 8734, 8775).** `U_Q(b + c) = U_Q(b) U_Q(c)` (`e(t + t') = e(t) e(t')`). -/
  U_add : ∀ b c, U (b + c) = U b * U c
  /-- **GLUE (tex 8734).** `U_Q(0) = 1`. -/
  U_zero : U 0 = 1
  /-- **GLUE (tex 8734–8735, change of variables).** `D(a) U_Q(b) D(a)⁻¹ = U_Q(a²b)`. -/
  D_conj_U : ∀ (a : kˣ) (b : k), (D a : A) * U b * ((D a)⁻¹ : Aˣ) = U ((a : k) ^ 2 * b)
  /-- **GLUE (tex 8646–8647, 8735, change of variables).** `𝓕_Q D(a) 𝓕_Q⁻¹ = D(a⁻¹)`. -/
  F_conj_D : ∀ a, F * D a * F⁻¹ = D a⁻¹
  /-- **ELLIOT + GLUE (tex 8653, Fourier inversion for the self-dual measure).**
  "`𝓕_Q² φ(x) = φ(−x)`", i.e. `𝓕_Q² = D(−1)`. -/
  F_sq : F * F = D (-1)
  /-- **PRINT (Weil 1964, I.14, Théorème 2, or its completion-of-the-square calculation;
  UNVERIFIED) + ELLIOT (tex 8746–8758, the operator form).** For `b ≠ 0`:
  `𝓕_Q U_Q(b) 𝓕_Q = γ(bQ) U_Q(−b⁻¹) D(b⁻¹) 𝓕_Q⁻¹ U_Q(−b⁻¹)`. -/
  fourier : ∀ b : kˣ, (F : A) * U b * F =
    gammaDiag γ (scaleForm b Q) •
      (U (-((b⁻¹ : kˣ) : k)) * (D b⁻¹ : A) * ((F⁻¹ : Aˣ) : A) * U (-((b⁻¹ : kˣ) : k)))

/-- **Definition (tex 8736).** `W_Q = γ_Q 𝓕_Q`, as a unit of `A`. -/
def weylOp (γ : kˣ → Rˣ) (Q : List kˣ) (F : Aˣ) : Aˣ := scalarOp (gammaDiag γ Q) * F

/-- **Definition (tex 8737–8738).** `M_Q(a) = r_Q(a) D(a)`, as a unit of `A`. -/
def diagOp (γ : kˣ → Rˣ) (Q : List kˣ) (D : kˣ →* Aˣ) (a : kˣ) : Aˣ :=
  scalarOp (rQ γ Q a) * D a

variable {Q : List kˣ} {U : k → A} {D : kˣ →* Aˣ} {F : Aˣ}

/-- **PROVED (tex 8775).** `U_Q(b) U_Q(c) = U_Q(b + c)` (restating the hypothesis). -/
theorem U_mul_U (hO : OperatorAxioms γ Q U D F) (b c : k) : U b * U c = U (b + c) :=
  (hO.U_add b c).symm

/-- **PROVED (tex 8776).** `M_Q(a) U_Q(b) M_Q(a)⁻¹ = U_Q(a²b)`. -/
theorem M_conj_U (hO : OperatorAxioms γ Q U D F) (a : kˣ) (b : k) :
    (diagOp γ Q D a : A) * U b * ((diagOp γ Q D a)⁻¹ : Aˣ) = U ((a : k) ^ 2 * b) := by
  simp only [diagOp, Units.val_mul, mul_inv_rev]
  calc ((scalarOp (rQ γ Q a) : Aˣ) : A) * (D a : A) * U b *
        (((D a)⁻¹ : Aˣ) * ((scalarOp (rQ γ Q a))⁻¹ : Aˣ))
      = ((scalarOp (rQ γ Q a) : Aˣ) : A) * ((D a : A) * U b * ((D a)⁻¹ : Aˣ)) *
          ((scalarOp (rQ γ Q a))⁻¹ : Aˣ) := by simp only [mul_assoc]
    _ = U ((a : k) ^ 2 * b) * (((scalarOp (rQ γ Q a) : Aˣ) : A) *
          ((scalarOp (rQ γ Q a))⁻¹ : Aˣ)) := by rw [hO.D_conj_U, coe_scalarOp_comm, mul_assoc]
    _ = U ((a : k) ^ 2 * b) := by rw [Units.mul_inv, mul_one]

/-- **PROVED (tex 8777).** For ternary `Q`: `M_Q(a) M_Q(b) = (a,b)_k M_Q(ab)`. -/
theorem M_mul (hW : WeilIndexAxioms γ hs) (hQ : Q.length = 3) (a b : kˣ) :
    (diagOp γ Q D a : A) * diagOp γ Q D b = hs a b • (diagOp γ Q D (a * b) : A) := by
  have h : diagOp γ Q D a * diagOp γ Q D b = scalarOp (hs a b) * diagOp γ Q D (a * b) := by
    simp only [diagOp]
    rw [mul_assoc, ← mul_assoc (D a), ← scalarOp_comm, mul_assoc, ← mul_assoc,
      ← map_mul scalarOp, ← map_mul D, rQ_mul hW hQ, map_mul scalarOp, mul_assoc]
  rw [← Units.val_mul, h, coe_scalarOp_mul]

/-- **PROVED (tex 8778).** `W_Q M_Q(a) W_Q⁻¹ = M_Q(a⁻¹)`. -/
theorem W_conj_M (hW : WeilIndexAxioms γ hs) (hO : OperatorAxioms γ Q U D F) (a : kˣ) :
    (weylOp γ Q F : A) * diagOp γ Q D a * ((weylOp γ Q F)⁻¹ : Aˣ) = diagOp γ Q D a⁻¹ := by
  have h : weylOp γ Q F * diagOp γ Q D a * (weylOp γ Q F)⁻¹ = diagOp γ Q D a⁻¹ := by
    simp only [weylOp, diagOp]
    rw [conj_scalarOp_mul, ← mul_assoc F, ← scalarOp_comm, mul_assoc, mul_assoc, ← mul_assoc F,
      hO.F_conj_D, rQ_inv hW]
  rw [← Units.val_mul, ← Units.val_mul, h]

/-- **PROVED (tex 8779).** For ternary `Q`: `W_Q² = (−1,−1)_k M_Q(−1)`. -/
theorem W_sq (hW : WeilIndexAxioms γ hs) (hQ : Q.length = 3) (hO : OperatorAxioms γ Q U D F) :
    (weylOp γ Q F : A) * weylOp γ Q F = hs (-1) (-1) • (diagOp γ Q D (-1) : A) := by
  have hsc : gammaDiag γ Q * gammaDiag γ Q = hs (-1) (-1) * rQ γ Q (-1) := by
    rw [rQ_neg_one hW, ← gamma_pow_four hW hQ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  have h : weylOp γ Q F * weylOp γ Q F = scalarOp (hs (-1) (-1)) * diagOp γ Q D (-1) := by
    simp only [weylOp, diagOp]
    rw [mul_assoc, ← mul_assoc F, ← scalarOp_comm (gammaDiag γ Q) F, mul_assoc, ← mul_assoc,
      ← map_mul scalarOp, hO.F_sq, hsc, map_mul scalarOp, mul_assoc]
  rw [← Units.val_mul, h, coe_scalarOp_mul]

/-- **PROVED (tex 8780–8787).** For ternary `Q` and `b ≠ 0`:
`W_Q U_Q(b) W_Q = (−b,−1)_k U_Q(−b⁻¹) M_Q(−b⁻¹) W_Q U_Q(−b⁻¹)`; the Fourier identity leaves the
scalar `γ(Q)²γ(bQ)²` (with `γ(−b⁻¹Q)⁻¹ = γ(b⁻¹Q) = γ(bQ)`), which `scalar_WUW` reduces to
`(−b,−1)_k`. -/
theorem W_U_W (hW : WeilIndexAxioms γ hs) (hQ : Q.length = 3) (hO : OperatorAxioms γ Q U D F)
    (b : kˣ) :
    (weylOp γ Q F : A) * U b * weylOp γ Q F =
      hs (-b) (-1) • (U (-((b⁻¹ : kˣ) : k)) * (diagOp γ Q D (-b⁻¹) : A) * weylOp γ Q F *
        U (-((b⁻¹ : kˣ) : k))) := by
  have hF3 : F * F * F = F⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc F * F * F * F = (F * F) * (F * F) := by group
      _ = D (-1) * D (-1) := by rw [hO.F_sq]
      _ = 1 := by rw [← map_mul]; simp
  have hDF : D (-b⁻¹) * F = D b⁻¹ * F⁻¹ := by
    rw [show (-b⁻¹ : kˣ) = b⁻¹ * -1 by simp, map_mul, ← hO.F_sq, ← hF3]
    group
  have hDF' : ((D (-b⁻¹) : Aˣ) : A) * (F : A) = (D b⁻¹ : A) * ((F⁻¹ : Aˣ) : A) := by
    rw [← Units.val_mul, hDF, Units.val_mul]
  have hsc : gammaDiag γ Q * gammaDiag γ Q * gammaDiag γ (scaleForm b Q) =
      hs (-b) (-1) * (rQ γ Q (-b⁻¹) * gammaDiag γ Q) := by
    rw [rQ, hW.gammaDiag_scaleForm_neg, hW.gammaDiag_scaleForm_inv, ← scalar_WUW hW hQ b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  set V : A := U (-((b⁻¹ : kˣ) : k)) with hV
  simp only [weylOp, diagOp, Units.val_mul]
  calc ((scalarOp (gammaDiag γ Q) : Aˣ) : A) * (F : A) * U b *
        (((scalarOp (gammaDiag γ Q) : Aˣ) : A) * F)
      = ((scalarOp (gammaDiag γ Q * gammaDiag γ Q) : Aˣ) : A) * ((F : A) * U b * F) := by
        rw [mul_assoc ((scalarOp (gammaDiag γ Q) : Aˣ) : A), scalar_mul_scalar_mul]
    _ = ((scalarOp (gammaDiag γ Q * gammaDiag γ Q) : Aˣ) : A) *
          (((scalarOp (gammaDiag γ (scaleForm b Q)) : Aˣ) : A) *
            (V * (D b⁻¹ : A) * ((F⁻¹ : Aˣ) : A) * V)) := by
        rw [hO.fourier, smul_eq_scalarOp_mul]
    _ = ((scalarOp (hs (-b) (-1)) : Aˣ) : A) *
          (((scalarOp (rQ γ Q (-b⁻¹) * gammaDiag γ Q) : Aˣ) : A) *
            (V * (D b⁻¹ : A) * ((F⁻¹ : Aˣ) : A) * V)) := by
        rw [← mul_assoc, ← Units.val_mul, ← map_mul, hsc, map_mul, Units.val_mul, mul_assoc]
    _ = hs (-b) (-1) • (V * (((scalarOp (rQ γ Q (-b⁻¹)) : Aˣ) : A) * (D (-b⁻¹) : A)) *
          (((scalarOp (gammaDiag γ Q) : Aˣ) : A) * F) * V) := by
        rw [smul_eq_scalarOp_mul]
        congr 1
        rw [← mul_assoc V, ← coe_scalarOp_comm, mul_assoc ((scalarOp (rQ γ Q (-b⁻¹)) : Aˣ) : A) V,
          scalar_mul_scalar_mul]
        simp only [mul_assoc]
        rw [← mul_assoc ((D (-b⁻¹) : Aˣ) : A), hDF', mul_assoc]

/-- **PROVED (tex 8805–8807).** For ternary `Q`: `M_Q(−1)² = (−1,−1)_k id` (at two this is
`−id`: the order-four lift of `−I`). -/
theorem M_neg_one_sq (hW : WeilIndexAxioms γ hs) (hQ : Q.length = 3) :
    (diagOp γ Q D (-1) : A) * diagOp γ Q D (-1) = hs (-1) (-1) • (1 : A) := by
  rw [M_mul hW hQ, show ((-1 : kˣ) * -1) = 1 by simp, diagOp, rQ_one, map_one, map_one, one_mul,
    Units.val_one]

/-- **PROVED (consistency check only).** `OperatorAxioms` is satisfiable: with the trivial index
the scalars `U = 1`, `D = 1`, `F = 1` on `A = R` satisfy it. (A model with a nontrivial index is
the Weil representation itself, not constructed here.) -/
theorem operatorAxioms_trivial (Q : List kˣ) :
    OperatorAxioms (fun _ => (1 : Rˣ)) Q (fun _ => (1 : R)) (1 : kˣ →* Rˣ) 1 where
  U_add _ _ := (mul_one 1).symm
  U_zero := rfl
  D_conj_U _ _ := by simp
  F_conj_D _ := by simp
  F_sq := by simp
  fourier _ := by
    have h : ∀ l : List kˣ, gammaDiag (fun _ => (1 : Rˣ)) l = 1 := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => rw [gammaDiag_cons, ih, mul_one]
    simp [h]

end Operators

/-! ### (O.5b): the two local characters multiply (tex 8869–8887) -/

/-- **Definition + PROVED (tex 8874–8882).** For a character `α` and `δ = det Q`, the eigenvalue
`a ↦ α(a)(a, det Q)` of (O.5b) is again a character (both local characters multiply). -/
def eigenCharacter (hW : WeilIndexAxioms γ hs) (α : kˣ →* Rˣ) (δ : kˣ) : kˣ →* Rˣ where
  toFun a := α a * hs a δ
  map_one' := by rw [map_one, one_mul, hW.hs_symm, hW.hs_one_right]
  map_mul' a b := by
    rw [map_mul, hW.hs_mul_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel

/-- **PROVED.** `eigenCharacter hW α δ a = α a * (a, δ)`. -/
theorem eigenCharacter_apply (hW : WeilIndexAxioms γ hs) (α : kˣ →* Rˣ) (δ a : kˣ) :
    eigenCharacter hW α δ a = α a * hs a δ := rfl

/-- **PROVED (tex 8880–8881).** "The upper-left entry of a product is congruent to the product of
the upper-left entries modulo `p^{A_p}`": if the lower-left entry of `h` lies in the ideal `I`,
then `(gh)₁₁ ≡ g₁₁ h₁₁ (mod I)`. -/
theorem upper_left_mul_sub_mem {S : Type*} [CommRing S] (I : Ideal S)
    (g h : Matrix (Fin 2) (Fin 2) S) (hh : h 1 0 ∈ I) : (g * h) 0 0 - g 0 0 * h 0 0 ∈ I := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, add_sub_cancel_left]
  exact I.mul_mem_left _ hh

/-- **PROVED (tex 8879–8884).** A multiplicative function of the upper-left entry that only depends
on it modulo `I` (a local character of conductor dividing `I`) is multiplicative on matrices whose
lower-left entry lies in `I`. -/
theorem O5b_mul {S : Type*} [CommRing S] (I : Ideal S) (ψ : S →* R)
    (hψ : ∀ x y, x - y ∈ I → ψ x = ψ y) (g h : Matrix (Fin 2) (Fin 2) S) (hh : h 1 0 ∈ I) :
    ψ ((g * h) 0 0) = ψ (g 0 0) * ψ (h 0 0) := by
  rw [hψ _ _ (upper_left_mul_sub_mem I g h hh), map_mul]

/-! ### Non-vacuity: a model of `WeilIndexAxioms` at the real place -/

/-- **Definition.** `ζ₈ = e^{πi/4}` as a unit of `ℂ`. -/
noncomputable def zetaEight : ℂˣ :=
  Units.mk0 (Complex.exp (Real.pi / 4 * Complex.I)) (Complex.exp_ne_zero _)

/-- **PROVED.** `ζ₈⁴ = −1`. -/
theorem zetaEight_pow_four : zetaEight ^ 4 = -1 := by
  ext
  rw [Units.val_pow_eq_pow_val, zetaEight, Units.val_mk0, ← Complex.exp_nat_mul, Units.val_neg,
    Units.val_one]
  rw [show ((4 : ℕ) : ℂ) * (↑Real.pi / 4 * Complex.I) = ↑Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- **Definition (tex 8651–8653, real place).** `γ(a) = ζ₈` for `a > 0` and `ζ₈⁻¹` for `a < 0`:
the archimedean Weil index of `x ↦ a x²` for the character `e^{2πix}` (Fresnel integral; GLUE,
used here only as a model). -/
noncomputable def gammaReal (a : ℝˣ) : ℂˣ := if 0 < (a : ℝ) then zetaEight else zetaEight⁻¹

/-- **Definition.** The real Hilbert symbol: `(a,b)_∞ = −1` iff `a < 0` and `b < 0`, else `1`. -/
noncomputable def hilbertReal (a b : ℝˣ) : ℂˣ := if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then -1 else 1

/-- **PROVED.** `γ(a) = ζ₈` for `a > 0`. -/
theorem gammaReal_pos {a : ℝˣ} (h : 0 < (a : ℝ)) : gammaReal a = zetaEight := by
  simp [gammaReal, h]

/-- **PROVED.** `γ(a) = ζ₈⁻¹` for `a < 0`. -/
theorem gammaReal_neg {a : ℝˣ} (h : (a : ℝ) < 0) : gammaReal a = zetaEight⁻¹ := by
  simp [gammaReal, not_lt.mpr h.le]

/-- **PROVED.** `(a,b)_∞ = (b<0 ? −1 : 1)` for `a < 0`. -/
theorem hilbertReal_of_neg {a : ℝˣ} (ha : (a : ℝ) < 0) (b : ℝˣ) :
    hilbertReal a b = if (b : ℝ) < 0 then -1 else 1 := by
  simp [hilbertReal, ha]

/-- **PROVED (non-vacuity; tex 8651–8653, 8688–8716, real place).** `k = ℝ`, `R = ℂ`, the
archimedean index `gammaReal` and the real Hilbert symbol satisfy every field of
`WeilIndexAxioms`: `γ(−a) = γ(a)⁻¹`, `γ(as²) = γ(a)`, the norm-form identity
`γ(1)γ(−u)γ(−a)γ(ua) = (u,a)_∞` (both negative: `ζ₈⁴ = −1`; otherwise `1`), and the
Hilbert-symbol laws. -/
theorem weilIndexAxioms_real : WeilIndexAxioms gammaReal hilbertReal where
  neg a := by
    rcases lt_or_gt_of_ne (Units.ne_zero a) with ha | ha
    · rw [gammaReal_neg ha, gammaReal_pos (by simpa using ha), inv_inv]
    · rw [gammaReal_pos ha, gammaReal_neg (by simpa using ha)]
  sq a s := by
    have hs : 0 < (s : ℝ) ^ 2 := by have := Units.ne_zero s; positivity
    rcases lt_or_gt_of_ne (Units.ne_zero a) with ha | ha
    · rw [gammaReal_neg ha, gammaReal_neg (by simpa using mul_neg_of_neg_of_pos ha hs)]
    · rw [gammaReal_pos ha, gammaReal_pos (by simpa using mul_pos ha hs)]
  norm_form u a := by
    simp only [gammaDiag_cons, gammaDiag_nil]
    rcases lt_or_gt_of_ne (Units.ne_zero u) with hu | hu <;>
    rcases lt_or_gt_of_ne (Units.ne_zero a) with ha | ha
    · rw [gammaReal_pos (by simp), gammaReal_pos (by simpa using hu),
        gammaReal_pos (by simpa using ha),
        gammaReal_pos (by simpa using mul_pos_of_neg_of_neg hu ha),
        show hilbertReal u a = -1 by simp [hilbertReal, hu, ha], ← zetaEight_pow_four]
      simp only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
    · rw [gammaReal_pos (by simp), gammaReal_pos (by simpa using hu),
        gammaReal_neg (by simpa using ha),
        gammaReal_neg (by simpa using mul_neg_of_neg_of_pos hu ha)]
      simp [hilbertReal, not_lt.mpr ha.le]
    · rw [gammaReal_pos (by simp), gammaReal_neg (by simpa using hu),
        gammaReal_pos (by simpa using ha),
        gammaReal_neg (by simpa using mul_neg_of_pos_of_neg hu ha)]
      simp [hilbertReal, not_lt.mpr hu.le]
    · rw [gammaReal_pos (by simp), gammaReal_neg (by simpa using hu),
        gammaReal_neg (by simpa using ha), gammaReal_pos (by simpa using mul_pos hu ha)]
      simp [hilbertReal, not_lt.mpr hu.le]
  hs_symm a b := by
    simp only [hilbertReal, and_comm]
  hs_mul a b c := by
    rcases lt_or_gt_of_ne (Units.ne_zero a) with ha | ha
    · rw [hilbertReal_of_neg ha, hilbertReal_of_neg ha, hilbertReal_of_neg ha, Units.val_mul]
      rcases lt_or_gt_of_ne (Units.ne_zero b) with hb | hb <;>
      rcases lt_or_gt_of_ne (Units.ne_zero c) with hc | hc
      · simp [hb, hc, not_lt.mpr (mul_pos_of_neg_of_neg hb hc).le]
      · simp [hb, not_lt.mpr hc.le, mul_neg_of_neg_of_pos hb hc]
      · simp [hc, not_lt.mpr hb.le, mul_neg_of_pos_of_neg hb hc]
      · simp [not_lt.mpr hb.le, not_lt.mpr hc.le, not_lt.mpr (mul_pos hb hc).le]
    · simp [hilbertReal, not_lt.mpr ha.le]
  hs_sq a b := by
    unfold hilbertReal
    split_ifs <;> simp

/-- **PROVED.** In the real model `γ(1)⁴ = −1 ≠ 1`. -/
theorem gammaReal_one_pow_four : gammaReal 1 ^ 4 = -1 := by
  rw [gammaReal_pos (by simp), zetaEight_pow_four]

/-- **PROVED (non-vacuity; tex 8764, real place).** In the real model
`γ(1)⁴ = (−1,−1)_∞ = −1`, and `−1 ≠ 1` in `ℂˣ`: the hypotheses are not satisfied only by trivial
data, and `gamma_one_pow_four` is a nontrivial identity there. -/
theorem real_place_nontrivial :
    gammaReal 1 ^ 4 = hilbertReal (-1) (-1) ∧ hilbertReal (-1) (-1) = -1 ∧ (-1 : ℂˣ) ≠ 1 := by
  refine ⟨gamma_one_pow_four weilIndexAxioms_real, ?_, ?_⟩
  · simp [hilbertReal]
  · intro h
    have h' := congrArg (fun x : ℂˣ => (x : ℂ)) h
    norm_num at h'

end ZInQ.Manuscript.RC.Visibility
