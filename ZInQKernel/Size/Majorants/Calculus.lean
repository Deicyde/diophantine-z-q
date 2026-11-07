import ZInQKernel.Size.Majorants.Rules
import ZInQKernel.Syntax.Templates.Library

/-!
# A size calculus for template formulas

The templates of the library are `Build` programs whose final formulas are built from pairs,
point codes, gadgets and calls. This file extends the scale `Scale B e s` of
`ZInQKernel.Size.Majorants.Basic` to pairs (`PScale`), argument tuples and point codes (`AScale`)
and lists of formulas (`FAll`), with one rule per constructor of the syntax. Every rule
computes the level of its conclusion from the levels of its premises (`max` for the binary
operations, `+ 1` for a ring operation, `+ 3` for a pair product), so the levels of an explicit
formula are found by applying the rules from the leaves up; the tactic `size` of
`ZInQKernel.Size.Majorants.Tactic` does exactly that. The resulting levels are small closed
numbers, compared with the target height by `decide`.

Three loops of the library have their own rules, proved by induction: repeated squaring
(`PScale.pow`), the product `slopeW` and the truncated logarithm `log25`.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax

variable {B : ℕ} {σ : Type*}

/-! ### Polynomials -/

namespace Scale

variable {e₁ e₂ s₁ s₂ : ℕ} {P Q : MvPolynomial σ ℤ}

theorem add' (hB : 1 ≤ B) (hP : Scale B e₁ s₁ P) (hQ : Scale B e₂ s₂ Q) :
    Scale B (max e₁ e₂) (max s₁ s₂ + 1) (P + Q) :=
  (hP.mono hB (le_max_left _ _) (le_max_left _ _)).add
    (hQ.mono hB (le_max_right _ _) (le_max_right _ _)) hB

theorem sub' (hB : 1 ≤ B) (hP : Scale B e₁ s₁ P) (hQ : Scale B e₂ s₂ Q) :
    Scale B (max e₁ e₂) (max s₁ s₂ + 1) (P - Q) :=
  (hP.mono hB (le_max_left _ _) (le_max_left _ _)).sub
    (hQ.mono hB (le_max_right _ _) (le_max_right _ _)) hB

theorem mul' (hB : 1 ≤ B) (hP : Scale B e₁ s₁ P) (hQ : Scale B e₂ s₂ Q) :
    Scale B (max e₁ e₂) (max s₁ s₂ + 1) (P * Q) :=
  (hP.mono hB (le_max_left _ _) (le_max_left _ _)).mul
    (hQ.mono hB (le_max_right _ _) (le_max_right _ _))

theorem neg' {e s : ℕ} (hP : Scale B e s P) : Scale B e s (-P) := hP.neg

theorem pow' {e s : ℕ} (k : ℕ) {n : ℕ} (hP : Scale B e s P) (hn : n ≤ 2 ^ k) :
    Scale B e (s + k) (P ^ n) := hP.pow hn

theorem X' (hB : 1 ≤ B) (i : σ) : Scale B 0 0 (MvPolynomial.X i : MvPolynomial σ ℤ) := Scale.X hB i

theorem C' (hB : 1 ≤ B) (k : ℕ) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ k) :
    Scale B 0 k (MvPolynomial.C c : MvPolynomial σ ℤ) := Scale.C hB hc

theorem intCast' (hB : 1 ≤ B) (k : ℕ) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ k) :
    Scale B 0 k (c : MvPolynomial σ ℤ) := Scale.intCast hB hc

theorem ofNat' (hB : 1 ≤ B) (k n : ℕ) [n.AtLeastTwo] (hn : n ≤ 2 ^ 2 ^ k) :
    Scale B 0 k (OfNat.ofNat n : MvPolynomial σ ℤ) := Scale.ofNat hB n hn

theorem zero' (hB : 1 ≤ B) : Scale B 0 0 (0 : MvPolynomial σ ℤ) := Scale.zero hB

theorem one' (hB : 1 ≤ B) : Scale B 0 0 (1 : MvPolynomial σ ℤ) := Scale.one hB

end Scale

/-! ### Argument tuples and point codes -/

/-- Every entry of an argument tuple (in particular of a point code) is at level `(e, s)`. -/
def AScale (B e s : ℕ) {n : ℕ} (g : Fin n → Poly) : Prop := ∀ k, Scale B e s (g k)

namespace AScale

variable {e₁ e₂ s₁ s₂ e s : ℕ}

theorem mono {n : ℕ} {g : Fin n → Poly} (h : AScale B e s g) (hB : 1 ≤ B) {e' s' : ℕ}
    (he : e ≤ e') (hs : s ≤ s') : AScale B e' s' g := fun k => (h k).mono hB he hs

theorem append' (hB : 1 ≤ B) {m n : ℕ} {a : Fin m → Poly} {b : Fin n → Poly} (ha : AScale B e₁ s₁ a)
    (hb : AScale B e₂ s₂ b) : AScale B (max e₁ e₂) (max s₁ s₂) (Fin.append a b) := by
  intro k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · rw [Fin.append_left]; exact (ha i).mono hB (le_max_left _ _) (le_max_left _ _)
  · rw [Fin.append_right]; exact (hb i).mono hB (le_max_right _ _) (le_max_right _ _)

theorem cons' (hB : 1 ≤ B) {n : ℕ} {a : Poly} {v : Fin n → Poly} (ha : Scale B e₁ s₁ a)
    (hv : AScale B e₂ s₂ v) : AScale B (max e₁ e₂) (max s₁ s₂) (Matrix.vecCons a v) := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [Matrix.cons_val_zero]; exact ha.mono hB (le_max_left _ _) (le_max_left _ _)
  · rw [Matrix.cons_val_succ]; exact (hv i).mono hB (le_max_right _ _) (le_max_right _ _)

theorem nil : AScale B 0 0 (![] : Fin 0 → Poly) := fun k => k.elim0

theorem varPoint (hB : 1 ≤ B) (k : ℕ) : AScale B 0 0 (ZInQ.Syntax.varPoint k) := fun _ => Scale.X hB _

theorem varArgs (hB : 1 ≤ B) (k n : ℕ) : AScale B 0 0 (ZInQ.Syntax.varArgs k n) := fun _ => Scale.X hB _

theorem neg {p : Code} (h : AScale B e s p) : AScale B e s p.neg := by
  intro k
  fin_cases k
  · exact h 0
  · exact h 1
  · exact h 2
  · exact (h 3).neg
  · exact (h 4).neg

theorem O (hB : 1 ≤ B) : AScale B 0 0 Code.O := by
  intro k
  fin_cases k
  · exact Scale.one hB
  all_goals exact Scale.zero hB

theorem codes {n : ℕ} {C : Fin n → Code} (h : ∀ i, AScale B e s (C i)) : AScale B e s (codesArgs C) :=
  fun _ => h _ _

end AScale

theorem Scale.app {e s n : ℕ} {g : Fin n → Poly} (h : AScale B e s g) (k : Fin n) : Scale B e s (g k) :=
  h k

/-! ### Pairs -/

/-- Both components of a pair are at level `(e, s)`. -/
def PScale (B e s : ℕ) (u : Pair) : Prop := Scale B e s u.1 ∧ Scale B e s u.2

namespace PScale

variable {e₁ e₂ s₁ s₂ e s : ℕ} {u v : Pair}

theorem mono (h : PScale B e s u) (hB : 1 ≤ B) {e' s' : ℕ} (he : e ≤ e') (hs : s ≤ s') :
    PScale B e' s' u := ⟨h.1.mono hB he hs, h.2.mono hB he hs⟩

theorem fst (h : PScale B e s u) : Scale B e s u.1 := h.1

theorem snd (h : PScale B e s u) : Scale B e s u.2 := h.2

theorem mk' (hB : 1 ≤ B) {a b : Poly} (ha : Scale B e₁ s₁ a) (hb : Scale B e₂ s₂ b) :
    PScale B (max e₁ e₂) (max s₁ s₂) (a, b) :=
  ⟨ha.mono hB (le_max_left _ _) (le_max_left _ _), hb.mono hB (le_max_right _ _) (le_max_right _ _)⟩

theorem add' (hB : 1 ≤ B) (hu : PScale B e₁ s₁ u) (hv : PScale B e₂ s₂ v) :
    PScale B (max e₁ e₂) (max s₁ s₂ + 1) (u.add v) :=
  ⟨Scale.add' hB hu.1 hv.1, Scale.add' hB hu.2 hv.2⟩

theorem neg' (hu : PScale B e s u) : PScale B e s u.neg := ⟨hu.1.neg, hu.2.neg⟩

theorem sub' (hB : 1 ≤ B) (hu : PScale B e₁ s₁ u) (hv : PScale B e₂ s₂ v) :
    PScale B (max e₁ e₂) (max s₁ s₂ + 1) (u.sub v) := add' hB hu hv.neg'

theorem smul' (hB : 1 ≤ B) {k : Poly} (hk : Scale B e₁ s₁ k) (hu : PScale B e₂ s₂ u) :
    PScale B (max e₁ e₂) (max s₁ s₂ + 1) (Pair.smul k u) :=
  ⟨Scale.mul' hB hk hu.1, Scale.mul' hB hk hu.2⟩

theorem conj' (hu : PScale B e s u) : PScale B e s u.conj := ⟨hu.1, hu.2.neg⟩

/-- A pair product costs three levels. -/
theorem mul_same (hB : 1 ≤ B) (hu : PScale B e s u) (hv : PScale B e s v) : PScale B e (s + 3) (u.mul v) := by
  have h2 : Scale B e (s + 1) (2 : Poly) := Scale.ofNat hB 2 (by
    calc 2 ≤ 2 ^ 2 ^ 0 := by norm_num
      _ ≤ 2 ^ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)))
  refine ⟨?_, ?_⟩
  · exact ((hu.1.mul hv.1).mono hB le_rfl (by omega)).add (h2.mul (hu.2.mul hv.2)) hB
  · exact ((hu.1.mul hv.2).add (hu.2.mul hv.1) hB).mono hB le_rfl (by omega)

theorem mul' (hB : 1 ≤ B) (hu : PScale B e₁ s₁ u) (hv : PScale B e₂ s₂ v) :
    PScale B (max e₁ e₂) (max s₁ s₂ + 3) (u.mul v) :=
  mul_same hB (hu.mono hB (le_max_left _ _) (le_max_left _ _))
    (hv.mono hB (le_max_right _ _) (le_max_right _ _))

theorem sq' (hB : 1 ≤ B) (hu : PScale B e s u) : PScale B e (s + 3) u.sq := mul_same hB hu hu

theorem ofInt' (hB : 1 ≤ B) (k : ℕ) {a b : ℤ} (ha : a.natAbs ≤ 2 ^ 2 ^ k)
    (hb : b.natAbs ≤ 2 ^ 2 ^ k) : PScale B 0 k (Pair.ofInt a b) := ⟨Scale.C hB ha, Scale.C hB hb⟩

theorem varPair (hB : 1 ≤ B) (k : ℕ) : PScale B 0 0 (ZInQ.Syntax.varPair k) := ⟨Scale.X hB _, Scale.X hB _⟩

theorem x {p : Code} (h : AScale B e s p) : PScale B e s p.x := ⟨h 1, h 2⟩

theorem y {p : Code} (h : AScale B e s p) : PScale B e s p.y := ⟨h 3, h 4⟩

theorem args {u : Pair} (h : PScale B e s u) : AScale B e s u.args := by
  intro k
  fin_cases k
  · exact h.1
  · exact h.2

theorem norm' (hB : 1 ≤ B) (hu : PScale B e s u) : Scale B e (s + 3) u.norm := by
  have h2 : Scale B e (s + 1) (2 : Poly) := Scale.ofNat hB 2 (by
    calc 2 ≤ 2 ^ 2 ^ 0 := by norm_num
      _ ≤ 2 ^ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)))
  have h1 := hu.1.pow (n := 2) (k := 1) (by norm_num)
  have h2' := h2.mul (hu.2.pow (n := 2) (k := 1) (by norm_num))
  exact (h1.mono hB le_rfl (by omega)).sub h2' hB

/-- **Repeated squaring.** For `n < 2^m`, `u^n` costs at most `3m` levels. -/
theorem powAux (hB : 1 ≤ B) {a : ℕ} :
    ∀ (m n : ℕ) {r q : Pair}, n < 2 ^ m → PScale B e a r → PScale B e a q →
      PScale B e (a + 3 * m) (Pair.powAux n r q) := by
  intro m
  induction m generalizing a with
  | zero =>
    intro n r q hn hr _
    obtain rfl : n = 0 := by simpa using hn
    rw [Pair.powAux]
    simpa using hr
  | succ m ih =>
    intro n r q hn hr hq
    rw [Pair.powAux]
    split_ifs with h0 h1 h2 h2
    · exact hr.mono hB le_rfl (by omega)
    · exact (mul_same hB hr hq).mono hB le_rfl (by omega)
    · have := ih (a := a + 3) (n / 2) (by rw [pow_succ] at hn; omega) (mul_same hB hr hq)
        (sq' hB hq)
      exact this.mono hB le_rfl (by omega)
    · exact hr.mono hB le_rfl (by omega)
    · have := ih (a := a + 3) (n / 2) (by rw [pow_succ] at hn; omega)
        (hr.mono hB le_rfl (by omega)) (sq' hB hq)
      exact this.mono hB le_rfl (by omega)

theorem pow (hB : 1 ≤ B) (m : ℕ) {n : ℕ} (hn : n < 2 ^ m) (hu : PScale B e s u) :
    PScale B e (s + 3 * m) (u.pow n) :=
  powAux hB m n hn ⟨(Scale.C hB (by simp)).mono hB (Nat.zero_le _) (Nat.zero_le _),
    (Scale.C hB (by simp)).mono hB (Nat.zero_le _) (Nat.zero_le _)⟩ hu

theorem one_le (hB : 1 ≤ B) (e s : ℕ) : PScale B e s Pair.one :=
  ⟨(Scale.C hB (by simp)).mono hB (Nat.zero_le _) (Nat.zero_le _),
    (Scale.C hB (by simp)).mono hB (Nat.zero_le _) (Nat.zero_le _)⟩

/-- **The product `slopeW`.** Each factor `1 + R C'²` costs five levels over `R` and `C'` and
each multiplication three. -/
theorem slopeW_aux (hB : 1 ≤ B) {a : ℕ} {R : Poly} (hR : Scale B e a R) :
    ∀ (N : List Pair), (∀ n ∈ N, PScale B e a n) → ∀ {W : Pair} {L : ℕ}, a + 5 ≤ L → PScale B e L W →
      PScale B e (L + 3 * N.length)
        (N.foldl (fun W n => W.mul (Pair.one.add (Pair.smul R n.sq))) W) := by
  intro N
  induction N with
  | nil => intro _ W L _ hW; simpa using hW
  | cons n N ih =>
    intro hN W L hL hW
    rw [List.foldl_cons]
    have hn := hN n List.mem_cons_self
    have ht : PScale B e (a + 5) (Pair.one.add (Pair.smul R n.sq)) := by
      have := add' hB (one_le hB e (a + 4)) (smul' hB hR (sq' hB hn))
      simpa using this
    have hW' : PScale B e (L + 3) (W.mul (Pair.one.add (Pair.smul R n.sq))) :=
      mul_same hB hW (ht.mono hB le_rfl hL)
    have := ih (fun m hm => hN m (List.mem_cons_of_mem _ hm)) (L := L + 3) (by omega) hW'
    simpa [List.length_cons, Nat.mul_succ, add_assoc, add_comm, add_left_comm] using this

theorem slopeW' (hB : 1 ≤ B) {R : Poly} {n : ℕ} {N : Fin n → Pair} (hR : Scale B e₁ s₁ R)
    (hN : ∀ j, PScale B e₂ s₂ (N j)) :
    PScale B (max e₁ e₂) (max s₁ s₂ + 5 + 3 * n) (slopeW R (List.ofFn N)) := by
  have := slopeW_aux hB (hR.mono hB (le_max_left e₁ e₂) (le_max_left s₁ s₂)) (List.ofFn N)
    (fun m hm => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hm
      exact (hN j).mono hB (le_max_right _ _) (le_max_right _ _))
    le_rfl (one_le hB _ _)
  simp only [List.length_ofFn] at this
  exact this

/-- **The truncated logarithm.** Each of its terms costs five levels. -/
theorem log25Aux (hB : 1 ≤ B) {a L : ℕ} {ζ : Pair} (hζ : PScale B e a ζ) (hL : a + 15 ≤ L)
    (h7 : 7 ≤ L) :
    ∀ (cs : List ℤ) (j : ℕ), j + cs.length ≤ 8 → (∀ c ∈ cs, c.natAbs ≤ 2 ^ 2 ^ 7) →
      ∀ {out dPower : Pair}, PScale B e L out → PScale B e L dPower →
      PScale B e (L + 5 * cs.length) (Pair.log25Aux ζ cs out dPower j) := by
  intro cs
  induction cs generalizing L with
  | nil => intro j _ _ out dPower hout _; simpa [Pair.log25Aux] using hout
  | cons c cs ih =>
    intro j hj hcs out dPower hout hd
    rw [Pair.log25Aux]
    have hpow : PScale B e (a + 3 * 5) (ζ.pow (4 * j + 1)) :=
      pow hB 5 (by simp at hj; omega) hζ
    have hc : Scale B e (L + 3) (C c : Poly) :=
      (Scale.C hB (hcs c List.mem_cons_self)).mono hB (Nat.zero_le _) (by omega)
    have hterm : PScale B e (L + 4) (Pair.smul (C c) (dPower.mul (ζ.pow (4 * j + 1)))) := by
      have := smul' hB hc (mul_same hB hd (hpow.mono hB le_rfl (by omega)))
      simpa using this
    have hout' : PScale B e (L + 5) (out.add (Pair.smul (C c) (dPower.mul (ζ.pow (4 * j + 1))))) := by
      have := add' hB hout hterm
      simpa using this
    have hdelta : PScale B e L Pair.delta :=
      (ofInt' hB 7 (by norm_num) (by norm_num)).mono hB (Nat.zero_le _) h7
    have hd' : PScale B e (L + 5) (dPower.mul Pair.delta) :=
      (mul_same hB hd hdelta).mono hB le_rfl (by omega)
    have := ih (L := L + 5) (by omega) (by omega) (j + 1) (by simp at hj; omega)
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hout' hd'
    simpa [List.length_cons, Nat.mul_succ, add_assoc, add_comm, add_left_comm] using this

theorem log25' (hB : 1 ≤ B) {ζ : Pair} (hζ : PScale B e s ζ) :
    PScale B e (max (s + 15) 7 + 35) ζ.log25 := by
  have hL := log25Aux hB hζ (le_max_left (s + 15) 7) (le_max_right _ _) log25Coeffs 0
    (by decide) (by decide) (out := Pair.zero) (dPower := Pair.one)
    ((ofInt' hB 0 (by norm_num) (by norm_num)).mono hB (Nat.zero_le _) (Nat.zero_le _))
    (one_le hB _ _)
  exact hL

end PScale

/-- The pair of psi nodes `psiPair I n p` at a point `p`: each component is a constructor at
level `(e₁, s₁)` substituted with four coordinates of `p`. -/
theorem Scale.bind₁_fin {e₁ e₂ s₁ s₂ n : ℕ} (hB : 1 ≤ B) {C : MvPolynomial (Fin n) ℤ}
    {f : Fin n → Poly} (hC : Scale B e₁ s₁ C) (hf : AScale B e₂ s₂ f) :
    Scale B (e₁ + e₂) (s₁ + s₂ + 1) (MvPolynomial.bind₁ f C) :=
  hC.bind₁ (fun i _ => hf i) hB

/-! ### Formulas -/

/-- Every formula of a list compiles to a polynomial at level `(e, s)`. -/
def FAll (B e s : ℕ) (fs : List Formula) : Prop := ∀ φ ∈ fs, Scale B e s φ.compile

namespace FAll

variable {e₁ e₂ s₁ s₂ e s : ℕ}

theorem nil : FAll B 0 0 [] := fun _ h => absurd h List.not_mem_nil

theorem nil_mono' (e s : ℕ) : FAll B e s [] := fun _ h => absurd h List.not_mem_nil

theorem cons' (hB : 1 ≤ B) {φ : Formula} {fs : List Formula} (hφ : Scale B e₁ s₁ φ.compile)
    (hfs : FAll B e₂ s₂ fs) : FAll B (max e₁ e₂) (max s₁ s₂) (φ :: fs) := by
  intro ψ hψ
  rcases List.mem_cons.1 hψ with rfl | hψ
  · exact hφ.mono hB (le_max_left _ _) (le_max_left _ _)
  · exact (hfs ψ hψ).mono hB (le_max_right _ _) (le_max_right _ _)

theorem append' (hB : 1 ≤ B) {fs gs : List Formula} (hf : FAll B e₁ s₁ fs) (hg : FAll B e₂ s₂ gs) :
    FAll B (max e₁ e₂) (max s₁ s₂) (fs ++ gs) := by
  intro ψ hψ
  rcases List.mem_append.1 hψ with hψ | hψ
  · exact (hf ψ hψ).mono hB (le_max_left _ _) (le_max_left _ _)
  · exact (hg ψ hψ).mono hB (le_max_right _ _) (le_max_right _ _)

end FAll

namespace Scale

variable {e₁ e₂ s₁ s₂ e s : ℕ}

theorem compile_eq' (hB : 1 ≤ B) {a b : Poly} (ha : Scale B e₁ s₁ a) (hb : Scale B e₂ s₂ b) :
    Scale B (max e₁ e₂) (max s₁ s₂ + 1) (Formula.eq a b).compile := by
  rw [Formula.compile_eq]; exact sub' hB ha hb

theorem compile_atom' {f : Poly} (hf : Scale B e s f) : Scale B e s (Formula.atom f).compile := by
  rw [Formula.compile_atom]; exact hf

theorem call' (hB : 1 ≤ B) {τ : ExPoly} {g : Fin τ.params → Poly} {w : ℕ}
    (hτ : Scale B e₁ s₁ τ.poly) (hg : AScale B e₂ s₂ g) :
    Scale B (e₁ + e₂) (s₁ + s₂ + 1) (τ.call g w) := by
  refine hτ.bind₁ (fun i _ => ?_) hB
  unfold callSubst
  split_ifs
  · exact hg _
  · exact (Scale.X hB _).mono hB (Nat.zero_le _) (Nat.zero_le _)

theorem compile_call' (hB : 1 ≤ B) {τ : ExPoly} {g : Fin τ.params → Poly} {w : ℕ}
    (hτ : Scale B e₁ s₁ τ.poly) (hg : AScale B e₂ s₂ g) :
    Scale B (e₁ + e₂) (s₁ + s₂ + 1) (Formula.call τ g w).compile := by
  rw [Formula.compile_call]; exact call' hB hτ hg

/-- A sum of at most `2^k` terms raises `s` by `k`. -/
theorem list_sum_pow {l : List Poly} (hB : 1 ≤ B) (h : ∀ f ∈ l, Scale B e s f) (k : ℕ)
    (hlen : l.length ≤ 2 ^ k) : Scale B e (s + k) l.sum := by
  have hsc : 2 ^ (s + k) * B ^ e = 2 ^ k * (2 ^ s * B ^ e) := by rw [pow_add]; ring
  have hM := one_le_scale hB e s
  rw [Scale, hsc]
  constructor
  · refine (totalDegree_list_sum_le' l _ fun f hf => (h f hf).1).trans ?_
    exact Nat.le_mul_of_pos_left _ (by positivity)
  · refine (l1_list_sum_le l).trans ?_
    have hsum : (l.map l1).sum ≤ l.length * 2 ^ (2 ^ s * B ^ e) := by
      have := List.sum_le_length_nsmul (l.map l1) (2 ^ (2 ^ s * B ^ e))
        (fun x hx => by obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx; exact (h f hf).2)
      simpa using this
    refine hsum.trans ((Nat.mul_le_mul_right _ hlen).trans ?_)
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    -- `k + M ≤ 2^k M` for `M ≥ 1`
    have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    calc k + 2 ^ s * B ^ e ≤ (2 ^ k - 1) * (2 ^ s * B ^ e) + 2 ^ s * B ^ e := by
          have : k ≤ (2 ^ k - 1) * 1 := by omega
          exact Nat.add_le_add_right (this.trans (Nat.mul_le_mul_left _ hM)) _
      _ = 2 ^ k * (2 ^ s * B ^ e) := by
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]

theorem compile_and' (hB : 1 ≤ B) (k : ℕ) {fs : List Formula} (hfs : FAll B e s fs)
    (hlen : fs.length ≤ 2 ^ k) : Scale B e (s + 1 + k) (Formula.and fs).compile := by
  rw [Formula.compile_and]
  refine list_sum_pow hB (fun f hf => ?_) k (by simpa using hlen)
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
  exact (hfs φ hφ).pow (n := 2) (k := 1) (by norm_num)

theorem compile_or' (k : ℕ) {fs : List Formula} (hfs : FAll B e s fs) (hlen : fs.length ≤ 2 ^ k) :
    Scale B e (s + k) (Formula.or fs).compile := by
  rw [Formula.compile_or]
  refine list_prod (fun f hf => ?_) (by simpa using hlen)
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
  exact hfs φ hφ

end Scale

/-! ### From levels to heights -/

/-- The majorant from a level: `e ≤ 8h` and `s ≤ 160` give height `h + 1`. -/
theorem maj_of_sz {e s h : ℕ} {P : MvPolynomial σ ℤ} (hB : 2 ^ 20 ≤ B) (hP : Scale B e s P)
    (he : e ≤ 8 * h) (hs : s ≤ 160) : Maj B (h + 1) P :=
  Scale.maj_succ (hP.mono (one_le_of_two_pow_twenty_le hB) he le_rfl)
    (two_pow_le_pow_eight hB hs)

end ZInQ.Size
