import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
namespace ZInQ.Manuscript.RC.Symbols
open Finset

/-- A singular program at target `x` for the pair `e` (tex 10696–10701). -/
def IsSingularProgram {Y : Type*} (x : Y) (e : Sym2 ℕ)
    (O : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) : Prop :=
  MvPolynomial.constantCoeff (O x) = 0 ∧
    (∀ f, (O x).coeff (Finsupp.single f 1) = if f = e then 1 else 0) ∧
    ∀ y, y ≠ x → MvPolynomial.constantCoeff (O y) = 1

open Classical in
/-- A varying program pair at target `x` for the pair `e` (tex 10704–10720). -/
def IsVaryingProgram {Y : Type*} (x : Y) (e : Sym2 ℕ)
    (O : ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) : Prop :=
  (∀ ε y, MvPolynomial.constantCoeff (O ε y) = 1) ∧
    ∀ y f, (O 0 y).coeff (Finsupp.single f 1) + (O 1 y).coeff (Finsupp.single f 1) =
      if y = x ∧ f = e then 1 else 0

/-- (G.1a): one choice for both symbols at every nonzero address (tex 10722–10768). -/
theorem degree_count {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Fin 2 → Y → Finset (Sym2 ℕ) → ZMod 2) (E : Y → Finset (Sym2 ℕ))
    (hE : ∀ s y U, P s y U = P s y (U ∩ E y)) (hP : ∀ s y, ∃ U, P s y U = 1) :
    ∃ (Ns Nv : Finset (Y × Sym2 ℕ)), Disjoint Ns Nv ∧ (∀ p ∈ Ns ∪ Nv, p.2 ∈ E p.1) ∧
      ∀ (Os : Y × Sym2 ℕ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2))
        (Ov : Y × Sym2 ℕ → ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)),
        (∀ p ∈ Ns, IsSingularProgram p.1 p.2 (Os p)) →
        (∀ p ∈ Nv, IsVaryingProgram p.1 p.2 (Ov p)) →
        ∃ εv : Y × Sym2 ℕ → ZMod 2, ∀ s y,
          act ((∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εv p) y) (P s y) ∅ = 1 := sorry

/-- The one-symbol specialization (tex 10778–10784): singular programs only. -/
theorem degree_count_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Y → Finset (Sym2 ℕ) → ZMod 2) (E : Y → Finset (Sym2 ℕ))
    (hE : ∀ y U, P y U = P y (U ∩ E y)) (hP : ∀ y, ∃ U, P y U = 1) :
    ∃ Ns : Finset (Y × Sym2 ℕ), (∀ p ∈ Ns, p.2 ∈ E p.1) ∧
      ∀ Os : Y × Sym2 ℕ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2),
        (∀ p ∈ Ns, IsSingularProgram p.1 p.2 (Os p)) →
        ∀ y, act (∏ p ∈ Ns, Os p y) (P y) ∅ = 1 := sorry
end ZInQ.Manuscript.RC.Symbols
