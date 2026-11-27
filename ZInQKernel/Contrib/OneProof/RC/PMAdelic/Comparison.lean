import ZInQKernel.Contrib.OneProof.RC.Adelic.Stage
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Geometry

/-!
# The adelic comparison on coarse supersingular points

Tex 8462–8474, 8481–8490 and 9331–9358. Two inputs: the class-set comparison
`JetchevKane` (GLUE; Jetchev–Kane §§1.1–1.2 and 2.5, arXiv v1; journal version
unread; Ribet 1990 Prop. 3.3 reports it without proof; a Lean proof is in
progress) and the operator comparison `OperatorComparison` (ELLIOT; asserted
in the manuscript; to be proved in Lean). The passage from double cosets to
ideal classes, including the independence of the Hecke sum from the enumeration
of the neighbours, is proved here.
-/

noncomputable section

open FreeAbelianGroup (of)

namespace ZInQ.Manuscript.RC.PMAdelic

open Eichler Adelic

/-- The points and operators of the coarse special fibre of `X₀(N)` over
the quadratic residue field. Frobenius here is the arithmetic prime-field action. -/
structure CoarseFibre where
  Point : Type
  ss : Set Point
  T : ℕ → Point → FreeAbelianGroup Point
  W : ℕ → Point → Point
  frobenius : Point → Point

/-- Supply each algebraic field from the constructed level order (tex 8462–8468). -/
def adelic (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3) (N : ℕ) (hN : 0 < N)
    (hcop : N.Coprime ell) : PMGeometry.Adelic (ell := ell) (N := N) (levelOrder ell h N hN) :=
  let A := algebraicGeometry ell h N hN hcop
  { ram := A.ram
    eichler := A.eichler
    atkin := A.atkin
    atkin_involutive := A.atkin_involutive
    uniformizer := A.uniformizer }

section Neighbours

variable {a b : ℚ} {R : Order a b} {p : ℕ} {hp : p ≠ 0} [NeZero p]

/-- On-the-spot (c): two line indices enumerate the same actual neighbours
once each before passage to their classes. Thus repetitions of a class are retained. -/
theorem neighbourMultiset_eq (lines lines' : LineIndex R p hp) (z : ClassSet R) :
    Finset.univ.val.map (nbAt lines z) = Finset.univ.val.map (nbAt lines' z) := by
  let e := (lines z).trans (lines' z).symm
  calc
    _ = Finset.univ.val.map (fun i => nbAt lines' z (e i)) := by
      congr 1
      funext i
      unfold nbAt
      rw [show (lines' z) (e i) = (lines z) i from (lines' z).apply_symm_apply _]
    _ = ((Finset.univ : Finset (Option (ZMod p))).map e.toEmbedding).val.map
        (nbAt lines' z) := by rw [Finset.map_val, Multiset.map_map]; rfl
    _ = _ := by rw [Finset.map_univ_equiv]

end Neighbours

section Level

variable (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3) (N : ℕ) (hN : 0 < N)
  (hcop : N.Coprime ell)

/-- The proved Atkin–Lehner permutation on double cosets, obtained by
undoing the transport to ideal classes in `Adelic.atkin`. -/
def atkinOnDoubleCosets (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p) :
    Equiv.Perm (DoubleCosets (levelOrder ell h N hN)) :=
  (classesEquiv _).symm.trans ((Adelic.atkin ell h N hN hcop p hp he).trans (classesEquiv _))

/-- The proved right division uniformizer on double cosets, obtained by
undoing the transport to ideal classes in `Adelic.uniformizer`. -/
def uniformizerOnDoubleCosets : Equiv.Perm (DoubleCosets (levelOrder ell h N hN)) :=
  (classesEquiv _).symm.trans ((Adelic.uniformizer ell h N hN).trans (classesEquiv _))

/-- **GLUE.** The class-set comparison on the coarse supersingular locus,
as used in Appendix F (tex 8465–8474). Cited as Jetchev–Kane §§1.1–1.2 and 2.5
(arXiv v1; journal version unread), whose standing hypothesis is `N ≥ 1` with
`ell` prime to `N`, and no squarefreeness. Ribet 1990 Prop. 3.3 reports it
without proof; a Lean proof is in progress. The source's order is the
endomorphism ring of a fixed enhanced curve, while this one is the explicit
`levelOrder`, and `ell % 4 = 3` narrows the source. The operator comparisons
are the separate `OperatorComparison`. -/
structure JetchevKane (hcop : N.Coprime ell) (X : CoarseFibre) where
  classes : DoubleCosets (levelOrder ell h N hN) ≃ X.ss

/-- **ELLIOT.** The geometric operators compared to the adelic ones through
the class-set comparison `J`: asserted in the manuscript; to be proved in Lean.
Hecke at tex 8480–8487, 9042 and 9067–9078; Atkin–Lehner at tex 8487–8489 and
9331–9341; Frobenius at tex 8489–8492 and 9343–9358. -/
structure OperatorComparison (hcop : N.Coprime ell) (X : CoarseFibre)
    (J : JetchevKane ell h N hN hcop X) : Prop where
  hecke : ∀ p (hp : p.Prime) (hgood : ¬ p ∣ N * ell) z,
    X.T p (J.classes z).val =
      ((Adelic.hecke ⟨p, hp⟩ (levelOrder_isEichler ell h N hN hcop) hgood z).map
        (fun w => of (J.classes w).val)).sum
  atkin : ∀ p (hp : p.Prime) (he : 0 < N.factorization p) z,
    X.W p (J.classes z).val = (J.classes (atkinOnDoubleCosets ell h N hN hcop p hp he z)).val
  frobenius : ∀ z, X.frobenius (J.classes z).val =
    (J.classes (uniformizerOnDoubleCosets ell h N hN z)).val

variable {ell h N hN hcop} {X : CoarseFibre} (J : JetchevKane ell h N hN hcop X)

namespace JetchevKane

/-- Compose the two class identifications to supply `GeometricInput.classes`. -/
def idealClasses : ClassSet (levelOrder ell h N hN) ≃ X.ss :=
  (classesEquiv _).trans J.classes

end JetchevKane

variable {J} (O : OperatorComparison ell h N hN hcop X J)

namespace OperatorComparison

include O in
/-- The good Hecke comparison for every actual line index (tex 8481–8487). -/
theorem hecke_compare (p : ℕ) (hp : p.Prime) (hgood : ¬ p ∣ N * ell)
    (lines : LineIndex (levelOrder ell h N hN) p hp.ne_zero) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ z, X.T p (J.idealClasses z).val = ∑ i, of (J.idealClasses (nbAt lines z i)).val := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  intro z
  let hE := levelOrder_isEichler ell h N hN hcop
  let c := classesEquiv (levelOrder ell h N hN)
  let f := fun w => of (J.idealClasses w).val
  have hm := Adelic.hecke_eq_neighbours ⟨p, hp⟩ hE hgood (c z)
  change (Adelic.hecke ⟨p, hp⟩ hE hgood (c z)).map c.symm =
    Finset.univ.val.map (nbAt (LineIndex.lineIndex hE hgood) (c.symm (c z))) at hm
  rw [c.symm_apply_apply, neighbourMultiset_eq _ lines z] at hm
  have hf : (fun w => of (J.classes w).val) = f ∘ c.symm := by
    funext w
    change of (J.classes w).val = of (J.classes (c (c.symm w))).val
    rw [c.apply_symm_apply]
  change X.T p (J.classes (c z)).val = (Finset.univ.val.map (f ∘ nbAt lines z)).sum
  rw [O.hecke p hp hgood (c z), hf, ← Multiset.map_map, hm, Multiset.map_map]

include O in
/-- Transport Atkin–Lehner back to ideal classes (tex 8487–8489, 9331–9339). -/
theorem atkin_compare (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p)
    (z : ClassSet (levelOrder ell h N hN)) :
    X.W p (J.idealClasses z).val =
      (J.idealClasses ((adelic ell h N hN hcop).atkin p hp he z)).val := by
  change X.W p (J.idealClasses z).val =
    (J.idealClasses (Adelic.atkin ell h N hN hcop p hp he z)).val
  simpa only [JetchevKane.idealClasses, atkinOnDoubleCosets, Equiv.trans_apply,
    Equiv.symm_apply_apply] using O.atkin p hp he (classesEquiv _ z)

include O in
/-- Transport the uniformizer comparison back to ideal classes (tex 8489–8490, 9347–9355). -/
theorem frobenius_compare (z : ClassSet (levelOrder ell h N hN)) :
    X.frobenius (J.idealClasses z).val =
      (J.idealClasses ((adelic ell h N hN hcop).uniformizer z)).val := by
  change X.frobenius (J.idealClasses z).val =
    (J.idealClasses (Adelic.uniformizer ell h N hN z)).val
  simpa only [JetchevKane.idealClasses, uniformizerOnDoubleCosets, Equiv.trans_apply,
    Equiv.symm_apply_apply] using O.frobenius (classesEquiv _ z)

include O in
/-- The comparison implies that Frobenius preserves the supersingular locus. -/
theorem frobenius_ss (x : X.Point) (hx : x ∈ X.ss) : X.frobenius x ∈ X.ss := by
  obtain ⟨z, hz⟩ := J.classes.surjective ⟨x, hx⟩
  have hz' : (J.classes z).val = x := congrArg Subtype.val hz
  rw [← hz', O.frobenius]
  exact (J.classes _).property

end OperatorComparison
end Level


end ZInQ.Manuscript.RC.PMAdelic
