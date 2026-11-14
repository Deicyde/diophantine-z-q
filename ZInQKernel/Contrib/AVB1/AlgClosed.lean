import ZInQKernel.Contrib.AVB1.BaseChange

/-!
# av-b1, II: T6 and T7 over any field from Mumford's statements over an algebraically closed field

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task av-b1, 2026-11-13).

Mumford, *Abelian varieties* (1970), works over an algebraically closed field throughout. The
kernel's leaves T6 (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3) and T7 (`PkgI3.CharPolyIndepOfEll`,
Mumford §19 Thm 4) are stated over an arbitrary field `k`. This file proves

* `homFreeFinite_of_algClosed : HomFreeFiniteAlgClosed → PkgI3.HomFreeFinite`
* `charPolyIndepOfEll_of_algClosed : CharPolyIndepOfEllAlgClosed → PkgI3.CharPolyIndepOfEll`

where the hypotheses are the same statements restricted to `[IsAlgClosed k]`, i.e. Mumford's
setting verbatim. The glue (base change to `K̄ = AlgebraicClosure k`) is in `BaseChange.lean`:
`Hom_k(A, B) ↪ Hom_{K̄}(A_{K̄}, B_{K̄})`, `T_ℓ(A) ≅ T_ℓ(A_{K̄})` naturally, `dim A_{K̄} = dim A`,
and `ℤ_ℓ` is flat over `ℤ`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open Polynomial

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AVB1

open ZInQ.Contrib.AbVarBC

/-- **T6 in Mumford's setting** (published theorem). D. Mumford, *Abelian varieties* (1970),
§19, Theorem 3 (UNVERIFIED locator; the ground field is algebraically closed throughout the book):
for abelian varieties `X, Y` over an algebraically closed field `k`, `Hom(X, Y)` is a free
`ℤ`-module of finite rank `≤ 4 dim X dim Y`, and for `ℓ ≠ char k` the natural map
`ℤ_ℓ ⊗ Hom(X, Y) → Hom_{ℤ_ℓ}(T_ℓ X, T_ℓ Y)` is injective. This is `PkgI3.HomFreeFinite` with
`[IsAlgClosed k]` added. -/
def HomFreeFiniteAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : _root_.PkgI3.AbVar k),
    Module.Free ℤ (_root_.PkgI3.AbVar.Hom A B) ∧ Module.Finite ℤ (_root_.PkgI3.AbVar.Hom A B) ∧
      ((Module.finrank ℤ (_root_.PkgI3.AbVar.Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
        Function.Injective (_root_.PkgI3.AbVar.tateHomZl ℓ A B)

/-- **T7 in Mumford's setting** (consequence of a published theorem). D. Mumford, *Abelian
varieties* (1970), §19, Theorem 4 (UNVERIFIED locator; `k` algebraically closed): for
`φ ∈ End(X)` the polynomial `P_φ(n) = deg(n - φ)` lies in `ℤ[X]`, is monic of degree `2g`, and is
the characteristic polynomial of `T_ℓ(φ)` for every `ℓ ≠ char k`. This is
`PkgI3.CharPolyIndepOfEll` with `[IsAlgClosed k]` added (it drops `deg P = 2g` and
`P(n) = deg(n - φ)`). -/
def CharPolyIndepOfEllAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : _root_.PkgI3.AbVar k)
    (φ : _root_.PkgI3.AbVar.End A), ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((_root_.PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

section Glue

variable {K : Type} [Field K]

theorem natCast_ne_zero_closure {ℓ : ℕ} (hℓ : (ℓ : K) ≠ 0) : (ℓ : AlgebraicClosure K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
  exact (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).mpr hℓ

/-- `tateHomZl` commutes with base change of homomorphisms and `tateBC`. -/
theorem tateHomZl_bc (A B : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (x : ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.Hom A B) (t : A.T ℓ) :
    _root_.PkgI3.AbVar.tateHomZl ℓ (A.baseChange (AlgebraicClosure K))
        (B.baseChange (AlgebraicClosure K))
        (LinearMap.lTensor ℤ_[ℓ] (bcHom (AlgebraicClosure K) A B).toIntLinearMap x)
        (tateBC A (κbar K) ℓ t) =
      tateBC B (κbar K) ℓ (_root_.PkgI3.AbVar.tateHomZl ℓ A B x t) := by
  induction x using TensorProduct.inductionOn with
  | tmul a f =>
    rw [LinearMap.lTensor_tmul]
    have e1 : _root_.PkgI3.AbVar.tateHomZl ℓ A B (a ⊗ₜ f) =
        a • _root_.PkgI3.AbVar.tateHom ℓ A B f := rfl
    have e2 : _root_.PkgI3.AbVar.tateHomZl ℓ (A.baseChange (AlgebraicClosure K))
        (B.baseChange (AlgebraicClosure K))
        (a ⊗ₜ (bcHom (AlgebraicClosure K) A B).toIntLinearMap f) =
        a • _root_.PkgI3.AbVar.tateHom ℓ _ _ (bcHom (AlgebraicClosure K) A B f) := rfl
    rw [e1, e2, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    change a • _root_.PkgI3.AbVar.homT (bcHom (AlgebraicClosure K) A B f) (tateBC A (κbar K) ℓ t) =
      a • tateBC B (κbar K) ℓ (_root_.PkgI3.AbVar.homT f t)
    rw [tateBC_homT]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- `ℤ_ℓ` is flat over `ℤ`. -/
theorem flat_int_padicInt (ℓ : ℕ) [Fact ℓ.Prime] : Module.Flat ℤ ℤ_[ℓ] := by
  haveI : Module.IsTorsionFree ℤ ℤ_[ℓ] :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 (algebraMap ℤ ℤ_[ℓ]).injective_int
  infer_instance

end Glue

/-- **T6 over any field from T6 over algebraically closed fields.** -/
theorem homFreeFinite_of_algClosed (h : HomFreeFiniteAlgClosed) : _root_.PkgI3.HomFreeFinite := by
  intro k _ A B
  obtain ⟨hfree, hfin, hrk, hinj⟩ :=
    h (AlgebraicClosure k) (A.baseChange (AlgebraicClosure k)) (B.baseChange (AlgebraicClosure k))
  set e := (bcHom (AlgebraicClosure k) A B).toIntLinearMap with he_def
  have he : Function.Injective e := bcHom_injective A B
  haveI : Module.Finite ℤ (_root_.PkgI3.AbVar.Hom A B) := Module.Finite.of_injective e he
  haveI : Module.IsTorsionFree ℤ (_root_.PkgI3.AbVar.Hom A B) :=
    Function.Injective.moduleIsTorsionFree e he (fun r m => map_zsmul e r m)
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · have h1 : Module.finrank ℤ (_root_.PkgI3.AbVar.Hom A B) ≤
        Module.finrank ℤ (_root_.PkgI3.AbVar.Hom (A.baseChange (AlgebraicClosure k))
          (B.baseChange (AlgebraicClosure k))) :=
      LinearMap.finrank_le_finrank_of_injective he
    rw [_root_.PkgI3.AbVar.dim_baseChange, _root_.PkgI3.AbVar.dim_baseChange] at hrk
    refine le_trans ?_ hrk
    exact_mod_cast h1
  · intro ℓ _ hℓ
    haveI := flat_int_padicInt ℓ
    have hinjL := hinj ℓ (natCast_ne_zero_closure hℓ)
    have hlt : Function.Injective (LinearMap.lTensor ℤ_[ℓ] e) :=
      Module.Flat.lTensor_preserves_injective_linearMap e he
    rw [← LinearMap.ker_eq_bot (f := _root_.PkgI3.AbVar.tateHomZl ℓ A B), LinearMap.ker_eq_bot']
    intro x hx
    apply hlt
    rw [map_zero]
    apply hinjL
    rw [map_zero]
    apply LinearMap.ext
    intro t'
    obtain ⟨t, rfl⟩ := (tateBC_bijective_closure A ℓ).2 t'
    rw [he_def, tateHomZl_bc, hx, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

/-- **T7 over any field from T7 over algebraically closed fields.** -/
theorem charPolyIndepOfEll_of_algClosed (h : CharPolyIndepOfEllAlgClosed) :
    _root_.PkgI3.CharPolyIndepOfEll := by
  intro k _ A φ
  obtain ⟨P, hP, hcp⟩ := h (AlgebraicClosure k) (A.baseChange (AlgebraicClosure k))
    (bcHom (AlgebraicClosure k) A A φ)
  refine ⟨P, hP, ?_⟩
  intro ℓ _ hℓ I _ _ b
  have hb := tateBC_bijective_closure A ℓ
  set eT := LinearEquiv.ofBijective (tateBC A (κbar k) ℓ) hb with heT
  set eV := eT.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ with heV
  -- `eV : V_ℓ(A) ≃ V_ℓ(A_{K̄})` intertwines `V(φ)` and `V(φ_{K̄})`.
  have hcomm : ∀ v : A.V ℓ,
      eV ((_root_.PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ] v) =
        (_root_.PkgI3.AbVar.homT (ℓ := ℓ) (bcHom (AlgebraicClosure k) A A φ)).baseChange ℚ_[ℓ]
          (eV v) := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul a t =>
      rw [LinearMap.baseChange_tmul, heV, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, heT,
        LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, tateBC_homT]
    | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]
  have key := hcp ℓ (natCast_ne_zero_closure hℓ) I (b.map eV)
  rw [← key]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_apply,
    Module.Basis.map_repr, LinearEquiv.trans_apply, ← hcomm, LinearEquiv.symm_apply_apply]
