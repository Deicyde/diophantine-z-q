import ZInQKernel.Contrib.OneProof.DirectWeil.FiniteWeilPairing

noncomputable section

open CategoryTheory AlgebraicGeometry
open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

variable {K : Type} [Field K] (A : AbVar K) (L : A.X.left.Pic) {ℓ : ℕ} [Fact ℓ.Prime]
variable (hℓ : (ℓ : K) ≠ 0)

def levelPairing (k : ℕ) : Pairing A A (ℓ ^ k) :=
  finitePairing A L (pow_pos (Fact.out : ℓ.Prime).pos k)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ)

abbrev levelPoint (x : A.T ℓ) (k : ℕ) : tors A (ℓ ^ k) := ⟨x.1 k, tors_pow ℓ k⟩

def tateSeq (x y : A.T ℓ) (k : ℕ) : Additive (AlgebraicClosure K)ˣ :=
  Additive.ofMul ((levelPairing A L hℓ k (levelPoint A x k) (levelPoint A y k)).val)

theorem tateSeq_mem (x y : A.T ℓ) : tateSeq A L hℓ x y ∈ Tate.T ℓ _ := by
  refine ⟨?_, fun k => ?_⟩
  · unfold tateSeq
    have hx : levelPoint A x 0 = 0 := Subtype.ext x.2.1
    rw [hx, map_zero, AddMonoidHom.zero_apply, Mu.val_zero]
    rfl
  · have hm : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    have hn : 0 < ℓ ^ k := pow_pos hm k
    have hchar : ((ℓ * ℓ ^ k : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_mul, Nat.cast_pow]
      exact mul_ne_zero hℓ (pow_ne_zero _ hℓ)
    have hnchar : ((ℓ ^ k : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ hℓ
    have hx : (ℓ * ℓ ^ k) • x.1 (k + 1) = 0 := by
      rw [← pow_succ']
      exact tors_pow ℓ (k + 1)
    have hy : (ℓ * ℓ ^ k) • y.1 (k + 1) = 0 := by
      rw [← pow_succ']
      exact tors_pow ℓ (k + 1)
    have hx' : torsSmul A ℓ (ℓ ^ k) ⟨x.1 (k + 1), hx⟩ = levelPoint A x k :=
      Subtype.ext (x.2.2 k)
    have hy' : torsSmul A ℓ (ℓ ^ k) ⟨y.1 (k + 1), hy⟩ = levelPoint A y k :=
      Subtype.ext (y.2.2 k)
    have h := value_transition A L hm hn hchar hnchar ⟨x.1 (k + 1), hx⟩ ⟨y.1 (k + 1), hy⟩
    rw [hx', hy'] at h
    have upper {s : ℕ} (hs : ℓ ^ (k + 1) = s) (hp : 0 < s) (hc : (s : K) ≠ 0)
        (hx : s • x.1 (k + 1) = 0) (hy : s • y.1 (k + 1) = 0) :
        value A L hp hc ⟨x.1 (k + 1), hx⟩ ⟨y.1 (k + 1), hy⟩ =
          (levelPairing A L hℓ (k + 1) (levelPoint A x (k + 1)) (levelPoint A y (k + 1))).val := by
      subst s
      rfl
    rw [upper (pow_succ' ℓ k) _ _ hx hy] at h
    exact congrArg Additive.ofMul h.symm

/-- The compatible finite-level Weil pairings define a bilinear pairing into the Tate twist. -/
def tatePairing : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ →ₗ[ℤ_[ℓ]] TMu K ℓ :=
  LinearMap.mk₂ ℤ_[ℓ] (fun x y => ⟨tateSeq A L hℓ x y, tateSeq_mem A L hℓ x y⟩)
    (fun x x' y => Subtype.ext <| funext fun k => by
      have h : levelPoint A (x + x') k = levelPoint A x k + levelPoint A x' k := rfl
      change tateSeq A L hℓ (x + x') y k = tateSeq A L hℓ x y k + tateSeq A L hℓ x' y k
      simp only [tateSeq, h, map_add, AddMonoidHom.add_apply, Mu.val_add]
      rfl)
    (fun a x y => Subtype.ext <| funext fun k => by
      let j := (PadicInt.toZModPow k a).val
      have h : levelPoint A (a • x) k = j • levelPoint A x k := rfl
      change tateSeq A L hℓ (a • x) y k = j • tateSeq A L hℓ x y k
      simp only [tateSeq, h, map_nsmul, AddMonoidHom.nsmul_apply, Mu.val_nsmul]
      rfl)
    (fun x y y' => Subtype.ext <| funext fun k => by
      have h : levelPoint A (y + y') k = levelPoint A y k + levelPoint A y' k := rfl
      change tateSeq A L hℓ x (y + y') k = tateSeq A L hℓ x y k + tateSeq A L hℓ x y' k
      simp only [tateSeq, h, map_add, Mu.val_add]
      rfl)
    (fun a x y => Subtype.ext <| funext fun k => by
      let j := (PadicInt.toZModPow k a).val
      have h : levelPoint A (a • y) k = j • levelPoint A y k := rfl
      change tateSeq A L hℓ x (a • y) k = j • tateSeq A L hℓ x y k
      simp only [tateSeq, h, map_nsmul, Mu.val_nsmul]
      rfl)

theorem tatePairing_apply (x y : A.T ℓ) (k : ℕ) :
    (tatePairing A L hℓ x y).1 k = tateSeq A L hℓ x y k := rfl

theorem tatePairing_self (x : A.T ℓ) : tatePairing A L hℓ x x = 0 := by
  apply Subtype.ext
  funext k
  rw [tatePairing_apply, tateSeq, levelPairing, finitePairing_self, Mu.val_zero]
  rfl

theorem tatePairing_gal (σ : Gal K) (x y : A.T ℓ) :
    tatePairing A L hℓ (A.galT σ x) (A.galT σ y) = galTMu ℓ σ (tatePairing A L hℓ x y) := by
  apply Subtype.ext
  funext k
  have hx : levelPoint A (A.galT σ x) k = galTors A (ℓ ^ k) σ (levelPoint A x k) := rfl
  have hy : levelPoint A (A.galT σ y) k = galTors A (ℓ ^ k) σ (levelPoint A y k) := rfl
  rw [tatePairing_apply, tateSeq, hx, hy, levelPairing, finitePairing_gal]
  rfl

theorem tatePairing_cyclotomic (σ : Gal K) (x y : A.T ℓ) :
    tatePairing A L hℓ (A.galT σ x) (A.galT σ y) =
      ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) •
        tatePairing A L hℓ x y := by
  let : NeZero (ℓ : K) := ⟨hℓ⟩
  rw [tatePairing_gal, galTMu_eq_cyclotomic]

include hℓ in
theorem levelPoint_surjective (k : ℕ) : Function.Surjective (fun x : A.T ℓ => levelPoint A x k) := by
  have hd (z : P A) : ∃ w : P A, ℓ • w = z := by
    obtain ⟨p, hp⟩ := WeilProof.Theta.divisibleAC (AlgebraicClosure K) (AKbar A) ℓ
      (Fact.out : ℓ.Prime).pos (natCast_ne_zero_bar hℓ) (pts (Additive.toMul z))
    obtain ⟨w, rfl⟩ := pts_surjective p
    refine ⟨Additive.ofMul w, ?_⟩
    apply Additive.toMul.injective
    apply pts_injective
    rw [toMul_nsmul, toMul_ofMul, pts_pow, hp]
  intro z
  obtain ⟨x, hx⟩ := tate_surj hd k (z : P A) (nsmul_tors z)
  exact ⟨x, Subtype.ext hx⟩

end PicDict.DirectPairing
