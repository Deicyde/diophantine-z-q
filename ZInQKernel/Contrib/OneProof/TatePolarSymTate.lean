import ZInQKernel.Contrib.OneProof.TatePolarSymWeil
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Main
import ZInQKernel.Contrib.OneProof.DeRhamPrint

/-! From the finite-level polarization pairings to the rational Tate module. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open PkgI3 PkgI3.AbVar HDec.WeilPairing
open scoped CategoryTheory.MonObj TensorProduct

namespace HodgeFil1.TatePolar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000

section Integral

variable {K : Type} [Field K] [CharZero K] {A : AbVar K} (D : NativePolarization A)

open Classical in
/-- `e^λ_n` on all of `A(K̄)`, as a unit of `K̄` (junk value `1` off `A[n]`); a non-dependent
form used to pass to the limit. -/
def wv (n : ℕ) (x y : P A) : (AlgebraicClosure K)ˣ :=
  if h : n • x = 0 ∧ n • y = 0 then (D.weil n ⟨x, h.1⟩ (torsMap D.q n ⟨y, h.2⟩)).val else 1

variable {D}

lemma wv_eq {n : ℕ} {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D n x y = (D.weil n ⟨x, hx⟩ (torsMap D.q n ⟨y, hy⟩)).val := by
  classical
  exact dite_eq_left_of_eq_true (eq_true ⟨hx, hy⟩)

lemma wv_pow (n : ℕ) (x y : P A) : wv D n x y ^ n = 1 := by
  classical
  unfold wv
  split_ifs
  · exact val_pow_eq_one _ _ _
  · exact one_pow n

lemma wv_one (x y : P A) : wv D 1 x y = 1 := by
  simpa using wv_pow (D := D) 1 x y

lemma wv_add_left {n : ℕ} {x x' y : P A} (hx : n • x = 0) (hx' : n • x' = 0) (hy : n • y = 0) :
    wv D n (x + x') y = wv D n x y * wv D n x' y := by
  have hxx' : n • (x + x') = 0 := by rw [smul_add, hx, hx', add_zero]
  rw [wv_eq hxx' hy, wv_eq hx hy, wv_eq hx' hy]
  exact val_mul_left _ ⟨x, hx⟩ ⟨x', hx'⟩ _

lemma wv_add_right {n : ℕ} {x y y' : P A} (hx : n • x = 0) (hy : n • y = 0) (hy' : n • y' = 0) :
    wv D n x (y + y') = wv D n x y * wv D n x y' := by
  have hyy' : n • (y + y') = 0 := by rw [smul_add, hy, hy', add_zero]
  rw [wv_eq hx hyy', wv_eq hx hy, wv_eq hx hy']
  have he : (⟨y + y', hyy'⟩ : tors A n) = ⟨y, hy⟩ + ⟨y', hy'⟩ := rfl
  rw [he, map_add (torsMap D.q n), val_mul_right]

lemma wv_nsmul_left {n : ℕ} (c : ℕ) {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D n (c • x) y = wv D n x y ^ c := by
  have hcx : n • (c • x) = 0 := by rw [smul_comm, hx, smul_zero]
  rw [wv_eq hcx hy, wv_eq hx hy, ← Mu.val_nsmul, ← nsmul_left]
  rfl

lemma wv_nsmul_right {n : ℕ} (c : ℕ) {x y : P A} (hx : n • x = 0) (hy : n • y = 0) :
    wv D n x (c • y) = wv D n x y ^ c := by
  have hcy : n • (c • y) = 0 := by rw [smul_comm, hy, smul_zero]
  have he : (⟨c • y, hcy⟩ : tors A n) = c • (⟨y, hy⟩ : tors A n) := rfl
  rw [wv_eq hx hcy, wv_eq hx hy, he, map_nsmul (torsMap D.q n), nsmul_right, Mu.val_nsmul]

/-- Compatibility: `e^λ_n(m x, m y) = e^λ_{mn}(x, y)^m`. -/
lemma wv_compat {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x y : P A}
    (hx : (m * n) • x = 0) (hy : (m * n) • y = 0) :
    wv D n (m • x) (m • y) = wv D (m * n) x y ^ m := by
  have hmx : n • (m • x) = 0 := by rw [← mul_smul, mul_comm, hx]
  have hmy : n • (m • y) = 0 := by rw [← mul_smul, mul_comm, hy]
  have ex : (⟨m • x, hmx⟩ : tors A n) = torsSmul A m n ⟨x, hx⟩ := rfl
  have ey : torsIncl _ (dvd_mul_left n m) (torsMap D.q n ⟨m • y, hmy⟩) =
      m • torsMap D.q (m * n) ⟨y, hy⟩ := by
    apply Subtype.ext
    change homP D.q (m • y) = m • homP D.q y
    rw [map_nsmul]
  rw [wv_eq hmx hmy, wv_eq hx hy, ex, ← D.weil_compat hm hn, ey, nsmul_right, Mu.val_nsmul]

/-- `G_K`-equivariance: `e^λ_n(σx, σy) = σ(e^λ_n(x, y))`. -/
lemma wv_galois {n : ℕ} (hn : 0 < n) (σ : Gal K) {x y : P A}
    (hx : n • x = 0) (hy : n • y = 0) :
    wv D n (galP A σ x) (galP A σ y) =
      Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K) (wv D n x y) := by
  have hσx : n • galP A σ x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hσy : n • galP A σ y = 0 := by rw [← map_nsmul, hy, map_zero]
  have ex : (⟨galP A σ x, hσx⟩ : tors A n) = galTors A n σ ⟨x, hx⟩ := rfl
  have ey : (⟨galP A σ y, hσy⟩ : tors A n) = galTors A n σ ⟨y, hy⟩ := rfl
  rw [wv_eq hσx hσy, wv_eq hx hy, ex, ey, torsMap_galTors, D.weil_galois hn]
  rfl

variable (D)
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The components `e^λ_{ℓᵏ}(x_k, y_k)`. -/
def tateSeq (x y : A.T ℓ) : ℕ → Additive (AlgebraicClosure K)ˣ :=
  fun k => Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k))

variable {ℓ}

lemma tateSeq_mem (x y : A.T ℓ) : tateSeq D ℓ x y ∈ Tate.T ℓ _ := by
  refine ⟨?_, fun k => ?_⟩
  · change Additive.ofMul (wv D (ℓ ^ 0) _ _) = 0
    rw [pow_zero, wv_one]
    rfl
  · change Additive.ofMul (wv D (ℓ ^ (k + 1)) (x.1 (k + 1)) (y.1 (k + 1)) ^ ℓ) =
      Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k))
    congr 1
    have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
    have hx : (ℓ * ℓ ^ k) • x.1 (k + 1) = 0 := by rw [← pow_succ']; exact tors_pow ℓ (k + 1)
    have hy : (ℓ * ℓ ^ k) • y.1 (k + 1) = 0 := by rw [← pow_succ']; exact tors_pow ℓ (k + 1)
    rw [← x.2.2 k, ← y.2.2 k, wv_compat hl (pow_pos hl k) hx hy, pow_succ']

/-- **The `ℓ`-adic Weil pairing** `E^λ : T_ℓ A × T_ℓ A → T_ℓ(μ)`, `ℤ_ℓ`-bilinear, with
components `e^λ_{ℓᵏ}(x_k, y_k)`. -/
def tatePairing : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ →ₗ[ℤ_[ℓ]] TMu K ℓ :=
  LinearMap.mk₂ ℤ_[ℓ] (fun x y => ⟨tateSeq D ℓ x y, tateSeq_mem D x y⟩)
    (fun x x' y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D (ℓ ^ k) (x.1 k + x'.1 k) (y.1 k)) =
        Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k) * wv D (ℓ ^ k) (x'.1 k) (y.1 k))
      rw [wv_add_left (tors_pow ℓ k) (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun a x y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D (ℓ ^ k) ((PadicInt.toZModPow k a).val • x.1 k) (y.1 k)) =
        Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k) ^ (PadicInt.toZModPow k a).val)
      rw [wv_nsmul_left _ (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun x y y' => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k + y'.1 k)) =
        Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k) * wv D (ℓ ^ k) (x.1 k) (y'.1 k))
      rw [wv_add_right (tors_pow ℓ k) (tors_pow ℓ k) (tors_pow ℓ k)])
    (fun a x y => Subtype.ext <| funext fun k => by
      change Additive.ofMul (wv D (ℓ ^ k) (x.1 k) ((PadicInt.toZModPow k a).val • y.1 k)) =
        Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k) ^ (PadicInt.toZModPow k a).val)
      rw [wv_nsmul_right _ (tors_pow ℓ k) (tors_pow ℓ k)])

lemma tatePairing_apply (x y : A.T ℓ) (k : ℕ) :
    (tatePairing D x y).1 k = Additive.ofMul (wv D (ℓ ^ k) (x.1 k) (y.1 k)) := rfl

/-- `E^λ` is `G_K`-equivariant: `E^λ(σx, σy) = σ E^λ(x, y)`. -/
theorem tatePairing_galois (σ : Gal K) (x y : A.T ℓ) :
    tatePairing D (A.galT σ x) (A.galT σ y) = galTMu ℓ σ (tatePairing D x y) := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  apply Subtype.ext; funext k
  change Additive.ofMul (wv D (ℓ ^ k) (galP A σ (x.1 k)) (galP A σ (y.1 k))) =
    Additive.ofMul (Units.map (σ : AlgebraicClosure K →* AlgebraicClosure K)
      (wv D (ℓ ^ k) (x.1 k) (y.1 k)))
  rw [wv_galois (pow_pos hl k) σ (tors_pow ℓ k)
    (tors_pow ℓ k)]

/-- If the form pulled back along the isogeny vanishes at a torsion point,
the quasi-inverse exponent kills that point. -/
theorem torsion_radical_killed {n d : ℕ} (hn : 0 < n) {ψ : Hom D.Q A}
    (hψ : ∀ z : P D.Q, homP D.q (homP ψ z) = d • z)
    (x : tors A n) (hx : ∀ y, D.weil n x (torsMap D.q n y) = 0) : d • x = 0 := by
  apply (D.weil_perfect hn).1
  intro z
  have hz : torsMap D.q n (torsMap ψ n z) = d • z := Subtype.ext (hψ z)
  rw [nsmul_left, ← nsmul_right, ← hz, hx]

/-- The left radical vanishes in the Tate limit: a compatible tower killed by one
positive integer has all its components zero. -/
theorem tatePairing_left_ker (x : A.T ℓ) (hx : ∀ y, tatePairing D x y = 0) : x = 0 := by
  have hl : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have ht := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hsurj := T5Torsion.TateFree.tate_surj_of_torsionStructure (AvSplit.Final.h25 ht)
    K A ℓ (Nat.cast_ne_zero.mpr hl.ne')
  obtain ⟨d, hd, ψ, hψ, _⟩ :=
    (AvSplit.isogenyQuasiInverse_of_milne
      ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof) K A D.Q D.q D.isogeny
  have hdk : ∀ k, d • x.1 k = 0 := by
    intro k
    have h := torsion_radical_killed D (pow_pos hl k) hψ ⟨x.1 k, tors_pow ℓ k⟩ (fun t => by
      obtain ⟨y, hy⟩ := hsurj k t (nsmul_tors t)
      have h1 := congrArg (fun z : TMu K ℓ => z.1 k) (hx y)
      simp only [tatePairing_apply] at h1
      have h2 : wv D (ℓ ^ k) (x.1 k) (y.1 k) = 1 := Additive.ofMul.injective h1
      have h3 : (⟨y.1 k, tors_pow ℓ k⟩ : tors A (ℓ ^ k)) = t := Subtype.ext hy
      rw [wv_eq (tors_pow ℓ k) (tors_pow ℓ k), h3] at h2
      exact Mu.val_injective h2)
    exact congrArg Subtype.val h
  obtain ⟨a, d', hd', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' ℓ
    (Fact.out : ℓ.Prime).one_lt.ne'
  apply Subtype.ext; funext k
  have hcop : d'.Coprime (ℓ ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_comm.1 ((Fact.out : ℓ.Prime).coprime_iff_not_dvd.2 hd')))
  refine eq_zero_of_coprime hcop ?_ (tors_pow ℓ k)
  have h := hdk (k + a)
  rw [mul_comm, mul_smul, iterate_smul x.2.2 k a] at h
  exact h

include D in
/-- An integral form with values in the cyclotomic line, written in a choice of
generator of the Tate module of roots of unity. -/
theorem integral_form : ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧
    ∀ (σ : Gal K) (x y : A.T ℓ), B (A.galT σ x) (A.galT σ y) =
      (cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]) * B x y := by
  have : NeZero (ℓ : K) := ⟨Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨g, hg⟩ := exists_tmu_gen K ℓ
  refine ⟨(tatePairing D).compr₂ (tmuCoordLin hg), ?_, ?_⟩
  · intro x hx
    exact tatePairing_left_ker D x fun y => tmuCoordLin_injective hg (by rw [map_zero]; exact hx y)
  · intro σ x y
    simp only [LinearMap.compr₂_apply]
    rw [tatePairing_galois, galTMu_eq_cyclotomic, map_smul, smul_eq_mul]

end Integral

/-- Extending scalars from the Tate lattice gives a nondegenerate form with
the same cyclotomic multiplier. -/
theorem rational_form {K : Type} [Field K] [CharZero K] {A : AbVar K}
    (D : NativePolarization A) (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ), B.Nondegenerate ∧
      ∀ (σ : Gal K) (x y : A.V ℓ), B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
        ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]) : ℚ_[ℓ]) * B x y := by
  classical
  obtain ⟨B0, hsep, hmult⟩ := integral_form D (ℓ := ℓ)
  have ht := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  obtain ⟨hfree, hfinite, _⟩ := DeRhamPrint.tateModuleFree_of_mumford ht K A ℓ
    (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV : Module.Basis _ ℚ_[ℓ] (A.V ℓ) := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hnd0 : B0.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  have hdet0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd0
  set G := LinearMap.BilinForm.toMatrix b B0 with hG
  let φ := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  haveI : IsDomain ℚ_[ℓ] := Field.isDomain
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  set G' := G.map φ with hG'
  let B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) := Matrix.toBilin bV G'
  have hBG : LinearMap.BilinForm.toMatrix bV B = G' := LinearMap.BilinForm.toMatrix_toBilin _ _
  refine ⟨B, ?_, ?_⟩
  · rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV, hBG, hG',
      show G.map φ = φ.mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hdet0 (hφ (by rw [h, map_zero]))
  · intro σ
    set c0 := (cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ])
    have hc0 : B0.comp (A.galT σ) (A.galT σ) = c0 • B0 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      change B0 (A.galT σ x) (A.galT σ y) = c0 * B0 x y
      exact hmult σ x y
    set M := LinearMap.toMatrix b b (A.galT σ)
    have h1 := LinearMap.BilinForm.toMatrix_comp b b B0 (A.galT σ) (A.galT σ)
    rw [hc0, map_smul] at h1
    have hfM : LinearMap.toMatrix bV bV (A.galRep ℓ σ) = M.map φ :=
      LinearMap.toMatrix_baseChange ℚ_[ℓ] (A.galT σ) b b
    have hcomp : B.comp (A.galRep ℓ σ) (A.galRep ℓ σ) = (φ c0) • B := by
      apply (LinearMap.BilinForm.toMatrix bV).injective
      rw [LinearMap.BilinForm.toMatrix_comp bV bV, hfM, hBG, map_smul, hBG, hG']
      have h2 := congrArg (fun X => X.map φ) h1
      simp only [Matrix.map_mul, Matrix.transpose_map] at h2
      rw [← hG] at h2
      exact h2.symm
    intro x y
    have := congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x y) hcomp
    simpa [φ] using this

#print axioms wv_eq
#print axioms wv_pow
#print axioms wv_one
#print axioms wv_add_left
#print axioms wv_add_right
#print axioms wv_nsmul_left
#print axioms wv_nsmul_right
#print axioms wv_compat
#print axioms wv_galois
#print axioms tateSeq_mem
#print axioms tatePairing_apply
#print axioms tatePairing_galois
#print axioms torsion_radical_killed
#print axioms tatePairing_left_ker
#print axioms integral_form
#print axioms rational_form

end HodgeFil1.TatePolar
