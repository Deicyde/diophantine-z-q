import ZInQKernel.Contrib.OneProof.IgusaGL2DSGal

/-! # igusa-gal: the one-basis form of Diamond–Shurman Thm 7.6.3 implies `IgusaGL2DSGal`

Task igusa-gal (2026-11-17), report `docs/research/igusa-gal.md`. Diamond–Shurman define `ρ` in one ordered basis
`(P_τ, Q_τ)` of `E_j[N]` ((7.11), analytic). `IgusaGL2DSGalSome` states the theorem for some basis; every basis
follows by conjugation in `GL₂(ℤ/N)` (`igusaGL2DSGal_of_some`; additive automorphisms of `(ℤ/N)²` are matrices,
`glOf`). An alternative leaf, closer to the print, for the field `igusaGL2DS`
(`igusaGL2DS_of_igusaGL2DSGalSome`). No `sorry`, no `axiom`, no build-time code. -/
noncomputable section

namespace X1Igusa

open WeierstrassCurve LeafModCurves ZInQ.RLeaf X1Belyi

/-- The matrix of an additive endomorphism of `(ℤ/N)²` (columns: the images of the standard basis). -/
def matOf {N : ℕ} (f : ZMod N × ZMod N →+ ZMod N × ZMod N) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  !![(f (1, 0)).1, (f (0, 1)).1; (f (1, 0)).2, (f (0, 1)).2]

theorem matAct_matOf {N : ℕ} (f : ZMod N × ZMod N →+ ZMod N × ZMod N) (v : ZMod N × ZMod N) :
    matAct (matOf f) v = f v := by
  have hv : v = v.1 • ((1 : ZMod N), (0 : ZMod N)) + v.2 • ((0 : ZMod N), (1 : ZMod N)) := by
    ext <;> simp
  let fl := f.toZModLinearMap N
  have h : f v = v.1 • f (1, 0) + v.2 • f (0, 1) := by
    change fl v = v.1 • fl (1, 0) + v.2 • fl (0, 1)
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  rw [h]
  ext <;> simp [matAct, matOf, mul_comm]

theorem matAct_mul {N : ℕ} (M M' : Matrix (Fin 2) (Fin 2) (ZMod N)) (v : ZMod N × ZMod N) :
    matAct (M * M') v = matAct M (matAct M' v) := by
  ext <;> simp [matAct, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem matAct_one {N : ℕ} (v : ZMod N × ZMod N) : matAct (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) v = v := by
  ext <;> simp [matAct]

theorem matAct_injective {N : ℕ} {M M' : Matrix (Fin 2) (Fin 2) (ZMod N)}
    (h : ∀ v, matAct M v = matAct M' v) : M = M' := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  simp only [matAct, mul_one, mul_zero, add_zero, zero_add, Prod.mk.injEq] at h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2]

/-- An additive automorphism of `(ℤ/N)²` as an element of `GL₂(ℤ/N)`. -/
def glOf {N : ℕ} (A : ZMod N × ZMod N ≃+ ZMod N × ZMod N) : GL (Fin 2) (ZMod N) where
  val := matOf A.toAddMonoidHom
  inv := matOf A.symm.toAddMonoidHom
  val_inv := matAct_injective fun v => by
    rw [matAct_mul, matAct_matOf, matAct_matOf, matAct_one]; exact A.apply_symm_apply v
  inv_val := matAct_injective fun v => by
    rw [matAct_mul, matAct_matOf, matAct_matOf, matAct_one]; exact A.symm_apply_apply v

theorem matAct_glOf {N : ℕ} (A : ZMod N × ZMod N ≃+ ZMod N × ZMod N) (v : ZMod N × ZMod N) :
    matAct ((glOf A : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) v = A v :=
  matAct_matOf _ v

theorem matAct_glOf_inv {N : ℕ} (A : ZMod N × ZMod N ≃+ ZMod N × ZMod N) (v : ZMod N × ZMod N) :
    matAct (((glOf A)⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) v = A.symm v :=
  matAct_matOf _ v

/-- **LEAF (Diamond–Shurman, GTM 228, Theorem 7.6.3, first part, in the print's one-basis form; printed form).**
As `IgusaGL2DSGal`, for one basis `e` of `E_j[N]` instead of every basis: for `N > 1` there is a basis
`e : (ℤ/N)² ≃ E_j[N]` such that every `g ∈ GL₂(ℤ/N)` is the action of some `σ₀ ∈ Gal(ℚ(j, E_j[N])/ℚ(j))` in the
basis `e`. The print's basis is `(P_τ, Q_τ)` of (7.11) (analytic); its `ρ`, defined by
`(P^σ, Q^σ)ᵀ = ρ(σ)(P, Q)ᵀ` (§7.6, as in Cor. 7.5.3), is onto `GL₂(ℤ/N)` (Thm 7.6.3), so in the
column convention `σ(e v) = e(ρ(σ)ᵀ v)` used here every `g = ρ(σ)ᵀ` occurs. `N > 1` is the
standing assumption of §7.5. Locators AI-read (igusa-gal); no human reading. -/
def IgusaGL2DSGalSome : Prop :=
  ∀ N : ℕ, 1 < N → ∃ e : (ZMod N × ZMod N) ≃+ nTors EDSBar N, ∀ g : GL (Fin 2) (ZMod N),
    ∃ σ₀ : LDS N ≃ₐ[Qj] LDS N, ∀ (v : ZMod N × ZMod N) (P : (EDS.baseChange (LDS N)).toAffine.Point),
      incDS N P = (e v : EDSBar.toAffine.Point) →
        incDS N (galPtL σ₀ P) = (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) : EDSBar.toAffine.Point)

/-- One basis gives every basis (conjugation in `GL₂(ℤ/N)`). -/
theorem igusaGL2DSGal_of_some (h : IgusaGL2DSGalSome) : IgusaGL2DSGal := by
  intro N hN e g
  obtain ⟨e₀, he₀⟩ := h N hN
  let A : ZMod N × ZMod N ≃+ ZMod N × ZMod N := e.trans e₀.symm
  obtain ⟨σ₀, hσ₀⟩ := he₀ (glOf A * g * (glOf A)⁻¹)
  refine ⟨σ₀, fun v P hP => ?_⟩
  have hA : ∀ w, e w = e₀ (A w) := fun w => by simp [A]
  rw [hA] at hP ⊢
  rw [hσ₀ (A v) P hP]
  congr 3
  rw [Units.val_mul, Units.val_mul, matAct_mul, matAct_mul, matAct_glOf_inv, matAct_glOf]
  simp [A]


/-- `IgusaGL2DSGalSome → IgusaGL2DS`. -/
theorem igusaGL2DS_of_igusaGL2DSGalSome (h : IgusaGL2DSGalSome) : IgusaGL2DS :=
  igusaGL2DS_of_igusaGL2DSGal (igusaGL2DSGal_of_some h)

end X1Igusa
