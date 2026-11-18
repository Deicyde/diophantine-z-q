import ZInQKernel.Contrib.CloudB3RC53.ResidualTransfer.TransferFinal
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.NonVacuity

/-!
# RC53 ResidualTransfer: non-vacuity of the hypotheses of `transfer_final`

Lesson-2 check for the corrected `transfer_final` (tex L4598–4647): its hypotheses are jointly
satisfiable. Over the local ring `ℚ`, the zero Selmer data with the trivial support change
(`SelmerDuality.zeroSupportChange`, `zeroSupportChangeUnramified`), the full condition equal to the
zero complex, the zero singular quotient, and the zero minimal model satisfy every hypothesis:
`transfer_final_nonvacuous` applies `transfer_final` to them. (The data are degenerate; the check is
that the fields of the model structures and the remaining hypotheses do not contradict each other.)

Classification: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ResidualTransfer

open CategoryTheory CategoryTheory.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- Two relation-indexed chain maps between complexes with subsingleton targets are equal. -/
theorem ghom_eq_of_subsingleton {S : Type} [CommRing S] {A B : GCx S}
    [∀ n, Subsingleton (B.X n)] (φ ψ : GHom A B) : φ = ψ := by
  obtain ⟨f₁, c₁⟩ := φ
  obtain ⟨f₂, c₂⟩ := ψ
  have : f₁ = f₂ := by
    funext i j h
    ext x
    exact Subsingleton.elim _ _
  subst this
  rfl

instance zeroSelCx_subsingleton (n : ℤ) : Subsingleton ((selCx (zeroSel ℚ)).toCC.X n) := by
  change Subsingleton ((zeroCx ℚ).X n × (zeroCx ℚ).X n × (zeroCx ℚ).X (n - 1))
  infer_instance

instance zeroCxCC_subsingleton (n : ℤ) : Subsingleton ((zeroCx ℚ).toCC.X n) := by
  change Subsingleton ((zeroCx ℚ).X n)
  infer_instance

theorem id_eq_zero_of_subsingleton (K : CochainComplex (ModuleCat.{0} ℚ) ℤ)
    [∀ n, Subsingleton (K.X n)] : 𝟙 K = 0 := by
  ext n x
  exact Subsingleton.elim _ _

theorem isStrictlyGE_of_subsingleton (K : CochainComplex (ModuleCat.{0} ℚ) ℤ)
    [∀ n, Subsingleton (K.X n)] (a : ℤ) : K.IsStrictlyGE a :=
  ⟨fun n _ => ModuleCat.isZero_of_subsingleton _⟩

theorem isStrictlyLE_of_subsingleton (K : CochainComplex (ModuleCat.{0} ℚ) ℤ)
    [∀ n, Subsingleton (K.X n)] (b : ℤ) : K.IsStrictlyLE b :=
  ⟨fun n _ => ModuleCat.isZero_of_subsingleton _⟩

theorem acyclic_of_subsingleton (K : CochainComplex (ModuleCat.{0} ℚ) ℤ)
    [∀ n, Subsingleton (K.X n)] : K.Acyclic := fun i => by
  have : Subsingleton ((K.sc i).X₂) := inferInstanceAs (Subsingleton (K.X i))
  exact (K.sc i).exact_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton _)

/-- The trivial support change on zero data: the support comparison is the identity. -/
theorem zeroSupportChangeInput :
    SupportChangeInput (zeroSupportChange ℚ) (zeroSupportChangeUnramified ℚ) := by
  have h : GHom.toCC (supportMap (zeroSupportChange ℚ)) = 𝟙 _ := by
    ext n x
    exact Subsingleton.elim _ _
  change QuasiIso (GHom.toCC (supportMap (zeroSupportChange ℚ)))
  rw [h]
  infer_instance

theorem zeroSel_eq_restrict :
    (zeroSupportChange ℚ).Dp = restrictData (zeroSel ℚ) (zeroHom ℚ (zeroCx ℚ) (zeroCx ℚ)) := by
  change (⟨zeroCx ℚ, zeroCx ℚ, zeroCx ℚ, zeroHom ℚ _ _, zeroHom ℚ _ _⟩ : SelData ℚ) =
    ⟨zeroCx ℚ, zeroCx ℚ, zeroCx ℚ, zeroHom ℚ _ _, ghomComp (zeroHom ℚ _ _) (zeroHom ℚ _ _)⟩
  rw [ghom_eq_of_subsingleton (ghomComp (zeroHom ℚ (zeroCx ℚ) (zeroCx ℚ))
    (zeroHom ℚ (zeroCx ℚ) (zeroCx ℚ))) (zeroHom ℚ _ _)]

/-- **Non-vacuity of the corrected `transfer_final`** (Lesson 2): all its hypotheses hold for the
zero data over `ℚ` (support comparison of zero Selmer data, full condition and singular quotient
zero, minimal model zero), so `transfer_final` applies. PROVED. -/
theorem transfer_final_nonvacuous : (0 : ℕ) ≤ 0 := by
  have hr : ∀ n, Subsingleton
      ((selCx (restrictData (zeroSel ℚ) (zeroHom ℚ (zeroCx ℚ) (zeroCx ℚ)))).toCC.X n) := fun n => by
    change Subsingleton ((zeroCx ℚ).X n × (zeroCx ℚ).X n × (zeroCx ℚ).X (n - 1))
    infer_instance
  have := isStrictlyGE_of_subsingleton
    (selCx (restrictData (zeroSel ℚ) (zeroHom ℚ (zeroCx ℚ) (zeroCx ℚ)))).toCC 0
  have := isStrictlyLE_of_subsingleton
    (selCx (restrictData (zeroSel ℚ) (zeroHom ℚ (zeroCx ℚ) (zeroCx ℚ)))).toCC 0
  have := isStrictlyGE_of_subsingleton (selCx (zeroSel ℚ)).toCC 0
  have := isStrictlyLE_of_subsingleton (selCx (zeroSel ℚ)).toCC 0
  have := isStrictlyGE_of_subsingleton (zeroCx ℚ).toCC 0
  have := isStrictlyLE_of_subsingleton (zeroCx ℚ).toCC 0
  have hL : HomotopyEquiv (zeroCx ℚ).toCC (selCx (zeroSel ℚ)).toCC :=
    homotopyEquivOfContractible (Homotopy.ofEq (id_eq_zero_of_subsingleton _))
      (Homotopy.ofEq (id_eq_zero_of_subsingleton _))
  have hmin : ∀ i j (x : (zeroCx ℚ).toCC.X i), ((zeroCx ℚ).toCC.d i j).hom x ∈
      IsLocalRing.maximalIdeal ℚ • (⊤ : Submodule ℚ ((zeroCx ℚ).toCC.X j)) := by
    intro i j x
    have : ((zeroCx ℚ).toCC.d i j).hom x = 0 := Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _
  exact transfer_final (zeroSupportChange ℚ) (zeroSupportChangeUnramified ℚ)
    zeroSupportChangeInput 0 0 (zeroSel ℚ) (zeroCx ℚ) (zeroHom ℚ _ _) (zeroHom ℚ _ _)
    zeroSel_eq_restrict (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _) (fun _ _ => ⟨0, Subsingleton.elim _ _⟩)
    (fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩) (acyclic_of_subsingleton _)
    (zeroCx ℚ).toCC hmin hL ∅ 0 0 (by simp) (by simp)

end ZInQ.Contrib.CloudB3RC53.ResidualTransfer
