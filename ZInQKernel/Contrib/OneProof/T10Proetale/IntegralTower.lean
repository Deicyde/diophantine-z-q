import ZInQKernel.Contrib.OneProof.T10Proetale.CountableLocalLifts
import ZInQKernel.Contrib.OneProof.T10Proetale.CohomologyLimit

/-!
# Integral degree one and the finite pro-étale tower

The product epimorphism needed for the residue tower follows from countable
local lifting on the actual site. The underlying cohomology groups are those
of the unchanged Tate-duality row.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable (X : Scheme.{0}) (ℓ : ℕ)

/-- The actual product of the residue sheaves' injective-presentation quotients is epi. -/
theorem residueQuotientProduct_epi :
    Epi (Limits.Pi.map fun n => (injectivePresentation (residueSheaf X ℓ n)).g) :=
  proProduct_epi (fun n => (injectivePresentation (residueSheaf X ℓ n)).g)

variable [Fact ℓ.Prime]

/-- The compatible families in the degree-one finite pro-étale groups. -/
def proFiniteH1Limit : AddSubgroup (∀ n, ProFiniteH X ℓ n 1) where
  carrier := {s | ∀ n, proTransition X ℓ n 1 (s (n + 1)) = s n}
  zero_mem' n := map_zero (proTransition X ℓ n 1)
  add_mem' ha hb n := by simp [ha n, hb n]
  neg_mem' ha n := by simp [ha n]

/-- Each compatible finite family has a unique integral degree-one lift. -/
theorem proReduction_existsUnique (s : proFiniteH1Limit X ℓ) :
    ∃! a : X.EllAdicCohomology ℓ 1, ∀ n, proReduction X ℓ n 1 a = s.val n :=
  proReduction_existsUnique_of_compatible X ℓ (residueQuotientProduct_epi X ℓ) s.val s.property

private def reductionToLimit : X.EllAdicCohomology ℓ 1 →+ proFiniteH1Limit X ℓ where
  toFun a := ⟨fun n => proReduction X ℓ n 1 a, fun n => proReduction_transition X ℓ n 1 a⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (proReduction X ℓ n 1))
  map_add' a b := Subtype.ext (funext fun n => map_add (proReduction X ℓ n 1) a b)

/-- The canonical additive identification of integral degree one with the inverse
limit of finite degree-one pro-étale cohomology, via its original reductions. -/
def proReductionEquiv : X.EllAdicCohomology ℓ 1 ≃+ proFiniteH1Limit X ℓ :=
  AddEquiv.ofBijective (reductionToLimit X ℓ) ⟨
    fun a b h => proReduction_injective X ℓ a b (fun n => congrArg (fun z => z.val n) h),
    fun s => let ⟨a, ha, _⟩ := proReduction_existsUnique X ℓ s
      ⟨a, Subtype.ext (funext ha)⟩⟩

@[simp]
theorem proReductionEquiv_apply (a : X.EllAdicCohomology ℓ 1) (n : ℕ) :
    (proReductionEquiv X ℓ a).val n = proReduction X ℓ n 1 a :=
  rfl

end
end ZInQ.Manuscript.T10Proetale
