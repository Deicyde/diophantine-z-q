import ZInQKernel.Contrib.OneProof.CarayolRefold
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# Darmon–Diamond–Taylor's Theorem 3.1 for newforms in the sense of their Definition 1.21

`CarayolDDT.CarayolDDT31` transcribes Darmon–Diamond–Taylor, *Fermat's Last Theorem* (1997), Theorem 3.1
(a)–(d), in weight 2, for Tau Ceti's `Newform N 2`: a normalized cusp form in the new subspace that is an
eigenvector of the Hecke operators of index coprime to the level only. Theorem 3.1 is stated for newforms in
the sense of DDT's Definition 1.21: normalized eigenforms of all the Hecke operators, lying in the new
subspace. Matching `CarayolDDT31` to the print therefore needed the promotion of a Tau Ceti newform to a
full eigenform (cited as DDT's Theorem 1.22); that step is proved in Lean
(`HeckeRing.GL2.Newform.toEigenform`). This file

* defines `IsDDTNewform F ψ`, that reading of Definition 1.21 in weight 2, over Tau Ceti's full Hecke
  eigenforms `HeckeRing.GL2.Eigenform` (eigenvector of `T_n` at every `n ≥ 1`, the indices sharing a prime
  with the level included);
* states `CarayolDDT31Full`: the body of `CarayolDDT31` verbatim, quantified over the DDT newforms
  `(F, ψ)` instead of over `f : Newform N 2` (`f.toCuspForm` becomes `F`, `f.χ` becomes `ψ`);
* proves `carayolDDT31_of_full : CarayolDDT31Full → CarayolDDT31`: a Tau Ceti newform is a DDT newform
  (`isDDTNewform_of_newform`), because Tau Ceti proves it is an eigenvector of every `T_n`
  (`HeckeRing.GL2.Newform.toEigenform`; Diamond–Shurman Theorem 5.8.2, Miyake Theorem 4.6.13, as cited
  there). The converse `carayolDDT31Full_of_DDT31` holds as well (a full eigenform is an eigenform away from
  the level), so the two leaves are equivalent (`carayolDDT31Full_iff`);
* proves `carayolThmAFrob_of_DDT31Full : CarayolDDT31Full → CarayolRefold.CarayolThmAFrob`.

No `sorry`, no `axiom`.
-/

namespace CarayolDDT

open PkgI4 LadicCond

section Leaf

open HeckeRing.GL2 NumberField IsDedekindDomain

/-- **Newform in the sense of Darmon–Diamond–Taylor, Definition 1.21 (weight 2), as read here.** A cusp
form `F ∈ S₂(Γ₁(N))` with nebentypus `ψ` is a newform if it is a normalized eigenform of all the Hecke
operators lying in the new subspace:

* `F` is a Hecke eigenform with nebentypus `ψ`: it underlies a Tau Ceti full Hecke eigenform
  `HeckeRing.GL2.Eigenform N 2` with character `ψ`. That is, `F ≠ 0`; `F ∈ S₂(N, ψ)`, i.e. `F` is an
  eigenvector of every diamond operator `⟨d⟩`, with eigenvalue `ψ(d)`; and `F` is an eigenvector of the
  Hecke operator `T_n` for every `n ≥ 1` (`heckeTCompositeGamma0 N n` acting on `S₂(N, ψ)`), the indices
  sharing a prime with `N` included (at a prime `p ∣ N`, `T_p` is `U_p`);
* `F` lies in the new subspace `S₂(Γ₁(N))ⁿᵉʷ`, the Petersson-orthogonal complement of the old subspace
  (`TauCeti.cuspFormsNew`);
* `F` is normalized: `a₁(F) = 1`.

Tau Ceti's `Newform N 2` demands eigen-ness only at the indices coprime to `N`; that such a form is an
eigenvector of every `T_n` is a theorem there (`HeckeRing.GL2.Newform.toEigenform`), so Tau Ceti's newforms
are DDT newforms (`isDDTNewform_of_newform`). Equivalently, `F` is a normalized eigenform in the sense of
`DSCoeffExt.IsNormalizedEigenformDS` lying in the new subspace (`isDDTNewform_iff_DS`). -/
def IsDDTNewform {N : ℕ} [NeZero N] (F : CF N 2) (ψ : (ZMod N)ˣ →* ℂˣ) : Prop :=
  ∃ f : Eigenform N 2, f.toCuspForm = F ∧ f.χ = ψ ∧ F ∈ TauCeti.cuspFormsNew N 2 ∧ coeff F 1 = 1

/-- `IsDDTNewform` through the project's Diamond–Shurman normalized eigenforms
(`DSCoeffExt.IsNormalizedEigenformDS`, nebentypus as a Dirichlet character): a DDT newform is a normalized
eigenform of every `T_n` lying in the new subspace. -/
theorem isDDTNewform_iff_DS {N : ℕ} [NeZero N] {F : CF N 2} {ψ : (ZMod N)ˣ →* ℂˣ} :
    IsDDTNewform F ψ ↔
      DSCoeffExt.IsNormalizedEigenformDS F (MulChar.ofUnitHom ψ) ∧ F ∈ TauCeti.cuspFormsNew N 2 := by
  have e : MulChar.toUnitHom (MulChar.ofUnitHom ψ : DirichletCharacter ℂ N) = ψ :=
    MulChar.equivToUnitHom.apply_symm_apply ψ
  constructor
  · rintro ⟨f, hf, hψ, hnew, h1⟩
    exact ⟨⟨f, hf, hψ.trans e.symm, h1⟩, hnew⟩
  · rintro ⟨⟨f, hf, hψ, h1⟩, hnew⟩
    exact ⟨f, hf, hψ.trans e, hnew, h1⟩

/-- **A Tau Ceti newform is a DDT newform**, with the same form and character: Tau Ceti's
`Newform.toEigenform` makes it an eigenvector of `T_n` at every `n ≥ 1`, the indices sharing a prime with
the level included, and it is new and normalized. -/
theorem isDDTNewform_of_newform {N : ℕ} [NeZero N] (f : Newform N 2) :
    IsDDTNewform (f.toCuspForm : CF N 2) f.χ :=
  ⟨f.toEigenform, f.toEigenform_toCuspForm, f.toEigenform_χ, f.isNew, f.isNorm⟩

/-- **LEAF (published, printed form): Darmon–Diamond–Taylor, *Fermat's Last Theorem* (1997), Theorem 3.1
(a)–(d) (heading p. 85, clauses p. 86 of the authors' copy), for newforms in the sense of Definition 1.21,
weight 2.**

This is `CarayolDDT31` with DDT's definition of newform. It quantifies over a cusp form `F ∈ S₂(Γ₁(N))` and
a character `ψ : (ℤ/N)ˣ → ℂˣ` with `IsDDTNewform F ψ` (a normalized eigenform of every Hecke operator `T_n`,
`n ≥ 1`, with nebentypus `ψ`, in the new subspace) instead of over Tau Ceti's `f : Newform N 2`. The body is
that of `CarayolDDT31` verbatim, with `f.toCuspForm` replaced by `F` and `f.χ` by `ψ`: if the coefficient
field `K_F = ℚ(a_n(F)) ⊆ ℂ` is a number field, then for a prime `ℓ` and a place `λ ∣ ℓ` of `K_F` there is a
continuous `ρ = ρ_{F,λ} : G_ℚ → GL₂(K_{F,λ})` that is absolutely irreducible, has `det ρ = ψ·χ_ℓ`, is
unramified at every `p ∤ Nℓ` with arithmetic Frobenius trace `a_p(F)`, and has conductor exponent `v_p(N)`
at every prime `p ≠ ℓ` in DDT's form; each clause is read as in `CarayolDDT31`.

`carayolDDT31_of_full` derives `CarayolDDT31` from it (Tau Ceti's newforms are DDT newforms), and
`carayolDDT31Full_of_DDT31` derives it from `CarayolDDT31`: the two leaves are equivalent
(`carayolDDT31Full_iff`). -/
def CarayolDDT31Full : Prop :=
  ∀ (N : ℕ) [NeZero N] (F : CF N 2) (ψ : (ZMod N)ˣ →* ℂˣ), IsDDTNewform F ψ →
    ∀ [NumberField (DSCoeffExt.coeffField (F : CF N 2))]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (DSCoeffExt.coeffField (F : CF N 2)))),
    (ℓ : 𝓞 (DSCoeffExt.coeffField (F : CF N 2))) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2))),
      Continuous ρ ∧
      (∀ W : Submodule
          (AlgebraicClosure (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2))))
          (Fin 2 → AlgebraicClosure
            (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))),
        (∀ σ : GQ, ∀ v ∈ W, ((ρ σ : Matrix (Fin 2) (Fin 2)
          (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))).map
            (algebraMap (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))
              (AlgebraicClosure
                (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))))).mulVec v ∈ W) →
        W = ⊥ ∨ W = ⊤) ∧
      (∃ ι : ℤ_[ℓ] →+* lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)),
        Continuous ι ∧ ∀ σ : GQ,
          ∀ h : ((ψ (cycN N σ) : ℂˣ) : ℂ) ∈ DSCoeffExt.coeffField (F : CF N 2),
            (ρ σ : Matrix (Fin 2) (Fin 2)
              (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))).det =
              algebraMap (DSCoeffExt.coeffField (F : CF N 2))
                (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2))) ⟨_, h⟩ *
              ι (cycL ℓ σ : ℤ_[ℓ])) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2)
            (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))).trace =
            algebraMap (DSCoeffExt.coeffField (F : CF N 2))
              (lam.adicCompletion (DSCoeffExt.coeffField (F : CF N 2)))
              ⟨coeff (F : CF N 2) p, DSCoeffExt.coeff_mem_coeffField _ p⟩) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ →
        (codimInv (ρ.comp (decomp p)) inertiaSet : ℝ) +
          ∫ u in Set.Ioi (0 : ℝ), (codimInv (ρ.comp (decomp p)) (upperAbs p u) : ℝ) =
          (N.factorization p : ℝ)

/-- **GLUE (proved): `CarayolDDT31Full` gives `CarayolDDT31`.** A Tau Ceti newform `f` is a DDT newform with
form `f.toCuspForm` and character `f.χ` (`isDDTNewform_of_newform`, through Tau Ceti's
`Newform.toEigenform`), and the body of `CarayolDDT31` at `f` is that of `CarayolDDT31Full` at
`F = f.toCuspForm`, `ψ = f.χ`. -/
theorem carayolDDT31_of_full (h : CarayolDDT31Full) : CarayolDDT31 := by
  intro N _ f _ ℓ _ lam hlam
  exact h N f.toCuspForm f.χ (isDDTNewform_of_newform f) ℓ lam hlam

/-- **GLUE (proved): the converse, `CarayolDDT31` gives `CarayolDDT31Full`.** A DDT newform is a Tau Ceti
newform with the same form and character: a full eigenform is an eigenform away from the level. -/
theorem carayolDDT31Full_of_DDT31 (h : CarayolDDT31) : CarayolDDT31Full := by
  intro N _ F ψ hF _ ℓ _ lam hlam
  obtain ⟨f, rfl, rfl, hnew, h1⟩ := hF
  exact h N ⟨⟨f.toCuspForm, f.χ, f.mem_charSpace, fun n _ => f.eigenvalue n,
    fun n _ => f.isEigen n, f.ne_zero⟩, hnew, h1⟩ ℓ lam hlam

/-- The leaf for DDT's newforms and the leaf for Tau Ceti's newforms are equivalent. -/
theorem carayolDDT31Full_iff : CarayolDDT31Full ↔ CarayolDDT31 :=
  ⟨carayolDDT31_of_full, carayolDDT31Full_of_DDT31⟩

/-- **The open hypothesis `CarayolRefold.CarayolThmAFrob` from Darmon–Diamond–Taylor 1997, Theorem 3.1, for
newforms in the sense of their Definition 1.21** (through `CarayolDDT31` and `CarayolRefold.frob_of_DDT31`). -/
theorem carayolThmAFrob_of_DDT31Full (h : CarayolDDT31Full) : CarayolRefold.CarayolThmAFrob :=
  CarayolRefold.frob_of_DDT31 (carayolDDT31_of_full h)

end Leaf

end CarayolDDT
