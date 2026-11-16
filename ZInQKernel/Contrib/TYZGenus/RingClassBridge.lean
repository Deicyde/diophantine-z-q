import ZInQKernel.Contrib.TYZGenus.Package
import ZInQKernel.Contrib.TYZGenus.RingClassGalois
import ZInQKernel.Contrib.TYZGenus.RingClassGenus

/-!
# ring-class → cm-points bridge (task ring-class)

Proves two of the leaves stated by task cm-points in `ZInQKernel/Contrib/TYZGenus/Package.lean`
from the ring class field theory of `RingClassGalois.lean` (Tau Ceti's ring class fields, Artin
isomorphism and Chebotarev density theorem):

* `hprimeNormal : Package.HprimeNormal` — `H'_d / ℚ` is normal (TYZ Proposition 3.2(1); Cox,
  *Primes of the form x² + ny²*, Lemma 9.3, UNVERIFIED numbering). Proved for every `d`, without
  the hypotheses `d ≡ 5 (mod 8)`, `d` squarefree.
* `iInH4 : Package.IInH4` — `i ∈ H_{n,4}` (genus theory). Proved for every `n ≥ 1`.

and the resulting strengthening of cm-points' headline reduction with these two hypotheses
discharged (`tyzThm35ReadingA_of_cmLeaves_ringClass`).
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.RingClassBridge

open ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.Package

/-- **cm-points' leaf `HprimeNormal`, proved.** -/
theorem hprimeNormal : HprimeNormal := fun d _ _ => normal_Hprimebar d

/-- **cm-points' leaf `IInH4`, proved.** -/
theorem iInH4 : IInH4 := fun n hn _ => iQ_mem_H4bar (by omega)

open ZInQ.Contrib.TYZDecomp in
/-- **cm-points' finest main theorem with `IInH4` and `HprimeNormal` discharged**: reading A of
TYZ Theorem 3.5 from the three `𝓛`-leaves, the CM leaves `CMFieldOfDefinitionTYZ` (Shimura) and
`TYZSigmaFixesZn` (TYZ Cor. 3.9), TYZ Lemma 3.18 (literal) and the bundled `GenusPointLeafCM`. -/
theorem tyzThm35ReadingA_of_cmLeaves_ringClass (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : CMFieldOfDefinitionTYZ) (hs : TYZSigmaFixesZn)
    (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves h11 h1 h29 hcm iInH4 hs hprimeNormal h318 hG

/-- **cm-points' TYZ instance `CMFieldOfDefinitionTYZ` from the general leaf
`CM.CMFieldOfDefinition` with `H` pinned to the ring class fields by discriminant**
(`ringClassFieldD (−64n) = H_{n,4}`, `ringClassFieldD_tyz`). -/
theorem cmFieldTYZ_of_ringClassD (h : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD) :
    CMFieldOfDefinitionTYZ :=
  cmFieldTYZ_of h fun _ hn hsq => (ringClassFieldD_tyz hn hsq).le

open ZInQ.Contrib.TYZDecomp in
/-- **Main theorem, ring-class form**: reading A of TYZ Theorem 3.5 from the three `𝓛`-leaves,
the general CM leaf `CM.CMFieldOfDefinition ringClassFieldD` (Heegner points of discriminant `D`
on `A` are defined over the ring class field of discriminant `D`: Gross 1984 §3, Shimura 1971),
`TYZSigmaFixesZn` (TYZ Cor. 3.9), TYZ Lemma 3.18 (literal) and the bundled `GenusPointLeafCM`. -/
theorem tyzThm35ReadingA_of_cmLeaves_ringClassD (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cmLeaves_ringClass h11 h1 h29 (cmFieldTYZ_of_ringClassD hcm) hs h318 hG

/-- `ℍ'_n / ℚ` is normal (cm-points' `NormalFields HHprime`, now unconditional). -/
theorem normalFields_HHprime' : NormalFields HHprime := normalFields_HHprime hprimeNormal

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.RouteK.Rank5b TauCeti.GlobalNumberFields in
/-- **`ρ` acting on `H_{n,4}` as an element of `Pic(O_{n,4})²` fixes `i`.** -/
theorem fixes_iQ_of_actsAsArtin4_sq {n : ℕ} [NeZero n] {ρ : ZInQ.Contrib.TYZGenus.CM.GalQ} {b : Pic (O4 n)}
    (hρ : ActsAsArtin4 ρ n (b ^ 2)) : ρ iQ = iQ := by
  have hx : jK (QNeg n) ∈ H4 n := jK_mem_H4
  have hfix := hρ ⟨jK (QNeg n), hx⟩
  rw [artin4_sq_apply_of_sq hx ⟨-1, by rw [jK_sq, map_neg, map_one]⟩] at hfix
  have hs2 : (embed n (jK (QNeg n))) ^ 2 = iQ ^ 2 := by
    rw [← map_pow, jK_sq, map_neg, map_one, iQ_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs2 with h | h
  · rw [← h]; exact hfix
  · have : iQ = -embed n (jK (QNeg n)) := by rw [h, neg_neg]
    rw [this, map_neg, hfix]

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.RouteK.Rank5b TauCeti.GlobalNumberFields in
/-- **Complex conjugation inverts `Cl'` in `ℚ̄`**: if `γ ∈ Gal(ℚ̄/ℚ)` is nontrivial on `K_n` and `ρ`
acts on `H_{n,4}` as the Artin symbol of `c`, then `γργ⁻¹` acts as the Artin symbol of `c⁻¹`. -/
theorem actsAsArtin4_conj {n : ℕ} [NeZero n] {γ ρ : ZInQ.Contrib.TYZGenus.CM.GalQ}
    {c : Pic (O4 n)}
    (hγ : γ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ≠
      embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega))
    (hρ : ActsAsArtin4 ρ n c) : ActsAsArtin4 (γ * ρ * γ⁻¹) n c⁻¹ := by
  have hb := (Algebra.IsAlgebraic.algHom_bijective₂ (embed n)
    (IsAlgClosed.lift : Qbar →ₐ[ℚ] SeparableClosure (QNeg n))).1
  set e := AlgEquiv.ofBijective (embed n) hb
  set τ : SeparableClosure (QNeg n) ≃ₐ[ℚ] SeparableClosure (QNeg n) := e.trans (γ.trans e.symm)
  have he : ∀ y, e y = embed n y := fun y => rfl
  have hγτ : ∀ y, γ (embed n y) = embed n (τ y) := by
    intro y
    rw [← he, ← he]
    simp [τ]
  have hγτ' : ∀ y, γ⁻¹ (embed n y) = embed n (τ.symm y) := by
    intro y
    apply γ.injective
    rw [show γ (γ⁻¹ (embed n y)) = embed n y from γ.apply_symm_apply _, hγτ, τ.apply_symm_apply]
  have hneg : τ (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) =
      -algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega := by
    rcases tau_omega_cases τ with h | h
    · exfalso; apply hγ; rw [hγτ, h]
    · exact h
  obtain ⟨σ, hσ, hτσ⟩ := exists_sigma_of_neg τ hneg
  intro x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγτ']
  have h1 := hρ ((tauH τ).symm x)
  rw [coe_tauH_symm] at h1
  rw [h1, hγτ, conj_artin4_apply τ σ hτσ hσ c x]

end ZInQ.Contrib.TYZGenus.RingClassBridge
