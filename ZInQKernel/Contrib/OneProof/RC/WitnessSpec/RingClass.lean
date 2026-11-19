import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusAction
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ResidueDegree

/-! The conductor-one residue degree at an inert prime (tex 8392–8398,
8439–8445). The use of principal ideal reciprocity to descend the residue
field of the datum is given here. -/

noncomputable section

open NumberField IsDedekindDomain TauCeti TauCeti.GlobalNumberFields
  TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST
open scoped NumberField

namespace ZInQ.Manuscript.RC.WitnessSpec

variable {K : Type} [Field K] [NumberField K]

private theorem conductor_one_eq :
    (conductorOrder K 1).conductor = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply ((conductorOrder K 1).mem_conductor_iff 1).mpr
  intro y
  exact ⟨0, y, by simp⟩

/-- An inert rational prime has residue degree one in the conductor-one ring class field. -/
theorem conductorOne_inertiaDeg_of_inert {p : ℕ}
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal = Ideal.span {(p : 𝓞 K)})
    (Q : Ideal (𝓞 (ringClassField (conductorOrder K 1)))) [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    Q.inertiaDeg (𝓞 K) = 1 := by
  let O := conductorOrder K 1
  let J : integralIdealsPrimeTo O.conductorModulus :=
    ⟨v.asIdeal, ZInQ.Contrib.CloudB3RC53.GenusOdd.mem_primeTo_of_not_dvd (K := K) (c := 1)
      (v := v) (by rw [conductor_one_eq, Ideal.dvd_iff_le]; exact fun h => v.isPrime.ne_top (top_le_iff.mp h))⟩
  let : (J : Ideal (𝓞 K)).IsMaximal := v.isMaximal
  have hpic : O.picClass J = 1 := by
    apply (O.picClass_eq_one_iff J).mpr
    exact ⟨(p : 𝓞 K), ⟨0, (p : 𝓞 K), by simp⟩, hv⟩
  rw [← orderOf_picClass_eq_inertiaDeg O J Q, hpic, orderOf_one]

/-- If the inert prime has degree two over the rational prime, its conductor-one
residue field has exactly p² elements. -/
theorem conductorOne_residue_card {p : ℕ}
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal = Ideal.span {(p : 𝓞 K)})
    (hbase : rationalPrimeBelow v = p) (hdegree : v.asIdeal.inertiaDeg ℤ = 2)
    (Q : HeightOneSpectrum (𝓞 (ringClassField (conductorOrder K 1))))
    [Q.asIdeal.LiesOver v.asIdeal] :
    Nat.card ((𝓞 (ringClassField (conductorOrder K 1))) ⧸ Q.asIdeal) = p ^ 2 := by
  change Q.asIdeal.absNorm = _
  rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal Q.asIdeal,
    conductorOne_inertiaDeg_of_inert v hv Q.asIdeal, pow_one,
    absNorm_eq_rationalPrimeBelow_pow v, hbase, hdegree]


end ZInQ.Manuscript.RC.WitnessSpec
