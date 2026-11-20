import ZInQKernel.Contrib.OneProof.RC.CMScope.Field

/-! The value form of the CM input for tex 2915–2916. -/

open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.BranchDescends

/-- **GLUE (value form of a printed point statement).** For an oriented
Heegner form in the scope of tex 2839–2844 and 2915–2916, every modular
function in `ℚ(j, j_N)` finite at its CM parameter has value in the
associated ring class field, with one complex embedding for all the values
at that parameter. The finite-germ condition excludes poles, not vanishing
denominators of individual presentations of the function.

Printed in point form only: Cai–Chen–Liu, *Heegner points on modular
curves*, Trans. AMS 370 (2018), p. 3721 (the point `(ℂ/𝔞, 𝔞𝒩⁻¹/𝔞)` of
`X₀(N)` "is defined over the ring class field `H_c`", for `(c, N) = 1` and
any proper ideal of the non-maximal order; asserted by CM theory, citing
Gross, *Heegner points on X₀(N)* (Durham 1983; 1984), pp. 87–105) and
p. 3730. The manuscript's "Theorem 2.15" at tex 2914–2922 is not where it
is printed. The value form also uses `ℚ(X₀(N)) = ℚ(j, j_N)`, which CCL does
not state; that is a separate classical input (locator UNVERIFIED). No
action of the class group or norm relation is assumed. -/
def HeegnerValuesInRingClassField (N : ℕ) [NeZero N] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → IsTotallyComplex K →
    (∀ p : ℕ, p.Prime → p ∣ 2 * N → SplitsIn K p) →
    discr K ≠ -4 → discr K ≠ -3 →
    ∀ (β : ℤ), Int.ModEq (4 * (N : ℤ)) (β ^ 2) (discr K) →
    ∀ (c : ℕ) [NeZero c], Nat.Coprime c (2 * N * (discr K).natAbs) →
    ∀ (d A B C : ℤ), (conductorOrder K c).discr = d → d < 0 →
      IsCoprime d (N : ℤ) → IsHeegnerForm N d A B C →
      Int.ModEq (2 * (N : ℤ)) B ((c : ℤ) * β) →
      let H := ringClassField (conductorOrder K c)
      let τ := cmPoint A B d
      ∃ ι : H →ₐ[ℚ] ℂ, ∀ (g : ModularCurve.modularFunctionField N)
        (s : X0Model.meromorphicValuation (τ : ℂ)),
        s.val = X0Model.fieldGerm N τ g →
        X0Model.valueOfGerm (τ : ℂ) s ∈ Set.range ι

end ZInQ.Manuscript.RC.BranchDescends
