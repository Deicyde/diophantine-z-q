import ZInQKernel.Contrib.TYZGenus.Package
import ZInQKernel.Contrib.TYZGenus.RingClassGalois

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

end ZInQ.Contrib.TYZGenus.RingClassBridge
