import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.SupportChange
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality
import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Naturality

/-!
# Non-vacuity of the model structures used as hypotheses (SelmerDuality, CommonCoordinate)

Every structure packaging a model that is used as a hypothesis has an instance of the model
itself:

* `PerfectCoefficientPairing`: `S × S → S`, multiplication (`perfectCoefficientPairing_mul`).
* `UnramifiedNewPlace` and `SupportChangeUnramified` (hypotheses of `SupportChangeInput`): the zero
  coefficient module with the zero complexes (`zeroNewPlace`, `zeroSupportChangeUnramified`); every
  field (the tame model at augmentation, the unramified condition, the retractions, the exact
  sequences, the compatibility of `ι`) holds, so the fields are consistent. They are not
  instantiable by genuine continuous cochains (the degreewise isomorphisms with the 3-term tame
  model fail for `C^•(G_{K_q}, M)`, which is nonzero in every degree `≥ 0`); re-pointing to the
  genuine Galois support data is pending.
* `RetainedPairing` (hypothesis of `cup_naturality`, `pairedFunctional_natural`): the constant
  Selmer data `constSel S` of `SelmerPairing.lean`, multiplication as both cup products, zero
  isotropy homotopies (`constRetainedPairing`).

`ActualStep` (CommonCoordinate) has the nondegenerate instance `actualStep_example`
(`CommonCoordinate/NonVacuity.lean`).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional

universe u

variable (S : Type u) [CommRing S]

/-- Multiplication `S × S → S` is a perfect coefficient pairing. -/
def perfectCoefficientPairing_mul : PerfectCoefficientPairing S where
  M := ModuleCat.of S S
  M' := ModuleCat.of S S
  pair := LinearMap.mul S S
  perfect_left := by
    refine ⟨fun a b h => ?_, fun f => ⟨f 1, LinearMap.ext fun x => ?_⟩⟩
    · simpa using LinearMap.congr_fun h 1
    · change f 1 * x = f x
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  perfect_right := by
    refine ⟨fun a b h => ?_, fun f => ⟨f 1, LinearMap.ext fun x => ?_⟩⟩
    · simpa using LinearMap.congr_fun h 1
    · change x * f 1 = f x
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- The zero complex. -/
abbrev zeroCx : GCx S where
  X _ := ModuleCat.of S PUnit.{u + 1}
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

/-- The zero chain map. -/
def zeroHom (A B : GCx S) : GHom A B where
  f _ _ _ := 0
  comm _ _ _ _ _ _ _ _ _ := by simp

/-- Zero Selmer data. -/
abbrev zeroSel : SelData S := ⟨zeroCx S, zeroCx S, zeroCx S, zeroHom S _ _, zeroHom S _ _⟩

instance (n : ℤ) : Subsingleton ((zeroCx S).X n) := ⟨fun _ _ => rfl⟩

/-- The zero coefficient module as an unramified new place (tame model at augmentation with
`M = 0`, `Φ = 0`, `q = 1`). -/
abbrev zeroNewPlace : UnramifiedNewPlace S where
  M := ModuleCat.of S PUnit.{u + 1}
  Φ := 0
  q := 1
  q_odd := odd_one
  Lq := zeroCx S
  Uq := zeroCx S
  ιq := zeroHom S _ _
  eL0 := LinearEquiv.refl S PUnit.{u + 1}
  eL1 := (LinearEquiv.prodUnique (R := S) (M := PUnit.{u + 1}) (M₂ := PUnit.{u + 1})).symm
  eL2 := LinearEquiv.refl S PUnit.{u + 1}
  Lq_zero _ _ _ _ := ⟨fun _ _ => rfl⟩
  Lq_d0 _ := Subsingleton.elim _ _
  Lq_d1 _ := Subsingleton.elim _ _
  eU0 := LinearEquiv.refl S PUnit.{u + 1}
  eU1 := LinearEquiv.refl S PUnit.{u + 1}
  Uq_zero _ _ _ := ⟨fun _ _ => rfl⟩
  Uq_d _ := Subsingleton.elim _ _
  ιq_0 _ := Subsingleton.elim _ _
  ιq_1 _ := Subsingleton.elim _ _

/-- The trivial support change on zero Selmer data. -/
abbrev zeroSupportChange : SupportChangeData S where
  D := zeroSel S
  Dp := zeroSel S
  g := zeroHom S _ _
  lam := zeroHom S _ _
  mu := zeroHom S _ _
  r := zeroHom S _ _
  hres _ _ _ _ := Subsingleton.elim _ _
  hι _ _ _ _ := Subsingleton.elim _ _

/-- **Non-vacuity of `SupportChangeUnramified`**: its fields are jointly satisfiable. -/
def zeroSupportChangeUnramified : SupportChangeUnramified (zeroSupportChange S) where
  P := zeroNewPlace S
  pL := zeroHom S _ _
  pU := zeroHom S _ _
  lam_retract _ := ⟨0, fun _ => Subsingleton.elim _ _⟩
  mu_retract _ := ⟨0, fun _ => Subsingleton.elim _ _⟩
  pL_surj _ _ := ⟨0, Subsingleton.elim _ _⟩
  pU_surj _ _ := ⟨0, Subsingleton.elim _ _⟩
  L_exact _ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  U_exact _ _ := ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  ι_compat _ _ := Subsingleton.elim _ _

/-- **Non-vacuity of `RetainedPairing`**: the constant Selmer data with multiplication as both cup
products and zero isotropy homotopies. -/
def constRetainedPairing :
    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.RetainedPairing (constSel S) (constSel S)
      (constId S) (constId S) where
  E := constCx S
  EL := constCx S
  resE := constId S
  cupG := constMul S
  cupL := constMul S
  compat _ _ _ _ _ _ _ _ _ _ _ _ _ := rfl
  hR _ _ _ _ := 0
  isoR i _ _ _ _ _ _ _ _ _ u v := by
    change (0 : S) + 0 + sgn i • (0 : S) = (show S from 0) * (0 : S)
    simp
  hP _ _ _ _ := 0
  isoP i _ _ _ _ _ _ _ _ _ u v := by
    change (0 : S) + 0 + sgn i • (0 : S) = (0 : S) * (show S from 0)
    simp
  retained _ _ _ _ _ _ := rfl

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
