import ZInQKernel.Contrib.OneProof.RC.KatoP2.Kodai08Checked
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! The degree-two argument in the support triangle (K16). The geometric
realization of the triangle is an input; its kernel comparison is proved here. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PrintsArith

/-- All the odd local summands, before localization at a prime of Λ. -/
abbrev KodaiFullOpen.OddLocal {NK : ℕ} (full : KodaiFullOpen NK) :=
  ∀ q : {q : {q // q ∈ NK.primeFactors} // q.val ≠ 2}, full.localH2 q.val

/-- Projection of the full local target to all odd primes of `NK`. -/
def KodaiFullOpen.oddProjection {NK : ℕ} (full : KodaiFullOpen NK) :
    full.iw.H2loc →ₗ[KatoLambda2] full.OddLocal :=
  (LinearMap.pi fun q => LinearMap.proj q.val).comp full.allLocal.toLinearMap

/-- Projection to the summand at two, identified with the retained local term. -/
def KodaiFullOpen.dyadicProjection {NK : ℕ} (full : KodaiFullOpen NK) (retained : KodaiJStar)
    (h2 : 2 ∈ NK.primeFactors)
    (e : full.localH2 ⟨2, h2⟩ ≃ₗ[KatoLambda2] retained.iw.H2loc) :
    full.iw.H2loc →ₗ[KatoLambda2] retained.iw.H2loc :=
  e.toLinearMap.comp ((LinearMap.proj ⟨2, h2⟩).comp full.allLocal.toLinearMap)

abbrev localMap (p : Ideal KatoLambda2) [p.IsPrime]
    {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module KatoLambda2 A] [Module KatoLambda2 B]
    (f : A →ₗ[KatoLambda2] B) :
    LocalizedModule p.primeCompl A →ₗ[Localization.AtPrime p] LocalizedModule p.primeCompl B :=
  LocalizedModule.map p.primeCompl f

private theorem localMap_comp (p : Ideal KatoLambda2) [p.IsPrime]
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module KatoLambda2 A] [Module KatoLambda2 B] [Module KatoLambda2 C]
    (f : A →ₗ[KatoLambda2] B) (g : B →ₗ[KatoLambda2] C)
    (x : LocalizedModule p.primeCompl A) :
    localMap p (g.comp f) x = localMap p g (localMap p f x) := by
  induction x using LocalizedModule.induction_on with
  | _ x s => simp [localMap, LocalizedModule.map_mk]

/-- The part of the support triangle on degree two. The arrow `res` is
restriction from `C_j` to `C_S`. The cone of this restriction is the sum of
the odd local complexes. Away from two, its degree-one cohomology vanishes
by injectivity in (K16); the long exact sequence then gives the injectivity
and exactness below. No assertion about the size of any term is needed. -/
structure KatoOddSupportCone {NK : ℕ} (full : KodaiFullOpen NK) (retained : KodaiJStar) where
  two_mem : 2 ∈ NK.primeFactors
  atTwo : full.localH2 ⟨2, two_mem⟩ ≃ₗ[KatoLambda2] retained.iw.H2loc
  res : retained.iw.H2 →ₗ[KatoLambda2] full.iw.H2
  dyadic_commutes :
    (full.dyadicProjection retained two_mem atTwo).comp (full.iw.loc.comp res) = retained.iw.loc
  inj_away : ∀ (p : Ideal KatoLambda2) [p.IsPrime], p.height = 1 → (2 : KatoLambda2) ∉ p →
    Function.Injective (localMap p res)
  exact_away : ∀ (p : Ideal KatoLambda2) [p.IsPrime], p.height = 1 → (2 : KatoLambda2) ∉ p →
    Function.Exact (localMap p res) (localMap p (full.oddProjection.comp full.iw.loc))

/-- At each height-one prime away from two: the dyadic kernel for `C_j`
is isomorphic to the all-prime kernel for `C_S`. -/
structure KatoSupportComparison {NK : ℕ} (full : KodaiFullOpen NK) (retained : KodaiJStar) where
  onKernel : ∀ (p : Ideal KatoLambda2) [p.IsPrime], p.height = 1 → (2 : KatoLambda2) ∉ p →
    LocalizedModule p.primeCompl retained.H2zero ≃ₗ[Localization.AtPrime p]
      LocalizedModule p.primeCompl full.H2zero

private def localizedKerEquiv (p : Ideal KatoLambda2) [p.IsPrime]
    {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module KatoLambda2 A] [Module KatoLambda2 B]
    (f : A →ₗ[KatoLambda2] B) :
    LocalizedModule p.primeCompl (LinearMap.ker f) ≃ₗ[Localization.AtPrime p]
      LinearMap.ker (localMap p f) := by
  let S := Localization.AtPrime p
  let i := LocalizedModule.mkLinearMap p.primeCompl A
  let j := LocalizedModule.mkLinearMap p.primeCompl B
  let k := LinearMap.ker f
  let e₁ : LocalizedModule p.primeCompl k ≃ₗ[KatoLambda2] k.localized' S p.primeCompl i :=
    IsLocalizedModule.linearEquiv p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl k) (k.toLocalized' S p.primeCompl i)
  have he₂ : k.localized' S p.primeCompl i = LinearMap.ker (localMap p f) :=
    LinearMap.localized'_ker_eq_ker_localizedMap S p.primeCompl i j f
  exact (e₁.extendScalarsOfIsLocalization p.primeCompl S).trans (LinearEquiv.ofEq _ _ he₂)

/-- The exact fragment of (K16) implies the desired comparison: lift
through the kernel of odd localization and check the remaining condition
at two by commutativity. The linear equivalence is induced by restriction. -/
def KatoOddSupportCone.toComparison {NK : ℕ} {full : KodaiFullOpen NK} {retained : KodaiJStar}
    (C : KatoOddSupportCone full retained) : KatoSupportComparison full retained where
  onKernel p _ hp h2 := by
    let r := localMap p C.res
    let f := full.allLocal.toLinearMap.comp full.iw.loc
    let dy := full.dyadicProjection retained C.two_mem C.atTwo
    let od := full.oddProjection
    have hr := C.inj_away p hp h2
    have hx := C.exact_away p hp h2
    have hdy (x : LocalizedModule p.primeCompl retained.iw.H2) :
        localMap p dy (localMap p full.iw.loc (r x)) = localMap p retained.iw.loc x := by
      rw [← localMap_comp, ← localMap_comp, LinearMap.comp_assoc, C.dyadic_commutes]
    have hsplit : Function.Injective (dy.prod od) := by
      intro x y h
      have h₁ : dy x = dy y := congrArg Prod.fst h
      have h₂ : od x = od y := congrArg Prod.snd h
      apply full.allLocal.injective
      funext q
      by_cases he : q.val = 2
      · have hq : q = ⟨2, C.two_mem⟩ := Subtype.ext he
        subst q
        exact C.atTwo.injective h₁
      · exact congrFun h₂ ⟨q, he⟩
    have hzero (x : LocalizedModule p.primeCompl full.iw.H2loc)
        (hd : localMap p dy x = 0) (ho : localMap p od x = 0) : x = 0 := by
      induction x using LocalizedModule.induction_on with
      | _ a s =>
        simp only [localMap, LocalizedModule.map_mk] at hd ho
        rw [← LocalizedModule.zero_mk (1 : p.primeCompl)] at hd ho ⊢
        simp only [LocalizedModule.mk_eq, one_smul, smul_zero] at hd ho ⊢
        obtain ⟨s₁, hs₁⟩ := hd
        obtain ⟨s₂, hs₂⟩ := ho
        refine ⟨s₁ * s₂, hsplit ?_⟩
        apply Prod.ext
        · change dy (((s₁ * s₂ : p.primeCompl) : KatoLambda2) • a) = dy 0
          rw [map_smul, map_zero]
          change (s₁ * s₂) • dy a = 0
          rw [mul_comm s₁ s₂, mul_smul, hs₁, smul_zero]
        · change od (((s₁ * s₂ : p.primeCompl) : KatoLambda2) • a) = od 0
          rw [map_smul, map_zero]
          change (s₁ * s₂) • od a = 0
          rw [mul_smul, hs₂, smul_zero]
    have hrange (x : LocalizedModule p.primeCompl full.iw.H2) :
        x ∈ LinearMap.ker (localMap p f) ↔
          localMap p dy (localMap p full.iw.loc x) = 0 ∧
          localMap p (od.comp full.iw.loc) x = 0 := by
      have e := (LocalizedModule.map_injective p.primeCompl full.allLocal.toLinearMap
        full.allLocal.injective)
      change localMap p f x = 0 ↔ _
      rw [show localMap p f x =
        localMap p full.allLocal.toLinearMap (localMap p full.iw.loc x) from localMap_comp _ _ _ _]
      constructor
      · intro h
        have hloc : localMap p full.iw.loc x = 0 := e (h.trans (map_zero _).symm)
        rw [localMap_comp, hloc, map_zero, map_zero]
        exact ⟨rfl, rfl⟩
      · rintro ⟨hd, ho⟩
        rw [localMap_comp] at ho
        rw [hzero _ hd ho, map_zero]
    let k : LinearMap.ker (localMap p retained.iw.loc) →ₗ[Localization.AtPrime p]
        LinearMap.ker (localMap p f) :=
      (r.comp (LinearMap.ker (localMap p retained.iw.loc)).subtype).codRestrict _ fun x =>
        (hrange _).2 ⟨(hdy x).trans x.property, (hx _).2 ⟨x, rfl⟩⟩
    have hk : Function.Bijective k := by
      refine ⟨fun x y he => Subtype.ext (hr (congrArg Subtype.val he)), ?_⟩
      intro y
      obtain ⟨hd, ho⟩ := (hrange y.val).1 y.property
      obtain ⟨x, he⟩ := (hx y.val).1 ho
      refine ⟨⟨x, ?_⟩, Subtype.ext he⟩
      rw [LinearMap.mem_ker, ← hdy, he]
      exact hd
    exact (localizedKerEquiv p retained.iw.loc).trans
      ((LinearEquiv.ofBijective k hk).trans (localizedKerEquiv p f).symm)

end ZInQ.Manuscript.RC.KatoP2.Checked
