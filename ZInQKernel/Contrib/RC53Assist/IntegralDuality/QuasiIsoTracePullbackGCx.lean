import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.QuasiIsoTracePullback

/-!
# Pulling a top-degree trace back along a chain map of relation-indexed complexes

For `f : GHom A B` with `GHom.toCC f` a quasi-isomorphism in degree `j`, and a functional
`tr : B.X j → R` satisfying `IsTopTraceIso` for the differentials of `B` around degree `j`,
the functional `tr ∘ f^j` satisfies `IsTopTraceIso` for the differentials of `A`
(`gcx_isTopTraceIso_comp_of_quasiIsoAt`). The map `f^j` is the component of the same `f` whose
homology map is assumed invertible.

Exports:
* `inducesIsoH3_comp_of_quasiIsoAt`: degree three, from `QuasiIsoAt (GHom.toCC f) 3`,
  vanishing of `tr` on coboundaries and `InducesIsoH3 tr`, the functional `tr ∘ f³` vanishes
  on coboundaries and satisfies `InducesIsoH3`. No condition on the cohomology of `A` is
  assumed.
* `shiftDown_isTopTraceIso_comp_of_quasiIsoAt`: for `f : GHom (shiftDown L) C` with
  `QuasiIsoAt (GHom.toCC f) 3`, the functional `tr ∘ f³` on `L.X 2` satisfies
  `IsTopTraceIso (L.d 1 2 rfl) (L.d 2 3 rfl)`; the signs of the differentials of `shiftDown L`
  are removed by `isTopTraceIso_neg_iff`. The general-degree form is
  `shiftDown_isTopTraceIso_comp_of_quasiIsoAt_general`.

Controls: `inducesIsoH3_comp_example` and `shiftDown_comp_example` are nonzero instances (the
pulled-back trace takes the value `1`); `zeroGHom_not_inducesIsoH3` shows that the
quasi-isomorphism hypothesis cannot be dropped, even when `A` itself carries a trace inducing
`H³(A) ≅ R`: the zero map pulls every trace back to zero, and accordingly the zero map is not a
quasi-isomorphism in degree three (`zeroGHom_not_quasiIsoAt`).
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory HomologicalComplex ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality ZInQ.Manuscript.RC.SelmerComplex

universe u

section General

variable {S : Type u} [CommRing S]

/-- The underlying linear map of a differential of `GCx.toCC`. -/
theorem gcx_toCC_d_hom_eq (C : GCx S) (p q : ℤ) (h : p + 1 = q) :
    (C.toCC.d p q).hom = C.d p q h :=
  LinearMap.ext (C.toCC_d_hom p q h)

/-- **Pullback along a quasi-isomorphism in degree `j`** for relation-indexed complexes. -/
theorem gcx_isTopTraceIso_comp_of_quasiIsoAt {A B : GCx S} (f : GHom A B) (i j k : ℤ)
    (hij : i + 1 = j) (hjk : j + 1 = k) (hf : QuasiIsoAt (GHom.toCC f) j)
    (tr : B.X j →ₗ[S] S) (htr : IsTopTraceIso (B.d i j hij) (B.d j k hjk) tr) :
    IsTopTraceIso (A.d i j hij) (A.d j k hjk) (tr ∘ₗ f.f j j rfl) := by
  have h := isTopTraceIso_comp_of_quasiIsoAt_int (GHom.toCC f) hij hjk hf tr
    (by rw [gcx_toCC_d_hom_eq B i j hij, gcx_toCC_d_hom_eq B j k hjk]; exact htr)
  rw [gcx_toCC_d_hom_eq A i j hij, gcx_toCC_d_hom_eq A j k hjk] at h
  exact h

end General

section DegreeThree

variable {R : Type} [CommRing R]

/-- **Degree three.** The pulled-back functional `tr ∘ f³` vanishes on coboundaries and satisfies
the literal degree-three predicate, from the quasi-isomorphism `f` in degree three and the
properties of `tr` only. -/
theorem inducesIsoH3_comp_of_quasiIsoAt {A B : GCx R} (f : GHom A B)
    (hf : QuasiIsoAt (GHom.toCC f) 3) (tr : B.X 3 →ₗ[R] R)
    (hbd : ∀ y, tr (B.d 2 3 rfl y) = 0) (hB : InducesIsoH3 (C := B) tr) :
    (∀ y, (tr ∘ₗ f.f 3 3 rfl) (A.d 2 3 rfl y) = 0) ∧
      InducesIsoH3 (C := A) (tr ∘ₗ f.f 3 3 rfl) :=
  gcx_isTopTraceIso_comp_of_quasiIsoAt f 2 3 4 rfl rfl hf tr ⟨hbd, hB⟩

/-- The local functional on `L.X 2` obtained from `f : GHom (shiftDown L) C` and a functional on
`C.X 3`. -/
def shiftDownTrace {L C : GCx R} (f : GHom (shiftDown L) C) (tr : C.X 3 →ₗ[R] R) :
    L.X 2 →ₗ[R] R :=
  tr ∘ₗ f.f 3 3 rfl

theorem shiftDownTrace_apply {L C : GCx R} (f : GHom (shiftDown L) C) (tr : C.X 3 →ₗ[R] R)
    (x : L.X 2) : shiftDownTrace f tr x = tr (f.f 3 3 rfl x) := rfl

/-- **`shiftDown`, general degree.** For `f : GHom (shiftDown L) C` a quasi-isomorphism in degree
`j`, the functional `tr ∘ f^j` on `L.X (j - 1)` satisfies the concrete trace condition for the
differentials of `L` itself (no signs). -/
theorem shiftDown_isTopTraceIso_comp_of_quasiIsoAt_general {S : Type u} [CommRing S]
    {L C : GCx S} (f : GHom (shiftDown L) C) (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k)
    (hf : QuasiIsoAt (GHom.toCC f) j) (tr : C.X j →ₗ[S] S)
    (htr : IsTopTraceIso (C.d i j hij) (C.d j k hjk) tr) :
    IsTopTraceIso (L.d (i - 1) (j - 1) (by omega)) (L.d (j - 1) (k - 1) (by omega))
      (tr ∘ₗ f.f j j rfl) :=
  isTopTraceIso_neg_iff.1 (gcx_isTopTraceIso_comp_of_quasiIsoAt f i j k hij hjk hf tr htr)

/-- **`shiftDown`, degree three.** For `f : GHom (shiftDown L) C` with
`QuasiIsoAt (GHom.toCC f) 3`, and `tr : C.X 3 → R` vanishing on coboundaries with
`InducesIsoH3 tr`, the local functional `tr ∘ f³ : L.X 2 → R` kills the boundaries of
`L.d 1 2`, every `L.d 2 3`-cycle of trace zero is an `L.d 1 2`-boundary, and some cycle has
trace one. -/
theorem shiftDown_isTopTraceIso_comp_of_quasiIsoAt {L C : GCx R} (f : GHom (shiftDown L) C)
    (hf : QuasiIsoAt (GHom.toCC f) 3) (tr : C.X 3 →ₗ[R] R)
    (hbd : ∀ y, tr (C.d 2 3 rfl y) = 0) (hC : InducesIsoH3 (C := C) tr) :
    IsTopTraceIso (L.d 1 2 rfl) (L.d 2 3 rfl) (shiftDownTrace f tr) :=
  shiftDown_isTopTraceIso_comp_of_quasiIsoAt_general f 2 3 4 rfl rfl hf tr ⟨hbd, hC⟩

end DegreeThree

section Examples

/-- The complex with every term the ring and only the differential out of degree `k + 1`
nonzero (the identity). Its cohomology is the ring in degree `k` and zero in degree `k + 1`. -/
def peakCx (T : Type) [CommRing T] (k : ℤ) : GCx T where
  X _ := ModuleCat.of T T
  d i _ _ := if i = k + 1 then LinearMap.id else 0
  d_d i j l hij hjl x := by
    by_cases h : i = k + 1
    · have : j ≠ k + 1 := by omega
      simp [h, this]
    · simp [h]

theorem peakCx_d_ne (T : Type) [CommRing T] (k i j : ℤ) (h : i + 1 = j) (hi : i ≠ k + 1)
    (x : (peakCx T k).X i) : (peakCx T k).d i j h x = 0 := by
  change (if i = k + 1 then LinearMap.id else 0) x = 0
  simp only [hi, ↓reduceIte]
  rfl

/-- The identity functional of `peakCx T 3` in degree three. -/
def peakTrace (T : Type) [CommRing T] : (peakCx T 3).X 3 →ₗ[T] T := LinearMap.id

theorem peakTrace_bd (T : Type) [CommRing T] (y : (peakCx T 3).X 2) :
    peakTrace T ((peakCx T 3).d 2 3 rfl y) = 0 := by
  rw [peakCx_d_ne T 3 2 3 rfl (by decide)]
  rfl

theorem peakTrace_inducesIsoH3 (T : Type) [CommRing T] :
    InducesIsoH3 (C := peakCx T 3) (peakTrace T) := by
  refine ⟨fun z _ hz => ⟨0, ?_⟩, (1 : T), peakCx_d_ne T 3 3 4 rfl (by decide) _, rfl⟩
  rw [peakCx_d_ne T 3 2 3 rfl (by decide)]
  exact hz.symm

theorem quasiIsoAt_toCC_idGHom {S : Type u} [CommRing S] (X : GCx S) (n : ℤ) :
    QuasiIsoAt (GHom.toCC (idGHom X)) n := by
  rw [toCC_idGHom, quasiIsoAt_iff_isIso_homologyMap, homologyMap_id]
  infer_instance

/-- **Nonzero instance, degree three.** The pullback of the identity trace of `peakCx ℤ 3` along
the identity chain map satisfies the conclusion and takes the value `1`. -/
theorem inducesIsoH3_comp_example :
    InducesIsoH3 (C := peakCx ℤ 3) (peakTrace ℤ ∘ₗ (idGHom (peakCx ℤ 3)).f 3 3 rfl) ∧
      (peakTrace ℤ ∘ₗ (idGHom (peakCx ℤ 3)).f 3 3 rfl) (show (peakCx ℤ 3).X 3 from (1 : ℤ)) = 1 :=
  ⟨(inducesIsoH3_comp_of_quasiIsoAt (idGHom (peakCx ℤ 3)) (quasiIsoAt_toCC_idGHom _ 3)
    (peakTrace ℤ) (peakTrace_bd ℤ) (peakTrace_inducesIsoH3 ℤ)).2, rfl⟩

theorem shiftDown_d_apply {S : Type u} [CommRing S] (L : GCx S) (i j : ℤ) (h : i + 1 = j)
    (x : (shiftDown L).X i) :
    (shiftDown L).d i j h x = -(L.d (i - 1) (j - 1) (by omega) x) := rfl

theorem shiftDown_peakCx_d_ne (T : Type) [CommRing T] (k i j : ℤ) (h : i + 1 = j)
    (hi : i - 1 ≠ k + 1) (x : (shiftDown (peakCx T k)).X i) :
    (shiftDown (peakCx T k)).d i j h x = 0 := by
  change (-(if i - 1 = k + 1 then (LinearMap.id : T →ₗ[T] T) else 0)) x = 0
  simp only [hi, ↓reduceIte, neg_zero]
  rfl

/-- The identity functional of `shiftDown (peakCx T 2)` in degree three. -/
def shiftPeakTrace (T : Type) [CommRing T] : (shiftDown (peakCx T 2)).X 3 →ₗ[T] T :=
  LinearMap.id

theorem shiftPeakTrace_bd (T : Type) [CommRing T] (y : (shiftDown (peakCx T 2)).X 2) :
    shiftPeakTrace T ((shiftDown (peakCx T 2)).d 2 3 rfl y) = 0 := by
  rw [shiftDown_peakCx_d_ne T 2 2 3 rfl (by decide)]
  rfl

theorem shiftPeakTrace_inducesIsoH3 (T : Type) [CommRing T] :
    InducesIsoH3 (C := shiftDown (peakCx T 2)) (shiftPeakTrace T) := by
  refine ⟨fun z _ hz => ⟨0, ?_⟩, (1 : T), ?_, rfl⟩
  · rw [shiftDown_peakCx_d_ne T 2 2 3 rfl (by decide)]
    exact hz.symm
  · exact shiftDown_peakCx_d_ne T 2 3 4 rfl (by decide) _

/-- **Nonzero instance, `shiftDown` local form.** With `L = peakCx ℤ 2`, `C = shiftDown L` and
`f` the identity, the local functional on `L.X 2` satisfies the unsigned concrete condition and
takes the value `1`. -/
theorem shiftDown_comp_example :
    IsTopTraceIso ((peakCx ℤ 2).d 1 2 rfl) ((peakCx ℤ 2).d 2 3 rfl)
        (shiftDownTrace (idGHom (shiftDown (peakCx ℤ 2))) (shiftPeakTrace ℤ)) ∧
      shiftDownTrace (idGHom (shiftDown (peakCx ℤ 2))) (shiftPeakTrace ℤ)
        (show (peakCx ℤ 2).X 2 from (1 : ℤ)) = 1 :=
  ⟨shiftDown_isTopTraceIso_comp_of_quasiIsoAt (idGHom (shiftDown (peakCx ℤ 2)))
    (quasiIsoAt_toCC_idGHom _ 3) (shiftPeakTrace ℤ) (shiftPeakTrace_bd ℤ)
    (shiftPeakTrace_inducesIsoH3 ℤ), rfl⟩

/-- **Missing quasi-isomorphism control** (with the existing zero chain map `zeroGHom`). On
`peakCx ℤ 3`, which carries the trace `peakTrace`
inducing `H³ ≅ ℤ`, the pullback of that trace along the zero chain map does not satisfy the
degree-three predicate: it vanishes identically, so no cocycle has trace one. -/
theorem zeroGHom_not_inducesIsoH3 :
    InducesIsoH3 (C := peakCx ℤ 3) (peakTrace ℤ) ∧
      ¬ InducesIsoH3 (C := peakCx ℤ 3)
        (peakTrace ℤ ∘ₗ (zeroGHom (peakCx ℤ 3) (peakCx ℤ 3)).f 3 3 rfl) := by
  refine ⟨peakTrace_inducesIsoH3 ℤ, ?_⟩
  rintro ⟨-, z, -, hz⟩
  have h0 : (peakTrace ℤ ∘ₗ (zeroGHom (peakCx ℤ 3) (peakCx ℤ 3)).f 3 3 rfl) z = 0 := by
    change peakTrace ℤ 0 = 0
    exact map_zero _
  rw [h0] at hz
  exact zero_ne_one hz

/-- Consequently, by `inducesIsoH3_comp_of_quasiIsoAt`, the zero chain map is not a
quasi-isomorphism in degree three. -/
theorem zeroGHom_not_quasiIsoAt :
    ¬ QuasiIsoAt (GHom.toCC (zeroGHom (peakCx ℤ 3) (peakCx ℤ 3))) 3 := fun hf =>
  zeroGHom_not_inducesIsoH3.2 (inducesIsoH3_comp_of_quasiIsoAt _ hf (peakTrace ℤ)
    (peakTrace_bd ℤ) (peakTrace_inducesIsoH3 ℤ)).2

end Examples

end ZInQ.Contrib.RC53Assist.IntegralDuality
