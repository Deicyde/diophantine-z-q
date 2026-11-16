import ZInQKernel.OneProof.H.TailZ24

/-! # pic-dict: L5 (`T09Pic.PicPointsAlgClosed`) is a theorem

At `T = Spec K̄` every fppf covering sieve of `T` (in `Over (Spec K)`) contains `𝟙 T`: a covering family is
jointly surjective, flat and locally of finite presentation, so its pull-back along any `k`-point (`k`
algebraically closed) is a nonempty scheme locally of finite type over `k`, which has a `k`-point
(Nullstellensatz, Mathlib's `pointOfClosedPoint`). Hence the sheafification map is injective and surjective
at `T` (Mathlib: `toSheafify` is locally injective and locally surjective). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite

namespace PicDict

universe u

/-- A nonempty scheme locally of finite type over an algebraically closed field `k` has a `k`-point
(Mathlib's `pointOfClosedPoint`, Nullstellensatz). -/
theorem exists_section_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (x0 : X) :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set X)) ⟨x0, trivial⟩
    isLocallyClosed_univ
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

/-- **Every fppf covering sieve contains every point with values in an algebraically closed field.** -/
theorem fppf_arrows_of_isAlgClosed {X : Scheme.{u}} {S : Sieve X} (hS : S ∈ Scheme.fppfTopology X)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ X) : S.arrows s := by
  rw [Precoverage.mem_toGrothendieck_iff] at hS
  induction hS with
  | of X R hR =>
    obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hR
    obtain ⟨hsurj, hP⟩ := hR
    obtain ⟨i, y, hy⟩ := hsurj (s (IsLocalRing.closedPoint k))
    haveI : Flat (f i) := (hP i).1
    haveI : LocallyOfFinitePresentation (f i) := (hP i).2
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := s) y
      (IsLocalRing.closedPoint k) hy
    obtain ⟨σ, hσ⟩ := exists_section_of_isAlgClosed (pullback.snd (f i) s) z
    refine ⟨Y i, σ ≫ pullback.fst (f i) s, f i, ⟨i⟩, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  | top X => trivial
  | pullback X S hS Y f ih => exact ih (s ≫ f)
  | transitive X S R hS hR ihS ihR =>
    have h1 := ihR (ihS s) (𝟙 _)
    simpa using h1

/-- `Spec K̄` in `Over (Spec K)`: every fppf covering sieve is the maximal sieve. -/
theorem over_fppf_id_mem {K : Type} [Field K] {S : Sieve (T09Pic.ptK K)}
    (hS : S ∈ (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (T09Pic.ptK K)) :
    S.arrows (𝟙 _) := by
  rw [GrothendieckTopology.mem_over_iff] at hS
  have h := fppf_arrows_of_isAlgClosed hS (k := AlgebraicClosure K) (𝟙 _)
  rw [Sieve.overEquiv_iff] at h
  have h2 := S.downward_closed h
    (Over.homMk (𝟙 (T09Pic.ptK K).left) (by simp) :
      T09Pic.ptK K ⟶ Over.mk (𝟙 _ ≫ (T09Pic.ptK K).hom))
  convert h2 using 1
  ext
  simp

/-- **L5 is a theorem** (`T09Pic.PicPointsAlgClosed`, Kleiman 9.2.5 at `T = Spec K̄`). -/
theorem picPointsAlgClosed : T09Pic.PicPointsAlgClosed := by
  intro K _ A
  constructor
  · intro c c' h
    have hm := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) c c' h
    have := over_fppf_id_mem hm
    simpa [Presheaf.equalizerSieve] using this
  · intro s
    have hm := Presheaf.imageSieve_mem (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (toPicardFunctor A.X.hom) s
    obtain ⟨t, ht⟩ := over_fppf_id_mem hm
    exact ⟨t, by simpa using ht⟩

end PicDict

#print axioms PicDict.picPointsAlgClosed
