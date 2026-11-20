import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.Index

/-!
# The size of torsion in an extension by a divisible group
-/

namespace SZRaynaud

variable {T G B : Type*} [AddCommGroup T] [AddCommGroup G] [AddCommGroup B]

/-- In a short exact sequence, multiplication by `m` onto the first term
makes the induced sequence of `m`-torsion groups exact. -/
theorem card_torsionBy_of_exact
    (i : T →+ G) (f : G →+ B)
    (hi : Function.Injective i) (hf : Function.Surjective f) (he : i.range = f.ker)
    (m : ℕ) (hm : Function.Surjective (fun t : T => m • t)) :
    Nat.card (AddSubgroup.torsionBy G (m : ℤ)) =
      Nat.card (AddSubgroup.torsionBy T (m : ℤ)) *
        Nat.card (AddSubgroup.torsionBy B (m : ℤ)) := by
  let T' := AddSubgroup.torsionBy T (m : ℤ)
  let G' := AddSubgroup.torsionBy G (m : ℤ)
  let B' := AddSubgroup.torsionBy B (m : ℤ)
  let f' : G' →+ B' := (f.comp G'.subtype).codRestrict B' fun g =>
    AddSubgroup.torsionBy.nsmul_iff.mpr <| by
      change m • f g.1 = 0
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp g.2, map_zero]
  have hker (t : T) : f (i t) = 0 := by
    apply AddMonoidHom.mem_ker.mp
    rw [← he]
    exact ⟨t, rfl⟩
  have hf' : Function.Surjective f' := by
    intro b
    obtain ⟨g, hg⟩ := hf b.1
    have hmg : m • g ∈ i.range := by
      rw [he]
      apply AddMonoidHom.mem_ker.mpr
      rw [map_nsmul, hg, AddSubgroup.torsionBy.nsmul_iff.mp b.2]
    obtain ⟨t, ht⟩ := hmg
    obtain ⟨u, hu⟩ := hm t
    change m • u = t at hu
    refine ⟨⟨g - i u, AddSubgroup.torsionBy.nsmul_iff.mpr ?_⟩, ?_⟩
    · rw [nsmul_sub, ← map_nsmul, hu, ht, sub_self]
    · apply Subtype.ext
      change f (g - i u) = b.1
      rw [map_sub, hg, hker, sub_zero]
  let e : T' → f'.ker := fun t =>
    ⟨⟨i t.1, AddSubgroup.torsionBy.nsmul_iff.mpr <| by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp t.2, map_zero]⟩,
      AddMonoidHom.mem_ker.mpr (Subtype.ext (hker t.1))⟩
  have he' : Function.Bijective e := by
    refine ⟨?_, ?_⟩
    · intro t u h
      apply Subtype.ext
      apply hi
      exact congrArg (fun q : f'.ker => q.1.1) h
    · intro g
      have hg : g.1.1 ∈ i.range := by
        rw [he]
        exact AddMonoidHom.mem_ker.mpr
          (congrArg (fun v : B' => v.1) (AddMonoidHom.mem_ker.mp g.2))
      obtain ⟨t, ht⟩ := hg
      have hmt : m • t = 0 := by
        apply hi
        rw [map_nsmul, ht, AddSubgroup.torsionBy.nsmul_iff.mp g.1.2, map_zero]
      exact ⟨⟨t, AddSubgroup.torsionBy.nsmul_iff.mpr hmt⟩, Subtype.ext (Subtype.ext ht)⟩
  have hcard := Nat.card_congr (Equiv.ofBijective e he')
  rw [hcard]
  exact (AddSubgroup.card_ker_mul_card_of_surjective hf').symm

#print axioms card_torsionBy_of_exact

end SZRaynaud
