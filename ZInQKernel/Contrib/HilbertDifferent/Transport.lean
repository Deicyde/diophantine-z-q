/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

Adapted from TauCetiProject/TauCeti at a6027b1d24fcb935c53bd5b50d11b40991cda418:
 RingTheory/LocalRing/RamificationGroup.lean, lines 692–712;
 RingTheory/Ideal/RamificationGroup.lean, lines 80–104;
 NumberTheory/NumberField/LocalGlobal/RamificationGroup.lean, lines 139–146.
The transport argument is generalized to explicitly named ideals and equivariant
ring maps. The actual completion/decomposition maps and their hypotheses are
NOT supplied by this file. No local/global comparison is silently assumed.
See docs/research/t20-hilbert-different.md for the source license and scope.
-/
import ZInQKernel.Contrib.HilbertDifferent.Global

namespace ZInQ.Contrib.HilbertDifferent

open scoped Pointwise

section CongruenceTransport

variable {G H B C : Type*} [Group G] [Group H] [CommRing B] [CommRing C]
  [MulSemiringAction G B] [MulSemiringAction H C]

/-- Power-ideal inertia is transported by an equivariant map which identifies ideal-power
preimages and is surjective modulo each power. Preservation of the target powers is explicit.
This is a comparison theorem, not the construction of the arithmetic completion maps. -/
theorem powerInertia_eq_comap_of_equivariant_dense (P : Ideal B) (Q : Ideal C)
    (φ : G →* H) (f : B →+* C)
    (hequiv : ∀ (g : G) (x : B), f (g • x) = φ g • f x)
    (hcomap : ∀ n : ℕ, (Q ^ n).comap f = P ^ n)
    (hpres : ∀ (g : G) (n : ℕ) (y : C), y ∈ Q ^ n → φ g • y ∈ Q ^ n)
    (hdense : ∀ (n : ℕ) (y : C), ∃ x : B, y - f x ∈ Q ^ n) (i : ℕ) :
    (P ^ (i + 1)).inertia G = ((Q ^ (i + 1)).inertia H).comap φ := by
  ext σ
  rw [Subgroup.mem_comap, Ideal.mem_inertia, Ideal.mem_inertia]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := hdense (i + 1) y
    have hσx : f (σ • x - x) ∈ Q ^ (i + 1) := by
      rw [← Ideal.mem_comap, hcomap]
      exact h x
    have hsplit : φ σ • y - y = φ σ • (y - f x) + f (σ • x - x) - (y - f x) := by
      rw [map_sub, hequiv, smul_sub]
      ring
    rw [hsplit]
    exact sub_mem (add_mem (hpres σ (i + 1) _ hx) hσx) hx
  · intro h x
    rw [← hcomap, Ideal.mem_comap, map_sub, hequiv]
    exact h (f x)

/-- A specified group equivalence with the congruence comparison above preserves the orders
of all the nonnegative-index ramification groups. -/
theorem card_powerInertia_eq_of_equivariant_dense (P : Ideal B) (Q : Ideal C)
    (e : G ≃* H) (f : B →+* C)
    (hequiv : ∀ (g : G) (x : B), f (g • x) = e g • f x)
    (hcomap : ∀ n : ℕ, (Q ^ n).comap f = P ^ n)
    (hpres : ∀ (g : G) (n : ℕ) (y : C), y ∈ Q ^ n → e g • y ∈ Q ^ n)
    (hdense : ∀ (n : ℕ) (y : C), ∃ x : B, y - f x ∈ Q ^ n) (i : ℕ) :
    Nat.card ((P ^ (i + 1)).inertia G) = Nat.card ((Q ^ (i + 1)).inertia H) := by
  have hmap : ((P ^ (i + 1)).inertia G).map e.toMonoidHom = (Q ^ (i + 1)).inertia H := by
    rw [powerInertia_eq_comap_of_equivariant_dense P Q e.toMonoidHom f
      hequiv hcomap hpres hdense i]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  calc
    Nat.card ((P ^ (i + 1)).inertia G) =
        Nat.card (((P ^ (i + 1)).inertia G).map e.toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv
    _ = _ := by rw [hmap]

end CongruenceTransport

/-- Restriction to a subgroup preserves the defining ideal-power congruence. -/
theorem powerInertia_subgroupOf {G B : Type*} [Group G] [CommRing B]
    [MulSemiringAction G B] (P : Ideal B) (i : ℕ) (D : Subgroup G) :
    ((P ^ (i + 1)).inertia G).subgroupOf D = (P ^ (i + 1)).inertia D := by
  ext σ
  simp only [Subgroup.mem_subgroupOf, Ideal.mem_inertia, Subgroup.smul_def]

open NumberField

/-- The actual global lower groups lie in the decomposition group at `P`. -/
theorem ramGroup_le_stabilizer (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) (i : ℕ) :
    GlueConductor.ramGroup L P i ≤ MulAction.stabilizer Gal(L/ℚ) P := by
  have hzero : GlueConductor.ramGroup L P 0 = P.inertia Gal(L/ℚ) := by
    simp only [GlueConductor.ramGroup, zero_add, pow_one]
  exact ((ramGroup_antitone L P (Nat.zero_le i)).trans_eq hzero).trans
    (Ideal.inertia_le_stabilizer P)

/-- Counting the actual global group inside the decomposition group introduces no degree
factor. This is the restriction step needed before applying a completion group equivalence. -/
theorem ramCard_eq_card_powerInertia_stabilizer (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) (i : ℕ) :
    GlueConductor.ramCard L P i =
      Nat.card ((P ^ (i + 1)).inertia (MulAction.stabilizer Gal(L/ℚ) P)) := by
  rw [← powerInertia_subgroupOf]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ramGroup_le_stabilizer L P i)).symm.toEquiv

end ZInQ.Contrib.HilbertDifferent
