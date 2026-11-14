import TailN
namespace HDec
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem carayolR17_ofK5 (h : _root_.LadicCond.CarayolR17') : LadicCond.CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp
  exact h ℓ ιC ιL N χ f ⟨ρ.toHom, ρ.continuous_toHom⟩ p hN hf hs ha hp

set_option maxHeartbeats 8000000 in
theorem eichlerShimuraJ1_ofK5 (h : _root_.LeafModCurves.R16_EichlerShimuraJ1') :
    LeafModCurves.R16_EichlerShimuraJ1' := by
  rintro N χ f J hN hf ⟨X, P₀, aj, hX, hJ⟩
  obtain ⟨h1, A, π, θ, h2⟩ := h N χ f (toAbVarK4 J) hN hf
    ⟨X, P₀, aj, ⟨⟨hX.1.proper, hX.1.smooth, hX.1.geomConnected⟩, hX.2⟩, isJacobianK_of5 hJ⟩
  exact ⟨h1, ofAbVarK4 A, π, θ, h2⟩

end HSyn
end HDec
