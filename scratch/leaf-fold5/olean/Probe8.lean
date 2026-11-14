import TailN
namespace HDec
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 8000000 in
theorem r03LinYang_ofK5 (h : _root_.ZInQ.LeafPush2.R03_LinYang) : ZInQ.LeafPush2.R03_LinYang := by
  intro A q hA
  rcases h (toAbVarK4 A) ⟨q.iota, q.injective⟩ hA with
    ⟨j, a, r, hj, hg, hl, C, hC, hI, hS, P₀, J, aj, hJ, e, he⟩ | ⟨E₁, E₂, h1, h2, hE⟩
  · exact Or.inl ⟨j, a, r, hj, hg, hl, C, ⟨hC.proper, hC.smooth, hC.geomConnected⟩, hI, hS, P₀,
      ofAbVarK4 J, aj, ⟨hJ.base, fun B f hf => hJ.univ (toAbVarK4 B) f hf⟩, e, he⟩
  · exact Or.inr ⟨ofAbVarK4 E₁, ofAbVarK4 E₂, h1, h2, hE⟩

end HSyn
end HDec
