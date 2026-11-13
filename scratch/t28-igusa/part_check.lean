
/-! ## Spot checks of the M3 identities in Lean (one sextic, the two highest-degree entries) -/

namespace PkgI1
open T28SO3

theorem spot_J : J2 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -896 ∧
    J4 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = 6976 ∧ J6 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -303616 ∧
    J10 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -2288538368 := by
  refine ⟨by norm_num [J2], by norm_num [J4], by norm_num [J6], ?_⟩
  decide +kernel

example : pair (yv (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] 2) (yv ![2, -1, 3, 0, 1, -2, 1] 2) =
    gramJ (-896) 6976 (-303616) (-2288538368) 2 2 := by
  norm_num [pair, yv, y3c0, y3c1, y3c2, y3c0_0, y3c0_1, y3c0_2, y3c0_3, y3c0_4, y3c1_0, y3c1_1, y3c1_2, y3c1_3, y3c1_4, y3c2_0, y3c2_1, y3c2_2, y3c2_3, y3c2_4, gramJ, m3G33]

example : p6 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] (cub (yv ![2, -1, 3, 0, 1, -2, 1] 2)
    (yv ![2, -1, 3, 0, 1, -2, 1] 2) (yv ![2, -1, 3, 0, 1, -2, 1] 2)) =
    cubJ (-896) 6976 (-303616) (-2288538368) 2 2 2 := by
  norm_num [p6, cub, yv, y3c0, y3c1, y3c2, y3c0_0, y3c0_1, y3c0_2, y3c0_3, y3c0_4, y3c1_0, y3c1_1, y3c1_2, y3c1_3, y3c1_4, y3c2_0, y3c2_1, y3c2_2, y3c2_3, y3c2_4, cubJ, m3a333]

end PkgI1
