import ZInQKernel.Compiler.NodeSkeleton.Static
import ZInQKernel.Compiler.NodeSkeleton.Data.Oracle

/-!
# The global checks of the pinned hubs and lanes, by the kernel
-/

namespace ZInQ.Compiler.NodeSkeleton

theorem static_sorted : sortedHubsB (hubsAll hubsData) = true := by decide +kernel

theorem static_lim : hubsLimB limsData hubsData = true := by decide +kernel

theorem static_first : firstHubGe 2 hubsData = true := by decide +kernel

theorem static_len : lanesLenB 5 lanesData = true := by decide +kernel

theorem static_lane0 : laneOKB hubsData lanesData 0 = true := by decide +kernel

theorem static_lane1 : laneOKB hubsData lanesData 1 = true := by decide +kernel

theorem static_lane2 : laneOKB hubsData lanesData 2 = true := by decide +kernel

theorem static_lane3 : laneOKB hubsData lanesData 3 = true := by decide +kernel

theorem static_lane4 : laneOKB hubsData lanesData 4 = true := by decide +kernel

end ZInQ.Compiler.NodeSkeleton
