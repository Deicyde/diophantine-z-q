import ZInQKernel.HDecomp.Objects
namespace HDec.Foo
open _root_.PkgI2 (IsAbelianVariety)
#check @IsAbelianVariety.proper
end HDec.Foo
namespace HDec.PkgI2 export _root_.PkgI2 (IsAbelianVariety) end HDec.PkgI2
namespace HDec.Bar
open PkgI2
#check @IsAbelianVariety.proper
#check @PkgI2.IsAbelianVariety.proper
end HDec.Bar
