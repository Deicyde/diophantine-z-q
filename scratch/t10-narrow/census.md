Base: `7c092f8c3753f783037df1d31a7253feb70fa323`. All paths are relative to the repository root. Each row below is **VERIFIED** by the corresponding proof term or source line. The `K` column means the field binder of `T10_TateDuality`, rather than the manuscript's auxiliary field `K`. Every `F` is a finite extension of `ℚ_p`. “Via” records the first call that passes the hypothesis onward.

| Declaration | Source (declaration / read) | Old T10 instance `(K, ℓ, g)` | Read |
|---|---|---|---|
| `dual_of_H1` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:102` / `:110` | `(F, p, dim A)`, any | **Direct application** to `F (toKer A) p hp` |
| `htDecomp_of_H1` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:138` / `:150` | `(F, p, g)`, any | Via `dual_of_H1` |
| `dual_deRham_of_scholzeH1` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:163` / `:168` | `(F, p, dim A)`, any | Via `dual_of_H1` |
| `deRhamVpAbVarDirect_of_scholzeH1` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:173` / `:176` | `(F, p, dim A)`, any | Via `dual_deRham_of_scholzeH1` |
| `deRhamVpAbVarDirect_of_scholzeH1Milne` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:179` / `:181` | `(F, p, dim A)`, any | Via `deRhamVpAbVarDirect_of_scholzeH1` |
| `hodgeTateDecompHom_of_scholzeH1` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:184` / `:187` | `(F, p, dim A)`, any | Via `dual_deRham_of_scholzeH1` |
| `hodgeTateDecompOr_of_scholzeH1Milne` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:192` / `:194` | `(F, p, dim A)`, any | Via `hodgeTateDecompHom_of_scholzeH1` |
| `hodgeTateDecompAbVar_of_scholzeH1` | `ZInQKernel/Contrib/OneProof/ScholzeH1AbVar.lean:199` / `:201` | `(F, p, g)`, any | Via `htDecomp_of_H1` |
| `openResearchLeaves60_y3x6_of_OpenResearchLeaves63_nos` | `ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4681` / `:4691` | `(F, p, dim A)`, any | **Projection** into `hodgeTateDecompOr_of_scholzeH1Milne` |
| `sixContactMin_of_open82_nos` | `ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4716` / `:4728` | `(F, p, g)`, any | **Projection** into `hodgeTateDecompAbVar_of_scholzeH1` |
| `openResearchLeaves65_of_OpenResearchLeaves66` | `ZInQKernel/OneProof/H/TailZ92.lean:67` / `:76` | `(F, p, dim A)`, any | **Projection** into `deRhamVpAbVarDirect_of_scholzeH1Milne` |

| Declaration that forwards the bundle | Source | Inherited instances |
|---|---|---|
| `sixContactMin_of_open83_nos` | `ZInQKernel/Contrib/OneProof/NOSNarrowChain.lean:4837` | `(F, p, g)`, any, via `open82_nos` |
| `sixContactMin_of_open84` | `ZInQKernel/OneProof/H/TailZ91.lean:105` | Same, via `open83_nos` |
| `sixContactMin_of_open85` | `ZInQKernel/OneProof/H/TailZ92.lean:98` | Same, via `open84` and the de Rham reader at line 76 |
| `sixContactMin_of_open86` | `ZInQKernel/OneProof/H/TailZ93.lean:96` | Same, via `open85` |
| `ZInQ.OneProof.frozenTarget` | `ZInQKernel/OneProof/Main.lean:214` | Same, via `open86` |

The projection is declared at `ZInQKernel/OneProof/H/TailZ87.lean:75`. The C8 extractor at that file's line 109 consumes the carrier but reads only `conradAppB`. The older TailZ87–89 uses of the projection and the other compatibility statements in `ScholzeH1AbVar.lean:204` and `:226` are outside this proof closure. Textual occurrences in legacy T10 bundles or helpers are not additional readers of the current headline.
