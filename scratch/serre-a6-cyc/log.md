# Serre A6 cyclotomic check log

- Base `8ed0590c0cd95dbb16643c338aca466ddb5fb1eb`. The cached remote-tracking
  ref matched. The fetch returned HTTP 403 from the proxy.
- The initial import build was stopped before restoring cache entries with
  matching source closures. Lake then completed each of the five direct
  import targets, starting with `LocalArtin` and
  `ExplicitCyclotomicSymbol.ArtinMap`.
- `lake env lean -j1 ZInQKernel/Contrib/OneProof/ConradSerre/SerreA6CyclotomicCheck.lean`
  passed. [Axiom output](axioms.txt)
- Each build and check ran serially under `MemoryMax=60G`, after checking load
  and available memory with `uptime` and `free -g`.
