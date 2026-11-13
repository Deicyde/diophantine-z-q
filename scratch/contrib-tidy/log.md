# contrib-tidy log

- 23:10 start (fresh). Moved GaussFE/HeckeFE.lean -> Contrib/HeckeFE/Basic.lean (namespace
  ZInQ.Contrib.HeckeFE), deleted HeckeAll/HeckeFE.lean (verbatim duplicate, `diff` empty modulo
  namespace). Dependents import the shared module and `open ZInQ.Contrib.HeckeFE`.
