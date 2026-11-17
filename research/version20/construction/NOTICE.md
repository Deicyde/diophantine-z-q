# Construction provenance

The six data files in `INPUTS.json` are unchanged selections from Gemini 4
Carbon's `20261117-0035` explicit247 package. They build on José Brox's
construction and the Version 19 arithmetic specialization at `N = 10220`.
The original 244-coordinate source is byte-identical to the retained Version 19
input. The Version 19 input inventory and its notices retain the provenance of
Brox's sources and the earlier Conant construction.

The Version 20 manuscript text and finite checkers were written by OpenAI
Codex's 6 Astra. `verify250_retained.py` strengthens the project's Version 19
checker without changing that released file. The other new checkers independently
read the supplied data; they do not execute Carbon's construction programs.

The data permit exact verification of the rational coordinate scaling,
invertible row operation, permutation, ladder, expansion and text size. These
checks do not replace the manuscript's arithmetic proof or its independent
review. No claim about impossibility with fewer than 247 variables is imported
from the package.
