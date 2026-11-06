import ZInQKernel.Syntax.Templates.Scope
import ZInQKernel.Syntax.Templates.Member
import ZInQKernel.Syntax.Templates.Core
import ZInQKernel.Syntax.Templates.Certificate
import ZInQKernel.Syntax.Templates.Multiply
import ZInQKernel.Syntax.Templates.Value
import ZInQKernel.Syntax.Templates.Library

/-!
# The template library of the specification

Root module of the template library (blueprint chapter `syntax/`, the template articles).
Every template is a `Build` program transcribing the corresponding builder of
`construction/*.js` with the same parameter order and witness layout; for each template the
parameter and witness counts, well-formedness and the relation in terms of its formula are
proved.
-/
