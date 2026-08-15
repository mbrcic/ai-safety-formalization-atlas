module

public import Aesop

/-!
# The `inference` aesop rule set

Aesop rule sets are not visible in the file that declares them, so the
declaration has to sit one import away from the attributes that use it. This
module is that one line; the rules themselves are in
`AISafetyAtlas.Inference.Search`.
-/

declare_aesop_rule_sets [inference]
