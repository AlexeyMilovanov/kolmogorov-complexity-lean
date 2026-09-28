import KolmogorovMathlib.Restricted.EffectiveSelection.Part01
import KolmogorovMathlib.Restricted.EffectiveSelection.Part02
import KolmogorovMathlib.Restricted.Selection

/-!
# The effective marked-code stream of a family

Group of the effective version of the greedy selection: `Part01` builds the candidate model codes
enumerated by a family and proves the machinery primitive recursive, `Part02` bounds the length
of the resulting marked code stream and shows it still covers every string with many
descriptions. The finite-stage selection lemmas these make effective come from the selection
module imported alongside.
-/
