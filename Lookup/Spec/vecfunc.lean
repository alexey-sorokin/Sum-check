import SumCheck.Spec.evalAndSum
import SumCheck.Spec.completenessSoundness_updated

noncomputable section
open Classical
open SumCheck

namespace Lookup

universe u
variable {F : Type u} [Field F]

-- Use SumCheck’s definitions directly:
abbrev vec := SumCheck.vec
abbrev func := SumCheck.func

abbrev funcSumTotal := SumCheck.funcSumTotal

end Lookup
