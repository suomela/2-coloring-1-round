import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

set_option maxHeartbeats 200000000 in
-- This proof is a large `decide` check; we increase `maxHeartbeats` to avoid timeouts.
theorem s0IntGoal_block6 :
    ∀ p q : Fin 3, S0IntGoal (r := (⟨6, by decide⟩ : Block)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
