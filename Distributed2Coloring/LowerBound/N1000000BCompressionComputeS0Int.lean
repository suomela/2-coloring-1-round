import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock0
import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock1
import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock2
import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock3
import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock4
import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock5
import Distributed2Coloring.LowerBound.N1000000BCompressionComputeS0IntBlock6

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

theorem s0IntGoal_all (r : Block) (p q : Fin 3) : S0IntGoal r p q := by
  fin_cases r <;> first
    | simpa using (s0IntGoal_block0 (p := p) (q := q))
    | simpa using (s0IntGoal_block1 (p := p) (q := q))
    | simpa using (s0IntGoal_block2 (p := p) (q := q))
    | simpa using (s0IntGoal_block3 (p := p) (q := q))
    | simpa using (s0IntGoal_block4 (p := p) (q := q))
    | simpa using (s0IntGoal_block5 (p := p) (q := q))
    | simpa using (s0IntGoal_block6 (p := p) (q := q))

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound

