import Mathlib

import Distributed2Coloring.LowerBound.N1000000StructureConstants

namespace Distributed2Coloring.LowerBound

namespace N1000000MaskAtFacts

open Distributed2Coloring.LowerBound.N1000000StructureConstants

abbrev Mask := Distributed2Coloring.LowerBound.Mask
abbrev DirIdx := N1000000StructureConstants.DirIdx

theorem maskAt_testBit_eq_decide_colMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (colMatch (maskAt d) j = some i) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

theorem maskAt_testBit_eq_decide_rowMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

end N1000000MaskAtFacts

end Distributed2Coloring.LowerBound

