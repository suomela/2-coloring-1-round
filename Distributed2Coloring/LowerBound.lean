/-
# `Distributed2Coloring.LowerBound` (entry point)

This module is the intended human-facing import for the Lean formalization of the `n = 1,000,000`
lower bound.

For the main statement and its meaning:

- Main theorem: `Distributed2Coloring.LowerBound.N1000000.monoFraction_ge_23879`
  (see `Distributed2Coloring/LowerBound/N1000000Main.lean`).
- Graph / coloring definitions: `Vertex`, `Edge`, `Coloring`, `monoFraction`, `Edge.monochromatic`
  (see `Distributed2Coloring/LowerBound/Defs.lean`).

If you just want to check the statement in Lean:

```
import Distributed2Coloring.LowerBound
#check Distributed2Coloring.LowerBound.N1000000.monoFraction_ge_23879
```
-/

import Distributed2Coloring.LowerBound.Defs
import Distributed2Coloring.LowerBound.MatrixFacts
import Distributed2Coloring.LowerBound.OverlapType
import Distributed2Coloring.LowerBound.N1000000Data
import Distributed2Coloring.LowerBound.N1000000ZData
import Distributed2Coloring.LowerBound.N1000000Z
import Distributed2Coloring.LowerBound.Certificate
import Distributed2Coloring.LowerBound.CorrAvgMatrix
import Distributed2Coloring.LowerBound.N1000000WeakDuality
import Distributed2Coloring.LowerBound.N1000000Relaxation
import Distributed2Coloring.LowerBound.N1000000RelaxationPsdSoundness
import Distributed2Coloring.LowerBound.N1000000MuLinear
import Distributed2Coloring.LowerBound.N1000000Objective
import Distributed2Coloring.LowerBound.N1000000CorrAvgMatrixSymmDecompose
import Distributed2Coloring.LowerBound.N1000000Bound
import Distributed2Coloring.LowerBound.N1000000Main
