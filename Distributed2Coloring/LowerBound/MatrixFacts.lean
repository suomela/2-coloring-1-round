import Mathlib

namespace Distributed2Coloring.LowerBound

open Matrix

/-- Determinant of a `3×3` matrix over a commutative ring, in expanded form. -/
def det3 {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) : R :=
  M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1)
    - M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0)
    + M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

end Distributed2Coloring.LowerBound
