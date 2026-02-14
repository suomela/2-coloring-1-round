import Mathlib

import Distributed2Coloring.LowerBound.Correlation
import Distributed2Coloring.LowerBound.N1000000Data
import Distributed2Coloring.LowerBound.N1000000PairTransitivity
import Distributed2Coloring.LowerBound.N1000000StructureConstants
import Distributed2Coloring.LowerBound.N1000000Witness

namespace Distributed2Coloring.LowerBound

namespace N1000000OrbitalBasis

set_option linter.style.longLine false

open scoped BigOperators
open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation
open Distributed2Coloring.LowerBound.N1000000Data
open Distributed2Coloring.LowerBound.N1000000PairTransitivity
open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Witness

abbrev n : Nat := N1000000Data.n
abbrev Q := ℚ
abbrev SymN := Sym n
abbrev V := Vertex n
abbrev G := Correlation.G n
abbrev Mask := Distributed2Coloring.LowerBound.Mask
abbrev DirIdx := N1000000StructureConstants.DirIdx

abbrev i0 : Fin 3 := ⟨0, by decide⟩
abbrev i1 : Fin 3 := ⟨1, by decide⟩
abbrev i2 : Fin 3 := ⟨2, by decide⟩

abbrev s0 : SymN := ⟨0, by decide⟩
abbrev s1 : SymN := ⟨1, by decide⟩
abbrev s2 : SymN := ⟨2, by decide⟩

def baseTuple : Tuple 3 n
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2

theorem baseTuple_injective : Function.Injective baseTuple := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [baseTuple] at hij <;> cases hij <;> rfl

def baseVertex : V :=
  ⟨baseTuple, baseTuple_injective⟩

def baseSet : Finset SymN :=
  insert s0 (insert s1 (insert s2 ∅))

def outside (x : SymN) : Prop := x ∉ baseSet

instance : DecidablePred outside := by
  intro x
  unfold outside
  infer_instance

abbrev OutsideSym := { x : SymN // outside x }

-- The directed orbital basis matrices, in the `N[k][a][d]` convention:
-- `A_d[u,v] = 1` iff the directed overlap mask of the ordered pair `(v,u)` is `maskAt d`.
def A (d : DirIdx) : Matrix V V Q :=
  fun u v => if dirMask v u = maskAt d then 1 else 0

@[simp] theorem A_apply (d : DirIdx) (u v : V) :
    A d u v = (if dirMask v u = maskAt d then 1 else 0) := rfl

-- The symmetric orbital basis element corresponding to a directed type `d`.
def ASymm (d : DirIdx) : Matrix V V Q :=
  if h : tTr[d.1]! = d.1 then
    A d
  else
    A d + A ⟨tTr[d.1]!, by
      -- `tTr` is a permutation of the 34 indices.
      fin_cases d <;> decide⟩

end N1000000OrbitalBasis

end Distributed2Coloring.LowerBound
