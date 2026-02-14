import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `8`.
theorem siIntGoal_block2_var8 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨8, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `9`.
theorem siIntGoal_block2_var9 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨9, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `10`.
theorem siIntGoal_block2_var10 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨10, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `2` and variable `11`.
theorem siIntGoal_block2_var11 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨2, by decide⟩ : Block)) (i := (⟨11, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
