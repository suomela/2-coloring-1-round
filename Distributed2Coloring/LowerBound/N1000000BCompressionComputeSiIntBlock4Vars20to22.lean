import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `20`.
theorem siIntGoal_block4_var20 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨20, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `21`.
theorem siIntGoal_block4_var21 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨21, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `22`.
theorem siIntGoal_block4_var22 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨22, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
