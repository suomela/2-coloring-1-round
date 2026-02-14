import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `12`.
theorem siIntGoal_block4_var12 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨12, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `13`.
theorem siIntGoal_block4_var13 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨13, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `14`.
theorem siIntGoal_block4_var14 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨14, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `4` and variable `15`.
theorem siIntGoal_block4_var15 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨4, by decide⟩ : Block)) (i := (⟨15, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
