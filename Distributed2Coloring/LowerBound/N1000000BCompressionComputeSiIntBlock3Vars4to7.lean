import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `4`.
theorem siIntGoal_block3_var4 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨4, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `5`.
theorem siIntGoal_block3_var5 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨5, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `6`.
theorem siIntGoal_block3_var6 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨6, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `7`.
theorem siIntGoal_block3_var7 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨7, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
