import Mathlib

import Distributed2Coloring.LowerBound.N1000000BCompressionComputeSiIntGoal

namespace Distributed2Coloring.LowerBound

namespace N1000000BCompressionCompute

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `16`.
theorem siIntGoal_block3_var16 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨16, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `17`.
theorem siIntGoal_block3_var17 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨17, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `18`.
theorem siIntGoal_block3_var18 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨18, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

set_option maxHeartbeats 300000000 in
-- Kernel-checked computation for the 9 entries of `SiIntGoal` at block `3` and variable `19`.
theorem siIntGoal_block3_var19 :
    ∀ p q : Fin 3,
      SiIntGoal (r := (⟨3, by decide⟩ : Block)) (i := (⟨19, by decide⟩ : Var)) p q := by
  intro p q
  fin_cases p <;> fin_cases q <;> decide

end N1000000BCompressionCompute

end Distributed2Coloring.LowerBound
