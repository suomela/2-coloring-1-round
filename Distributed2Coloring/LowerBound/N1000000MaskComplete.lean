import Mathlib

import Distributed2Coloring.LowerBound.N1000000StructureConstants
import Distributed2Coloring.LowerBound.N1000000Witness
import Distributed2Coloring.LowerBound.OverlapType

namespace Distributed2Coloring.LowerBound

namespace N1000000MaskComplete

set_option linter.style.longLine false

open Distributed2Coloring.LowerBound.N1000000StructureConstants
open Distributed2Coloring.LowerBound.N1000000Witness

abbrev Mask := Distributed2Coloring.LowerBound.Mask
abbrev DirIdx := N1000000StructureConstants.DirIdx

instance : DecidablePred IsPartialPermMask := by
  intro m
  unfold IsPartialPermMask
  infer_instance

def partialPermMasks : Finset Mask :=
  (Finset.range (1 <<< 9)).filter IsPartialPermMask

-- A one-time, finite check: the witness-provided `masks` list is exactly the 34 partial
-- permutation masks in `0..2^9`.
set_option maxRecDepth 2000 in
theorem masks_toFinset_eq_partialPermMasks :
    (masks.toList.toFinset : Finset Mask) = partialPermMasks := by
  decide

theorem mem_masks_toFinset_of_isPartialPermMask {m : Mask} (hm : m < (1 <<< 9))
    (hperm : IsPartialPermMask m) : m ∈ (masks.toList.toFinset : Finset Mask) := by
  have hm' : m < 512 := by simpa using hm
  have hmemb : m ∈ partialPermMasks := by
    simp [partialPermMasks, hm', hperm]
  -- Rewrite the goal using the finite-check equality and finish.
  -- (`rw` keeps the goal in membership form, rather than expanding it to a disjunction.)
  -- (Using `simpa` alone here can unfold membership in `masks.toList.toFinset`.)
  rw [masks_toFinset_eq_partialPermMasks]
  exact hmemb

theorem maskAt_injective : Function.Injective (maskAt : DirIdx → Mask) := by
  decide

theorem exists_dirIdx_of_isPartialPermMask {m : Mask} (hm : m < (1 <<< 9))
    (hperm : IsPartialPermMask m) : ∃ d : DirIdx, maskAt d = m := by
  classical
  -- Convert membership in `toFinset` back to membership in the list.
  have hmemFinset : m ∈ (masks.toList.toFinset : Finset Mask) :=
    mem_masks_toFinset_of_isPartialPermMask (m := m) hm hperm
  have hmemList : m ∈ masks.toList := by
    simpa [List.mem_toFinset] using hmemFinset
  -- Extract an index `i` with `masks.toList[i] = m`.
  rcases (List.mem_iff_get).1 hmemList with ⟨i, hi⟩
  have hiLt : i.1 < masks.size := by
    exact i.2
  have hList : masks.toList[i.1] = m := by
    simpa [List.get_eq_getElem] using hi
  have hToList : masks.toList[i.1] = masks[i.1] := Array.getElem_toList (xs := masks) (i := i.1) hiLt
  have hArr : masks[i.1] = m := by
    exact hToList.symm.trans hList
  refine ⟨⟨i.1, hiLt⟩, ?_⟩
  simpa [maskAt, hiLt] using hArr

end N1000000MaskComplete

end Distributed2Coloring.LowerBound
