import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Fin

import Distributed2Coloring.LowerBound.Defs
import Distributed2Coloring.LowerBound.EdgePatterns

namespace Distributed2Coloring.LowerBound

/-!
Small “sanity checks” intended to validate that the Lean definitions in `Defs.lean` match the
intended combinatorial model.

This file proves, in a fully kernel-checked way, that for `n = 5` there is an explicit coloring
with monochromatic edge fraction exactly `1/5`.
-/

namespace Sanity

open Distributed2Coloring.LowerBound

/-- Local rule from the report: `g(0,0,0)=1`, `g(1,1,1)=0`, otherwise `g(x,y,z)=y`. -/
def g : Bool → Bool → Bool → Bool
  | false, false, false => true
  | true, true, true => false
  | _, y, _ => y

/-!
## `n = 5`

We split the symbols into `{0,1}` (“small”) and `{2,3,4}` (“big”), round to a bit, and apply `g`.
This yields `24` monochromatic edges out of `120`, hence `monoFraction = 1/5`.
-/

abbrev two5 : Sym 5 := ⟨2, by decide⟩
abbrev Small5 : Type := Set.Iio two5
abbrev Big5 : Type := Set.Ici two5

def round5 (a : Sym 5) : Bool :=
  decide (two5 ≤ a)

@[simp] lemma round5_eq_true {a : Sym 5} : round5 a = true ↔ two5 ≤ a := by
  simp [round5]

@[simp] lemma round5_eq_false {a : Sym 5} : round5 a = false ↔ a < two5 := by
  simp [round5, not_le]

abbrev f5 : Coloring 5 :=
  fun v => g (round5 (Vertex.a v)) (round5 (Vertex.b v)) (round5 (Vertex.c v))

@[simp] lemma card_Small5 : Fintype.card Small5 = 2 := by
  simp [Small5, two5]

@[simp] lemma card_Big5 : Fintype.card Big5 = 3 := by
  simp [Big5, two5]

lemma g_eq_iff_patterns (x y z w : Bool) :
    g x y z = g y z w ↔
      (x = false ∧ y = false ∧ z = false ∧ w = false) ∨
      (x = true ∧ y = true ∧ z = true ∧ w = true) ∨
      (x = true ∧ y = false ∧ z = false ∧ w = true) ∨
      (x = false ∧ y = true ∧ z = true ∧ w = false) := by
  cases x <;> cases y <;> cases z <;> cases w <;> decide

private lemma not_all_small (e : Edge 5) : ¬ (∀ i : Fin 4, e.1 i < two5) := by
  classical
  intro hall
  let emb : Fin 4 ↪ Small5 :=
    { toFun := fun i => ⟨e.1 i, hall i⟩
      inj' := by
        intro i j hij
        apply e.2
        exact congrArg Subtype.val hij }
  have hle : Fintype.card (Fin 4) ≤ Fintype.card Small5 :=
    Fintype.card_le_of_embedding emb
  -- Turn the card inequality into a numeral contradiction.
  simp only [Fintype.card_fin, card_Small5] at hle
  exact (by decide : ¬(4 : Nat) ≤ 2) hle

private lemma not_all_big (e : Edge 5) : ¬ (∀ i : Fin 4, two5 ≤ e.1 i) := by
  classical
  intro hall
  let emb : Fin 4 ↪ Big5 :=
    { toFun := fun i => ⟨e.1 i, hall i⟩
      inj' := by
        intro i j hij
        apply e.2
        exact congrArg Subtype.val hij }
  have hle : Fintype.card (Fin 4) ≤ Fintype.card Big5 :=
    Fintype.card_le_of_embedding emb
  simp only [Fintype.card_fin, card_Big5] at hle
  exact (by decide : ¬(4 : Nat) ≤ 3) hle

@[simp] private lemma srcIndex_0 : Edge.srcIndex (0 : Fin 3) = (0 : Fin 4) := by
  ext; rfl

@[simp] private lemma srcIndex_1 : Edge.srcIndex (1 : Fin 3) = (1 : Fin 4) := by
  ext; rfl

@[simp] private lemma srcIndex_2 : Edge.srcIndex (2 : Fin 3) = (2 : Fin 4) := by
  ext; rfl

@[simp] private lemma dstIndex_0 : Edge.dstIndex (0 : Fin 3) = (1 : Fin 4) := by
  ext; rfl

@[simp] private lemma dstIndex_1 : Edge.dstIndex (1 : Fin 3) = (2 : Fin 4) := by
  ext; rfl

@[simp] private lemma dstIndex_2 : Edge.dstIndex (2 : Fin 3) = (3 : Fin 4) := by
  ext; rfl

private lemma monochromatic_iff_bits (e : Edge 5) :
    Edge.monochromatic f5 e ↔
      g (round5 (e.1 0)) (round5 (e.1 1)) (round5 (e.1 2))
        =
      g (round5 (e.1 1)) (round5 (e.1 2)) (round5 (e.1 3)) := by
  classical
  unfold Edge.monochromatic f5
  -- Expand the definition of `Edge.src`/`Edge.dst` and evaluate the `Fin 3` indices.
  simp [Edge.src, Edge.dst, Vertex.a, Vertex.b, Vertex.c, g, round5]

private def pat1001 (e : Edge 5) : Prop :=
  two5 ≤ e.1 0 ∧ e.1 1 < two5 ∧ e.1 2 < two5 ∧ two5 ≤ e.1 3

private def pat0110 (e : Edge 5) : Prop :=
  e.1 0 < two5 ∧ two5 ≤ e.1 1 ∧ two5 ≤ e.1 2 ∧ e.1 3 < two5

private instance : DecidablePred pat1001 := by
  intro e
  dsimp [pat1001]
  infer_instance

private instance : DecidablePred pat0110 := by
  intro e
  dsimp [pat0110]
  infer_instance

private lemma monochromatic_iff_pat (e : Edge 5) :
    Edge.monochromatic f5 e ↔ pat1001 e ∨ pat0110 e := by
  have hbits := monochromatic_iff_bits (e := e)
  have hpatBits :
      (g (round5 (e.1 0)) (round5 (e.1 1)) (round5 (e.1 2))
          =
        g (round5 (e.1 1)) (round5 (e.1 2)) (round5 (e.1 3)))
        ↔
      (round5 (e.1 0) = false ∧ round5 (e.1 1) = false ∧ round5 (e.1 2) = false ∧
          round5 (e.1 3) = false) ∨
      (round5 (e.1 0) = true ∧ round5 (e.1 1) = true ∧ round5 (e.1 2) = true ∧
          round5 (e.1 3) = true) ∨
      (round5 (e.1 0) = true ∧ round5 (e.1 1) = false ∧ round5 (e.1 2) = false ∧
          round5 (e.1 3) = true) ∨
      (round5 (e.1 0) = false ∧ round5 (e.1 1) = true ∧ round5 (e.1 2) = true ∧
          round5 (e.1 3) = false) := by
    simpa using
      (g_eq_iff_patterns (x := round5 (e.1 0)) (y := round5 (e.1 1))
        (z := round5 (e.1 2)) (w := round5 (e.1 3)))
  constructor
  · intro hmono
    have hcases := (hpatBits.mp (hbits.mp hmono))
    rcases hcases with hall0 | hall1 | hall2 | hall3
    · -- all bits `false` is impossible for an injective 4-tuple into `Small5` (only 2 elements)
      have ha : e.1 0 < two5 := by simpa [round5_eq_false] using hall0.1
      have hb : e.1 1 < two5 := by simpa [round5_eq_false] using hall0.2.1
      have hc : e.1 2 < two5 := by simpa [round5_eq_false] using hall0.2.2.1
      have hd : e.1 3 < two5 := by simpa [round5_eq_false] using hall0.2.2.2
      have hall : ∀ i : Fin 4, e.1 i < two5 := by
        intro i; fin_cases i <;> assumption
      exact False.elim (not_all_small (e := e) hall)
    · -- all bits `true` is impossible for an injective 4-tuple into `Big5` (only 3 elements)
      have ha : two5 ≤ e.1 0 := by simpa [round5_eq_true] using hall1.1
      have hb : two5 ≤ e.1 1 := by simpa [round5_eq_true] using hall1.2.1
      have hc : two5 ≤ e.1 2 := by simpa [round5_eq_true] using hall1.2.2.1
      have hd : two5 ≤ e.1 3 := by simpa [round5_eq_true] using hall1.2.2.2
      have hall : ∀ i : Fin 4, two5 ≤ e.1 i := by
        intro i; fin_cases i <;> assumption
      exact False.elim (not_all_big (e := e) hall)
    · -- pattern 1001
      left
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [round5_eq_true] using hall2.1
      · simpa [round5_eq_false] using hall2.2.1
      · simpa [round5_eq_false] using hall2.2.2.1
      · simpa [round5_eq_true] using hall2.2.2.2
    · -- pattern 0110
      right
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [round5_eq_false] using hall3.1
      · simpa [round5_eq_true] using hall3.2.1
      · simpa [round5_eq_true] using hall3.2.2.1
      · simpa [round5_eq_false] using hall3.2.2.2
  · rintro (h1001 | h0110)
    · have hall2 :
        (round5 (e.1 0) = true ∧ round5 (e.1 1) = false ∧ round5 (e.1 2) = false ∧
            round5 (e.1 3) = true) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [round5_eq_true] using h1001.1
        · simpa [round5_eq_false] using h1001.2.1
        · simpa [round5_eq_false] using h1001.2.2.1
        · simpa [round5_eq_true] using h1001.2.2.2
      have heq :=
        (g_eq_iff_patterns (x := round5 (e.1 0)) (y := round5 (e.1 1))
          (z := round5 (e.1 2)) (w := round5 (e.1 3))).2
          (Or.inr <| Or.inr <| Or.inl hall2)
      exact hbits.2 heq
    · have hall3 :
        (round5 (e.1 0) = false ∧ round5 (e.1 1) = true ∧ round5 (e.1 2) = true ∧
            round5 (e.1 3) = false) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [round5_eq_false] using h0110.1
        · simpa [round5_eq_true] using h0110.2.1
        · simpa [round5_eq_true] using h0110.2.2.1
        · simpa [round5_eq_false] using h0110.2.2.2
      have heq :=
        (g_eq_iff_patterns (x := round5 (e.1 0)) (y := round5 (e.1 1))
          (z := round5 (e.1 2)) (w := round5 (e.1 3))).2
          (Or.inr <| Or.inr <| Or.inr hall3)
      exact hbits.2 heq

private def subtypeIffEquiv {α : Type} {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    {a : α // p a} ≃ {a : α // q a} where
  toFun x := ⟨x.1, (h x.1).1 x.2⟩
  invFun y := ⟨y.1, (h y.1).2 y.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
private lemma card_pat1001 : Fintype.card {e : Edge 5 // pat1001 e} = 12 := by
  classical
  have h :
      Fintype.card {e : Edge 5 // pat1001 e}
        = (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 := by
    simpa [pat1001, EdgePatterns.Pat1001, Big5, Small5, EdgePatterns.Big, EdgePatterns.Small] using
      (EdgePatterns.card_pat1001 (n := 5) (two := two5))
  have hnum : (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 = 12 := by
    rw [card_Big5, card_Small5]
    decide
  exact h.trans hnum

private lemma card_pat0110 : Fintype.card {e : Edge 5 // pat0110 e} = 12 := by
  classical
  have h :
      Fintype.card {e : Edge 5 // pat0110 e}
        = (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 := by
    simpa [pat0110, EdgePatterns.Pat0110, Big5, Small5, EdgePatterns.Big, EdgePatterns.Small] using
      (EdgePatterns.card_pat0110 (n := 5) (two := two5))
  have hnum : (Fintype.card Big5).descFactorial 2 * (Fintype.card Small5).descFactorial 2 = 12 := by
    rw [card_Big5, card_Small5]
    decide
  exact h.trans hnum

theorem edgeCount_5 : edgeCount 5 = 120 := by
  classical
  -- `Edge 5` is equivalent to the type of embeddings `Fin 4 ↪ Fin 5`.
  have hcongr : edgeCount 5 = Fintype.card (Fin 4 ↪ Sym 5) := by
    have : Fintype.card (Edge 5) = Fintype.card (Fin 4 ↪ Sym 5) :=
      Fintype.card_congr
        { toFun := fun e => ⟨e.1, e.2⟩
          invFun := fun x => ⟨x, x.injective⟩
          left_inv := by intro e; apply Subtype.ext; funext i; rfl
          right_inv := by intro x; ext i; rfl }
    simpa [edgeCount] using this
  have : edgeCount 5 = (5 : Nat).descFactorial 4 := by
    simp [hcongr, Sym, Fintype.card_embedding_eq]
  simpa using this.trans (by decide : (5 : Nat).descFactorial 4 = 120)

theorem monoCount_f5 : monoCount f5 = 24 := by
  classical
  have hsub :
      monoCount f5 = Fintype.card {e : Edge 5 // Edge.monochromatic f5 e} := by
    simpa [monoCount, monoEdges] using
      (Fintype.card_subtype (α := Edge 5) (p := Edge.monochromatic f5)).symm
  have hmono :
      Fintype.card {e : Edge 5 // Edge.monochromatic f5 e}
        = Fintype.card {e : Edge 5 // pat1001 e ∨ pat0110 e} := by
    exact Fintype.card_congr <|
      subtypeIffEquiv (α := Edge 5)
        (p := Edge.monochromatic f5)
        (q := fun e => pat1001 e ∨ pat0110 e)
        (fun e => monochromatic_iff_pat (e := e))
  have hdisj : Disjoint pat1001 pat0110 := by
    intro r hr hs
    intro e hre
    have h1 : pat1001 e := hr e hre
    have h2 : pat0110 e := hs e hre
    exact (not_lt_of_ge h1.1) h2.1
  calc
    monoCount f5
        = Fintype.card {e : Edge 5 // Edge.monochromatic f5 e} := hsub
    _ = Fintype.card {e : Edge 5 // pat1001 e ∨ pat0110 e} := hmono
    _ = Fintype.card {e : Edge 5 // pat1001 e} + Fintype.card {e : Edge 5 // pat0110 e} := by
          simpa using
            (Fintype.card_subtype_or_disjoint (p := pat1001) (q := pat0110) hdisj)
    _ = 12 + 12 := by simp [card_pat1001, card_pat0110]
    _ = 24 := by decide

theorem monoFraction_f5 : monoFraction f5 = (1 : ℚ) / 5 := by
  simp [monoFraction, monoCount_f5, edgeCount_5]
  norm_num

end Sanity

end Distributed2Coloring.LowerBound
