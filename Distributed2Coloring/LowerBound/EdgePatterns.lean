import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

import Distributed2Coloring.LowerBound.Defs

namespace Distributed2Coloring.LowerBound

/-!
Reusable lemmas for counting edges with coordinate-wise constraints relative to a threshold `two`.

These are used in auxiliary “sanity check” and “upper bound” files to avoid repeating large
case-bashy equivalence proofs.
-/

namespace EdgePatterns

variable {n : Nat} (two : Sym n)

abbrev Small : Type := Set.Iio two
abbrev Big : Type := Set.Ici two

def Pat0000 (e : Edge n) : Prop :=
  e.1 0 < two ∧ e.1 1 < two ∧ e.1 2 < two ∧ e.1 3 < two

def Pat1111 (e : Edge n) : Prop :=
  two ≤ e.1 0 ∧ two ≤ e.1 1 ∧ two ≤ e.1 2 ∧ two ≤ e.1 3

def Pat1001 (e : Edge n) : Prop :=
  two ≤ e.1 0 ∧ e.1 1 < two ∧ e.1 2 < two ∧ two ≤ e.1 3

def Pat0110 (e : Edge n) : Prop :=
  e.1 0 < two ∧ two ≤ e.1 1 ∧ two ≤ e.1 2 ∧ e.1 3 < two

instance : DecidablePred (Pat0000 (two := two)) := by
  intro e
  dsimp [Pat0000]
  infer_instance

instance : DecidablePred (Pat1111 (two := two)) := by
  intro e
  dsimp [Pat1111]
  infer_instance

instance : DecidablePred (Pat1001 (two := two)) := by
  intro e
  dsimp [Pat1001]
  infer_instance

instance : DecidablePred (Pat0110 (two := two)) := by
  intro e
  dsimp [Pat0110]
  infer_instance

private lemma big_ne_small {n : Nat} {two : Sym n} (x : Big (two := two)) (y : Small (two := two)) :
    (x.1 : Sym n) ≠ y.1 := by
  intro hxy
  have hx : two ≤ (y.1 : Sym n) := hxy ▸ x.2
  exact (not_lt_of_ge hx) y.2

private lemma small_ne_big {n : Nat} {two : Sym n} (x : Small (two := two)) (y : Big (two := two)) :
    (x.1 : Sym n) ≠ y.1 := by
  intro hxy
  exact big_ne_small (two := two) (x := y) (y := x) hxy.symm

private def tuple1001 {n : Nat} (two : Sym n) (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => (ad 0).1
    | 1 => (bc 0).1
    | 2 => (bc 1).1
    | _ => (ad 1).1

private lemma tuple1001_injective {n : Nat} {two : Sym n} (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Function.Injective (tuple1001 two ad bc) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have : (ad 0).1 = (bc 0).1 := by simpa [tuple1001] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 0) (y := bc 0) this
  · have : (ad 0).1 = (bc 1).1 := by simpa [tuple1001] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 0) (y := bc 1) this
  · have : (ad 0).1 = (ad 1).1 := by simpa [tuple1001] using hij
    have : (0 : Fin 2) = 1 := by
      apply ad.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this)
  · have : (bc 0).1 = (ad 0).1 := by simpa [tuple1001] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 0) (y := ad 0) this
  · rfl
  · have : (bc 0).1 = (bc 1).1 := by simpa [tuple1001] using hij
    have : (0 : Fin 2) = 1 := by
      apply bc.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this)
  · have : (bc 0).1 = (ad 1).1 := by simpa [tuple1001] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 0) (y := ad 1) this
  · have : (bc 1).1 = (ad 0).1 := by simpa [tuple1001] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 1) (y := ad 0) this
  · have : (bc 1).1 = (bc 0).1 := by simpa [tuple1001] using hij
    have : (1 : Fin 2) = 0 := by
      apply bc.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this.symm)
  · rfl
  · have : (bc 1).1 = (ad 1).1 := by simpa [tuple1001] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 1) (y := ad 1) this
  · have : (ad 1).1 = (ad 0).1 := by simpa [tuple1001] using hij
    have : (1 : Fin 2) = 0 := by
      apply ad.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this.symm)
  · have : (ad 1).1 = (bc 0).1 := by simpa [tuple1001] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 1) (y := bc 0) this
  · have : (ad 1).1 = (bc 1).1 := by simpa [tuple1001] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 1) (y := bc 1) this
  · rfl

private def tuple0110 {n : Nat} (two : Sym n) (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Tuple 4 n :=
  fun i =>
    match i.1 with
    | 0 => (bc 0).1
    | 1 => (ad 0).1
    | 2 => (ad 1).1
    | _ => (bc 1).1

private lemma tuple0110_injective {n : Nat} {two : Sym n} (ad : Fin 2 ↪ Big (two := two))
    (bc : Fin 2 ↪ Small (two := two)) : Function.Injective (tuple0110 two ad bc) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have : (bc 0).1 = (ad 0).1 := by simpa [tuple0110] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 0) (y := ad 0) this
  · have : (bc 0).1 = (ad 1).1 := by simpa [tuple0110] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 0) (y := ad 1) this
  · have : (bc 0).1 = (bc 1).1 := by simpa [tuple0110] using hij
    have : (0 : Fin 2) = 1 := by
      apply bc.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this)
  · have : (ad 0).1 = (bc 0).1 := by simpa [tuple0110] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 0) (y := bc 0) this
  · rfl
  · have : (ad 0).1 = (ad 1).1 := by simpa [tuple0110] using hij
    have : (0 : Fin 2) = 1 := by
      apply ad.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this)
  · have : (ad 0).1 = (bc 1).1 := by simpa [tuple0110] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 0) (y := bc 1) this
  · have : (ad 1).1 = (bc 0).1 := by simpa [tuple0110] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 1) (y := bc 0) this
  · have : (ad 1).1 = (ad 0).1 := by simpa [tuple0110] using hij
    have : (1 : Fin 2) = 0 := by
      apply ad.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this.symm)
  · rfl
  · have : (ad 1).1 = (bc 1).1 := by simpa [tuple0110] using hij
    exact False.elim <| big_ne_small (two := two) (x := ad 1) (y := bc 1) this
  · have : (bc 1).1 = (bc 0).1 := by simpa [tuple0110] using hij
    have : (1 : Fin 2) = 0 := by
      apply bc.injective
      apply Subtype.ext
      exact this
    exact False.elim (h01 this.symm)
  · have : (bc 1).1 = (ad 0).1 := by simpa [tuple0110] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 1) (y := ad 0) this
  · have : (bc 1).1 = (ad 1).1 := by simpa [tuple0110] using hij
    exact False.elim <| small_ne_big (two := two) (x := bc 1) (y := ad 1) this
  · rfl

theorem card_pat0000 :
    Fintype.card {e : Edge n // Pat0000 (two := two) e}
      = (Fintype.card (Small (two := two))).descFactorial 4 := by
  classical
  let toEmb : {e : Edge n // Pat0000 (two := two) e} → (Fin 4 ↪ Small (two := two)) :=
    fun e =>
      (⟨e.1.1, e.1.2⟩ : Fin 4 ↪ Sym n).codRestrict (Set.Iio two) (by
        intro i
        fin_cases i
        · simpa [Pat0000] using e.2.1
        · simpa [Pat0000] using e.2.2.1
        · simpa [Pat0000] using e.2.2.2.1
        · simpa [Pat0000] using e.2.2.2.2)
  let ofEmb : (Fin 4 ↪ Small (two := two)) → {e : Edge n // Pat0000 (two := two) e} :=
    fun x =>
      ⟨⟨fun i => (x i).1, by
          intro i j hij
          exact x.injective (Subtype.ext hij)⟩,
        ⟨(x 0).2, (x 1).2, (x 2).2, (x 3).2⟩⟩
  have hEquiv : {e : Edge n // Pat0000 (two := two) e} ≃ (Fin 4 ↪ Small (two := two)) :=
    { toFun := toEmb
      invFun := ofEmb
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        rfl
      right_inv := by
        intro x
        ext i
        rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat0000 (two := two) e}
        = Fintype.card (Fin 4 ↪ Small (two := two)) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq]

theorem card_pat1111 :
    Fintype.card {e : Edge n // Pat1111 (two := two) e}
      = (Fintype.card (Big (two := two))).descFactorial 4 := by
  classical
  let toEmb : {e : Edge n // Pat1111 (two := two) e} → (Fin 4 ↪ Big (two := two)) :=
    fun e =>
      (⟨e.1.1, e.1.2⟩ : Fin 4 ↪ Sym n).codRestrict (Set.Ici two) (by
        intro i
        fin_cases i
        · simpa [Pat1111] using e.2.1
        · simpa [Pat1111] using e.2.2.1
        · simpa [Pat1111] using e.2.2.2.1
        · simpa [Pat1111] using e.2.2.2.2)
  let ofEmb : (Fin 4 ↪ Big (two := two)) → {e : Edge n // Pat1111 (two := two) e} :=
    fun x =>
      ⟨⟨fun i => (x i).1, by
          intro i j hij
          exact x.injective (Subtype.ext hij)⟩,
        ⟨(x 0).2, (x 1).2, (x 2).2, (x 3).2⟩⟩
  have hEquiv : {e : Edge n // Pat1111 (two := two) e} ≃ (Fin 4 ↪ Big (two := two)) :=
    { toFun := toEmb
      invFun := ofEmb
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        rfl
      right_inv := by
        intro x
        ext i
        rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat1111 (two := two) e}
        = Fintype.card (Fin 4 ↪ Big (two := two)) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq]

theorem card_pat1001 :
    Fintype.card {e : Edge n // Pat1001 (two := two) e}
      = (Fintype.card (Big (two := two))).descFactorial 2
          * (Fintype.card (Small (two := two))).descFactorial 2 := by
  classical
  let toProd : {e : Edge n // Pat1001 (two := two) e} →
      (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    fun e =>
      ( { toFun := fun i =>
            match i.1 with
            | 0 => ⟨e.1.1 0, by simpa [Pat1001] using e.2.1⟩
            | _ => ⟨e.1.1 3, by simpa [Pat1001] using e.2.2.2.2⟩
          inj' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · rfl
            · exfalso
              have hIdx : (0 : Fin 4) = (3 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (0 : Fin 4) ≠ (3 : Fin 4)) hIdx
            · exfalso
              have hIdx : (3 : Fin 4) = (0 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (3 : Fin 4) ≠ (0 : Fin 4)) hIdx
            · rfl },
        { toFun := fun i =>
            match i.1 with
            | 0 => ⟨e.1.1 1, by simpa [Pat1001] using e.2.2.1⟩
            | _ => ⟨e.1.1 2, by simpa [Pat1001] using e.2.2.2.1⟩
          inj' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · rfl
            · exfalso
              have hIdx : (1 : Fin 4) = (2 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (1 : Fin 4) ≠ (2 : Fin 4)) hIdx
            · exfalso
              have hIdx : (2 : Fin 4) = (1 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (2 : Fin 4) ≠ (1 : Fin 4)) hIdx
            · rfl } )
  let ofProd : (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) →
      {e : Edge n // Pat1001 (two := two) e} :=
    fun p =>
      let ad := p.1
      let bc := p.2
      ⟨⟨tuple1001 two ad bc, tuple1001_injective (two := two) ad bc⟩,
        ⟨(ad 0).2, (bc 0).2, (bc 1).2, (ad 1).2⟩⟩
  have hEquiv : {e : Edge n // Pat1001 (two := two) e}
      ≃ (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    { toFun := toProd
      invFun := ofProd
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        cases p with
        | mk ad bc =>
            apply Prod.ext <;> ext i <;> fin_cases i <;> rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat1001 (two := two) e}
        = Fintype.card ((Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two))) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq, Fintype.card_prod]

theorem card_pat0110 :
    Fintype.card {e : Edge n // Pat0110 (two := two) e}
      = (Fintype.card (Big (two := two))).descFactorial 2
          * (Fintype.card (Small (two := two))).descFactorial 2 := by
  classical
  let toProd : {e : Edge n // Pat0110 (two := two) e} →
      (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    fun e =>
      ( { toFun := fun i =>
            match i.1 with
            | 0 => ⟨e.1.1 1, by simpa [Pat0110] using e.2.2.1⟩
            | _ => ⟨e.1.1 2, by simpa [Pat0110] using e.2.2.2.1⟩
          inj' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · rfl
            · exfalso
              have hIdx : (1 : Fin 4) = (2 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (1 : Fin 4) ≠ (2 : Fin 4)) hIdx
            · exfalso
              have hIdx : (2 : Fin 4) = (1 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (2 : Fin 4) ≠ (1 : Fin 4)) hIdx
            · rfl },
        { toFun := fun i =>
            match i.1 with
            | 0 => ⟨e.1.1 0, by simpa [Pat0110] using e.2.1⟩
            | _ => ⟨e.1.1 3, by simpa [Pat0110] using e.2.2.2.2⟩
          inj' := by
            intro i j hij
            fin_cases i <;> fin_cases j
            · rfl
            · exfalso
              have hIdx : (0 : Fin 4) = (3 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (0 : Fin 4) ≠ (3 : Fin 4)) hIdx
            · exfalso
              have hIdx : (3 : Fin 4) = (0 : Fin 4) :=
                e.1.2 (by simpa using congrArg Subtype.val hij)
              exact (by decide : (3 : Fin 4) ≠ (0 : Fin 4)) hIdx
            · rfl } )
  let ofProd : (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) →
      {e : Edge n // Pat0110 (two := two) e} :=
    fun p =>
      let ad := p.1
      let bc := p.2
      ⟨⟨tuple0110 two ad bc, tuple0110_injective (two := two) ad bc⟩,
        ⟨(bc 0).2, (ad 0).2, (ad 1).2, (bc 1).2⟩⟩
  have hEquiv : {e : Edge n // Pat0110 (two := two) e}
      ≃ (Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two)) :=
    { toFun := toProd
      invFun := ofProd
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        cases p with
        | mk ad bc =>
            apply Prod.ext <;> ext i <;> fin_cases i <;> rfl }
  have hcard :
      Fintype.card {e : Edge n // Pat0110 (two := two) e}
        = Fintype.card ((Fin 2 ↪ Big (two := two)) × (Fin 2 ↪ Small (two := two))) :=
    Fintype.card_congr hEquiv
  simp [hcard, Fintype.card_embedding_eq, Fintype.card_prod]

end EdgePatterns

end Distributed2Coloring.LowerBound
