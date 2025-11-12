/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Cell

/-!
TODO: Document this file.
-/

universe u

namespace HigherCategoryTheory

namespace SingleSortedNCategory

open SingleSortedCategoryFamily in
def toUnderlyingSingleSortedMCategory {n : ℕ} {Obj : Type u}
    (nS : SingleSortedNCategory n Obj)
    (m : Fin n) :
    SingleSortedNCategory m (cell Obj m) where
  Sc k f := by
    simp
    have k_lt_n : k < n := Nat.lt_trans k.isLt m.isLt
    let sc_k_f : Obj := nS.Sc ⟨k, k_lt_n⟩ f
    use sc_k_f
    exact nS.sck_scj_is_scj f k.isLt
  Tg k f := by
    rw [cell_eq_cell_tg]
    simp
    have k_lt_n : k < n := Nat.lt_trans k.isLt m.isLt
    let tg_k_f : Obj := nS.Tg ⟨k, k_lt_n⟩ f
    use tg_k_f
    exact nS.tgk_tgj_is_tgj f k.isLt
  PComp k g f :=
    {
      Dom := by
        have k_lt_n : k < n := Nat.lt_trans k.isLt m.isLt
        exact (nS.PComp ⟨k, k_lt_n⟩ g f).Dom
      get nS_pcomp_dom := by
        have k_lt_n : k < n := Nat.lt_trans k.isLt m.isLt
        let nS_comp_gf := nS.pcomp_dom.mp nS_pcomp_dom
        let pcomp_k_gf : Obj := nS.comp (⟨k, k_lt_n⟩ : Fin n) g f nS_comp_gf
        simp
        use pcomp_k_gf
        calc
          sc m pcomp_k_gf
          _ = _ := nS.sck_compj_is_compj_sck k.isLt nS_comp_gf
          _ = pcomp_k_gf := congr_pcomp g.property f.property _ _
    }
  -- TODO: Prove remaining axioms
  pcomp_dom := by sorry
  sc_sc_is_sc := by sorry
  tg_sc_is_sc := by sorry
  sc_tg_is_tg := by sorry
  tg_tg_is_tg := by sorry
  sc_comp_is_sc := by sorry
  tg_comp_is_tg := by sorry
  comp_sc_is_id := by sorry
  comp_tg_is_id := by sorry
  compr_assoc := by sorry
  compl_assoc := by sorry
  assoc := by sorry
  sck_scj_is_scj := by sorry
  scj_sck_is_scj := by sorry
  scj_tgk_is_scj := by sorry
  tgk_tgj_is_tgj := by sorry
  tgj_tgk_is_tgj := by sorry
  tgj_sck_is_tgj := by sorry
  comp_j_sc := by sorry
  comp_j_tg := by sorry
  sck_compj_is_compj_sck := by sorry
  tgk_compj_is_compj_tgk := by sorry
  comp_k_exchange := by sorry
  comp_j_exchange := by sorry
  exchange := by sorry

end SingleSortedNCategory

end HigherCategoryTheory
