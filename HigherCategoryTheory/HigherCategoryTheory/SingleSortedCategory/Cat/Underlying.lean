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

macro (name := inherit_axiom) "inherit_axiom" axiom_name:ident : tactic =>
  `(tactic| (intros; simp; apply $axiom_name <;> (simp at *; omega)))

open SingleSortedCategoryFamily in
def toUnderlyingSingleSortedMCategory {n : ℕ} {Obj : Type u}
    (nS : SingleSortedNCategory n Obj)
    (m : Fin n) :
    SingleSortedNCategory m (cell Obj m) where
  Sc k f := ⟨nS.Sc ⟨k, Nat.lt_trans k.isLt m.isLt⟩ f, by
    exact nS.sck_scj_is_scj f k.isLt⟩
  Tg k f := ⟨nS.Tg ⟨k, Nat.lt_trans k.isLt m.isLt⟩ f, by
    apply (nS.id_sc_iff_id_tg m (nS.Tg ⟨k, Nat.lt_trans k.isLt m.isLt⟩ f)).mpr
    exact nS.tgk_tgj_is_tgj f k.isLt⟩
  PComp k g f :=
    {
      Dom := (nS.PComp ⟨k, Nat.lt_trans k.isLt m.isLt⟩ g f).Dom
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
  pcomp_dom := by inherit_axiom nS.pcomp_dom
  sc_sc_is_sc := by inherit_axiom nS.sc_sc_is_sc
  tg_sc_is_sc := by inherit_axiom nS.tg_sc_is_sc
  sc_tg_is_tg := by inherit_axiom nS.sc_tg_is_tg
  tg_tg_is_tg := by inherit_axiom nS.tg_tg_is_tg
  sc_comp_is_sc := by inherit_axiom nS.sc_comp_is_sc
  tg_comp_is_tg := by inherit_axiom nS.tg_comp_is_tg
  comp_sc_is_id := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.comp_sc_is_id _ _
  comp_tg_is_id := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.comp_tg_is_id _ _
  assoc := by inherit_axiom nS.assoc
  sck_scj_is_scj := by inherit_axiom nS.sck_scj_is_scj
  scj_sck_is_scj := by inherit_axiom nS.scj_sck_is_scj
  scj_tgk_is_scj := by inherit_axiom nS.scj_tgk_is_scj
  tgk_tgj_is_tgj := by inherit_axiom nS.tgk_tgj_is_tgj
  tgj_tgk_is_tgj := by inherit_axiom nS.tgj_tgk_is_tgj
  tgj_sck_is_tgj := by inherit_axiom nS.tgj_sck_is_tgj
  sck_compj_is_compj_sck := by inherit_axiom nS.sck_compj_is_compj_sck
  tgk_compj_is_compj_tgk := by inherit_axiom nS.tgk_compj_is_compj_tgk
  exchange := by inherit_axiom nS.exchange

end SingleSortedNCategory

end HigherCategoryTheory
