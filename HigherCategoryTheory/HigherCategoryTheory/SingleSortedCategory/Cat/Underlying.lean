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
  pcomp_dom := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.pcomp_dom
  sc_sc_is_sc := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.sc_sc_is_sc _ _
  tg_sc_is_sc := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.tg_sc_is_sc _ _
  sc_tg_is_tg := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.sc_tg_is_tg _ _
  tg_tg_is_tg := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.tg_tg_is_tg _ _
  sc_comp_is_sc := by
    intro k g f comp_gf
    rw [Subtype.mk.injEq]
    apply nS.sc_comp_is_sc
    simp only [sc_is_tg] at *
    rw [Subtype.mk.injEq] at *
    exact comp_gf
  tg_comp_is_tg := by
    intro k g f comp_gf
    rw [Subtype.mk.injEq]
    apply nS.tg_comp_is_tg
    simp only [sc_is_tg] at *
    rw [Subtype.mk.injEq] at *
    exact comp_gf
  comp_sc_is_id := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.comp_sc_is_id _ _
  comp_tg_is_id := by
    intros
    rw [Subtype.mk.injEq]
    exact nS.comp_tg_is_id _ _
  assoc := by
    intro k f g h comp_fg comp_gh
    rw [Subtype.mk.injEq]
    apply nS.assoc
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_fg
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_gh
  sck_scj_is_scj := by
    intros k j f j_lt_k
    rw [Subtype.mk.injEq]
    apply nS.sck_scj_is_scj
    exact j_lt_k
  scj_sck_is_scj := by
    intros k j f j_lt_k
    rw [Subtype.mk.injEq]
    apply nS.scj_sck_is_scj
    exact j_lt_k
  scj_tgk_is_scj := by
    intros k j f j_lt_k
    rw [Subtype.mk.injEq]
    apply nS.scj_tgk_is_scj
    exact j_lt_k
  tgk_tgj_is_tgj := by
    intros k j f j_lt_k
    rw [Subtype.mk.injEq]
    apply nS.tgk_tgj_is_tgj
    exact j_lt_k
  tgj_tgk_is_tgj := by
    intros k j f j_lt_k
    rw [Subtype.mk.injEq]
    apply nS.tgj_tgk_is_tgj
    exact j_lt_k
  tgj_sck_is_tgj := by
    intros k j f j_lt_k
    rw [Subtype.mk.injEq]
    apply nS.tgj_sck_is_tgj
    exact j_lt_k
  sck_compj_is_compj_sck := by
    intros k j f g j_lt_k comp_j_gf
    rw [Subtype.mk.injEq]
    apply nS.sck_compj_is_compj_sck
    · exact j_lt_k
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_j_gf
  tgk_compj_is_compj_tgk := by
    intros k j f g j_lt_k comp_j_gf
    rw [Subtype.mk.injEq]
    apply nS.tgk_compj_is_compj_tgk
    · exact j_lt_k
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_j_gf
  exchange := by
    intro k j f₁ f₂ g₁ g₂ j_lt_k
      comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁
    rw [Subtype.mk.injEq]
    apply nS.exchange
    · exact j_lt_k
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_k_g₂g₁
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_k_f₂f₁
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_j_g₂f₂
    · simp only [sc_is_tg] at *
      rw [Subtype.mk.injEq] at *
      exact comp_j_g₁f₁

end SingleSortedNCategory

end HigherCategoryTheory
