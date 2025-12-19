/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor
import HigherCategoryTheory.SingleSorted.Cells

/-!
TODO: Comment.
-/

universe u v

namespace HigherCategoryTheory

-- TODO: Improve the tactic.
/-- TODO: Comment. -/
macro (name := inherit_axiom) "inherit_axiom" axiom_name:ident : tactic =>
  `(tactic| (intros; rw [Subtype.mk.injEq]; try (apply $axiom_name <;> (simp at *; assumption))))

variable {n : ℕ} {obj : Type u}

/-- TODO: Comment. -/
@[simp]
def SingleSortedNCategory.underlying (S : SingleSortedNCategory n obj) (m : Fin n) :
    SingleSortedNCategory m (cells m obj) where
  sc k f := ⟨S.sc ⟨k, lt_trans k.isLt m.isLt⟩ f, by apply underlying_source_is_cell; exact k.isLt⟩
  tg k f := ⟨S.tg ⟨k, lt_trans k.isLt m.isLt⟩ f, by apply underlying_target_is_cell; exact k.isLt⟩
  pcomp k g f :=
    let k' : Fin n := ⟨k, lt_trans k.isLt m.isLt⟩
    { S.pcomp k' g f with
      get dom := ⟨S.comp k' g f (S.pcomp_dom.mp dom), by
        apply underlying_comp_is_cell dom; exact k.isLt⟩ }
  pcomp_dom := by inherit_axiom S.pcomp_dom
  sck_sck_eq_sck := by inherit_axiom S.sck_sck_eq_sck
  tgk_sck_eq_sck := by inherit_axiom S.tgk_sck_eq_sck
  sck_tgk_eq_tgk := by inherit_axiom S.sck_tgk_eq_tgk
  tgk_tgk_eq_tgk := by inherit_axiom S.tgk_tgk_eq_tgk
  sck_compk_eq_sck := by inherit_axiom S.sck_compk_eq_sck
  tgk_compk_eq_tgk := by inherit_axiom S.tgk_compk_eq_tgk
  compk_sck_eq_id := by inherit_axiom S.compk_sck_eq_id
  compk_tgk_eq_id := by inherit_axiom S.compk_tgk_eq_id
  assoc := by inherit_axiom S.assoc
  sck_scj_eq_scj := by inherit_axiom S.sck_scj_eq_scj
  scj_sck_eq_scj := by inherit_axiom S.scj_sck_eq_scj
  scj_tgk_eq_scj := by inherit_axiom S.scj_tgk_eq_scj
  tgk_tgj_eq_tgj := by inherit_axiom S.tgk_tgj_eq_tgj
  tgj_tgk_eq_tgj := by inherit_axiom S.tgj_tgk_eq_tgj
  tgj_sck_eq_tgj := by inherit_axiom S.tgj_sck_eq_tgj
  sck_compj_eq_compj_sck := by inherit_axiom S.sck_compj_eq_compj_sck
  tgk_compj_eq_compj_tgk := by inherit_axiom S.tgk_compj_eq_compj_tgk
  exchange := by inherit_axiom S.exchange

/-- TODO: Comment. -/
@[simp]
def SingleSortedOmegaCategory.underlying (S : SingleSortedOmegaCategory obj) (m : ℕ) :
    SingleSortedNCategory m (cells m obj) where
  sc k f := ⟨S.sc k f, by apply underlying_source_is_cell; exact k.isLt⟩
  tg k f := ⟨S.tg k f, by apply underlying_target_is_cell; exact k.isLt⟩
  pcomp k g f := { S.pcomp k g f with
    get dom := ⟨S.comp k g f (S.pcomp_dom.mp dom), by
      apply underlying_comp_is_cell dom; exact k.isLt⟩ }
  pcomp_dom := by inherit_axiom S.pcomp_dom
  sck_sck_eq_sck := by inherit_axiom S.sck_sck_eq_sck
  tgk_sck_eq_sck := by inherit_axiom S.tgk_sck_eq_sck
  sck_tgk_eq_tgk := by inherit_axiom S.sck_tgk_eq_tgk
  tgk_tgk_eq_tgk := by inherit_axiom S.tgk_tgk_eq_tgk
  sck_compk_eq_sck := by inherit_axiom S.sck_compk_eq_sck
  tgk_compk_eq_tgk := by inherit_axiom S.tgk_compk_eq_tgk
  compk_sck_eq_id := by inherit_axiom S.compk_sck_eq_id
  compk_tgk_eq_id := by inherit_axiom S.compk_tgk_eq_id
  assoc := by inherit_axiom S.assoc
  sck_scj_eq_scj := by inherit_axiom S.sck_scj_eq_scj
  scj_sck_eq_scj := by inherit_axiom S.scj_sck_eq_scj
  scj_tgk_eq_scj := by inherit_axiom S.scj_tgk_eq_scj
  tgk_tgj_eq_tgj := by inherit_axiom S.tgk_tgj_eq_tgj
  tgj_tgk_eq_tgj := by inherit_axiom S.tgj_tgk_eq_tgj
  tgj_sck_eq_tgj := by inherit_axiom S.tgj_sck_eq_tgj
  sck_compj_eq_compj_sck := by inherit_axiom S.sck_compj_eq_compj_sck
  tgk_compj_eq_compj_tgk := by inherit_axiom S.tgk_compj_eq_compj_tgk
  exchange := by inherit_axiom S.exchange

variable {C : Type u} {D : Type v} [SC : SingleSortedNCategory n C] [SD : SingleSortedNCategory n D]
  [ωSC : SingleSortedOmegaCategory C] [ωSD : SingleSortedOmegaCategory D]

/-- TODO: Comment. -/
@[simp]
def SingleSortedNFunctor.underlying (F : SingleSortedNFunctor n C D) (m : Fin n) :
    letI := SC.underlying m
    letI := SD.underlying m
    SingleSortedNFunctor m (cells m C) (cells m D) :=
  let uSC := SC.underlying m
  let uSD := SD.underlying m
  {
    map f := ⟨F f, by apply underlying_functor_is_cell⟩
    map_sc_eq_sc_map := by inherit_axiom F.map_sc_eq_sc_map
    map_tg_eq_tg_map := by inherit_axiom F.map_tg_eq_tg_map
    map_comp_eq_comp_map := by inherit_axiom F.map_comp_eq_comp_map
  }

/-- TODO: Comment. -/
@[simp]
def SingleSortedOmegaFunctor.underlying (F : SingleSortedOmegaFunctor C D) (m : ℕ) :
    letI := ωSC.underlying m
    letI := ωSD.underlying m
    SingleSortedNFunctor m (cells m C) (cells m D) :=
  let uSC := ωSC.underlying m
  let uSD := ωSD.underlying m
  {
    map f := ⟨F f, by apply underlying_functor_is_cell⟩
    map_sc_eq_sc_map := by inherit_axiom F.map_sc_eq_sc_map
    map_tg_eq_tg_map := by inherit_axiom F.map_tg_eq_tg_map
    map_comp_eq_comp_map := by inherit_axiom F.map_comp_eq_comp_map
  }

end HigherCategoryTheory
