/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Cat
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor
import HigherCategoryTheory.SingleSorted.Cat

/-!
**Important note:** This file is work in progress and proofs should be highly improved.
-/

universe u v

namespace HigherCategoryTheory.SingleSorted

variable {n : ℕ} {C : Type u}

/-- TODO: Document. -/
-- TODO: The remaining `sorry`s follow the same proof pattern as the completed axioms. They will be
-- filled in once the proof strategy is refined.
def NCategory.discrete (S : NCategory n C) (m : ℕ) (_n_lt_m : n < m) : NCategory m C where
  sc k f := if k_lt_n : k < n then S.sc ⟨k, k_lt_n⟩ f else f
  tg k f := if k_lt_n : k < n then S.tg ⟨k, k_lt_n⟩ f else f
  pcomp k g f := if k_lt_n : k < n then S.pcomp ⟨k, k_lt_n⟩ g f else ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by
    intro k f g
    split_ifs
    · apply S.pcomp_dom
    · trivial
  sck_sck_eq_sck := by sorry
  tgk_sck_eq_sck := by sorry
  sck_tgk_eq_tgk := by sorry
  tgk_tgk_eq_tgk := by sorry
  sck_compk_eq_sck := by
    intro k f g sc_tg_gf
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.sck_compk_eq_sck
      simp [h] at sc_tg_gf
      assumption
    · simp [h]
  tgk_compk_eq_tgk := by sorry
  compk_sck_eq_id := by
    intro k f
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.compk_sck_eq_id
    · simp [h]
  compk_tgk_eq_id := by sorry
  assoc := by
    intro k f g h sc_tg_gf sc_tg_hg
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.assoc
      · simp [h] at sc_tg_gf
        assumption
      · simp [h] at sc_tg_hg
        assumption
    · simp [h]
  sck_scj_eq_scj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.sck_scj_eq_scj
      assumption
    · omega
    · trivial
    · trivial
  scj_sck_eq_scj := by sorry
  scj_tgk_eq_scj := by sorry
  tgk_tgj_eq_tgj := by sorry
  tgj_tgk_eq_tgj := by sorry
  tgj_sck_eq_tgj := by sorry
  sck_compj_eq_compj_sck := by
    intro k j f g j_lt_k sc_tg_j_gf
    simp only [CategoryStruct.comp]
    split_ifs with h₁ h₂
    · apply S.sck_compj_eq_compj_sck
      · assumption
      · simp [h₂] at sc_tg_j_gf
        assumption
    · trivial
    · trivial
    · trivial
  tgk_compj_eq_compj_tgk := by sorry
  interchange := by
    intro k j f₁ f₂ g₁ g₂ j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_j_g₂f₂ sc_tg_j_g₁f₁
    simp only [CategoryStruct.comp]
    split_ifs with h₁ h₂
    · apply S.interchange
      · assumption
      · simp [h₁] at sc_tg_k_g₂g₁
        assumption
      · simp [h₁] at sc_tg_k_f₂f₁
        assumption
      · simp [h₂] at sc_tg_j_g₂f₂
        assumption
      · simp [h₂] at sc_tg_j_g₁f₁
        assumption
    · trivial
    · trivial
    · trivial

/-- TODO: Document. -/
-- TODO: The proofs follow the same structure as those in `Category.discrete`.
def NCategory.discreteOmega (S : NCategory n C) : OmegaCategory C where
  sc k f := if k_lt_n : k < n then S.sc ⟨k, k_lt_n⟩ f else f
  tg k f := if k_lt_n : k < n then S.tg ⟨k, k_lt_n⟩ f else f
  pcomp k g f := if k_lt_n : k < n then S.pcomp ⟨k, k_lt_n⟩ g f else ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by sorry
  sck_sck_eq_sck := by sorry
  tgk_sck_eq_sck := by sorry
  sck_tgk_eq_tgk := by sorry
  tgk_tgk_eq_tgk := by sorry
  sck_compk_eq_sck := by sorry
  tgk_compk_eq_tgk := by sorry
  compk_sck_eq_id := by sorry
  compk_tgk_eq_id := by sorry
  assoc := by sorry
  sck_scj_eq_scj := by sorry
  scj_sck_eq_scj := by sorry
  scj_tgk_eq_scj := by sorry
  tgk_tgj_eq_tgj := by sorry
  tgj_tgk_eq_tgj := by sorry
  tgj_sck_eq_tgj := by sorry
  sck_compj_eq_compj_sck := by sorry
  tgk_compj_eq_compj_tgk := by sorry
  interchange := by sorry
  is_cell := by sorry

section Functor

variable {n : ℕ} {C : Type u} {D : Type v} [SC : NCategory n C] [SD : NCategory n D]

/-- TODO: Document. -/
-- TODO: The proofs follow the same structure as those in `Category.discrete`.
def NFunctor.discrete (F : NFunctor n C D) (m : ℕ) (n_lt_m : n < m) :
    letI := SC.discrete m n_lt_m
    letI := SD.discrete m n_lt_m
    NFunctor m C D :=
  letI := SC.discrete m n_lt_m
  letI := SD.discrete m n_lt_m
  {
    map := F.map
    map_sc_eq_sc_map := by sorry
    map_tg_eq_tg_map := by sorry
    map_comp_eq_comp_map := by sorry
  }

/-- TODO: Document. -/
-- TODO: The proofs follow the same structure as those in `Category.discrete`.
def NFunctor.discreteOmega (F : NFunctor n C D) :
    letI := SC.discreteOmega
    letI := SD.discreteOmega
    OmegaFunctor C D :=
  letI := SC.discreteOmega
  letI := SD.discreteOmega
  {
    map := F.map
    map_sc_eq_sc_map := by sorry
    map_tg_eq_tg_map := by sorry
    map_comp_eq_comp_map := by sorry
  }

end Functor

end HigherCategoryTheory.SingleSorted
