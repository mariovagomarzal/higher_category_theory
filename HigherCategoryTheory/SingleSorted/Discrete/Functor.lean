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
@[simp]
def NCategory.discrete (S : NCategory n C) (m : ℕ) (_n_lt_m : n < m) : NCategory m C where
  sc k f := if k_lt_n : k < n then S.sc ⟨k, k_lt_n⟩ f else f
  tg k f := if k_lt_n : k < n then S.tg ⟨k, k_lt_n⟩ f else f
  pcomp k g f := if k_lt_n : k < n then S.pcomp ⟨k, k_lt_n⟩ g f else ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by
    intro k f g
    split_ifs
    · apply S.pcomp_dom
    · rfl
  sck_sck_eq_sck := by
    intro k f
    split_ifs
    · apply S.sck_sck_eq_sck
    · rfl
  tgk_sck_eq_sck := by
    intro k f
    split_ifs
    · apply S.tgk_sck_eq_sck
    · rfl
  sck_tgk_eq_tgk := by
    intro k f
    split_ifs
    · apply S.sck_tgk_eq_tgk
    · rfl
  tgk_tgk_eq_tgk := by
    intro k f
    split_ifs
    · apply S.tgk_tgk_eq_tgk
    · rfl
  sck_compk_eq_sck := by
    intro k f g sc_tg_gf
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.sck_compk_eq_sck
      simp [h] at sc_tg_gf
      assumption
    · simp [h]
  tgk_compk_eq_tgk := by
    intro k f g sc_tg_gf
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.tgk_compk_eq_tgk
      simp [h] at sc_tg_gf
      assumption
    · simp only [CategoryStruct.comp, h]
      simp [h] at sc_tg_gf
      exact sc_tg_gf.symm
  compk_sck_eq_id := by
    intro k f
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.compk_sck_eq_id
    · simp [h]
  compk_tgk_eq_id := by
    intro k f
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.compk_tgk_eq_id
    · simp [h]
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
    · rfl
    · rfl
  scj_sck_eq_scj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.scj_sck_eq_scj
      assumption
    · rfl
    · omega
    · rfl
  scj_tgk_eq_scj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.scj_tgk_eq_scj
      assumption
    · rfl
    · omega
    · rfl
  tgk_tgj_eq_tgj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.tgk_tgj_eq_tgj
      assumption
    · omega
    · rfl
    · rfl
  tgj_tgk_eq_tgj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.tgj_tgk_eq_tgj
      assumption
    · rfl
    · omega
    · rfl
  tgj_sck_eq_tgj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.tgj_sck_eq_tgj
      assumption
    · rfl
    · omega
    · rfl
  sck_compj_eq_compj_sck := by
    intro k j f g j_lt_k sc_tg_j_gf
    simp only [CategoryStruct.comp]
    split_ifs with h₁ h₂
    · apply S.sck_compj_eq_compj_sck
      · assumption
      · simp [h₂] at sc_tg_j_gf
        assumption
    · rfl
    · rfl
    · rfl
  tgk_compj_eq_compj_tgk := by
    intro k j f g j_lt_k sc_tg_j_gf
    simp only [CategoryStruct.comp]
    split_ifs with h₁ h₂
    · apply S.tgk_compj_eq_compj_tgk
      · assumption
      · simp [h₂] at sc_tg_j_gf
        assumption
    · rfl
    · rfl
    · rfl
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
    · rfl
    · rfl
    · rfl

/-- TODO: Document. -/
@[simp]
def NCategory.discreteOmega (S : NCategory n C) : OmegaCategory C where
  sc k f := if k_lt_n : k < n then S.sc ⟨k, k_lt_n⟩ f else f
  tg k f := if k_lt_n : k < n then S.tg ⟨k, k_lt_n⟩ f else f
  pcomp k g f := if k_lt_n : k < n then S.pcomp ⟨k, k_lt_n⟩ g f else ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by
    intro k f g
    split_ifs
    · apply S.pcomp_dom
    · rfl
  sck_sck_eq_sck := by
    intro k f
    split_ifs
    · apply S.sck_sck_eq_sck
    · rfl
  tgk_sck_eq_sck := by
    intro k f
    split_ifs
    · apply S.tgk_sck_eq_sck
    · rfl
  sck_tgk_eq_tgk := by
    intro k f
    split_ifs
    · apply S.sck_tgk_eq_tgk
    · rfl
  tgk_tgk_eq_tgk := by
    intro k f
    split_ifs
    · apply S.tgk_tgk_eq_tgk
    · rfl
  sck_compk_eq_sck := by
    intro k f g sc_tg_gf
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.sck_compk_eq_sck
      simp [h] at sc_tg_gf
      assumption
    · simp [h]
  tgk_compk_eq_tgk := by
    intro k f g sc_tg_gf
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.tgk_compk_eq_tgk
      simp [h] at sc_tg_gf
      assumption
    · simp only [CategoryStruct.comp, h]
      simp [h] at sc_tg_gf
      exact sc_tg_gf.symm
  compk_sck_eq_id := by
    intro k f
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.compk_sck_eq_id
    · simp [h]
  compk_tgk_eq_id := by
    intro k f
    split_ifs with h
    · simp only [CategoryStruct.comp, h]
      apply S.compk_tgk_eq_id
    · simp [h]
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
    · rfl
    · rfl
  scj_sck_eq_scj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.scj_sck_eq_scj
      assumption
    · rfl
    · omega
    · rfl
  scj_tgk_eq_scj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.scj_tgk_eq_scj
      assumption
    · rfl
    · omega
    · rfl
  tgk_tgj_eq_tgj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.tgk_tgj_eq_tgj
      assumption
    · omega
    · rfl
    · rfl
  tgj_tgk_eq_tgj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.tgj_tgk_eq_tgj
      assumption
    · rfl
    · omega
    · rfl
  tgj_sck_eq_tgj := by
    intro k j f j_lt_k
    split_ifs
    · apply S.tgj_sck_eq_tgj
      assumption
    · rfl
    · omega
    · rfl
  sck_compj_eq_compj_sck := by
    intro k j f g j_lt_k sc_tg_j_gf
    simp only [CategoryStruct.comp]
    split_ifs with h₁ h₂
    · apply S.sck_compj_eq_compj_sck
      · assumption
      · simp [h₂] at sc_tg_j_gf
        assumption
    · rfl
    · rfl
    · rfl
  tgk_compj_eq_compj_tgk := by
    intro k j f g j_lt_k sc_tg_j_gf
    simp only [CategoryStruct.comp]
    split_ifs with h₁ h₂
    · apply S.tgk_compj_eq_compj_tgk
      · assumption
      · simp [h₂] at sc_tg_j_gf
        assumption
    · rfl
    · rfl
    · rfl
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
    · rfl
    · rfl
    · rfl
  is_cell := by
    intro f
    use n
    have not_n_lt_n : ¬(n < n) := (lt_self_iff_false n).mp
    simp only [cell, dif_neg not_n_lt_n]

section Functor

variable {n : ℕ} {C : Type u} {D : Type v} [SC : NCategory n C] [SD : NCategory n D]

/-- TODO: Document. -/
def NFunctor.discrete (F : NFunctor n C D) (m : ℕ) (n_lt_m : n < m) :
    letI := SC.discrete m n_lt_m
    letI := SD.discrete m n_lt_m
    NFunctor m C D :=
  letI := SC.discrete m n_lt_m
  letI := SD.discrete m n_lt_m
  {
    map := F.map
    map_sc_eq_sc_map := by
      intro k f
      simp only [NCategory.discrete]
      split_ifs
      · apply F.map_sc_eq_sc_map
      · rfl
    map_tg_eq_tg_map := by
      intro k f
      simp only [NCategory.discrete]
      split_ifs
      · apply F.map_tg_eq_tg_map
      · rfl
    map_comp_eq_comp_map := by
      intro k f g sc_tg_gf
      simp only [NCategory.discrete, CategoryStruct.comp]
      split_ifs with h
      · apply F.map_comp_eq_comp_map
        simp [h] at sc_tg_gf
        assumption
      · rfl
  }

/-- TODO: Document. -/
def NFunctor.discreteOmega (F : NFunctor n C D) :
    letI := SC.discreteOmega
    letI := SD.discreteOmega
    OmegaFunctor C D :=
  letI := SC.discreteOmega
  letI := SD.discreteOmega
  {
    map := F.map
    map_sc_eq_sc_map := by
      intro k f
      simp only [NCategory.discreteOmega]
      split_ifs
      · apply F.map_sc_eq_sc_map
      · rfl
    map_tg_eq_tg_map := by
      intro k f
      simp only [NCategory.discreteOmega]
      split_ifs
      · apply F.map_tg_eq_tg_map
      · rfl
    map_comp_eq_comp_map := by
      intro k f g sc_tg_gf
      simp only [NCategory.discreteOmega, CategoryStruct.comp]
      split_ifs with h
      · apply F.map_comp_eq_comp_map
        simp [h] at sc_tg_gf
        assumption
      · rfl
  }

end Functor

end HigherCategoryTheory.SingleSorted
