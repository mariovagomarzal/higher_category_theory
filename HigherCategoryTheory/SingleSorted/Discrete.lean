/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.SingleSorted.Category
import HigherCategoryTheory.SingleSorted.Functor

/-!
**Important note:** This file is work in progress and exists only to save the work done previous to
a codebase refactor.
-/

universe u v

namespace HigherCategoryTheory

variable {m : ℕ} {obj : Type u}

/-- TODO: Comment. -/
@[simp]
def SingleSortedNCategory.discrete (S : SingleSortedNCategory m obj) (n : ℕ) :
    SingleSortedNCategory n obj where
  sc k f := if h : k < m then S.sc ⟨k, h⟩ f else f
  tg k f := if h : k < m then S.tg ⟨k, h⟩ f else f
  pcomp k g f := if h : k < m then S.pcomp ⟨k, h⟩ g f else ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by
    intro k f g
    by_cases k_lt_m : k < m
    · simp [k_lt_m]
      apply S.pcomp_dom
    · simp [k_lt_m]
  sck_sck_eq_sck := by
    intro k f
    by_cases k_lt_m : k < m <;> simp [k_lt_m]
  tgk_sck_eq_sck := by
    intro k f
    by_cases k_lt_m : k < m <;> simp [k_lt_m]
  sck_tgk_eq_tgk := by
    intro k f
    by_cases k_lt_m : k < m <;> simp [k_lt_m]
  tgk_tgk_eq_tgk := by
    intro k f
    by_cases k_lt_m : k < m <;> simp [k_lt_m]
  sck_compk_eq_sck := by
    intro k f g sc_tg_gf
    by_cases k_lt_m : k < m
    · simp [k_lt_m]
      apply S.sck_compk_eq_sck
      simp [k_lt_m] at sc_tg_gf
      assumption
    · simp [k_lt_m]
  tgk_compk_eq_tgk := by
    intro k f g sc_tg_gf
    by_cases k_lt_m : k < m
    · simp [k_lt_m]
      apply S.tgk_compk_eq_tgk
      simp [k_lt_m] at sc_tg_gf
      assumption
    · simp [k_lt_m]
      simp [k_lt_m] at sc_tg_gf
      exact sc_tg_gf.symm
  compk_sck_eq_id := by
    intro k f
    by_cases k_lt_m : k < m
    · simp [k_lt_m]
      apply S.compk_sck_eq_id
    · simp [k_lt_m]
  compk_tgk_eq_id := by
    intro k f
    by_cases k_lt_m : k < m
    · simp [k_lt_m]
      apply S.compk_tgk_eq_id
    · simp [k_lt_m]
  assoc := by
    intro k f g h sc_tg_hg sc_tg_gf
    by_cases k_lt_m : k < m
    · simp [k_lt_m]
      apply S.assoc <;> (simp [k_lt_m] at *; assumption)
    · simp [k_lt_m]
  sck_scj_eq_scj := by
    intro k j f j_lt_k
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.sck_scj_eq_scj
      assumption
    · simp [k_lt_m]
  scj_tgk_eq_scj := by
    intro k j f j_lt_k
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.scj_tgk_eq_scj
      assumption
    · simp [k_lt_m]
  scj_sck_eq_scj := by
    intro k j f j_lt_k
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.scj_sck_eq_scj
      assumption
    · simp [k_lt_m]
  tgk_tgj_eq_tgj := by
    intro k j f j_lt_k
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.tgk_tgj_eq_tgj
      assumption
    · simp [k_lt_m]
  tgj_sck_eq_tgj := by
    intro k j f j_lt_k
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.tgj_sck_eq_tgj
      assumption
    · simp [k_lt_m]
  tgj_tgk_eq_tgj := by
    intro k j f j_lt_k
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.tgj_tgk_eq_tgj
      assumption
    · simp [k_lt_m]
  sck_compj_eq_compj_sck := by
    intro k j f g j_lt_k sc_tg_j_gf
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.sck_compj_eq_compj_sck
      · assumption
      · simp [j_lt_m] at *
        assumption
    · simp [k_lt_m]
      by_cases j_lt_m : j < m <;> simp [j_lt_m]
  tgk_compj_eq_compj_tgk := by
    intro k j f g j_lt_k tg_k_j_gf
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      apply S.tgk_compj_eq_compj_tgk
      · assumption
      · simp [j_lt_m] at *
        assumption
    · simp [k_lt_m]
      by_cases j_lt_m : j < m <;> simp [j_lt_m]
  exchange := by
    intro k j f₁ f₂ g₁ g₂ j_lt_k sc_tg_g₂g₁ sc_tg_f₂f₁ tg_k_g₂f₂ tg_k_g₁f₁
    by_cases k_lt_m : k < m
    · have j_lt_m : j < m := lt_trans j_lt_k k_lt_m
      simp [k_lt_m, j_lt_m]
      simp [k_lt_m, j_lt_m] at sc_tg_g₂g₁ sc_tg_f₂f₁ tg_k_g₂f₂ tg_k_g₁f₁
      apply S.exchange j_lt_k <;> assumption
    · simp [k_lt_m]
      by_cases j_lt_m : j < m <;> simp [j_lt_m]

-- TODO: Implement this following the same pattern as `SingleSortedNCategory.discrete`.
/-- TODO: Comment. -/
@[simp]
def SingleSortedNCategory.discrete_omega (S : SingleSortedNCategory m obj) :
    SingleSortedOmegaCategory obj := by sorry

variable {n : ℕ} {C : Type u} {D : Type v}
  [SC : SingleSortedNCategory n C] [SD : SingleSortedNCategory n D]

/-- TODO: Comment. -/
@[simp]
def SingleSortedNFunctor.discrete (F : SingleSortedNFunctor n C D) (m : ℕ) :
    letI := SC.discrete m
    letI := SD.discrete m
    SingleSortedNFunctor m C D :=
  let dSC := SC.discrete m
  let dSD := SD.discrete m
  {
    map := F
    map_sc_eq_sc_map := by
      intro k f
      by_cases k_lt_n : k < n
      · simp [k_lt_n]
      · simp [k_lt_n]
    map_tg_eq_tg_map := by
      intro k f
      by_cases k_lt_n : k < n
      · simp [k_lt_n]
      · simp [k_lt_n]
    map_comp_eq_comp_map := by
      intro k f g sc_tg_gf
      by_cases k_lt_n : k < n
      · simp [k_lt_n]
        apply F.map_comp_eq_comp_map
        simp [k_lt_n] at sc_tg_gf
        assumption
      · simp [k_lt_n]
  }

-- TODO: Implement this following the same pattern as `SingleSortedNFunctor.discrete`.
/-- TODO: Comment. -/
@[simp]
def SingleSortedNFunctor.discrete_omega (F : SingleSortedNFunctor n C D) :
    letI := SC.discrete_omega
    letI := SD.discrete_omega
    SingleSortedOmegaFunctor C D := by sorry

end HigherCategoryTheory
