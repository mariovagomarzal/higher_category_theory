/-
Copyright (c) 2026 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Cat
import HigherCategoryTheory.ManySorted.Category
import HigherCategoryTheory.ManySorted.Functor
import HigherCategoryTheory.ManySorted.Cat

/-!
# Discrete many-sorted categories

TODO: Comment.
-/

universe u

namespace HigherCategoryTheory.ManySorted

/-- TODO: Comment. -/
abbrev NTypeFamily.discrete {n : ℕ} (C : NTypeFamily.{u} n) (m : ℕ) : NTypeFamily.{u} m :=
  -- TODO: Find an explicit proof instead of using `omega`.
  fun k ↦ if k_le_n : k ≤ n then C ⟨k, by omega⟩ else C ⟨n, by omega⟩

/-- TODO: Comment. -/
abbrev OmegaTypeFamily.discrete {n : ℕ} (C : NTypeFamily.{u} n) : OmegaTypeFamily.{u} :=
  -- TODO: Find an explicit proof instead of using `omega`.
  fun k ↦ if k_le_n : k ≤ n then C ⟨k, by omega⟩ else C ⟨n, by omega⟩

section Category

variable {n : ℕ} {C : NTypeFamily.{u} n}

/-- TODO: Comment. -/
@[simp]
def NCategory.discrete (S : NCategory n C) (m : ℕ) (_n_lt_m : n < m) :
    NCategory m (NTypeFamily.discrete C m) := by
  sorry

/-- TODO: Comment. -/
@[simp]
def OmegaCategory.discrete (S : NCategory n C) : OmegaCategory (OmegaTypeFamily.discrete C) := by
  sorry

end Category

section Functor

variable {n : ℕ} {C : NTypeFamily.{u} n} [SC : NCategory n C]
  {D : NTypeFamily.{u} n} [SD : NCategory n D]

/-- TODO: Comment. -/
@[simp]
def NFunctor.discrete (F : NFunctor n C D) (m : ℕ) (n_lt_m : n < m) :
    letI := SC.discrete m n_lt_m
    letI := SD.discrete m n_lt_m
    NFunctor m (NTypeFamily.discrete C m) (NTypeFamily.discrete D m) :=
  letI := SC.discrete m n_lt_m
  letI := SD.discrete m n_lt_m
  by sorry

/-- TODO: Comment. -/
@[simp]
def OmegaFunctor.discrete (F : NFunctor n C D) :
    letI := OmegaCategory.discrete SC
    letI := OmegaCategory.discrete SD
    OmegaFunctor (OmegaTypeFamily.discrete C) (OmegaTypeFamily.discrete D) :=
  letI := OmegaCategory.discrete SC
  letI := OmegaCategory.discrete SD
  by sorry

end Functor

section DiscretizationFunctor

open CategoryTheory in
/-- TODO: Comment. -/
@[simp]
def DiscretizationFunctor (n m : ℕ∞) (_n_le_m : n ≤ m) : ICat.{u} n ⥤ ICat.{u} m :=
  match n, m with
  | fin _, fin _ => by sorry
  | fin _, ω => by sorry
  | ω, ω => by sorry

end DiscretizationFunctor

end HigherCategoryTheory.ManySorted
