/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Algebra.Group.Defs
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic

/-!
# Monoids as single-sorted categories

This file shows that every monoid can be viewed as a single-sorted category, where the monoid
elements are the morphisms and monoid multiplication is composition.
-/

universe u

namespace Monoid

open HigherCategoryTheory

/-- Every monoid `M` is a single-sorted category where all morphisms have the same source and
target (the unit), and composition is given by monoid multiplication. -/
instance instSingleSortedCategory (M : Type u) [Monoid M] : SingleSortedCategory M where
  Sc _ _ := 1
  Tg _ _ := 1
  PComp _ b a := ⟨_, fun _ ↦ b * a⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      rfl
    · intro h
      simp
      simp at h
      exact h
  comp_sc_is_id := mul_one _
  comp_tg_is_id := one_mul _
  assoc _ _ := (mul_assoc _ _ _).symm

end Monoid
