/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Algebra.Group.Defs
import HigherCategoryTheory.SingleSorted.Category

/-!
# Monoids as single-sorted categories

This file defines monoid-related instances of single-sorted categories.
-/

universe u

namespace Monoid.SingleSorted

open HigherCategoryTheory.SingleSorted

/-- Every monoid is a single-sorted pre-category where all morphisms have the same source and
target, the unit, and composition is always defined via monoid multiplication. -/
instance instPreCategory (Index : Type) (M : Type u) [Monoid M] : PreCategory Index M where
  sc _ _ := 1
  tg _ _ := 1
  pcomp _ b a := ⟨True, fun _ ↦ b * a⟩
  compk_sck_eq_id := by intros; apply mul_one
  compk_tgk_eq_id := by intros; apply one_mul
  assoc := by intros; apply mul_assoc

/-- Specialization of the monoid pre-category instance to `NCategory 1`. -/
instance (priority := 1100) inst1Category (M : Type u) [Monoid M] : NCategory 1 M :=
  PreCategory.lift

end Monoid.SingleSorted
