/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Algebra.Group.Defs
import HigherCategoryTheory.SingleSorted.Category

/-!
# Monoids as single-sorted categories

This file defines monoid-related instances of single-sorted categories.
-/

universe u

namespace Monoid

open HigherCategoryTheory

/--
An instance from `Monoid M` to `SingleSortedNCategory 1 M`.

Every monoid is a single-sorted $1$-category where all morphisms have the same source and target,
the unit, and composition is always defined via monoid multiplication.
-/
instance instSingleSorted1Category (M : Type u) [Monoid M] : SingleSortedNCategory 1 M where
  sc _ _ := 1
  tg _ _ := 1
  pcomp _ b a := ⟨True, fun _ ↦ b * a⟩
  compk_sck_eq_id := by intros; apply mul_one
  compk_tgk_eq_id := by intros; apply one_mul
  assoc := by intros; apply mul_assoc

end Monoid
