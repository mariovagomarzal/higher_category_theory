/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.Init

/-!
# Proof automation for higher category theory

This file provides the `hcat_disch` tactic, a proof automation tool for discharging common goals in
higher category theory proofs. It is used extensively as the default proof method for most of the
definitions of the library.

TODO: The tactics in this file are currently incomplete.
-/

namespace HigherCategoryTheory

-- Add the `omega` tactic as a safe rule for the `HigherCategoryTheory` Aesop rule set.
add_aesop_rules safe (rule_sets := [HigherCategoryTheory]) [(by omega)]

/-- A wrapper around Aesop for the `HigherCategoryTheory` rule set. -/
macro (name := aesop_hcat) "aesop_hcat" c:Aesop.tactic_clause* : tactic =>
  `(tactic| aesop $c* (rule_sets := [HigherCategoryTheory]))

/--
A tactic for discharging common goals in higher category theory proofs. This tactic first attempts
reflexivity (for definitional equalities), then omega (for arithmetic goals on indices), and finally
grind (for more complex goals involving equational reasoning).

TODO: This tactic is incomplete.
-/
macro (name := hcat_disch) "hcat_disch" : tactic =>
  `(tactic|
    first
    | (intros; rfl)
    | aesop_hcat)

end HigherCategoryTheory
