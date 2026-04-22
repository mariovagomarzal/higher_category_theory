/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Aesop

/-!
# Higher Category Theory Rule Set and Options

In this file we define the `HigherCategoryTheory` rule set for Aesop as well as some options for
controlling custom behavior of the library.
-/

declare_aesop_rule_sets [HigherCategoryTheory]

/-- Option to override the suggestive behavior of `hcat_disch` and `aesop_hcat`. -/
register_option hcat.tactic.suggest : Bool := {
  defValue := false
  descr := "The `hcat_disch` and `aesop_hcat` tactics produce \"Try this\" suggestions."
}

/-- Option to control whether `aesop_hcat` runs in non-terminal mode. -/
register_option hcat.tactic.nonterminal : Bool := {
  defValue := false
  descr := "The `aesop_hcat` tactic runs in non-terminal mode."
}

/-- Option to control whether a wrapped `omega` is tried as part of `hcat_disch`. -/
register_option hcat.tactic.omega : Bool := {
  defValue := false
  descr := "A wrapped version of `omega` is tried as part of the `hcat_disch` tactic."
}
