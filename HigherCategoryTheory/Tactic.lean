/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/

/-!
# Proof automation for higher category theory

This file provides the `hcat_disch` tactic, a proof automation tool for discharging common goals in
higher category theory proofs. It is used extensively as the default proof method for most of the
definitions of the library.
-/

namespace HigherCategoryTheory

/--
A tactic for discharging common goals in higher category theory proofs. This tactic first attempts
reflexivity (for definitional equalities), then omega (for arithmetic goals on indices), and finally
grind (for more complex goals involving equational reasoning).

TODO: This tactic is incomplete and highly inefficient.
-/
macro (name := hcat_disch) "hcat_disch" : tactic =>
  `(tactic| first | (intros; rfl) | omega | grind)

end HigherCategoryTheory
