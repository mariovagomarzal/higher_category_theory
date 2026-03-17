/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.Fin.Basic
import HigherCategoryTheory.Tactic

/-!
# Single-sorted presentation of higher-order categories

This file defines the single-sorted presentation of higher-order categories, where objects,
morphisms, 2-morphisms, and higher morphisms all live in a single type, distinguished by source and
target operations, and a partial composition operation at each dimension.

In a single-sorted presentation, unlike the traditional many-sorted approach, all morphisms
(including what would traditionally be called objects, 1-morphisms, 2-morphisms, etc.) are elements
of a single type. The dimension of a morphism is determined by source and target operations at each
level, and composition is defined as a partial operation that is only defined when certain
source-target matching conditions are satisfied.

## Main definitions

* `CategoryStruct`: The basic structure with source, target, and partial composition
  operations, along with the composability condition.
* `PreCategory`: A structure satisfying the single-sorted category axioms at each
  dimension.
* `Category`: A structure with additional axioms ensuring compatibility between
  different dimensions.
* `NCategory`: A single-sorted $n$-category is a `Category` with index type
  `Fin n`, representing categories with exactly `n` dimensions.
* `OmegaCategory`: A single-sorted $\omega$-category is a `Category` with
  index type `ℕ`, together with an axiom ensuring every morphism is a $k$-cell for some finite `k`.

## Notation

* `sc` and `tg`: Source and target operations at each dimension.
* `sc_is_tg k g f`: The composability condition at dimension `k`, stating that the source of `g` at
  dimension `k` equals the target of `f` at dimension `k`.
* `g ♯.[k] f`: The partial composition of `g` and `f` at dimension `k`.
* `g ♯[k] f ← sc_tg_gf`: The composition of `g` and `f` at dimension `k`, given a proof `sc_tg_gf`
  that the source of `g` at dimension `k` equals the target of `f` at dimension `k`.

## Implementation notes

The formalization uses partial functions (`PFun`) from Mathlib to represent composition, that is,
functions that return a value of type `Part obj`.  The `pcomp_dom` axiom characterizes exactly when
composition is defined.

## References

* [vidal2024higher]
-/

universe u

namespace HigherCategoryTheory.SingleSorted

/--
The basic structure of a single-sorted category, parametrized by an index type.

This structure contains only the data and the composability condition; the structure axioms are
defined in `PreCategory` and `Category`.
-/
class CategoryStruct (index : Type) (obj : Type u) where
  /-- Source operation at dimension `k`. -/
  sc : index → obj → obj
  /-- Target operation at dimension `k`. -/
  tg : index → obj → obj
  /-- Partial composition operation at dimension `k`. -/
  pcomp : index → obj → obj →. obj
  /-- The composition of `g` and `f` at dimension `k` is defined if and only if the source of `g` at
  dimension `k` equals the target of `f` at dimension `k`. -/
  pcomp_dom : ∀ {k : index} {f g : obj}, (pcomp k g f).Dom ↔ sc k g = tg k f := by
    /- In most cases, when defining the partial composition `pcomp`, the domain condition trivially
    coincides with the condition `sc k g = tg k f`. Thus, in these cases, proving both directions of
    the implication simply consists of simplifying the hypothesis and the goal, and providing
    the hypothesis as the conclusion. -/
    intros
    apply Iff.intro <;> {
      intro h
      simp at *
      -- We use `try` because, in some trivial cases, `simp at *` already closes the goal, making
      -- `exact h` unnecessary.
      try exact h
    }

namespace CategoryStruct

variable {index : Type} {obj : Type u} [CategoryStruct index obj]
variable {k : index} {f g : obj}

@[inherit_doc]
scoped[HigherCategoryTheory.SingleSorted] notation g " ♯.[" k "] " f:100 =>
  CategoryStruct.pcomp k g f

/-- A method to express the composability condition for morphisms `g` and `f` at dimension `k`, that
is, that the source of `g` at dimension `k` equals the target of `f` at dimension `k`. -/
@[simp high]
def sc_is_tg (k : index) (g f : obj) : Prop := sc k g = tg k f

/-- If `g` and `f` satisfy the composability condition `sc_is_tg k g f`, then the partial
composition `g ♯.[k] f` is defined. This lemma represents the forward direction of the
`pcomp_dom` axiom. -/
lemma dom_of_sc_is_tg (sc_tg_gf : sc_is_tg k g f) : (g ♯.[k] f).Dom := pcomp_dom.mpr sc_tg_gf

/-- If the partial composition `g ♯.[k] f` is defined, then `g` and `f` satisfy the composability
condition `sc_is_tg k g f`. This is the backward direction of the `pcomp_dom` axiom, that is, the
converse of `dom_of_sc_is_tg`. -/
lemma sc_is_tg_of_dom (dom_gf : (g ♯.[k] f).Dom) : sc_is_tg k g f := pcomp_dom.mp dom_gf

/-- The (total) composition operation at dimension `k`, defined for composable morphisms.
Given morphisms `f` and `g` with a proof of `sc_is_tg k g f`, this returns their composite
`g ♯[k] f`. -/
@[simp high]
def comp (k : index) (g f : obj) (sc_tg_gf : sc_is_tg k g f) : obj :=
  (g ♯.[k] f).get (dom_of_sc_is_tg sc_tg_gf)

@[inherit_doc]
scoped[HigherCategoryTheory.SingleSorted] notation g " ♯[" k "] " f " ← " sc_tg_gf:100 =>
  CategoryStruct.comp k g f sc_tg_gf

end CategoryStruct

-- Export the main components of `CategoryStruct` for easier access.
export CategoryStruct (sc tg sc_is_tg)

section Congruence

variable {index : Type} {obj : Type u} [CategoryStruct index obj]
variable {k : index} {f₁ f₂ g₁ g₂ : obj}

/-- Congruence lemma for the domain of partial composition: if `f₁ = f₂` and `g₁ = g₂`, and the
partial composition `g₁ ♯.[k] f₁` is defined, then `g₂ ♯.[k] f₂` is also defined. -/
lemma congr_dom (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (dom_g₁f₁ : (g₁ ♯.[k] f₁).Dom) :
    (g₂ ♯.[k] f₂).Dom := by
  grind

/-- Congruence lemma for composability: if `f₁ = f₂` and `g₁ = g₂`, and `g₁` is composable with
`f₁` at dimension `k`, then `g₂` is composable with `f₂` at dimension `k`. -/
lemma congr_sc_is_tg (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (sc_tg_g₁f₁ : sc_is_tg k g₁ f₁) :
    sc_is_tg k g₂ f₂ := by
  grind

/-- Congruence lemma for partial composition: if `f₁ = f₂` and `g₁ = g₂`, then the partial
compositions `g₁ ♯.[k] f₁` and `g₂ ♯.[k] f₂` are equal as partial functions. -/
lemma congr_pcomp (k : index) (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) :
    g₁ ♯.[k] f₁ = g₂ ♯.[k] f₂  := by
  grind

/-- Congruence lemma for total composition (first-pair version): if `f₁ = f₂` and `g₁ = g₂`, then
the compositions `g₁ ♯[k] f₁` and `g₂ ♯[k] f₂` are equal, using the composability proof from the
first pair. -/
lemma congr_comp₁ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₁f₁ : sc_is_tg k g₁ f₁) :
    g₁ ♯[k] f₁ ← sc_tg_g₁f₁ = g₂ ♯[k] f₂ ← congr_sc_is_tg eq_f eq_g sc_tg_g₁f₁ := by
  grind

/-- Congruence lemma for total composition (second-pair verion): if `f₁ = f₂` and `g₁ = g₂`, then
the compositions `g₁ ♯[k] f₁` and `g₂ ♯[k] f₂` are equal, using the composability proof from the
second pair. -/
lemma congr_comp₂ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₂f₂ : sc_is_tg k g₂ f₂) :
    g₁ ♯[k] f₁ ← congr_sc_is_tg eq_f.symm eq_g.symm sc_tg_g₂f₂ = g₂ ♯[k] f₂ ← sc_tg_g₂f₂ := by
  grind

end Congruence

/--
A preliminary version of a single-sorted category.

This structure captures the axioms that govern behavior within a single dimension, including:
* **Idempotency**: Sources and targets are idempotent.
* **Identity laws**: Composing with sources and targets yields identities.
* **Associativity**: Composition is associative at each dimension.

This serves as an intermediate step in the construction of `Category`, allowing us to
establish dimension-specific properties before enforcing cross-dimensional compatibility.
-/
class PreCategory (index : Type) [LinearOrder index] (obj : Type u)
    extends CategoryStruct index obj where
  /-- Applying source twice at dimension `k` is idempotent. -/
  sck_sck_eq_sck : ∀ (k : index) (f : obj), sc k (sc k f) = sc k f := by hcat_disch
  /-- The target of a source is itself. -/
  tgk_sck_eq_sck : ∀ (k : index) (f : obj), tg k (sc k f) = sc k f := by hcat_disch
  /-- The source of a target is itself. -/
  sck_tgk_eq_tgk : ∀ (k : index) (f : obj), sc k (tg k f) = tg k f := by hcat_disch
  /-- Applying target twice at dimension `k` is idempotent. -/
  tgk_tgk_eq_tgk : ∀ (k : index) (f : obj), tg k (tg k f) = tg k f := by hcat_disch
  /-- The source of a composite `g ♯[k] f` is the source of `f`. -/
  sck_compk_eq_sck : ∀ {k : index} {f g : obj} (sc_tg_gf : sc_is_tg k g f),
      sc k (g ♯[k] f ← sc_tg_gf) = sc k f := by
    hcat_disch
  /-- The target of a composite `g ♯[k] f` is the target of `g`. -/
  tgk_compk_eq_tgk : ∀ {k : index} {f g : obj} (sc_tg_gf : sc_is_tg k g f),
      tg k (g ♯[k] f ← sc_tg_gf) = tg k g := by
    hcat_disch
  /-- Composing `f` with its source `sc k f` yields `f`. -/
  compk_sck_eq_id : ∀ (k : index) (f : obj),
      f ♯[k] (sc k f) ← (tgk_sck_eq_sck k f).symm = f := by
    hcat_disch
  /-- Composing the target `tg k f` with `f` yields `f`. -/
  compk_tgk_eq_id : ∀ (k : index) (f : obj),
      (tg k f) ♯[k] f ← (sck_tgk_eq_tgk k f) = f := by
    hcat_disch
  /-- If `g` and `f` compose and `h` and `g` compose, then `h ♯[k] g` and `f` compose. This is an
  auxiliary method for the associativity axiom. -/
  protected compl_assoc {k : index} {f g h : obj}
      (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g) :
      sc_is_tg k (h ♯[k] g ← sc_tg_hg) f := calc
    _
    _ = sc k g := sck_compk_eq_sck sc_tg_hg
    _ = tg k f := sc_tg_gf
  /-- If `g` and `f` compose and `h` and `g` compose, then `h` and `g ♯[k] f` compose. This is an
  auxiliary method for the associativity axiom. -/
  protected compr_assoc {k : index} {f g h : obj}
      (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g) :
      sc_is_tg k h (g ♯[k] f ← sc_tg_gf) := calc
    sc k h
    _ = tg k g := sc_tg_hg
    _ = _ := (tgk_compk_eq_tgk sc_tg_gf).symm
  /-- The **associative property**: if `g` and `f` compose and `h` and `g` compose, then the two
  ways of composing `h`, `g`, and `f` exist and are equal. -/
  assoc : ∀ {k : index} {f g h : obj} (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g),
      ((h ♯[k] g ← sc_tg_hg) ♯[k] f ← (compl_assoc sc_tg_gf sc_tg_hg)) =
      (h ♯[k] (g ♯[k] f ← sc_tg_gf) ← (compr_assoc sc_tg_gf sc_tg_hg)) := by
    hcat_disch

-- Use axioms of `PreCategory` as simp lemmas.
open PreCategory in
attribute [simp] sck_sck_eq_sck tgk_sck_eq_sck sck_tgk_eq_tgk tgk_tgk_eq_tgk sck_compk_eq_sck
  tgk_compk_eq_tgk compk_sck_eq_id compk_tgk_eq_id assoc

/--
A **single-sorted category** is a `PreCategory` with additional axioms ensuring
compatibility between different dimensions.

This structure extends `PreCategory` by adding cross-dimensional axioms that govern how
operations at different dimensions interact:
* **Source/target interaction**: How source and target operations at different dimensions commute.
* **Distributivity**: Source and target operations distribute over composition at lower dimensions.
* **Exchange law**: Stating that composing first horizontally then vertically yields the same result
  as composing first vertically then horizontally
-/
class Category (index : Type) [LinearOrder index] (obj : Type u)
    extends PreCategory index obj where
  /-- Applying source at dimension `k` to a source at a lower dimension `j < k` yields the source
  at dimension `j`. -/
  sck_scj_eq_scj : ∀ {k j : index} (f : obj), j < k → sc k (sc j f) = sc j f := by hcat_disch
  /-- Applying source at dimension `j` to a source at a higher dimension `k > j` yields the source
  at dimension `j`. -/
  scj_sck_eq_scj : ∀ {k j : index} (f : obj), j < k → sc j (sc k f) = sc j f := by hcat_disch
  /-- Applying source at dimension `j` to a target at a higher dimension `k > j` yields the source
  at dimension `j`. -/
  scj_tgk_eq_scj : ∀ {k j : index} (f : obj), j < k → sc j (tg k f) = sc j f := by hcat_disch
  /-- Applying target at dimension `k` to a target at a lower dimension `j < k` yields the target
  at dimension `j`. -/
  tgk_tgj_eq_tgj : ∀ {k j : index} (f : obj), j < k → tg k (tg j f) = tg j f := by hcat_disch
  /-- Applying target at dimension `j` to a target at a higher dimension `k > j` yields the target
  at dimension `j`. -/
  tgj_tgk_eq_tgj : ∀ {k j : index} (f : obj), j < k → tg j (tg k f) = tg j f := by hcat_disch
  /-- Applying target at dimension `j` to a source at a higher dimension `k > j` yields the target
  at dimension `j`. -/
  tgj_sck_eq_tgj : ∀ {k j : index} (f : obj), j < k → tg j (sc k f) = tg j f := by hcat_disch
  /-- If `g` and `f` are composable at dimension `j < k`, then `sc k g` and `sc k f` are composable
  at dimension `j`. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_j_sc {k j : index} {f g : obj} (j_lt_k : j < k) (sc_tg_j_gf : sc_is_tg j g f) :
      sc_is_tg j (sc k g) (sc k f) := calc
    sc j (sc k g)
    _ = sc j g := scj_sck_eq_scj g j_lt_k
    _ = tg j f := sc_tg_j_gf
    _ = tg j (sc k f) := (tgj_sck_eq_tgj f j_lt_k).symm
  /-- If `g` and `f` are composable at dimension `j < k`, then `tg k g` and `tg k f` are composable
  at dimension `j`. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_j_tg {k j : index} {f g : obj} (j_lt_k : j < k) (sc_tg_j_gf : sc_is_tg j g f) :
      sc_is_tg j (tg k g) (tg k f) := calc
    sc j (tg k g)
    _ = sc j g := scj_tgk_eq_scj g j_lt_k
    _ = tg j f := sc_tg_j_gf
    _ = tg j (tg k f) := (tgj_tgk_eq_tgj f j_lt_k).symm
  /-- Source at dimension `k` distributes over composition at dimension `j < k`. -/
  sck_compj_eq_compj_sck : ∀ {k j : index} {f g : obj} (j_lt_k : j < k)
      (sc_tg_j_gf : sc_is_tg j g f),
      sc k (g ♯[j] f ← sc_tg_j_gf) =
      (sc k g) ♯[j] (sc k f) ← (sc_tg_j_sc j_lt_k sc_tg_j_gf) := by
    hcat_disch
  /-- Target at dimension `k` distributes over composition at dimension `j < k`. -/
  tgk_compj_eq_compj_tgk : ∀ {k j : index} {f g : obj} (j_lt_k : j < k)
      (sc_tg_j_gf : sc_is_tg j g f),
      tg k (g ♯[j] f ← sc_tg_j_gf) =
      (tg k g) ♯[j] (tg k f) ← (sc_tg_j_tg j_lt_k sc_tg_j_gf) := by
    hcat_disch
  /-- Given morphisms `f₁, f₂, g₁, g₂` where `g₂` is composable with `f₂` at dimension `j`, `g₁` is
  composable with `f₁` at dimension `j`, `g₂` is composable with `g₁` at dimension `k`, and `f₂` is
  composable with `f₁` at dimension `k` (with `j < k`), then `g₂ ♯[j] f₂` is composable with
  `g₁ ♯[j] f₁` at dimension `k`. This is an auxiliary method for the `exchange` axiom. -/
  protected sc_tg_k_exchange {k j : index} {f₁ f₂ g₁ g₂ : obj} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_k_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_k_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg k (g₂ ♯[j] f₂ ← sc_tg_k_g₂f₂) (g₁ ♯[j] f₁ ← sc_tg_k_g₁f₁) := calc
    _
    _ = (sc k g₂) ♯[j] (sc k f₂) ← (sc_tg_j_sc j_lt_k sc_tg_k_g₂f₂) :=
      sck_compj_eq_compj_sck j_lt_k sc_tg_k_g₂f₂
    _ = (tg k g₁) ♯[j] (tg k f₁) ← (sc_tg_j_tg j_lt_k sc_tg_k_g₁f₁) :=
      congr_comp₁ sc_tg_k_f₂f₁ sc_tg_k_g₂g₁ (sc_tg_j_sc j_lt_k sc_tg_k_g₂f₂)
    _ = _ := (tgk_compj_eq_compj_tgk j_lt_k sc_tg_k_g₁f₁).symm
  /-- Given morphisms `f₁, f₂, g₁, g₂` where `g₂` is composable with `f₂` at dimension `j`, `g₁` is
  composable with `f₁` at dimension `j`, `g₂` is composable with `g₁` at dimension `k`, and `f₂` is
  composable with `f₁` at dimension `k` (with `j < k`), then `g₂ ♯[k] g₁` is composable with
  `f₂ ♯[k] f₁` at dimension `j`. This is an auxiliary method for the `exchange` axiom. -/
  protected sc_tg_j_exchange {k j : index} {f₁ f₂ g₁ g₂ : obj} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_k_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_k_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg j (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁) (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) := calc
    _
    _ = sc j (sc k (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁)) := (scj_sck_eq_scj _ j_lt_k).symm
    _ = sc j (sc k g₁) := by rw [sck_compk_eq_sck sc_tg_k_g₂g₁]
    _ = sc j g₁ := scj_sck_eq_scj g₁ j_lt_k
    _ = tg j f₁ := sc_tg_k_g₁f₁
    _ = tg j (sc k f₁) := (tgj_sck_eq_tgj f₁ j_lt_k).symm
    _ = tg j (sc k (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁)) := by rw [sck_compk_eq_sck sc_tg_k_f₂f₁]
    _ = tg j (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) := tgj_sck_eq_tgj _ j_lt_k
  /--
  The **exchange law**: Given morphisms `f₁, f₂, g₁, g₂` and indices `j < k` such that:
  - `g₂` is composable with `f₂` at dimension `j`,
  - `g₁` is composable with `f₁` at dimension `j`,
  - `g₂` is composable with `g₁` at dimension `k`, and
  - `f₂` is composable with `f₁` at dimension `k`,

  then both `(g₂ ♯[j] f₂) ♯[k] (g₁ ♯[j] f₁)` and `(g₂ ♯[k] g₁) ♯[j] (f₂ ♯[k] f₁)` are defined and
  equal. That is, composing first at dimension `j` and then at dimension `k` yields the same result
  as composing first at dimension `k` and then at dimension `j`.
  -/
  exchange : ∀ {k j : index} {f₁ f₂ g₁ g₂ : obj} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_k_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_k_g₁f₁ : sc_is_tg j g₁ f₁),
      (g₂ ♯[j] f₂ ← sc_tg_k_g₂f₂) ♯[k] (g₁ ♯[j] f₁ ← sc_tg_k_g₁f₁) ←
        (sc_tg_k_exchange j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_k_g₂f₂ sc_tg_k_g₁f₁) =
      (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁) ♯[j] (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) ←
        (sc_tg_j_exchange j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_k_g₂f₂ sc_tg_k_g₁f₁) := by
    hcat_disch

-- Use axioms of `Category` as simp lemmas.
open Category in
attribute [simp] sck_scj_eq_scj scj_sck_eq_scj scj_tgk_eq_scj tgk_tgj_eq_tgj tgj_tgk_eq_tgj
  tgj_sck_eq_tgj sck_compj_eq_compj_sck tgk_compj_eq_compj_tgk exchange

/-- A **single-sorted $n$-category** is a `Category` with index type `Fin n`,
representing a category with exactly `n` dimensions. -/
abbrev NCategory (n : ℕ) (obj : Type u) := Category (Fin n) obj

section Cells

variable {index : Type} [LinearOrder index] {obj : Type u} [Category index obj]

/-- A morphism `f` is a **$k$-cell** if `sc k f = f`. -/
@[simp]
def cell (k : index) (f : obj) : Prop :=
  sc k f = f

/-- The set of all **$k$-cells** in a single-sorted category. -/
@[simp]
def cells (k : index) (obj : Type u) [Category index obj] : Set obj :=
  {f : obj | cell k f}

end Cells

open Category in
/-- A **single-sorted $\omega$-category** is a `Category` with index type `ℕ`,
representing a category with infinitely (countably) many dimensions and an additional axiom ensuring
that every morphism is a $k$-cell for some finite `k`. -/
class OmegaCategory (obj : Type u) extends Category ℕ obj where
  /-- Every morphism is a $k$-cell for some `k : ℕ`. -/
  is_cell : ∀ f : obj, ∃ k : ℕ, cell k f

-- Use axioms of `OmegaCategory` as simp lemmas.
attribute [simp] OmegaCategory.is_cell

end HigherCategoryTheory.SingleSorted
