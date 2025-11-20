/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.Fin.Basic

/-!
# Single-sorted presentation of higher-order categories

This file defines the single-sorted presentation of higher order categories, where objects,
morphisms, 2-morphisms, and higher morphisms all live in a single type, distinguished by source and
target operations, and a partial composition operation at each dimension.

## Notation

* `g ♯.[k] f`: The partial composition of `g` and `f` at dimension `k`.
* `g ♯[k] f ← sc_tg_gf`: The composition of `g` and `f` at dimension `k`, given a proof
  `sc_tg_gf` that the source of `g` at dimension `k` equals the target of `f` at dimension `k`.
-/

universe u

namespace HigherCategoryTheory

/-- TODO: Comment. -/
macro (name := hcat_disch) "hcat_disch" : tactic =>
  `(tactic| first | (intros; rfl) | omega | grind)

/-- TODO: Comment. -/
class SingleSortedCategoryStruct (index : Type) (obj : Type u) where
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

namespace SingleSortedCategoryStruct

variable {index : Type} {obj : Type u} [SingleSortedCategoryStruct index obj]
variable {k : index} {f g : obj}

@[inherit_doc]
scoped[HigherCategoryTheory] notation g " ♯.[" k "] " f:100 =>
  SingleSortedCategoryStruct.pcomp k g f

/-- TODO: Comment. -/
@[simp]
def sc_is_tg (k : index) (g f : obj) : Prop :=
  sc k g = tg k f

/-- TODO: Comment. -/
theorem dom_of_sc_is_tg (sc_tg_gf : sc_is_tg k g f) : (g ♯.[k] f).Dom :=
  pcomp_dom.mpr sc_tg_gf

/-- TODO: Comment. -/
theorem sc_is_tg_of_dom (dom_gf : (g ♯.[k] f).Dom) : sc_is_tg k g f :=
  pcomp_dom.mp dom_gf

/-- TODO: Comment. -/
@[simp]
def comp (k : index) (g f : obj) (sc_tg_gf : sc_is_tg k g f) : obj :=
  (g ♯.[k] f).get (dom_of_sc_is_tg sc_tg_gf)

@[inherit_doc]
scoped[HigherCategoryTheory] notation g " ♯[" k "] " f " ← " sc_tg_gf:100 =>
  SingleSortedCategoryStruct.comp k g f sc_tg_gf

end SingleSortedCategoryStruct

-- Export the main components of `SingleSortedCategoryStruct` for easier access.
export SingleSortedCategoryStruct (sc tg sc_is_tg)

section Congruence

variable {index : Type} {obj : Type u} [SingleSortedCategoryStruct index obj]
variable {k : index} {f₁ f₂ g₁ g₂ : obj}

/-- TODO: Comment. -/
theorem congr_dom (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (dom_g₁f₁ : (g₁ ♯.[k] f₁).Dom) :
    (g₂ ♯.[k] f₂).Dom := by
  grind

/-- TODO: Comment. -/
theorem congr_sc_is_tg (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (sc_tg_g₁f₁ : sc_is_tg k g₁ f₁) :
    sc_is_tg k g₂ f₂ := by
  grind

/-- TODO: Comment. -/
theorem congr_pcomp (k : index) (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) :
    g₁ ♯.[k] f₁ = g₂ ♯.[k] f₂  := by
  grind

/-- TODO: Comment. -/
theorem congr_comp₁ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₁f₁ : sc_is_tg k g₁ f₁) :
    g₁ ♯[k] f₁ ← sc_tg_g₁f₁ = g₂ ♯[k] f₂ ← congr_sc_is_tg eq_f eq_g sc_tg_g₁f₁ := by
  grind

/-- TODO: Comment. -/
theorem congr_comp₂ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₂f₂ : sc_is_tg k g₂ f₂) :
    g₁ ♯[k] f₁ ← congr_sc_is_tg eq_f.symm eq_g.symm sc_tg_g₂f₂ = g₂ ♯[k] f₂ ← sc_tg_g₂f₂ := by
  grind

end Congruence

/-- TODO: Comment. -/
class PreSingleSortedCategory (index : Type) [LinearOrder index] (obj : Type u)
    extends SingleSortedCategoryStruct index obj where
  /-- Applying source twice at dimension `k` is idempotent. -/
  sck_sck_is_sck : ∀ (k : index) (f : obj), sc k (sc k f) = sc k f := by hcat_disch
  /-- The target of a source is itself. -/
  tgk_sck_is_sck : ∀ (k : index) (f : obj), tg k (sc k f) = sc k f := by hcat_disch
  /-- The source of a target is itself. -/
  sck_tgk_is_tgk : ∀ (k : index) (f : obj), sc k (tg k f) = tg k f := by hcat_disch
  /-- Applying target twice at dimension `k` is idempotent. -/
  tgk_tgk_is_tgk : ∀ (k : index) (f : obj), tg k (tg k f) = tg k f := by hcat_disch
  /-- The source of a composite `g ♯[k] f` is the source of `f`. -/
  sck_compk_is_sck : ∀ {k : index} {f g : obj} (sc_tg_gf : sc_is_tg k g f),
      sc k (g ♯[k] f ← sc_tg_gf) = sc k f := by hcat_disch
  /-- The target of a composite `g ♯[k] f` is the target of `g`. -/
  tgk_compk_is_tgk : ∀ {k : index} {f g : obj} (sc_tg_gf : sc_is_tg k g f),
      tg k (g ♯[k] f ← sc_tg_gf) = tg k g := by hcat_disch
  /-- Composing `f` with its source `sc k f` yields `f`. -/
  compk_sck_is_id : ∀ (k : index) (f : obj),
      f ♯[k] (sc k f) ← (tgk_sck_is_sck k f).symm = f := by hcat_disch
  /-- Composing the target `tg k f` with `f` yields `f`. -/
  compk_tgk_is_id : ∀ (k : index) (f : obj),
    (tg k f) ♯[k] f ← (sck_tgk_is_tgk k f) = f := by hcat_disch
  /-- If `g` and `f` compose and `h` and `g` compose, then `h ♯[k] g` and `f` compose. This is an
  auxiliary method for the associativity axiom. -/
  protected compl_assoc {k : index} {f g h : obj}
      (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g) :
      sc_is_tg k (h ♯[k] g ← sc_tg_hg) f := calc
    _
    _ = sc k g := sck_compk_is_sck sc_tg_hg
    _ = tg k f := sc_tg_gf
  /-- If `g` and `f` compose and `h` and `g` compose, then `h` and `g ♯[k] f` compose. This is an
  auxiliary method for the associativity axiom. -/
  protected compr_assoc {k : index} {f g h : obj}
      (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g) :
      sc_is_tg k h (g ♯[k] f ← sc_tg_gf) := calc
    sc k h
    _ = tg k g := sc_tg_hg
    _ = _ := (tgk_compk_is_tgk sc_tg_gf).symm
  /-- If `g` and `f` compose and `h` and `g` compose, then the two ways of composing `h`, `g`, and
  `f` exist and are equal, that is, composition is associative. -/
  assoc : ∀ {k : index} {f g h : obj} (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g),
      ((h ♯[k] g ← sc_tg_hg) ♯[k] f ← (compl_assoc sc_tg_gf sc_tg_hg)) =
      (h ♯[k] (g ♯[k] f ← sc_tg_gf) ← (compr_assoc sc_tg_gf sc_tg_hg)) := by hcat_disch

-- Use axioms of `PreSingleSortedCategory` as simp lemmas.
open PreSingleSortedCategory in
attribute [simp] sck_sck_is_sck tgk_sck_is_sck sck_tgk_is_tgk tgk_tgk_is_tgk sck_compk_is_sck
  tgk_compk_is_tgk compk_sck_is_id compk_tgk_is_id assoc

/-- TODO: Comment. -/
class SingleSortedCategory (index : Type) [LinearOrder index] (obj : Type u)
    extends PreSingleSortedCategory index obj where
  /-- Applying source at dimension `k` to a source at a lower dimension `j < k` yields the source
  at dimension `j`. -/
  sck_scj_is_scj : ∀ {k j : index} (f : obj),
      j < k → sc k (sc j f) = sc j f := by hcat_disch
  /-- Applying source at dimension `j` to a source at a higher dimension `k > j` yields the source
  at dimension `j`. -/
  scj_sck_is_scj : ∀ {k j : index} (f : obj),
      j < k → sc j (sc k f) = sc j f := by hcat_disch
  /-- Applying source at dimension `j` to a target at a higher dimension `k > j` yields the source
  at dimension `j`. -/
  scj_tgk_is_scj : ∀ {k j : index} (f : obj),
      j < k → sc j (tg k f) = sc j f := by hcat_disch
  /-- Applying target at dimension `k` to a target at a lower dimension `j < k` yields the target
  at dimension `j`. -/
  tgk_tgj_is_tgj : ∀ {k j : index} (f : obj),
      j < k → tg k (tg j f) = tg j f := by hcat_disch
  /-- Applying target at dimension `j` to a target at a higher dimension `k > j` yields the target
  at dimension `j`. -/
  tgj_tgk_is_tgj : ∀ {k j : index} (f : obj),
      j < k → tg j (tg k f) = tg j f := by hcat_disch
  /-- Applying target at dimension `j` to a source at a higher dimension `k > j` yields the target
  at dimension `j`. -/
  tgj_sck_is_tgj : ∀ {k j : index} (f : obj),
      j < k → tg j (sc k f) = tg j f := by hcat_disch
  /-- If `g` and `f` are composable at dimension `j < k`, then `sc k g` and `sc k f` are composable
  at dimension `j`. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_j_sc {k j : index} {f g : obj} (j_lt_k : j < k) (sc_tg_j_gf : sc_is_tg j g f) :
      sc_is_tg j (sc k g) (sc k f) := calc
    sc j (sc k g)
    _ = sc j g := scj_sck_is_scj g j_lt_k
    _ = tg j f := sc_tg_j_gf
    _ = tg j (sc k f) := (tgj_sck_is_tgj f j_lt_k).symm
  /-- If `g` and `f` are composable at dimension `j < k`, then `tg k g` and `tg k f` are composable
  at dimension `j`. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_j_tg {k j : index} {f g : obj} (j_lt_k : j < k) (sc_tg_j_gf : sc_is_tg j g f) :
      sc_is_tg j (tg k g) (tg k f) := calc
    sc j (tg k g)
    _ = sc j g := scj_tgk_is_scj g j_lt_k
    _ = tg j f := sc_tg_j_gf
    _ = tg j (tg k f) := (tgj_tgk_is_tgj f j_lt_k).symm
  /-- Source at dimension `k` distributes over composition at dimension `j < k`. -/
  sck_compj_is_compj_sck : ∀ {k j : index} {f g : obj} (j_lt_k : j < k)
      (sc_tg_j_gf : sc_is_tg j g f),
      sc k (g ♯[j] f ← sc_tg_j_gf) =
      (sc k g) ♯[j] (sc k f) ← (sc_tg_j_sc j_lt_k sc_tg_j_gf) := by hcat_disch
  /-- Target at dimension `k` distributes over composition at dimension `j < k`. -/
  tgk_compj_is_compj_tgk : ∀ {k j : index} {f g : obj} (j_lt_k : j < k)
      (sc_tg_j_gf : sc_is_tg j g f),
      tg k (g ♯[j] f ← sc_tg_j_gf) =
      (tg k g) ♯[j] (tg k f) ← (sc_tg_j_tg j_lt_k sc_tg_j_gf) := by hcat_disch
  /-- Given a $2 \times 2$ pasting diagram of composable morphisms, we can compose first vertically
  and then horizontally. This is an auxiliary method for the `exchange` axiom. -/
  protected sc_tg_k_exchange {k j : index} {f₁ f₂ g₁ g₂ : obj} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_k_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_k_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg k (g₂ ♯[j] f₂ ← sc_tg_k_g₂f₂) (g₁ ♯[j] f₁ ← sc_tg_k_g₁f₁) := calc
    _
    _ = (sc k g₂) ♯[j] (sc k f₂) ← (sc_tg_j_sc j_lt_k sc_tg_k_g₂f₂) :=
      sck_compj_is_compj_sck j_lt_k sc_tg_k_g₂f₂
    _ = (tg k g₁) ♯[j] (tg k f₁) ← (sc_tg_j_tg j_lt_k sc_tg_k_g₁f₁) :=
      congr_comp₁ sc_tg_k_f₂f₁ sc_tg_k_g₂g₁ (sc_tg_j_sc j_lt_k sc_tg_k_g₂f₂)
    _ = _ := (tgk_compj_is_compj_tgk j_lt_k sc_tg_k_g₁f₁).symm
  /-- Given a $2 \times 2$ pasting diagram of composable morphisms, we can compose first
  horizontally and then vertically. This is an auxiliary method for the `exchange` axiom. -/
  protected sc_tg_j_exchange {k j : index} {f₁ f₂ g₁ g₂ : obj} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_k_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_k_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg j (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁) (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) := calc
    _
    _ = sc j (sc k (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁)) := (scj_sck_is_scj _ j_lt_k).symm
    _ = sc j (sc k g₁) := by rw [sck_compk_is_sck sc_tg_k_g₂g₁]
    _ = sc j g₁ := scj_sck_is_scj g₁ j_lt_k
    _ = tg j f₁ := sc_tg_k_g₁f₁
    _ = tg j (sc k f₁) := (tgj_sck_is_tgj f₁ j_lt_k).symm
    _ = tg j (sc k (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁)) := by rw [sck_compk_is_sck sc_tg_k_f₂f₁]
    _ = tg j (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) := tgj_sck_is_tgj _ j_lt_k
  /--
  Given a $2 \times 2$ pasting diagram of composable morphisms,
  ```
  g₂ --[j]--> f₂
   |           |
  [k]         [k]
   |           |
   ↓           ↓
  g₁ --[j]--> f₁,
  ```
  where `j < k`, the two ways of composing the diagram (vertically then horizontally, or
  horizontally then vertically) yield the same result.
  -/
  exchange : ∀ {k j : index} {f₁ f₂ g₁ g₂ : obj} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_k_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_k_g₁f₁ : sc_is_tg j g₁ f₁),
      (g₂ ♯[j] f₂ ← sc_tg_k_g₂f₂) ♯[k] (g₁ ♯[j] f₁ ← sc_tg_k_g₁f₁) ←
        (sc_tg_k_exchange j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_k_g₂f₂ sc_tg_k_g₁f₁) =
      (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁) ♯[j] (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) ←
        (sc_tg_j_exchange j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_k_g₂f₂ sc_tg_k_g₁f₁) := by
    hcat_disch

-- Use axioms of `SingleSortedCategory` as simp lemmas.
open SingleSortedCategory in
attribute [simp] sck_scj_is_scj scj_sck_is_scj scj_tgk_is_scj tgk_tgj_is_tgj tgj_tgk_is_tgj
  tgj_sck_is_tgj sck_compj_is_compj_sck tgk_compj_is_compj_tgk exchange

namespace SingleSortedCategory

open PreSingleSortedCategory

variable {index : Type} [LinearOrder index] {obj : Type u} [SingleSortedCategory index obj]

section Cells

/-- A morphism `f` is a $k$-cell (via source) if `sc k f = f`. This means `f` behaves as an
identity at dimension $k$. -/
@[simp]
def cell_sc (k : index) (f : obj) : Prop :=
  sc k f = f

/-- A morphism `f` is a $k$-cell (via target) if `tg k f = f`. This means `f` behaves as an
identity at dimension $k$. -/
@[simp]
def cell_tg (k : index) (f : obj) : Prop :=
  tg k f = f

/-- TODO: Comment. -/
@[simp]
abbrev cell (k : index) (f : obj) : Prop :=
  cell_sc k f

/-- TODO: Comment. -/
theorem cell_sc_iff_cell_tg (k : index) (f : obj) :
    cell_sc k f ↔ cell_tg k f := by
  apply Iff.intro
  · intro sc_eq
    calc
      tg k f
      _ = tg k (sc k f) := by rw [sc_eq]
      _ = sc k f := tgk_sck_is_sck k f
      _ = f := sc_eq
  · intro tg_eq
    calc
      sc k f
      _ = sc k (tg k f) := by rw [tg_eq]
      _ = tg k f := sck_tgk_is_tgk k f
      _ = f := tg_eq

/-- TODO: Comment. -/
@[simp]
def cells_sc (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  {f : obj | cell_sc k f}

/-- TODO: Comment. -/
@[simp]
def cells_tg (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  {f : obj | cell_tg k f}

/-- TODO: Comment. -/
theorem cell_sc_eq_cell_tg (k : index) (obj : Type u) [SingleSortedCategory index obj] :
    cells_sc k obj = cells_tg k obj := by
  ext f
  exact cell_sc_iff_cell_tg k f

/-- TODO: Comment. -/
@[simp]
abbrev cells (k : index) (obj : Type u) [SingleSortedCategory index obj] : Set obj :=
  cells_sc k obj

end Cells

end SingleSortedCategory

/-- TODO: Comment. -/
abbrev SingleSortedNCategory (n : ℕ) (obj : Type u) := SingleSortedCategory (Fin n) obj

/-- TODO: Comment. -/
abbrev SingleSorted1Category (obj : Type u) := SingleSortedNCategory 1 obj

namespace SingleSorted1Category

/-- TODO: Comment. -/
def ofPreSingleSortedCategory {obj : Type u} (PS1 : PreSingleSortedCategory (Fin 1) obj) :
    SingleSorted1Category obj := {PS1 with}

end SingleSorted1Category

open SingleSortedCategory in
/-- TODO: Comment. -/
class SingleSortedOmegaCategory (obj : Type u) extends SingleSortedCategory ℕ obj where
  /-- Every element is a k-cell for some `k : ℕ`. -/
  is_cell : ∀ f : obj, ∃ k : ℕ, cell k f

-- Use axioms of `SingleSortedOmegaCategory` as simp lemmas.
attribute [simp] SingleSortedOmegaCategory.is_cell

namespace SingleSortedOmegaCategory

-- TODO: Add useful lemmas and definitions about `SingleSortedOmegaCategory` here.

end SingleSortedOmegaCategory

end HigherCategoryTheory
