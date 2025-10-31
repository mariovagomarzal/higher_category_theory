/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.PFun
import Mathlib.Data.Part
import HigherCategoryTheory.Data.NatIndex

/-!
# Single-sorted presentation of higher-order categories

This file defines the single-sorted presentation of higher order categories, where objects,
morphisms, 2-morphisms, and higher morphisms all live in a single type, distinguished by source and
target operations, and a partial composition operation at each dimension.

## Notation

* `sc k f`: The source of `f` at dimension `k`.
* `tg k f`: The target of `f` at dimension `k`.
* `g ♯.[k] f`: The partial composition of `g` and `f` at dimension `k`.
* `g ♯[k] f ← comp_gf`: The composition of `g` and `f` at dimension `k`, given a proof
  `comp_gf` that they are composable.

## Implementation notes

The formalization uses the `NatIndex` typeclass to handle index sets uniformly, allowing both
finite dimensions (via `Fin n`) and infinite dimensions (via `ℕ`). This design choice enables
defining $n$-categories and $\omega$-categories within a single framework.

The partial composition operation `PComp` is a partial function that returns a `Part Obj` (partial
function) whose domain is determined by the composability condition. The definitional composition
operation `SingleSortedCategoryStruct.comp` extracts the value using a proof of composability.
-/

universe u

namespace HigherCategoryTheory

/-- A `SingleSortedCategoryStruct` indexed by a type `index` (equipped with `NatIndex`) on a
type `Obj` consists of:
- Source and target operations `Sc` and `Tg` at each dimension `k : index`.
- A partial composition operation `PComp` at each dimension.
- An axiom `pcomp_dom` asserting that composition is defined precisely when
  `Sc k g = Tg k f`.

This is the basic structure underlying single-sorted categories, before imposing any other
axioms (like identity laws, associativity, etc.). -/
@[ext]
class SingleSortedCategoryStruct (index : Type) [NatIndex index] (Obj : Type u) where
  /-- Source operation at dimension `k`. -/
  Sc : index → Obj → Obj
  /-- Target operation at dimension `k`. -/
  Tg : index → Obj → Obj
  /-- Partial composition operation at dimension `k`. -/
  PComp : index → Obj → Obj →. Obj
  /-- Composition `PComp k g f` is defined if and only if `Sc k g = Tg k f`. -/
  pcomp_dom : ∀ {k : index} {f g : Obj}, (PComp k g f).Dom ↔ Sc k g = Tg k f := by
    /- In most cases, when defining the partial composition `Pcomp`, the domain condition trivially
    coincides with the condition `Sc k g = Tg k f`. Thus, in these cases, proving both directions of
    the implication simply consists of simplifying the hypothesis and the goal, and providing
    the hypothesis as the conclusion. -/
    intros
    apply Iff.intro <;> {
      intro h
      simp at *
      -- We use `try` because in the simplest cases `simp at *` already closes the goal, making
      -- `exact h` unnecessary.
      try exact h
    }

@[inherit_doc] scoped prefix:max "sc " => SingleSortedCategoryStruct.Sc
@[inherit_doc] scoped prefix:max "tg " => SingleSortedCategoryStruct.Tg
@[inherit_doc] scoped notation g " ♯.[" k "] " f:100 => SingleSortedCategoryStruct.PComp k g f

/-- The composability condition at dimension `k`. Two morphisms `g` and `f` are composable at
dimension `k` when `sc k g = tg k f`. -/
def sc_is_tg {index : Type} [NatIndex index] {Obj : Type u}
    [SingleSortedCategoryStruct index Obj]
    (k : index) (g f : Obj) : Prop :=
  sc k g = tg k f

/--
If `g` and `f` are composable at dimension `k` (i.e., `sc_is_tg k g f`), then the partial
composition `g ♯.[k] f` is defined.

This can be used to get a proof of the domain of the partial composition.
-/
theorem dom_of_sc_is_tg {index : Type} [NatIndex index] {Obj : Type u}
    [SingleSortedCategoryStruct index Obj]
    {k : index} {f g : Obj} (comp_gf : sc_is_tg k g f) :
    (g ♯.[k] f).Dom :=
  SingleSortedCategoryStruct.pcomp_dom.mpr comp_gf

/-- The (total) composition operation at dimension `k`, defined for composable morphisms.
Given `f` and `g` with a proof `composable_gf : sc_is_tg k g f`, this returns the
composite `g ♯[k] f`. -/
def SingleSortedCategoryStruct.comp {index : Type} [NatIndex index] {Obj : Type u}
    [SingleSortedCategoryStruct index Obj]
    (k : index) (g f : Obj) (composable_gf : sc_is_tg k g f) : Obj :=
  (g ♯.[k] f).get (dom_of_sc_is_tg composable_gf)

@[inherit_doc]
scoped notation g " ♯[" k "] " f " ← " comp_gf:100 => SingleSortedCategoryStruct.comp k g f comp_gf

/-- Congruence lemma for composition: if `g₁ = g₂` and `f₁ = f₂`, and both pairs are composable,
then their composites are equal. -/
theorem congr_pcomp {index : Type} [NatIndex index] {Obj : Type u}
    [S : SingleSortedCategoryStruct index Obj]
    {k : index} {f₁ f₂ g₁ g₂ : Obj} (eq_g₁g₂ : g₁ = g₂) (eq_f₁f₂ : f₁ = f₂)
    (comp_g₁f₁ : sc_is_tg k g₁ f₁) (comp_g₂f₂ : sc_is_tg k g₂ f₂) :
    g₁ ♯[k] f₁ ← comp_g₁f₁ = g₂ ♯[k] f₂ ← comp_g₂f₂ := by
  have pcomp_eq : g₁ ♯.[k] f₁ = g₂ ♯.[k] f₂ :=
    congrArg₂ (· ♯.[k] ·) eq_g₁g₂ eq_f₁f₂
  let comp_g₁f₁_dom := dom_of_sc_is_tg comp_g₁f₁
  let comp_g₂f₂_dom := dom_of_sc_is_tg comp_g₂f₂
  apply (Part.eq_iff_of_dom comp_g₁f₁_dom comp_g₂f₂_dom).mpr pcomp_eq

/-- A `SingleSortedCategoryFamily` is a `SingleSortedCategoryStruct` satisfying the axioms of a
single-sorted category at each dimension. -/
class SingleSortedCategoryFamily (index : Type) [NatIndex index] (Obj : Type u)
    extends SingleSortedCategoryStruct index Obj where
  /-- Applying source twice at dimension `k` is idempotent. -/
  sc_sc_is_sc : ∀ (k : index) (f : Obj), sc k (sc k f) = sc k f := by intros; rfl
  /-- The target of a source is itself. -/
  tg_sc_is_sc : ∀ (k : index) (f : Obj), tg k (sc k f) = sc k f := by intros; rfl
  /-- The source of a target is itself. -/
  sc_tg_is_tg : ∀ (k : index) (f : Obj), sc k (tg k f) = tg k f := by intros; rfl
  /-- Applying target twice at dimension `k` is idempotent. -/
  tg_tg_is_tg : ∀ (k : index) (f : Obj), tg k (tg k f) = tg k f := by intros; rfl
  /-- The source of a composite `g ♯[k] f` is the source of `f`. -/
  sc_comp_is_sc : ∀ {k : index} {f g : Obj} (comp_gf : sc_is_tg k g f),
      sc k (g ♯[k] f ← comp_gf) = sc k f := by intros; rfl
  /-- The target of a composite `g ♯[k] f` is the target of `g`. -/
  tg_comp_is_tg : ∀ {k : index} {f g : Obj} (comp_gf : sc_is_tg k g f),
      tg k (g ♯[k] f ← comp_gf) = tg k g := by intros; rfl
  /-- Composing `f` with its source `sc k f` yields `f`. -/
  comp_sc_is_id : ∀ (k : index) (f : Obj),
      f ♯[k] (sc k f) ← (tg_sc_is_sc _ _).symm = f := by intros; rfl
  /-- Composing the target `tg k f` with `f` yields `f`. -/
  comp_tg_is_id : ∀ (k : index) (f : Obj),
    (tg k f) ♯[k] f ← (sc_tg_is_tg _ _) = f := by intros; rfl
  /-- If `g` and `f` compose and `h` and `g` compose, then `h` and `g ♯[k] f` compose. This is an
  auxiliary method for the associativity axiom. -/
  compr_assoc {k : index} {f g h : Obj}
      (comp_gf : sc_is_tg k g f) (comp_hg : sc_is_tg k h g) :
      sc_is_tg k h (g ♯[k] f ← comp_gf) :=
    comp_hg.trans (tg_comp_is_tg comp_gf).symm
  /-- If `g` and `f` compose and `h` and `g` compose, then `h ♯[k] g` and `f` compose. This is an
  auxiliary method for the associativity axiom. -/
  compl_assoc {k : index} {f g h : Obj}
      (comp_gf : sc_is_tg k g f) (comp_hg : sc_is_tg k h g) :
      sc_is_tg k (h ♯[k] g ← comp_hg) f :=
    (sc_comp_is_sc comp_hg).trans comp_gf
  /-- If `g` and `f` compose and `h` and `g` compose, then the two ways of composing `h`, `g`, and
  `f` exist and are equal, that is, composition is associative. -/
  assoc : ∀ {k : index} {f g h : Obj} (comp_gf : sc_is_tg k g f) (comp_hg : sc_is_tg k h g),
      (h ♯[k] (g ♯[k] f ← comp_gf) ← (compr_assoc comp_gf comp_hg)) =
      ((h ♯[k] g ← comp_hg) ♯[k] f ← (compl_assoc comp_gf comp_hg)) := by intros; rfl

/-- A `SingleSorted2CategoryFamily` is a `SingleSortedCategoryFamily` with additional axioms
ensuring compatibility between two dimensions of composition. -/
class SingleSorted2CategoryFamily (index : Type) [NatIndex index]
    (Obj : Type u)
    extends SingleSortedCategoryFamily index Obj where
  /-- Applying source at dimension `k` to a source at a lower dimension `j < k` yields the source
  at dimension `j`. -/
  sck_scj_is_scj : ∀ {k j : index} (f : Obj),
      j < k → sc k (sc j f) = sc j f := by intros; rfl
  /-- Applying source at dimension `j` to a source at a higher dimension `k > j` yields the source
  at dimension `j`. -/
  scj_sck_is_scj : ∀ {k j : index} (f : Obj),
      j < k → sc j (sc k f) = sc j f := by intros; rfl
  /-- Applying source at dimension `j` to a target at a higher dimension `k > j` yields the source
  at dimension `j`. -/
  scj_tgk_is_scj : ∀ {k j : index} (f : Obj),
      j < k → sc j (tg k f) = sc j f := by intros; rfl
  /-- Applying target at dimension `k` to a target at a lower dimension `j < k` yields the target
  at dimension `j`. -/
  tgk_tgj_is_tgj : ∀ {k j : index} (f : Obj),
      j < k → tg k (tg j f) = tg j f := by intros; rfl
  /-- Applying target at dimension `j` to a target at a higher dimension `k > j` yields the target
  at dimension `j`. -/
  tgj_tgk_is_tgj : ∀ {k j : index} (f : Obj),
      j < k → tg j (tg k f) = tg j f := by intros; rfl
  /-- Applying target at dimension `j` to a source at a higher dimension `k > j` yields the target
  at dimension `j`. -/
  tgj_sck_is_tgj : ∀ {k j : index} (f : Obj),
      j < k → tg j (sc k f) = tg j f := by intros; rfl
  /-- If `g` and `f` are composable at dimension `j < k`, then `sc k g` and `sc k f` are composable
  at dimension `j`. This is an auxiliary method for the distributivity axioms. -/
  comp_j_sc {k j : index} {f g : Obj} (j_lt_k : j < k) (comp_j_gf : sc_is_tg j g f) :
      sc_is_tg j (sc k g) (sc k f) := calc
    sc j (sc k g)
    _ = sc j g := scj_sck_is_scj _ j_lt_k
    _ = tg j f := comp_j_gf
    _ = tg j (sc k f) := (tgj_sck_is_tgj _ j_lt_k).symm
  /-- If `g` and `f` are composable at dimension `j < k`, then `tg k g` and `tg k f` are composable
  at dimension `j`. This is an auxiliary method for the distributivity axioms. -/
  comp_j_tg {k j : index} {f g : Obj} (j_lt_k : j < k) (comp_j_gf : sc_is_tg j g f) :
      sc_is_tg j (tg k g) (tg k f) := calc
    sc j (tg k g)
    _ = sc j g := scj_tgk_is_scj _ j_lt_k
    _ = tg j f := comp_j_gf
    _ = tg j (tg k f) := (tgj_tgk_is_tgj _ j_lt_k).symm
  /-- Source at dimension `k` distributes over composition at dimension `j < k`. -/
  sck_compj_is_compj_sck : ∀ {k j : index} {f g : Obj} (j_lt_k : j < k)
      (comp_j_gf : sc_is_tg j g f),
      sc k (g ♯[j] f ← comp_j_gf) =
      (sc k g) ♯[j] (sc k f) ← (comp_j_sc j_lt_k comp_j_gf) := by intros; rfl
  /-- Target at dimension `k` distributes over composition at dimension `j < k`. -/
  tgk_compj_is_compj_tgk : ∀ {k j : index} {f g : Obj} (j_lt_k : j < k)
      (comp_j_gf : sc_is_tg j g f),
      tg k (g ♯[j] f ← comp_j_gf) =
      (tg k g) ♯[j] (tg k f) ← (comp_j_tg j_lt_k comp_j_gf) := by intros; rfl
  /-- Given a $2 \times 2$ pasting diagram of composable morphisms, we can compose first vertically
  and then horizontally. An auxiliary method for the `exchange` axiom. -/
  comp_k_exchange {k j : index} {f₁ f₂ g₁ g₂ : Obj} (j_lt_k : j < k)
      (comp_k_g₂g₁ : sc_is_tg k g₂ g₁) (comp_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (comp_j_g₂f₂ : sc_is_tg j g₂ f₂) (comp_j_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg k (g₂ ♯[j] f₂ ← comp_j_g₂f₂) (g₁ ♯[j] f₁ ← comp_j_g₁f₁) := calc
    sc k (g₂ ♯[j] f₂ ← comp_j_g₂f₂)
    _ = (sc k g₂) ♯[j] (sc k f₂) ← (comp_j_sc j_lt_k comp_j_g₂f₂) :=
      sck_compj_is_compj_sck j_lt_k comp_j_g₂f₂
    _ = (tg k g₁) ♯[j] (tg k f₁) ← (comp_j_tg j_lt_k comp_j_g₁f₁) :=
      congr_pcomp comp_k_g₂g₁ comp_k_f₂f₁
        (comp_j_sc j_lt_k comp_j_g₂f₂) (comp_j_tg j_lt_k comp_j_g₁f₁)
    _ = tg k (g₁ ♯[j] f₁ ← comp_j_g₁f₁) := (tgk_compj_is_compj_tgk j_lt_k comp_j_g₁f₁).symm
  /-- Given a $2 \times 2$ pasting diagram of composable morphisms, we can compose first
  horizontally and then vertically. An auxiliary method for the `exchange` axiom. -/
  comp_j_exchange {k j : index} {f₁ f₂ g₁ g₂ : Obj} (j_lt_k : j < k)
      (comp_k_g₂g₁ : sc_is_tg k g₂ g₁) (comp_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (comp_j_g₂f₂ : sc_is_tg j g₂ f₂) (comp_j_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg j (g₂ ♯[k] g₁ ← comp_k_g₂g₁) (f₂ ♯[k] f₁ ← comp_k_f₂f₁) := calc
    sc j (g₂ ♯[k] g₁ ← comp_k_g₂g₁)
    _ = sc j (sc k (g₂ ♯[k] g₁ ← comp_k_g₂g₁)) := (scj_sck_is_scj _ j_lt_k).symm
    _ = sc j (sc k g₁) := congrArg (fun x => sc j x) (sc_comp_is_sc comp_k_g₂g₁)
    _ = sc j g₁ := scj_sck_is_scj _ j_lt_k
    _ = tg j f₁ := comp_j_g₁f₁
    _ = tg j (sc k f₁) := (tgj_sck_is_tgj _ j_lt_k).symm
    _ = tg j (sc k (f₂ ♯[k] f₁ ← comp_k_f₂f₁)) :=
      congrArg (fun x => tg j x) (sc_comp_is_sc comp_k_f₂f₁).symm
    _ = tg j (f₂ ♯[k] f₁ ← comp_k_f₂f₁) := tgj_sck_is_tgj _ j_lt_k
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
  exchange : ∀ {k j : index} {f₁ f₂ g₁ g₂ : Obj} (j_lt_k : j < k)
      (comp_k_g₂g₁ : sc_is_tg k g₂ g₁) (comp_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (comp_j_g₂f₂ : sc_is_tg j g₂ f₂) (comp_j_g₁f₁ : sc_is_tg j g₁ f₁),
      (g₂ ♯[j] f₂ ← comp_j_g₂f₂) ♯[k] (g₁ ♯[j] f₁ ← comp_j_g₁f₁) ←
        (comp_k_exchange j_lt_k comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁) =
      (g₂ ♯[k] g₁ ← comp_k_g₂g₁) ♯[j] (f₂ ♯[k] f₁ ← comp_k_f₂f₁) ←
        (comp_j_exchange j_lt_k comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁) := by intros; rfl

/-- A single-sorted category: a `SingleSortedCategoryFamily` with a single dimension, indexed by
`Fin 1`. -/
class SingleSortedCategory (Obj : Type u)
    extends SingleSortedCategoryFamily (Fin 1) Obj

/-- A single-sorted 2-category: a `SingleSorted2CategoryFamily` with two dimensions, indexed by
`Fin 2`. -/
class SingleSorted2Category (Obj : Type u)
    extends SingleSorted2CategoryFamily (Fin 2) Obj

/-- A single-sorted n-category for a fixed `n : ℕ`: a `SingleSorted2CategoryFamily` with `n`
dimensions, indexed by `Fin n`. -/
class SingleSortedNCategory (n : ℕ) (Obj : Type u)
    extends SingleSorted2CategoryFamily (Fin n) Obj

/-- A single-sorted ω-category: a `SingleSorted2CategoryFamily` with infinitely many dimensions,
indexed by `ℕ`. -/
class SingleSortedOmegaCategory (Obj : Type u)
    extends SingleSorted2CategoryFamily ℕ Obj where
  /-- Every element is a k-cell for some `k : ℕ`. -/
  is_cell : ∀ f : Obj, ∃ k : ℕ, sc k f = f

end HigherCategoryTheory
