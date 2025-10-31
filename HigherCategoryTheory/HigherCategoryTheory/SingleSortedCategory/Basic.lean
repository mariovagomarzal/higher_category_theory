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

* `sc i f`: The source of `f` at dimension `i`.
* `tg i f`: The target of `f` at dimension `i`.
* `g ♯.[i] f`: The partial composition of `g` and `f` at dimension `i`.
* `g ♯[i] f ← comp_gf`: The composition of `g` and `f` at dimension `i`, given a proof
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

/-- A `SingleSortedCategoryStruct` on a type `Obj` indexed by a type `index` (equipped with
`NatIndex`) consists of:
- Source and target operations `Sc` and `Tg` at each dimension `i : index`.
- A partial composition operation `PComp` at each dimension.
- An axiom `pcomp_dom` asserting that composition is defined precisely when
  `Sc i g = Tg i f`.

This is the basic structure underlying single-sorted categories, before imposing any other
axioms (like identity laws, associativity, etc.). -/
@[ext]
class SingleSortedCategoryStruct (Obj : Type u) (index : Type) [NatIndex index] where
  /-- Source operation at dimension `i`. -/
  Sc : index → Obj → Obj
  /-- Target operation at dimension `i`. -/
  Tg : index → Obj → Obj
  /-- Partial composition operation at dimension `i`. -/
  PComp : index → Obj → Obj →. Obj
  /-- Composition `PComp i g f` is defined if and only if `Sc i g = Tg i f`. -/
  pcomp_dom : ∀ {i : index} {f g : Obj}, (PComp i g f).Dom ↔ Sc i g = Tg i f := by
    /- In most cases, when defining the partial composition `Pcomp`, the domain condition trivially
    coincides with the condition `Sc i g = Tg i f`. Thus, in these cases, proving both directions of
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
@[inherit_doc] scoped notation g " ♯.[" i "] " f:100 => SingleSortedCategoryStruct.PComp i g f

/-- The composability condition at dimension `i`. Two morphisms `g` and `f` are composable at
dimension `i` when `sc i g = tg i f`. -/
def sc_is_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct Obj index]
    (i : index) (g f : Obj) : Prop :=
  sc i g = tg i f

/--
If `g` and `f` are composable at dimension `i` (i.e., `sc_is_tg i g f`), then the partial
composition `g ♯.[i] f` is defined.

This can be used to get a proof of the domain of the partial composition.
-/
theorem dom_of_sc_is_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct Obj index]
    {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f) :
    (g ♯.[i] f).Dom :=
  SingleSortedCategoryStruct.pcomp_dom.mpr comp_gf

/-- The (total) composition operation at dimension `i`, defined for composable morphisms.
Given `f` and `g` with a proof `composable_gf : sc_is_tg i g f`, this returns the
composite `g ♯[i] f`. -/
def SingleSortedCategoryStruct.comp {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedCategoryStruct Obj index]
    (i : index) (g f : Obj) (composable_gf : sc_is_tg i g f) : Obj :=
  (g ♯.[i] f).get (dom_of_sc_is_tg composable_gf)

@[inherit_doc]
scoped notation g " ♯[" i "] " f " ← " comp_gf:100 => SingleSortedCategoryStruct.comp i g f comp_gf

/-- Congruence lemma for composition: if `g₁ = g₂` and `f₁ = f₂`, and both pairs are composable,
then their composites are equal. -/
theorem congr_pcomp {Obj : Type u} {index : Type} [NatIndex index]
    [S : SingleSortedCategoryStruct Obj index]
    {i : index} {f₁ f₂ g₁ g₂ : Obj} (eq_g₁g₂ : g₁ = g₂) (eq_f₁f₂ : f₁ = f₂)
    (comp_g₁f₁ : sc_is_tg i g₁ f₁) (comp_g₂f₂ : sc_is_tg i g₂ f₂) :
    g₁ ♯[i] f₁ ← comp_g₁f₁ = g₂ ♯[i] f₂ ← comp_g₂f₂ := by
  have pcomp_eq : g₁ ♯.[i] f₁ = g₂ ♯.[i] f₂ :=
    congrArg₂ (· ♯.[i] ·) eq_g₁g₂ eq_f₁f₂
  let comp_g₁f₁_dom := dom_of_sc_is_tg comp_g₁f₁
  let comp_g₂f₂_dom := dom_of_sc_is_tg comp_g₂f₂
  apply (Part.eq_iff_of_dom comp_g₁f₁_dom comp_g₂f₂_dom).mpr pcomp_eq

/-- A `SingleSortedCategoryFamily` is a `SingleSortedCategoryStruct` satisfying the axioms of a
single-sorted category at each dimension. -/
class SingleSortedCategoryFamily (Obj : Type u) (index : Type) [NatIndex index]
    extends SingleSortedCategoryStruct Obj index where
  /-- Applying source twice at dimension `i` is idempotent. -/
  sc_sc_is_sc : ∀ (i : index) (f : Obj), sc i (sc i f) = sc i f := by intros; rfl
  /-- The target of a source is itself. -/
  tg_sc_is_sc : ∀ (i : index) (f : Obj), tg i (sc i f) = sc i f := by intros; rfl
  /-- The source of a target is itself. -/
  sc_tg_is_tg : ∀ (i : index) (f : Obj), sc i (tg i f) = tg i f := by intros; rfl
  /-- Applying target twice at dimension `i` is idempotent. -/
  tg_tg_is_tg : ∀ (i : index) (f : Obj), tg i (tg i f) = tg i f := by intros; rfl
  /-- The source of a composite `g ♯[i] f` is the source of `f`. -/
  sc_comp_is_sc : ∀ {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f),
      sc i (g ♯[i] f ← comp_gf) = sc i f := by intros; rfl
  /-- The target of a composite `g ♯[i] f` is the target of `g`. -/
  tg_comp_is_tg : ∀ {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f),
      tg i (g ♯[i] f ← comp_gf) = tg i g := by intros; rfl
  /-- Composing `f` with its source `sc i f` yields `f`. -/
  comp_sc_is_id : ∀ (i : index) (f : Obj),
      f ♯[i] (sc i f) ← (tg_sc_is_sc _ _).symm = f := by intros; rfl
  /-- Composing the target `tg i f` with `f` yields `f`. -/
  comp_tg_is_id : ∀ (i : index) (f : Obj),
    (tg i f) ♯[i] f ← (sc_tg_is_tg _ _) = f := by intros; rfl
  /-- If `g` and `f` compose and `h` and `g` compose, then `h` and `g ♯[i] f` compose. This is an
  auxiliary method for the associativity axiom. -/
  compr_assoc {i : index} {f g h : Obj}
      (comp_gf : sc_is_tg i g f) (comp_hg : sc_is_tg i h g) :
      sc_is_tg i h (g ♯[i] f ← comp_gf) :=
    comp_hg.trans (tg_comp_is_tg comp_gf).symm
  /-- If `g` and `f` compose and `h` and `g` compose, then `h ♯[i] g` and `f` compose. This is an
  auxiliary method for the associativity axiom. -/
  compl_assoc {i : index} {f g h : Obj}
      (comp_gf : sc_is_tg i g f) (comp_hg : sc_is_tg i h g) :
      sc_is_tg i (h ♯[i] g ← comp_hg) f :=
    (sc_comp_is_sc comp_hg).trans comp_gf
  /-- If `g` and `f` compose and `h` and `g` compose, then the two ways of composing `h`, `g`, and
  `f` exist and are equal, that is, composition is associative. -/
  assoc : ∀ {i : index} {f g h : Obj} (comp_gf : sc_is_tg i g f) (comp_hg : sc_is_tg i h g),
      (h ♯[i] (g ♯[i] f ← comp_gf) ← (compr_assoc comp_gf comp_hg)) =
      ((h ♯[i] g ← comp_hg) ♯[i] f ← (compl_assoc comp_gf comp_hg)) := by intros; rfl

/-- A `SingleSorted2CategoryFamily` is a `SingleSortedCategoryFamily` with additional axioms
ensuring compatibility between two dimensions of composition. -/
class SingleSorted2CategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedCategoryFamily Obj index where
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
    extends SingleSortedCategoryFamily Obj (Fin 1)

/-- A single-sorted 2-category: a `SingleSorted2CategoryFamily` with two dimensions, indexed by
`Fin 2`. -/
class SingleSorted2Category (Obj : Type u)
    extends SingleSorted2CategoryFamily Obj (Fin 2)

/-- A single-sorted n-category for a fixed `n : ℕ`: a `SingleSorted2CategoryFamily` with `n`
dimensions, indexed by `Fin n`. -/
class SingleSortedNCategory (Obj : Type u) (n : ℕ)
    extends SingleSorted2CategoryFamily Obj (Fin n)

/-- A single-sorted ω-category: a `SingleSorted2CategoryFamily` with infinitely many dimensions,
indexed by `ℕ`. -/
class SingleSortedOmegaCategory (Obj : Type u)
    extends SingleSorted2CategoryFamily Obj ℕ where
  /-- Every element is a k-cell for some `k : ℕ`. -/
  is_cell : ∀ f : Obj, ∃ k : ℕ, sc k f = f

end HigherCategoryTheory
