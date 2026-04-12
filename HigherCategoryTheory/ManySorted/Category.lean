/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Part
import Mathlib.Data.PFun
import Mathlib.Order.Fin.Basic
import HigherCategoryTheory.Indices
import HigherCategoryTheory.Tactic

/-!
# Many-sorted presentation of higher-order categories

This file defines the many-sorted presentation of higher-order categories, where morphisms at each
dimension live in separate types, connected by source, target, and identity maps between dimensions.
Composition at each dimension is defined as a partial operation on morphisms of the same dimension,
subject to appropriate source-target matching conditions.

In a many-sorted presentation, unlike the single-sorted approach, the morphisms at each dimension
`k` form a separate type `C k`. The operations (source, target, identity, composition) are
parameterized by pairs of indices `(k, j)` with `j < k`.

## Main definitions

* `CategoryStruct`: The basic structure with source, target, identity, and partial composition
  operations, along with the composability condition.
* `PreCategory`: A structure satisfying the many-sorted category axioms at each pair of dimensions,
  ensuring that each pair `(k, j)` with `j < k` independently forms a classical category with
  objects `C j` and morphisms `C k`.
* `Category`: A structure with additional cross-dimensional axioms ensuring compatibility between
  different pairs of dimensions.

## Notation

* `sc` and `tg`: Source and target operations at dimensions `(k, j)`.
* `sc_is_tg k j g f`: The composability condition at dimensions `(k, j)`, stating that the source
  of `g` at `(k, j)` equals the target of `f` at `(k, j)`.
* `g ♯.[k,j] f`: The partial composition of `g` and `f` at dimensions `(k, j)`.
* `g ♯[k,j] f ← sc_tg_gf`: The composition of `g` and `f` at dimensions `(k, j)`, given a proof
  `sc_tg_gf` that the source of `g` equals the target of `f` at `(k, j)`.

## Implementation notes

The formalization uses partial functions (`PFun`) from Mathlib to represent composition, that is,
functions that return a value of type `Part (C k)`. The `pcomp_dom` axiom characterizes exactly when
composition is defined.

## References

* [vidal2024higher]
-/

universe u

namespace HigherCategoryTheory.ManySorted

/--
The basic structure of a many-sorted category, parametrized by an index type and a family of types.

This structure contains only the data and the composability condition; the structure axioms are
defined in `PreCategory` and `Category`.
-/
class CategoryStruct (Index : Type) [Preorder Index] (C : Index → Type u) where
  /-- Source operation at dimensions `(k, j)`. Maps `k`-morphisms to `j`-morphisms. -/
  sc : (k : Index) → (j : IndexBelow k) → C k → C j
  /-- Target operation at dimensions `(k, j)`. Maps `k`-morphisms to `j`-morphisms. -/
  tg : (k : Index) → (j : IndexBelow k) → C k → C j
  /-- Identity operation at dimensions `(k, j)`. Lifts `j`-morphisms to `k`-morphisms. -/
  idm : (k : Index) → (j : IndexBelow k) → C j → C k
  /-- Partial composition operation at dimensions `(k, j)`. -/
  pcomp : (k : Index) → (j : IndexBelow k) → C k → C k →. C k
  /-- The composition of `g` and `f` at dimensions `(k, j)` is defined if and only if the source of
  `g` at `(k, j)` equals the target of `f` at `(k, j)`. -/
  pcomp_dom : ∀ {k : Index} {j : IndexBelow k} {f g : C k},
      (pcomp k j g f).Dom ↔ sc k j g = tg k j f := by
    hcat_disch

namespace CategoryStruct

variable {Index : Type} [Preorder Index] {C : Index → Type u} [CategoryStruct Index C]
variable {k : Index} {j : IndexBelow k} {f g : C k}

@[inherit_doc]
scoped[HigherCategoryTheory.ManySorted] notation g " ♯.[" k "," j "] " f:100 =>
  CategoryStruct.pcomp k j g f

/-- A method to express the composability condition for morphisms `g` and `f` at dimensions `(k,
j)`, that is, that the source of `g` at `(k, j)` equals the target of `f` at `(k, j)`. -/
@[simp high]
def sc_is_tg (k : Index) (j : IndexBelow k) (g f : C k) : Prop := sc k j g = tg k j f

/-- If `g` and `f` satisfy the composability condition `sc_is_tg k j g f`, then the partial
composition `g ♯.[k,j] f` is defined. This lemma represents the forward direction of the `pcomp_dom`
axiom. -/
lemma dom_of_sc_is_tg (sc_tg_gf : sc_is_tg k j g f) : (g ♯.[k,j] f).Dom :=
  pcomp_dom.mpr sc_tg_gf

/-- If the partial composition `g ♯.[k,j] f` is defined, then `g` and `f` satisfy the composability
condition `sc_is_tg k j g f`. This is the backward direction of the `pcomp_dom` axiom, that is, the
converse of `dom_of_sc_is_tg`. -/
lemma sc_is_tg_of_dom (dom_gf : (g ♯.[k,j] f).Dom) : sc_is_tg k j g f := pcomp_dom.mp dom_gf

/-- The (total) composition operation at dimensions `(k, j)`, defined for composable morphisms.
Given morphisms `f` and `g` with a proof of `sc_is_tg k j g f`, this returns their composite
`g ♯[k,j] f`. -/
@[simp high]
def comp (k : Index) (j : IndexBelow k) (g f : C k) (sc_tg_gf : sc_is_tg k j g f) : C k :=
  (g ♯.[k,j] f).get (dom_of_sc_is_tg sc_tg_gf)

@[inherit_doc]
scoped[HigherCategoryTheory.ManySorted] notation g " ♯[" k "," j "] " f " ← " sc_tg_gf:100 =>
  CategoryStruct.comp k j g f sc_tg_gf

end CategoryStruct

-- Export the main components of `CategoryStruct` for easier access.
export CategoryStruct (sc tg idm sc_is_tg)

section Congruence

variable {Index : Type} [Preorder Index] {C : Index → Type u} [CategoryStruct Index C]
variable {k : Index} {j : IndexBelow k} {f₁ f₂ g₁ g₂ : C k}

/-- Congruence lemma for the domain of partial composition: if `f₁ = f₂` and `g₁ = g₂`, and the
partial composition `g₁ ♯.[k,j] f₁` is defined, then `g₂ ♯.[k,j] f₂` is also defined. -/
lemma congr_dom (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (dom_g₁f₁ : (g₁ ♯.[k,j] f₁).Dom) :
    (g₂ ♯.[k,j] f₂).Dom := by
  grind

/-- Congruence lemma for composability: if `f₁ = f₂` and `g₁ = g₂`, and `g₁` is composable with `f₁`
at dimensions `(k, j)`, then `g₂` is composable with `f₂` at dimensions `(k, j)`. -/
lemma congr_sc_is_tg (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (sc_tg_g₁f₁ : sc_is_tg k j g₁ f₁) :
    sc_is_tg k j g₂ f₂ := by
  grind

/-- Congruence lemma for partial composition: if `f₁ = f₂` and `g₁ = g₂`, then the partial
compositions `g₁ ♯.[k,j] f₁` and `g₂ ♯.[k,j] f₂` are equal as partial functions. -/
lemma congr_pcomp (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) :
    g₁ ♯.[k,j] f₁ = g₂ ♯.[k,j] f₂ := by
  grind

/-- Congruence lemma for total composition (first-pair version): if `f₁ = f₂` and `g₁ = g₂`, then
the compositions `g₁ ♯[k,j] f₁` and `g₂ ♯[k,j] f₂` are equal, using the composability proof from the
first pair. -/
lemma congr_comp₁ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₁f₁ : sc_is_tg k j g₁ f₁) :
    g₁ ♯[k,j] f₁ ← sc_tg_g₁f₁ = g₂ ♯[k,j] f₂ ← congr_sc_is_tg eq_f eq_g sc_tg_g₁f₁ := by
  grind

/-- Congruence lemma for total composition (second-pair version): if `f₁ = f₂` and `g₁ = g₂`, then
the compositions `g₁ ♯[k,j] f₁` and `g₂ ♯[k,j] f₂` are equal, using the composability proof from the
second pair. -/
lemma congr_comp₂ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₂f₂ : sc_is_tg k j g₂ f₂) :
    g₁ ♯[k,j] f₁ ← congr_sc_is_tg eq_f.symm eq_g.symm sc_tg_g₂f₂ =
    g₂ ♯[k,j] f₂ ← sc_tg_g₂f₂ := by
  grind

end Congruence

instance {Index : Type} [Preorder Index] {k j : Index} {j_lt_k : j < k} : IndexBelow k :=
  ⟨j, j_lt_k⟩

/--
A preliminary version of a many-sorted category.

This structure captures the axioms that govern behavior within a single pair of dimensions `(k, j)`
with `j < k`, including:
* **Source/target of composition**: The source of a composite is the source of the first morphism,
  and the target of a composite is the target of the second morphism.
* **Source/target of identity**: The source and target of an identity morphism are the original
  morphism.
* **Identity laws**: Composing with the identity of a source or target yields the original morphism.
* **Associativity**: Composition is associative at each pair of dimensions.

That is, for each pair `(k, j)` with `j < k`, the data `(C j, C k, sc, tg, idm, comp)` forms a
classical category with objects `C j` and morphisms `C k`.

This serves as an intermediate step in the construction of `Category`, allowing us to establish
per-pair properties before enforcing cross-dimensional compatibility.
-/
class PreCategory (Index : Type) [Preorder Index] (C : Index → Type u)
    extends CategoryStruct Index C where
  /-- The source of a composite `g ♯[k,j] f` at dimensions `(k, j)` is the source of `f`. -/
  sckj_compkj_eq_sckj : ∀ {k : Index} {j : IndexBelow k} {f g : C k} (sc_tg_gf : sc_is_tg k j g f),
      sc k j (g ♯[k,j] f ← sc_tg_gf) = sc k j f := by
    hcat_disch
  /-- The target of a composite `g ♯[k,j] f` at dimensions `(k, j)` is the target of `g`. -/
  tgkj_compkj_eq_tgkj : ∀ {k : Index} {j : IndexBelow k} {f g : C k} (sc_tg_gf : sc_is_tg k j g f),
      tg k j (g ♯[k,j] f ← sc_tg_gf) = tg k j g := by
    hcat_disch
  /-- The source of an identity `idm k j f` at dimensions `(k, j)` is `f`. -/
  sckj_idmkj : ∀ {k : Index} {j : IndexBelow k} (f : C j), sc k j (idm k j f) = f := by
    hcat_disch
  /-- The target of an identity `idm k j f` at dimensions `(k, j)` is `f`. -/
  tgkj_idmkj : ∀ {k : Index} {j : IndexBelow k} (f : C j), tg k j (idm k j f) = f := by
    hcat_disch
  /-- Composing `f` with the identity of its source at dimensions `(k, j)` yields `f`. -/
  compkj_idmkj_sckj_eq_id : ∀ {k : Index} {j : IndexBelow k} (f : C k),
      f ♯[k,j] (idm k j (sc k j f)) ← (tgkj_idmkj (sc k j f)).symm = f := by
    hcat_disch
  /-- Composing the identity of the target of `f` with `f` at dimensions `(k, j)` yields `f`. -/
  compkj_tgkj_idmkj_eq_id : ∀ {k : Index} {j : IndexBelow k} (f : C k),
      (idm k j (tg k j f)) ♯[k,j] f ← sckj_idmkj (tg k j f) = f := by
    hcat_disch
  /-- If `g` and `f` compose and `h` and `g` compose at dimensions `(k, j)`, then `h ♯[k,j] g` and
  `f` compose. This is an auxiliary method for the associativity axiom. -/
  protected compl_assoc {k : Index} {j : IndexBelow k} {f g h : C k}
      (sc_tg_gf : sc_is_tg k j g f) (sc_tg_hg : sc_is_tg k j h g) :
      sc_is_tg k j (h ♯[k,j] g ← sc_tg_hg) f := calc
    _
    _ = sc k j g := sckj_compkj_eq_sckj sc_tg_hg
    _ = tg k j f := sc_tg_gf
  /-- If `g` and `f` compose and `h` and `g` compose at dimensions `(k, j)`, then `h` and `g ♯[k,j]
  f` compose. This is an auxiliary method for the associativity axiom. -/
  protected compr_assoc {k : Index} {j : IndexBelow k} {f g h : C k}
      (sc_tg_gf : sc_is_tg k j g f) (sc_tg_hg : sc_is_tg k j h g) :
      sc_is_tg k j h (g ♯[k,j] f ← sc_tg_gf) := calc
    sc k j h
    _ = tg k j g := sc_tg_hg
    _ = _ := (tgkj_compkj_eq_tgkj sc_tg_gf).symm
  /-- The **associative property**: if `g` and `f` compose and `h` and `g` compose at dimensions
  `(k, j)`, then the two ways of composing `h`, `g`, and `f` exist and are equal. -/
  assoc : ∀ {k : Index} {j : IndexBelow k} {f g h : C k}
      (sc_tg_gf : sc_is_tg k j g f) (sc_tg_hg : sc_is_tg k j h g),
      ((h ♯[k,j] g ← sc_tg_hg) ♯[k,j] f ← (compl_assoc sc_tg_gf sc_tg_hg)) =
      (h ♯[k,j] (g ♯[k,j] f ← sc_tg_gf) ← (compr_assoc sc_tg_gf sc_tg_hg)) := by
    hcat_disch

-- Use axioms of `PreCategory` as simp lemmas.
open PreCategory in
attribute [simp] sckj_compkj_eq_sckj tgkj_compkj_eq_tgkj sckj_idmkj tgkj_idmkj
  compkj_idmkj_sckj_eq_id compkj_tgkj_idmkj_eq_id assoc

/-- In a `PreCategory`, the identity map at `(k, j)` is injective as a function from `C j` to `C k`.
-/
theorem PreCategory.injetive_idm {Index : Type} [Preorder Index] {C : Index → Type u}
    [PreCategory Index C] {k : Index} {j : IndexBelow k} :
    Function.Injective (idm k j : C j → C k) := by
  intros f g eq_idm
  calc
    f
    _ = sc k j (idm k j f) := (sckj_idmkj f).symm
    _ = sc k j (idm k j g) := congrArg (sc k j) eq_idm
    _ = g := sckj_idmkj g

/--
A **many-sorted category** is a `PreCategory` with additional axioms ensuring compatibility between
different pairs of dimensions.

This structure extends `PreCategory` by adding cross-dimensional axioms that govern how
operations at different dimensions interact:
* **Source/target interaction**: How source and target operations at different dimensions compose.
* **Distributivity**: Source and target operations distribute over composition at lower dimensions.
* **Identity transitivity**: Iterated identity maps compose transitively.
* **Identity functoriality**: Identity maps preserve composition at lower dimensions.
* **Interchange law**: Composing first at one dimension and then at another yields the same result
  regardless of the order.
-/
class Category (Index : Type) [Preorder Index] (C : Index → Type u)
    extends PreCategory Index C where
  /-- Applying source at `(j, i)` to a source at `(k, j)` yields the source at `(k, i)`. -/
  scji_sckj_eq_scki : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} (f : C k),
      sc j i (sc k j f) = sc k i f := by
    hcat_disch
  /-- Applying source at `(j, i)` to a target at `(k, j)` yields the source at `(k, i)`. -/
  scji_tgkj_eq_scki : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} (f : C k),
      sc j i (tg k j f) = sc k i f := by
    hcat_disch
  /-- Applying target at `(j, i)` to a target at `(k, j)` yields the target at `(k, i)`. -/
  tgji_tgkj_eq_tgki : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} (f : C k),
      tg j i (tg k j f) = tg k i f := by
    hcat_disch
  /-- Applying target at `(j, i)` to a source at `(k, j)` yields the target at `(k, i)`. -/
  tgji_sckj_eq_tgki : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} (f : C k),
      tg j i (sc k j f) = tg k i f := by
    hcat_disch
  /-- If `g` and `f` are `(k, i)`-composable, then `sc k j g` and `sc k j f` are
  `(j, i)`-composable. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_ji_sc {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg k i g f) : sc_is_tg j.val i (sc k j g) (sc k j f) := calc
    sc j i (sc k j g)
    _ = sc k i g := scji_sckj_eq_scki g
    _ = tg k i f := sc_tg_ki_gf
    _ = tg j i (sc k j f) := (tgji_sckj_eq_tgki f).symm
  /-- If `g` and `f` are `(k, i)`-composable, then `tg k j g` and `tg k j f` are
  `(j, i)`-composable. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_ji_tg {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg k i g f) : sc_is_tg j.val i (tg k j g) (tg k j f) := calc
    sc j i (tg k j g)
    _ = sc k i g := scji_tgkj_eq_scki g
    _ = tg k i f := sc_tg_ki_gf
    _ = tg j i (tg k j f) := (tgji_tgkj_eq_tgki f).symm
  /-- Source at `(k, j)` distributes over composition at `(k, i)` with `i < j < k`. -/
  sckj_compki_eq_compji_sckj : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg k i g f),
      sc k j (g ♯[k,i] f ← sc_tg_ki_gf) =
      (sc k j g) ♯[j.val,i] (sc k j f) ← (sc_tg_ji_sc sc_tg_ki_gf) := by
    hcat_disch
  /-- Target at `(k, j)` distributes over composition at `(k, i)` with `i < j < k`. -/
  tgkj_compki_eq_compji_tgkj : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg k i g f),
      tg k j (g ♯[k,i] f ← sc_tg_ki_gf) =
      (tg k j g) ♯[j.val,i] (tg k j f) ← (sc_tg_ji_tg sc_tg_ki_gf) := by
    hcat_disch
  /-- Iterated identity maps compose transitively: `idm k j (idm j i f) = idm k i f`. -/
  idmkj_idmji_eq_idmki : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} (f : C i),
      idm k j (idm j i f) = idm k i f := by
    hcat_disch
  /-- If `g` and `f` are `(j, i)`-composable, then `idm k j g` and `idm k j f` are `(k,
  i)`-composable. This is an auxiliary method for the identity composition axiom. -/
  protected sc_tg_ki_idmkj {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f g : C j}
      (sc_tg_ji_gf : sc_is_tg j.val i g f) : sc_is_tg k i (idm k j g) (idm k j f) := calc
    sc k i (idm k j g)
    _ = sc j i (sc k j (idm k j g)) := (scji_sckj_eq_scki (idm k j g)).symm
    _ = sc j i g := congrArg (sc j i) (sckj_idmkj g)
    _ = tg j i f := sc_tg_ji_gf
    _ = tg j i (tg k j (idm k j f)) := congrArg (tg j i) (tgkj_idmkj f).symm
    _ = tg k i (idm k j f) := tgji_tgkj_eq_tgki (idm k j f)
  /-- Identity at `(k, j)` preserves composition at `(j, i)` with `i < j < k`. -/
  idmkj_compji_eq_compki_idmkj : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f g : C j}
      (sc_tg_ji_gf : sc_is_tg j.val i g f),
      idm k j (g ♯[j.val,i] f ← sc_tg_ji_gf) =
      (idm k j g) ♯[k,i] (idm k j f) ← (sc_tg_ki_idmkj sc_tg_ji_gf) := by
    hcat_disch
  /-- Given morphisms `f₁, f₂, g₁, g₂` with `g₂` and `g₁` `(k, j)`-composable, `f₂` and `f₁` `(k,
  j)`-composable, `g₂` and `f₂` `(k, i)`-composable, and `g₁` and `f₁` `(k, i)`-composable (with `i
  < j < k`), then `g₂ ♯[k,i] f₂` and `g₁ ♯[k,i] f₁` are `(k, j)`-composable. This is an auxiliary
  method for the `interchange` axiom. -/
  protected sc_tg_kj_interchange {k : Index} {j : IndexBelow k} {i : IndexBelow j}
      {f₁ f₂ g₁ g₂ : C k}
      (sc_tg_kj_g₂g₁ : sc_is_tg k j g₂ g₁)
      (sc_tg_kj_f₂f₁ : sc_is_tg k j f₂ f₁)
      (sc_tg_ki_g₂f₂ : sc_is_tg k i g₂ f₂)
      (sc_tg_ki_g₁f₁ : sc_is_tg k i g₁ f₁) :
      sc_is_tg k j (g₂ ♯[k,i] f₂ ← sc_tg_ki_g₂f₂) (g₁ ♯[k,i] f₁ ← sc_tg_ki_g₁f₁) := calc
    _
    _ = (sc k j g₂) ♯[j.val,i] (sc k j f₂) ← (sc_tg_ji_sc sc_tg_ki_g₂f₂) :=
      sckj_compki_eq_compji_sckj sc_tg_ki_g₂f₂
    _ = (tg k j g₁) ♯[j.val,i] (tg k j f₁) ← (sc_tg_ji_tg sc_tg_ki_g₁f₁) :=
      congr_comp₁ sc_tg_kj_f₂f₁ sc_tg_kj_g₂g₁ (sc_tg_ji_sc sc_tg_ki_g₂f₂)
    _ = _ := (tgkj_compki_eq_compji_tgkj sc_tg_ki_g₁f₁).symm
  /--
  Given morphisms `f₁, f₂, g₁, g₂` with `g₂` and `g₁` `(k, j)`-composable, `f₂` and `f₁` `(k,
  j)`-composable, and `g₂` and `f₂` `(k, i)`-composable (with `i < j < k`), then `g₂ ♯[k,j] g₁` and
  `f₂ ♯[k,j] f₁` are `(k, i)`-composable. This is an auxiliary method for the `interchange` axiom.

  Note: an equivalent formulation replaces the hypothesis `sc_is_tg k i g₂ f₂` with `sc_is_tg k i g₁
  f₁`. Both are interderivable from the remaining hypotheses and the cross-dimensional axioms, so
  either one suffices. We choose `sc_is_tg k i g₂ f₂` because it aligns directly with the target
  side of the goal, yielding a shorter proof.
  -/
  protected sc_tg_ki_interchange {k : Index} {j : IndexBelow k} {i : IndexBelow j}
      {f₁ f₂ g₁ g₂ : C k}
      (sc_tg_kj_g₂g₁ : sc_is_tg k j g₂ g₁)
      (sc_tg_kj_f₂f₁ : sc_is_tg k j f₂ f₁)
      (sc_tg_ki_g₂f₂ : sc_is_tg k i g₂ f₂) :
      sc_is_tg k i (g₂ ♯[k,j] g₁ ← sc_tg_kj_g₂g₁) (f₂ ♯[k,j] f₁ ← sc_tg_kj_f₂f₁) := calc
    _
    _ = sc j i (tg k j (g₂ ♯[k,j] g₁ ← sc_tg_kj_g₂g₁)) := (scji_tgkj_eq_scki _).symm
    _ = sc j i (tg k j g₂) := by rw [tgkj_compkj_eq_tgkj sc_tg_kj_g₂g₁]
    _ = sc k i g₂ := scji_tgkj_eq_scki g₂
    _ = tg k i f₂ := sc_tg_ki_g₂f₂
    _ = tg j i (tg k j f₂) := (tgji_tgkj_eq_tgki f₂).symm
    _ = tg j i (tg k j (f₂ ♯[k,j] f₁ ← sc_tg_kj_f₂f₁)) :=
      congrArg (tg j i) (tgkj_compkj_eq_tgkj sc_tg_kj_f₂f₁).symm
    _ = tg k i (f₂ ♯[k,j] f₁ ← sc_tg_kj_f₂f₁) :=
      tgji_tgkj_eq_tgki _
  /--
  The **interchange law**: Given morphisms `f₁, f₂, g₁, g₂` and indices `i < j < k` such that:
  - `g₂` is composable with `g₁` at dimensions `(k, j)`,
  - `f₂` is composable with `f₁` at dimensions `(k, j)`,
  - `g₂` is composable with `f₂` at dimensions `(k, i)`, and
  - `g₁` is composable with `f₁` at dimensions `(k, i)`,

  then both `(g₂ ♯[k,i] f₂) ♯[k,j] (g₁ ♯[k,i] f₁)` and `(g₂ ♯[k,j] g₁) ♯[k,i] (f₂ ♯[k,j] f₁)` are
  defined and equal. That is, composing first at dimension `i` and then at dimension `j` yields the
  same result as composing first at dimension `j` and then at dimension `i`.
  -/
  interchange : ∀ {k : Index} {j : IndexBelow k} {i : IndexBelow j} {f₁ f₂ g₁ g₂ : C k}
      (sc_tg_kj_g₂g₁ : sc_is_tg k j g₂ g₁)
      (sc_tg_kj_f₂f₁ : sc_is_tg k j f₂ f₁)
      (sc_tg_ki_g₂f₂ : sc_is_tg k i g₂ f₂)
      (sc_tg_ki_g₁f₁ : sc_is_tg k i g₁ f₁),
      (g₂ ♯[k,i] f₂ ← sc_tg_ki_g₂f₂) ♯[k,j] (g₁ ♯[k,i] f₁ ← sc_tg_ki_g₁f₁) ←
        (sc_tg_kj_interchange sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁ sc_tg_ki_g₂f₂
          sc_tg_ki_g₁f₁) =
      (g₂ ♯[k,j] g₁ ← sc_tg_kj_g₂g₁) ♯[k,i] (f₂ ♯[k,j] f₁ ← sc_tg_kj_f₂f₁) ←
        (sc_tg_ki_interchange sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁
          sc_tg_ki_g₂f₂) := by
    hcat_disch

-- Use axioms of `Category` as simp lemmas.
open Category in
attribute [simp] scji_sckj_eq_scki scji_tgkj_eq_scki tgji_tgkj_eq_tgki tgji_sckj_eq_tgki
  sckj_compki_eq_compji_sckj tgkj_compki_eq_compji_tgkj idmkj_idmji_eq_idmki
  idmkj_compji_eq_compki_idmkj interchange

/-- `FinSucc n` is an abbreviation for `Fin (n + 1)`, the type of natural numbers strictly less than
`n + 1`. This is the index type used for many-sorted $n$-categories. -/
abbrev FinSucc (n : ℕ) := Fin (n + 1)

/-- A **many-sorted $n$-category** is a `Category` with index type `Fin n`,
representing a category with exactly `n` dimensions. -/
abbrev NCategory (n : ℕ) (C : FinSucc n → Type u) := Category (FinSucc n) C

/--
Any `PreCategory (FinSucc 1) C` lifts to a full `NCategory 1 C`.

Since `FinSucc 1 = Fin 2` has exactly two elements, there are no triples of distinct indices `i < j
< k`, making all cross-dimensional axioms of `Category` vacuously satisfied. Thus, a pre-many-sorted
1-category is essentially a many-sorted 1-category.
-/
-- TODO: All cross-dimensional axioms are vacuously satisfied since `FinSucc 1 = Fin 2` has no
-- triples `i < j < k`. The proof should be `{S with}`, but the default `hcat_disch` tactic
-- cannot synthesize the vacuous proofs because `omega` does not pick up the inequalities from
-- `IndexBelow` subtypes automatically.
def PreCategory.lift {C : FinSucc 1 → Type u} [S : PreCategory (FinSucc 1) C] : NCategory 1 C :=
  by sorry

/-- A **many-sorted $\omega$-category** is a `Category` with index type `ℕ`, representing a category
with infinitely (countably) many dimensions. -/
abbrev OmegaCategory (C : ℕ → Type u) := Category ℕ C

end HigherCategoryTheory.ManySorted
