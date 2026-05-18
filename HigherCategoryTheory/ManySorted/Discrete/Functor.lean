/-
Copyright (c) 2026 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.CategoryTheory.Category.Cat
import HigherCategoryTheory.ManySorted.Category
import HigherCategoryTheory.ManySorted.Functor
import HigherCategoryTheory.ManySorted.Cat

/-!
# Discrete many-sorted categories

This file defines the discrete $m$-category (or $\omega$-category) structure of a many-sorted
$n$-category by extending the type family to higher dimensions, where $n < m$, and declaring all
dimensions above $n$ to be trivial. This file also defines the discrete functor between discrete
categories induced by a functor between many-sorted $n$-categories.

## Main definitions

* `NCategory.discrete`: Given a many-sorted $n$-category and $n < m$, constructs the discrete
  $m$-category where dimensions below $n$ retain the original structure and dimensions
  $n \leq k < m$ are trivial.
* `OmegaCategory.discrete`: Given a many-sorted $n$-category, constructs the discrete
  $\omega$-category.
* `NFunctor.discrete`: Lifts a functor between many-sorted $n$-categories to a functor between
  their discrete $m$-categories.
* `OmegaFunctor.discrete`: Lifts a functor between many-sorted $n$-categories to a functor between
  their discrete $\omega$-categories.
* `DiscretizationFunctor`: The functor from `ICat n` to `ICat m` sending each category and functor
  to its discrete higher-dimensional counterpart.

## Implementation notes

The type family of the discrete category is obtained by composing the original family with the
retract `retract n : ℕ → FinSucc n`, which sends dimensions $k \geq n$ to $n$ so that all such
dimensions share a single type. The category structure is then defined by case analysis on $k < n$:
below $n$ it inherits the original operations, and at or above $n$ source, target and identity-cell
operations act as the identity (modulo casts along retract-equalities), with composition defined
only between equal morphisms.
-/

universe u

namespace HigherCategoryTheory.ManySorted

/-- Retract of dimensions onto `FinSucc n`. Sends `k` to `min k n` viewed as an element of
`FinSucc n`, collapsing every dimension at or above `n` onto the top. -/
abbrev retract (n k : ℕ) : FinSucc n :=
  ⟨min k n, by omega⟩

namespace retract

variable {n : ℕ}

/-- Below `n`, `retract n` acts as the identity. -/
theorem eq_self {k : ℕ} (k_lt_n : k < n) :
    retract n k = ⟨k, by omega⟩ := by
  apply Fin.ext
  change min k n = k
  exact min_eq_left k_lt_n.le

/-- At or above `n`, `retract n` collapses to `n`. -/
theorem eq_top {k : ℕ} (n_le_k : n ≤ k) :
    retract n k = ⟨n, by omega⟩ := by
  apply Fin.ext
  change min k n = n
  exact min_eq_right n_le_k

/-- Below `n`, `retract n` is strictly monotone. -/
theorem strict_mono {j k : ℕ} (j_lt_k : j < k) (j_lt_n : j < n) :
    retract n j < retract n k := by
  change min j n < min k n
  omega

/-- At or above `n`, `retract n` is constant. -/
theorem eq_of_ge {j k : ℕ} (j_lt_k : j < k) (n_le_j : n ≤ j) :
    retract n j = retract n k := by
  apply Fin.ext
  change min j n = min k n
  omega

end retract

/-- Extension of a many-sorted type family `C : NTypeFamily n` to `NTypeFamily m` by composing
with the retract `retract n`. Dimensions $k \geq n$ all share the type `C n`. -/
abbrev NTypeFamily.discrete {n : ℕ} (C : NTypeFamily.{u} n) (m : ℕ) : NTypeFamily.{u} m :=
  fun k ↦ C (retract n k)

/-- Extension of a many-sorted type family `C : NTypeFamily n` to an `OmegaTypeFamily` by composing
with the retract `retract n`. Dimensions $k \geq n$ all share the type `C n`. -/
abbrev OmegaTypeFamily.discrete {n : ℕ} (C : NTypeFamily.{u} n) : OmegaTypeFamily.{u} :=
  fun k ↦ C (retract n k)

section Category

variable {n : ℕ} {C : NTypeFamily.{u} n}

section DiscreteCategoryHelpers

variable {S : NCategory n C}

/-- Auxiliary lemma: applying `S.sc` to a cast value along a retract-equality `eq : k = k'`
matches the result of applying `S.sc` directly. -/
private theorem cast_sc {k k' j : FinSucc n} (eq : k = k')
    (j_lt_k : j < k) (j_lt_k' : j < k') (f : C k') :
    S.sc j_lt_k (cast (congrArg C eq.symm) f) = S.sc j_lt_k' f := by
  subst eq
  rfl

/-- Auxiliary lemma: applying `S.tg` to a cast value along a retract-equality `eq : k = k'`
matches the result of applying `S.tg` directly. -/
private theorem cast_tg {k k' j : FinSucc n} (eq : k = k')
    (j_lt_k : j < k) (j_lt_k' : j < k') (f : C k') :
    S.tg j_lt_k (cast (congrArg C eq.symm) f) = S.tg j_lt_k' f := by
  subst eq
  rfl

/-- Auxiliary lemma: casting the result of `S.idm` along a retract-equality `eq : k = k'`
matches `S.idm` taken at the target. -/
private theorem cast_idm {k k' j : FinSucc n} (eq : k = k')
    (j_lt_k : j < k) (j_lt_k' : j < k') (f : C j) :
    cast (congrArg C eq) (S.idm j_lt_k f) = S.idm j_lt_k' f := by
  subst eq
  rfl

/-- Auxiliary lemma: transports a composability proof through a cast along a retract-equality
`eq : k = k'`. The reverse direction follows by applying this lemma to `eq.symm`. -/
private theorem sc_tg_cast {k k' j : FinSucc n} (eq : k = k')
    {j_lt_k : j < k} {j_lt_k' : j < k'} {g f : C k'}
    (sc_tg : S.sc j_lt_k' g = S.tg j_lt_k' f) :
    S.sc j_lt_k (cast (congrArg C eq.symm) g) =
    S.tg j_lt_k (cast (congrArg C eq.symm) f) := by
  subst eq
  exact sc_tg

/-- Auxiliary lemma: the composition of cast arguments equals the cast of the composition along a
retract-equality `eq : k = k'`. The reverse direction follows by applying this lemma to `eq.symm`
and then `.symm`. -/
private theorem cast_comp {k k' j : FinSucc n} (eq : k = k')
    (j_lt_k : j < k) (j_lt_k' : j < k') (g f : C k')
    (sc_tg : S.sc j_lt_k' g = S.tg j_lt_k' f)
    (sc_tg' : S.sc j_lt_k (cast (congrArg C eq.symm) g) =
              S.tg j_lt_k (cast (congrArg C eq.symm) f)) :
    (S.pcomp j_lt_k (cast (congrArg C eq.symm) g)
      (cast (congrArg C eq.symm) f)).get (S.pcomp_dom.mpr sc_tg') =
    cast (congrArg C eq.symm) ((S.pcomp j_lt_k' g f).get (S.pcomp_dom.mpr sc_tg)) := by
  subst eq
  rfl

end DiscreteCategoryHelpers

/--
Constructs the discrete $m$-category of a many-sorted $n$-category by declaring all dimensions
above $n$ to be trivial.

Given a many-sorted $n$-category `S` and $n < m$, this produces a many-sorted $m$-category on the
extended type family `NTypeFamily.discrete C m`. Dimensions below $n$ retain the original
structure, and dimensions $n \leq k < m$ have identity source, target and identity-cell operations
(modulo casts along retract-equalities), with composition defined only between equal morphisms.
-/
@[simp]
def NCategory.discrete (S : NCategory n C) (m : ℕ) (_n_lt_m : n < m) :
    NCategory m (NTypeFamily.discrete C m) where
  sc {k j} j_lt_k f :=
    if h : j < n then
      S.sc (retract.strict_mono j_lt_k h) f
    else
      cast (congrArg C (retract.eq_of_ge j_lt_k (not_lt.mp h)).symm) f
  tg {k j} j_lt_k f :=
    if h : j < n then
      S.tg (retract.strict_mono j_lt_k h) f
    else
      cast (congrArg C (retract.eq_of_ge j_lt_k (not_lt.mp h)).symm) f
  idm {k j} j_lt_k f :=
    if h : j < n then
      S.idm (retract.strict_mono j_lt_k h) f
    else
      cast (congrArg C (retract.eq_of_ge j_lt_k (not_lt.mp h))) f
  pcomp {k j} j_lt_k g f :=
    if h : j < n then
      S.pcomp (retract.strict_mono j_lt_k h) g f
    else
      ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by
    intro k j j_lt_k f g
    split_ifs with h
    · exact S.pcomp_dom
    · exact (cast_inj _).symm
  sckj_compkj_eq_sckj := by
    intro k j j_lt_k f g sc_tg_gf
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.sckj_compkj_eq_sckj
      simp only [sc_is_tg, dif_pos h] at sc_tg_gf
      exact sc_tg_gf
    · simp only [CategoryStruct.comp, dif_neg h]
  tgkj_compkj_eq_tgkj := by
    intro k j j_lt_k f g sc_tg_gf
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.tgkj_compkj_eq_tgkj
      simp only [sc_is_tg, dif_pos h] at sc_tg_gf
      exact sc_tg_gf
    · simp only [CategoryStruct.comp, dif_neg h]
      simp only [sc_is_tg, dif_neg h] at sc_tg_gf
      exact sc_tg_gf.symm
  sckj_idmkj := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [dif_pos h]
      apply S.sckj_idmkj
    · simp only [dif_neg h]
      rw [cast_cast, cast_eq]
  tgkj_idmkj := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [dif_pos h]
      apply S.tgkj_idmkj
    · simp only [dif_neg h]
      rw [cast_cast, cast_eq]
  compkj_idmkj_sckj_eq_id := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.compkj_idmkj_sckj_eq_id
    · simp only [CategoryStruct.comp, dif_neg h]
      rw [cast_cast, cast_eq]
  compkj_tgkj_idmkj_eq_id := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.compkj_tgkj_idmkj_eq_id
    · simp only [CategoryStruct.comp, dif_neg h]
  assoc := by
    intro k j j_lt_k f g e sc_tg_gf sc_tg_hg
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.assoc
      · simp only [sc_is_tg, dif_pos h] at sc_tg_gf
        exact sc_tg_gf
      · simp only [sc_is_tg, dif_pos h] at sc_tg_hg
        exact sc_tg_hg
    · simp only [CategoryStruct.comp, dif_neg h]
  scji_sckj_eq_scki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.scji_sckj_eq_scki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_sc (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  scji_tgkj_eq_scki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.scji_tgkj_eq_scki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_sc (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  tgji_tgkj_eq_tgki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.tgji_tgkj_eq_tgki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_tg (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  tgji_sckj_eq_tgki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.tgji_sckj_eq_tgki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_tg (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  sckj_compki_eq_compji_sckj := by
    intro k j i j_lt_k i_lt_j f g sc_tg_ki_gf
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      apply S.sckj_compki_eq_compji_sckj
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
      exact sc_tg_ki_gf
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
        simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
        exact (cast_comp
          (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ g f sc_tg_ki_gf
          (sc_tg_cast (retract.eq_of_ge j_lt_k (not_lt.mp h_j))
            sc_tg_ki_gf)).symm
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]
  tgkj_compki_eq_compji_tgkj := by
    intro k j i j_lt_k i_lt_j f g sc_tg_ki_gf
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      apply S.tgkj_compki_eq_compji_tgkj
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
      exact sc_tg_ki_gf
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
        simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
        exact (cast_comp
          (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ g f sc_tg_ki_gf
          (sc_tg_cast (retract.eq_of_ge j_lt_k (not_lt.mp h_j))
            sc_tg_ki_gf)).symm
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]
  idmkj_idmji_eq_idmki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.idmkj_idmji_eq_idmki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_idm (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  idmkj_compji_eq_compki_idmkj := by
    intro k j i j_lt_k i_lt_j f g sc_tg_ji_gf
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      apply S.idmkj_compji_eq_compki_idmkj
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ji_gf
      exact sc_tg_ji_gf
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
        simp only [sc_is_tg, dif_pos h_i] at sc_tg_ji_gf
        exact (cast_comp
          (retract.eq_of_ge j_lt_k (not_lt.mp h_j)).symm _ _ g f sc_tg_ji_gf
          (sc_tg_cast (retract.eq_of_ge j_lt_k (not_lt.mp h_j)).symm
            sc_tg_ji_gf)).symm
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]
  interchange := by
    intro k j i j_lt_k i_lt_j f₁ f₂ g₁ g₂ sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁ sc_tg_ki_g₂f₂
      sc_tg_ki_g₁f₁
    by_cases h_j : j < n
    · have h_i : (i : ℕ) < n := lt_trans (Fin.lt_def.mp i_lt_j) h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      simp only [sc_is_tg, dif_pos h_j] at sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_g₂f₂ sc_tg_ki_g₁f₁
      exact S.interchange (i_lt_j := retract.strict_mono i_lt_j h_i)
        sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁ sc_tg_ki_g₂f₂ sc_tg_ki_g₁f₁
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]

/--
Constructs the discrete $\omega$-category of a many-sorted $n$-category.

This definition is analogous to `NCategory.discrete`, but produces a many-sorted $\omega$-category
on the extended type family `OmegaTypeFamily.discrete C`.
-/
@[simp]
def OmegaCategory.discrete (S : NCategory n C) : OmegaCategory (OmegaTypeFamily.discrete C) where
  sc {k j} j_lt_k f :=
    if h : j < n then
      S.sc (retract.strict_mono j_lt_k h) f
    else
      cast (congrArg C (retract.eq_of_ge j_lt_k (not_lt.mp h)).symm) f
  tg {k j} j_lt_k f :=
    if h : j < n then
      S.tg (retract.strict_mono j_lt_k h) f
    else
      cast (congrArg C (retract.eq_of_ge j_lt_k (not_lt.mp h)).symm) f
  idm {k j} j_lt_k f :=
    if h : j < n then
      S.idm (retract.strict_mono j_lt_k h) f
    else
      cast (congrArg C (retract.eq_of_ge j_lt_k (not_lt.mp h))) f
  pcomp {k j} j_lt_k g f :=
    if h : j < n then
      S.pcomp (retract.strict_mono j_lt_k h) g f
    else
      ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by
    intro k j j_lt_k f g
    split_ifs with h
    · exact S.pcomp_dom
    · exact (cast_inj _).symm
  sckj_compkj_eq_sckj := by
    intro k j j_lt_k f g sc_tg_gf
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.sckj_compkj_eq_sckj
      simp only [sc_is_tg, dif_pos h] at sc_tg_gf
      exact sc_tg_gf
    · simp only [CategoryStruct.comp, dif_neg h]
  tgkj_compkj_eq_tgkj := by
    intro k j j_lt_k f g sc_tg_gf
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.tgkj_compkj_eq_tgkj
      simp only [sc_is_tg, dif_pos h] at sc_tg_gf
      exact sc_tg_gf
    · simp only [CategoryStruct.comp, dif_neg h]
      simp only [sc_is_tg, dif_neg h] at sc_tg_gf
      exact sc_tg_gf.symm
  sckj_idmkj := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [dif_pos h]
      apply S.sckj_idmkj
    · simp only [dif_neg h]
      rw [cast_cast, cast_eq]
  tgkj_idmkj := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [dif_pos h]
      apply S.tgkj_idmkj
    · simp only [dif_neg h]
      rw [cast_cast, cast_eq]
  compkj_idmkj_sckj_eq_id := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.compkj_idmkj_sckj_eq_id
    · simp only [CategoryStruct.comp, dif_neg h]
      rw [cast_cast, cast_eq]
  compkj_tgkj_idmkj_eq_id := by
    intro k j j_lt_k f
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.compkj_tgkj_idmkj_eq_id
    · simp only [CategoryStruct.comp, dif_neg h]
  assoc := by
    intro k j j_lt_k f g e sc_tg_gf sc_tg_hg
    by_cases h : j < n
    · simp only [CategoryStruct.comp, dif_pos h]
      apply S.assoc
      · simp only [sc_is_tg, dif_pos h] at sc_tg_gf
        exact sc_tg_gf
      · simp only [sc_is_tg, dif_pos h] at sc_tg_hg
        exact sc_tg_hg
    · simp only [CategoryStruct.comp, dif_neg h]
  scji_sckj_eq_scki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.scji_sckj_eq_scki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_sc (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  scji_tgkj_eq_scki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.scji_tgkj_eq_scki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_sc (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  tgji_tgkj_eq_tgki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.tgji_tgkj_eq_tgki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_tg (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  tgji_sckj_eq_tgki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.tgji_sckj_eq_tgki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_tg (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  sckj_compki_eq_compji_sckj := by
    intro k j i j_lt_k i_lt_j f g sc_tg_ki_gf
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      apply S.sckj_compki_eq_compji_sckj
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
      exact sc_tg_ki_gf
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
        simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
        exact (cast_comp
          (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ g f sc_tg_ki_gf
          (sc_tg_cast (retract.eq_of_ge j_lt_k (not_lt.mp h_j))
            sc_tg_ki_gf)).symm
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]
  tgkj_compki_eq_compji_tgkj := by
    intro k j i j_lt_k i_lt_j f g sc_tg_ki_gf
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      apply S.tgkj_compki_eq_compji_tgkj
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
      exact sc_tg_ki_gf
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
        simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_gf
        exact (cast_comp
          (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ g f sc_tg_ki_gf
          (sc_tg_cast (retract.eq_of_ge j_lt_k (not_lt.mp h_j))
            sc_tg_ki_gf)).symm
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]
  idmkj_idmji_eq_idmki := by
    intro k j i j_lt_k i_lt_j f
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [dif_pos h_j, dif_pos h_i]
      apply S.idmkj_idmji_eq_idmki
    · by_cases h_i : i < n
      · simp only [dif_neg h_j, dif_pos h_i]
        exact cast_idm (retract.eq_of_ge j_lt_k (not_lt.mp h_j)) _ _ f
      · simp only [dif_neg h_j, dif_neg h_i]
        rw [cast_cast]
  idmkj_compji_eq_compki_idmkj := by
    intro k j i j_lt_k i_lt_j f g sc_tg_ji_gf
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      apply S.idmkj_compji_eq_compki_idmkj
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ji_gf
      exact sc_tg_ji_gf
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
        simp only [sc_is_tg, dif_pos h_i] at sc_tg_ji_gf
        exact (cast_comp
          (retract.eq_of_ge j_lt_k (not_lt.mp h_j)).symm _ _ g f sc_tg_ji_gf
          (sc_tg_cast (retract.eq_of_ge j_lt_k (not_lt.mp h_j)).symm
            sc_tg_ji_gf)).symm
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]
  interchange := by
    intro k j i j_lt_k i_lt_j f₁ f₂ g₁ g₂ sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁ sc_tg_ki_g₂f₂
      sc_tg_ki_g₁f₁
    by_cases h_j : j < n
    · have h_i : i < n := lt_trans i_lt_j h_j
      simp only [CategoryStruct.comp, dif_pos h_j, dif_pos h_i]
      simp only [sc_is_tg, dif_pos h_j] at sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁
      simp only [sc_is_tg, dif_pos h_i] at sc_tg_ki_g₂f₂ sc_tg_ki_g₁f₁
      exact S.interchange (i_lt_j := retract.strict_mono i_lt_j h_i)
        sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁ sc_tg_ki_g₂f₂ sc_tg_ki_g₁f₁
    · by_cases h_i : i < n
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_pos h_i]
      · simp only [CategoryStruct.comp, dif_neg h_j, dif_neg h_i]

end Category

section Functor

variable {n : ℕ} {C : NTypeFamily.{u} n} [SC : NCategory n C]
  {D : NTypeFamily.{u} n} [SD : NCategory n D]

section DiscreteFunctorHelpers

variable {F : NFunctor n C D}

/-- Auxiliary lemma: applying `F.map` after a cast along a retract-equality matches casting after
applying `F.map`. -/
private theorem map_cast {k k' : FinSucc n} (eq : k = k') (f : C k') :
    F.map k (cast (congrArg C eq.symm) f) =
    cast (congrArg D eq.symm) (F.map k' f) := by
  subst eq
  rfl

/-- Auxiliary lemma: applying `F.map` after a cast along a retract-equality (target direction)
matches casting after applying `F.map`. -/
private theorem cast_map {k k' : FinSucc n} (eq : k = k') (f : C k) :
    F.map k' (cast (congrArg C eq) f) =
    cast (congrArg D eq) (F.map k f) := by
  subst eq
  rfl

end DiscreteFunctorHelpers

/--
Lifts a functor between many-sorted $n$-categories to a functor between their discrete
$m$-categories.

Given a functor `F` between many-sorted $n$-categories and $n < m$, this produces a functor between
their discrete $m$-categories whose mapping at dimension `k` uses `F.map (retract n k)`.
Functoriality follows from `F` at dimensions below $n$, and is trivial at dimensions $k \geq n$.
-/
@[simp]
def NFunctor.discrete (F : NFunctor n C D) (m : ℕ) (n_lt_m : n < m) :
    letI := SC.discrete m n_lt_m
    letI := SD.discrete m n_lt_m
    NFunctor m (NTypeFamily.discrete C m) (NTypeFamily.discrete D m) :=
  letI := SC.discrete m n_lt_m
  letI := SD.discrete m n_lt_m
  {
    map := fun k f ↦ F.map (retract n k) f
    map_sc_eq_sc_map := by
      intro k j j_lt_k f
      by_cases h : j < n
      · simp only [NCategory.discrete, dif_pos h]
        apply F.map_sc_eq_sc_map
      · simp only [NCategory.discrete, dif_neg h]
        exact map_cast (retract.eq_of_ge j_lt_k (not_lt.mp h)) f
    map_tg_eq_tg_map := by
      intro k j j_lt_k f
      by_cases h : j < n
      · simp only [NCategory.discrete, dif_pos h]
        apply F.map_tg_eq_tg_map
      · simp only [NCategory.discrete, dif_neg h]
        exact map_cast (retract.eq_of_ge j_lt_k (not_lt.mp h)) f
    map_idm_eq_idm_map := by
      intro k j j_lt_k f
      by_cases h : j < n
      · simp only [NCategory.discrete, dif_pos h]
        apply F.map_idm_eq_idm_map
      · simp only [NCategory.discrete, dif_neg h]
        exact cast_map (retract.eq_of_ge j_lt_k (not_lt.mp h)) f
    map_comp_eq_comp_map := by
      intro k j j_lt_k f g sc_tg_gf
      by_cases h : j < n
      · simp only [NCategory.discrete, CategoryStruct.comp, dif_pos h]
        apply F.map_comp_eq_comp_map
        simp only [NCategory.discrete, sc_is_tg, dif_pos h] at sc_tg_gf
        exact sc_tg_gf
      · simp only [NCategory.discrete, CategoryStruct.comp, dif_neg h]
  }

/--
Lifts a functor between many-sorted $n$-categories to a functor between their discrete
$\omega$-categories.

This definition is analogous to `NFunctor.discrete`, but produces an $\omega$-functor.
-/
@[simp]
def OmegaFunctor.discrete (F : NFunctor n C D) :
    letI := OmegaCategory.discrete SC
    letI := OmegaCategory.discrete SD
    OmegaFunctor (OmegaTypeFamily.discrete C) (OmegaTypeFamily.discrete D) :=
  letI := OmegaCategory.discrete SC
  letI := OmegaCategory.discrete SD
  {
    map := fun k f ↦ F.map (retract n k) f
    map_sc_eq_sc_map := by
      intro k j j_lt_k f
      by_cases h : j < n
      · simp only [OmegaCategory.discrete, dif_pos h]
        apply F.map_sc_eq_sc_map
      · simp only [OmegaCategory.discrete, dif_neg h]
        exact map_cast (retract.eq_of_ge j_lt_k (not_lt.mp h)) f
    map_tg_eq_tg_map := by
      intro k j j_lt_k f
      by_cases h : j < n
      · simp only [OmegaCategory.discrete, dif_pos h]
        apply F.map_tg_eq_tg_map
      · simp only [OmegaCategory.discrete, dif_neg h]
        exact map_cast (retract.eq_of_ge j_lt_k (not_lt.mp h)) f
    map_idm_eq_idm_map := by
      intro k j j_lt_k f
      by_cases h : j < n
      · simp only [OmegaCategory.discrete, dif_pos h]
        apply F.map_idm_eq_idm_map
      · simp only [OmegaCategory.discrete, dif_neg h]
        exact cast_map (retract.eq_of_ge j_lt_k (not_lt.mp h)) f
    map_comp_eq_comp_map := by
      intro k j j_lt_k f g sc_tg_gf
      by_cases h : j < n
      · simp only [OmegaCategory.discrete, CategoryStruct.comp, dif_pos h]
        apply F.map_comp_eq_comp_map
        simp only [OmegaCategory.discrete, sc_is_tg, dif_pos h] at sc_tg_gf
        exact sc_tg_gf
      · simp only [OmegaCategory.discrete, CategoryStruct.comp, dif_neg h]
  }

end Functor

section DiscretizationFunctor

open CategoryTheory

/-- The discretization functor from the category of many-sorted $n$-categories to the category of
many-sorted $m$-categories for finite dimensions, where $n < m$. Sends each $n$-category to its
discrete $m$-category and each functor to its lift between the discrete categories. -/
def FinDiscretizationFunctor (n m : ℕ) (n_lt_m : n < m) : ICat.{u} n ⥤ ICat.{u} m where
  obj C := letI := NCategory.discrete C.str m n_lt_m; Cat.of (NTypeFamily.discrete C.carrier m)
  map {C D} F := F.discrete m n_lt_m

/-- The discretization functor from the category of many-sorted $n$-categories to the category of
many-sorted $\omega$-categories. Sends each $n$-category to its discrete $\omega$-category and each
functor to its lift between the discrete categories. -/
def OmegaDiscretizationFunctor (n : ℕ) : ICat.{u} n ⥤ ICat.{u} ω where
  obj C := letI := OmegaCategory.discrete C.str; Cat.of (OmegaTypeFamily.discrete C.carrier)
  map {C D} F := OmegaFunctor.discrete F

/-- The discretization functor from the category of many-sorted $n$-categories to the category of
many-sorted $m$-categories (where $n \leq m$). Sends each $n$-category to its discrete $m$-category
by declaring all dimensions above $n$ to be trivial, and each functor to its lift between the
discrete categories. -/
@[simp]
def DiscretizationFunctor (n m : ℕ∞) (n_le_m : n ≤ m) : ICat.{u} n ⥤ ICat.{u} m :=
  match n, m with
  | fin n, fin m =>
    if h : n < m then
      FinDiscretizationFunctor n m h
    else by
      simp only [ENat.some_eq_coe, Nat.cast_le] at n_le_m
      have : n = m := n_le_m.eq_of_not_lt h
      rw [this]
      exact 𝟭 (ICat.{u} m)
  | fin n, ω => OmegaDiscretizationFunctor n
  | ω, ω => 𝟭 (ICat.{u} ω)

end DiscretizationFunctor

end HigherCategoryTheory.ManySorted
