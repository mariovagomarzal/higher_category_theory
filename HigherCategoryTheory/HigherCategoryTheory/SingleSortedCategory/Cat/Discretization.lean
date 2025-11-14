/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Basic
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Cell
import HigherCategoryTheory.HigherCategoryTheory.SingleSortedCategory.Functor

/-!
TODO: Document this file.
-/

universe u u₁ u₂

namespace HigherCategoryTheory

namespace SingleSortedNCategory

-- TODO: Try to generalize the following tactics to work for every axiom.
macro "discrete_above" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k
    by_cases k_lt_n : k < $n
    · simp [dif_pos k_lt_n]
      apply $base_axiom
    · simp [dif_neg k_lt_n]
  ))

macro "discrete_above_1comp" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k _ _ comp_gf
    by_cases k_lt_n : k < $n
    · simp [dif_pos k_lt_n]
      simp [dif_pos k_lt_n] at comp_gf
      apply $base_axiom comp_gf
    · simp [dif_neg k_lt_n]
      -- Axiom `tg_comp_is_tg` needs this extra two steps because the left-hand side and the
      -- right-hand side of the goal equation are `tg k (g ♯[k] f)` and `tg k g`, respectively.
      -- Since `k` is a discrete dimension, the first term reduces to `tg k f` and then to `f`, and
      -- the second term reduces to `g`. Now, the hypothesis `comp_gf : g = f` is necessary to close
      -- the goal.
      try simp [dif_neg k_lt_n] at comp_gf
      try exact comp_gf.symm
  ))

macro "discrete_above_2comp" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k _ _ _ comp_gf comp_hg
    by_cases k_lt_n : k < $n
    · simp [dif_pos k_lt_n]
      simp [dif_pos k_lt_n] at comp_gf comp_hg
      apply $base_axiom comp_gf comp_hg
    · simp [dif_neg k_lt_n]
  ))

macro "discrete_above2" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k j _ j_lt_k
    by_cases k_lt_n : k < $n
    · have j_lt_n : j < $n := j_lt_k.trans k_lt_n
      simp [dif_pos k_lt_n, dif_pos j_lt_n]
      apply $base_axiom _ j_lt_k
    · simp [dif_neg k_lt_n]
  ))

macro "discrete_above2_1comp" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k j _ _ j_lt_k comp_j_gf
    by_cases k_lt_n : k < $n
    · have j_lt_n : j < $n := j_lt_k.trans k_lt_n
      simp [dif_pos k_lt_n, dif_pos j_lt_n]
      simp [dif_pos j_lt_n] at comp_j_gf
      apply $base_axiom j_lt_k comp_j_gf
    · simp [dif_neg k_lt_n]
      by_cases j_lt_n : j < $n
      · simp [dif_pos j_lt_n]
      · simp [dif_neg j_lt_n]
  ))

macro "discrete_above2_4comp" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k j _ _ _ _ j_lt_k comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁
    by_cases k_lt_n : k < $n
    · have j_lt_n : j < $n := j_lt_k.trans k_lt_n
      simp [dif_pos k_lt_n, dif_pos j_lt_n]
      simp [dif_pos k_lt_n] at comp_k_g₂g₁ comp_k_f₂f₁
      simp [dif_pos j_lt_n] at comp_j_g₂f₂ comp_j_g₁f₁
      apply $base_axiom j_lt_k comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁
    · simp [dif_neg k_lt_n]
      by_cases j_lt_n : j < $n
      · simp [dif_pos j_lt_n]
      · simp [dif_neg j_lt_n]
  ))

/-- Given a structure of `SingleSortedNCategory` on `Obj` (for some `n : Nat`), we can construct a
more general structure of `SingleSorted2CategoryFamily` on `Obj` for any `NatIndex` `index` by
adding discrete dimensions above the `n`-th dimension. -/
@[simp]
def toSingleSorted2CategoryFamilyDiscreteAbove {n : ℕ} {Obj : Type u}
    (nS : SingleSortedNCategory n Obj)
    (index : Type) [NatIndex index] : SingleSorted2CategoryFamily index Obj where
  Sc k := if h : k < n then nS.Sc ⟨k, h⟩ else id
  Tg k := if h : k < n then nS.Tg ⟨k, h⟩ else id
  PComp k g f := if h : k < n then nS.PComp ⟨k, h⟩ g f else ⟨g = f, fun _ ↦ f⟩
  pcomp_dom := by discrete_above n nS.pcomp_dom
  sc_sc_is_sc := by discrete_above n nS.sc_sc_is_sc
  tg_sc_is_sc := by discrete_above n nS.tg_sc_is_sc
  sc_tg_is_tg := by discrete_above n nS.sc_tg_is_tg
  tg_tg_is_tg := by discrete_above n nS.tg_tg_is_tg
  sc_comp_is_sc := by discrete_above_1comp n nS.sc_comp_is_sc
  tg_comp_is_tg := by discrete_above_1comp n nS.tg_comp_is_tg
  comp_sc_is_id := by discrete_above n nS.comp_sc_is_id
  comp_tg_is_id := by discrete_above n nS.comp_tg_is_id
  assoc := by discrete_above_2comp n nS.assoc
  sck_scj_is_scj := by discrete_above2 n nS.sck_scj_is_scj
  scj_sck_is_scj := by discrete_above2 n nS.scj_sck_is_scj
  scj_tgk_is_scj := by discrete_above2 n nS.scj_tgk_is_scj
  tgk_tgj_is_tgj := by discrete_above2 n nS.tgk_tgj_is_tgj
  tgj_tgk_is_tgj := by discrete_above2 n nS.tgj_tgk_is_tgj
  tgj_sck_is_tgj := by discrete_above2 n nS.tgj_sck_is_tgj
  sck_compj_is_compj_sck := by discrete_above2_1comp n nS.sck_compj_is_compj_sck
  tgk_compj_is_compj_tgk := by discrete_above2_1comp n nS.tgk_compj_is_compj_tgk
  exchange := by discrete_above2_4comp n nS.exchange

-- TODO: Document the case when `m < n`, which consists in forgetting `n - m` dimensions.
/-- Given a structure of `SingleSortedNCategory` on `Obj` (for some `n : Nat`), we can construct
another structure of `SingleSortedNCategory` on `Obj` (for some `m : Nat`) by adding $m - n$
discrete dimensions above the `n`-th dimension. -/
@[simp]
def toSingleSortedMCategoryDiscreteAbove {n : ℕ} {Obj : Type u}
    (nS : SingleSortedNCategory n Obj)
    (m : Nat) : SingleSortedNCategory m Obj :=
  toSingleSorted2CategoryFamilyDiscreteAbove nS (Fin m)

end SingleSortedNCategory

namespace SingleSortedFunctorFamily

-- TODO: As with the previous tactics related to categories, try to generalize these tactics to work
-- for every axiom.
macro "functor_discrete_above" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k f
    by_cases k_lt_n : k < $n
    · simp [dif_pos k_lt_n]
      apply $base_axiom
    · simp [dif_neg k_lt_n]
  ))

macro "functor_discrete_above_1comp" n:ident base_axiom:ident : tactic =>
  `(tactic| (
    intro k f g comp_gf
    by_cases k_lt_n : k < $n
    · simp [dif_pos k_lt_n]
      simp [dif_pos k_lt_n] at comp_gf
      apply $base_axiom comp_gf
    · simp [dif_neg k_lt_n]
  ))

/-- Given a structure of `SingleSortedNFunctor` between `C` and `D` (for some `n : Nat`), we can
construct a more general structure of `SingleSortedFunctorFamily` between `C` and `D` for any
`NatIndex` `index` with `C` and `D` endowed with the structures of `SingleSorted2CategoryFamily`
obtained by the defined discretization method. -/
@[simp]
def toSingleSortedMFunctorDiscreteAbove {n : ℕ} {C : Type u₁} {D : Type u₂}
    [nC : SingleSortedNCategory n C]
    [nD : SingleSortedNCategory n D]
    (nF : SingleSortedNFunctor n C D)
    (index : Type) [NatIndex index] :
    letI := nC.toSingleSorted2CategoryFamilyDiscreteAbove index
    letI := nD.toSingleSorted2CategoryFamilyDiscreteAbove index
    SingleSortedFunctorFamily index C D :=
  let _ := nC.toSingleSorted2CategoryFamilyDiscreteAbove index
  let _ := nD.toSingleSorted2CategoryFamilyDiscreteAbove index
  {
    map := nF.map
    map_sc_is_sc_map := by functor_discrete_above n nF.map_sc_is_sc_map
    map_tg_is_tg_map := by functor_discrete_above n nF.map_tg_is_tg_map
    map_comp_is_comp_map := by functor_discrete_above_1comp n nF.map_comp_is_comp_map
  }

/-- Given a structure of `SingleSortedNFunctor` between `C` and `D` (for some `n : Nat`), we can
construct another structure of `SingleSortedNFunctor` between `C` and `D` (for some `m : Nat`) with
`C` and `D` endowed with the structures of `SingleSortedNCategory` obtained by the defined
discretization method. -/
@[simp]
def toSingleSortedMFunctorDiscreteAboveN {n : ℕ} {C : Type u₁} {D : Type u₂}
    [nC : SingleSortedNCategory n C]
    [nD : SingleSortedNCategory n D]
    (nF : SingleSortedNFunctor n C D)
    (m : Nat) :
    letI := nC.toSingleSortedMCategoryDiscreteAbove m
    letI := nD.toSingleSortedMCategoryDiscreteAbove m
    SingleSortedNFunctor m C D :=
  nF.toSingleSortedMFunctorDiscreteAbove (Fin m)

end SingleSortedFunctorFamily

end HigherCategoryTheory
