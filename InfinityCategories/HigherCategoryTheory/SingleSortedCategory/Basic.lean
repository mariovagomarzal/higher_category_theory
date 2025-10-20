/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Pfun
import InfinityCategories.Data.NatIndex

/-!
TODO: Document the file.
-/

universe u

namespace HigherCategoryTheory

class SingleSortedStruct (Obj : Type u)
    (index : Type) [NatIndex index] where
  Sc : index → Obj → Obj
  Tg : index → Obj → Obj
  PComp : index → Obj → Obj →. Obj
  pcomp_dom : ∀ {i : index} {f g : Obj},
    (PComp i g f).Dom ↔ Sc i g = Tg i f

instance {Obj : Type u}
    {index : Type} [NatIndex index]
    [S : SingleSortedStruct Obj index] {k : index} :
    SingleSortedStruct Obj (Fin k) where
  Sc j := S.Sc (j : index)
  Tg j := S.Tg (j : index)
  PComp j := S.PComp (j : index)
  pcomp_dom := S.pcomp_dom

scoped prefix:max "sc " => SingleSortedStruct.Sc
scoped prefix:max "tg " => SingleSortedStruct.Tg

def sc_is_tg {Obj : Type u}
    {index : Type} [NatIndex index]
    [SingleSortedStruct Obj index]
    (i : index) (g f : Obj) : Prop :=
  sc i g = tg i f

def comp {Obj : Type u}
    {index : Type} [NatIndex index]
    [S : SingleSortedStruct Obj index]
    (i : index) (g f : Obj) (composable_gf : sc_is_tg i g f) : Obj :=
  (S.PComp i g f).get (S.pcomp_dom.mpr composable_gf)

scoped notation g " ♯[" i "] " f " ← " composable_gf:100 =>
  comp i g f composable_gf

class SingleSortedCategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedStruct Obj index where
  idemp_sc_sc : ∀ {i : index} {f : Obj}, sc i (sc i f) = sc i f := by intros; rfl
  idemp_tg_sc : ∀ {i : index} {f : Obj}, tg i (sc i f) = sc i f := by intros; rfl
  idemp_sc_tg : ∀ {i : index} {f : Obj}, sc i (tg i f) = tg i f := by intros; rfl
  idemp_tg_tg : ∀ {i : index} {f : Obj}, tg i (tg i f) = tg i f := by intros; rfl
  sc_comp_is_sc : ∀ {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f),
      sc i (g ♯[i] f ← comp_gf) = sc i f := by intros; rfl
  tg_comp_is_tg : ∀ {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f),
      tg i (g ♯[i] f ← comp_gf) = tg i g := by intros; rfl
  comp_sc_is_id : ∀ {i : index} {f : Obj}, f ♯[i] (sc i f) ← idemp_tg_sc.symm = f := by intros; rfl
  comp_tg_is_id : ∀ {i : index} {f : Obj}, (tg i f) ♯[i] f ← idemp_sc_tg = f := by intros; rfl
  compr_assoc {i : index} {f g h : Obj}
      (comp_gf : sc_is_tg i g f) (comp_hg : sc_is_tg i h g) :
      sc_is_tg i h (g ♯[i] f ← comp_gf) :=
    comp_hg.trans (tg_comp_is_tg comp_gf).symm
  compl_assoc {i : index} {f g h : Obj}
      (comp_gf : sc_is_tg i g f) (comp_hg : sc_is_tg i h g) :
      sc_is_tg i (h ♯[i] g ← comp_hg) f :=
    (sc_comp_is_sc comp_hg).trans comp_gf
  assoc : ∀ {i : index} {f g h : Obj} (comp_gf : sc_is_tg i g f) (comp_hg : sc_is_tg i h g),
      (h ♯[i] (g ♯[i] f ← comp_gf) ← (compr_assoc comp_gf comp_hg)) =
      ((h ♯[i] g ← comp_hg) ♯[i] f ← (compl_assoc comp_gf comp_hg)) := by intros; rfl

class SingleSorted2CategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedCategoryFamily Obj index where
  idemp_sc : ∀ {k : index} {j : Fin k} {f : Obj},
      sc k (sc j f) = sc j f ∧
      sc j f = sc j (sc k f) ∧
      sc j (sc k f) = sc j (tg k f)
  idemp_tg : ∀ {k : index} {j : Fin k} {f : Obj},
      tg k (tg j f) = tg j f ∧
      tg j f = tg j (tg k f) ∧
      tg j (tg k f) = tg j (sc k f)
  sc_comp_is_comp_sc : ∀ {k : index} {j : Fin k} {f g : Obj}
      (comp_j_gf : sc_is_tg j g f),
      sc k (g ♯[j] f ← comp_j_gf) =
      (sc k g) ♯[j] (sc k f) ← (by sorry)
  tg_comp_is_comp_tg : ∀ {k : index} {j : Fin k} {f g : Obj}
      (comp_j_gf : sc_is_tg j g f),
      tg k (g ♯[j] f ← comp_j_gf) =
      (tg k g) ♯[j] (tg k f) ← (by sorry)
  -- TODO: Implement the remaining axiom of single-sorted 2-categories. It may
  -- require some auxiliary axioms/definitions.

@[ext]
class SingleSortedCategory (Obj : Type u)
    extends SingleSortedCategoryFamily Obj (Fin 1)

@[ext]
class SingleSorted2Category (Obj : Type u)
    extends SingleSorted2CategoryFamily Obj (Fin 2)

@[ext]
class SingleSortedNCategory (Obj : Type u) (index : Nat)
    extends SingleSorted2CategoryFamily Obj (Fin index)

@[ext]
class SingleSortedOmegaCategory (Obj : Type u)
    extends SingleSorted2CategoryFamily Obj Nat
  -- TODO: Implement the extra axioms of single-sorted ω-categories.

end HigherCategoryTheory
