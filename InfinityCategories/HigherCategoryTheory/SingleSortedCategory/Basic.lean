/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Pfun
import Mathlib.Data.Part
import InfinityCategories.Data.NatIndex

/-!
TODO: Document the file.
-/

universe u

namespace HigherCategoryTheory

class SingleSortedStruct (Obj : Type u) (index : Type) [NatIndex index] where
  Sc : index → Obj → Obj
  Tg : index → Obj → Obj
  PComp : index → Obj → Obj →. Obj
  pcomp_dom : ∀ {i : index} {f g : Obj},
    (PComp i g f).Dom ↔ Sc i g = Tg i f

instance {Obj : Type u} {index : Type} [NatIndex index]
    [S : SingleSortedStruct Obj index]
    {k : index} : SingleSortedStruct Obj (Fin k) where
  Sc j := S.Sc (j : index)
  Tg j := S.Tg (j : index)
  PComp j := S.PComp (j : index)
  pcomp_dom := S.pcomp_dom

scoped prefix:max "sc " => SingleSortedStruct.Sc
scoped prefix:max "tg " => SingleSortedStruct.Tg
scoped notation g " ♯.[" i "] " f:100 => SingleSortedStruct.PComp i g f

def sc_is_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedStruct Obj index]
    (i : index) (g f : Obj) : Prop :=
  sc i g = tg i f

def get_dom_of_sc_is_tg {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedStruct Obj index]
    {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f) :
    (g ♯.[i] f).Dom :=
  SingleSortedStruct.pcomp_dom.mpr comp_gf

def comp {Obj : Type u} {index : Type} [NatIndex index]
    [SingleSortedStruct Obj index]
    (i : index) (g f : Obj) (composable_gf : sc_is_tg i g f) : Obj :=
  (g ♯.[i] f).get (get_dom_of_sc_is_tg composable_gf)

scoped notation g " ♯[" i "] " f " ← " comp_gf:100 => comp i g f comp_gf

theorem congr_pcomp {Obj : Type u} {index : Type} [NatIndex index]
    [S : SingleSortedStruct Obj index]
    {i : index} {f₁ f₂ g₁ g₂ : Obj} (eq_g₁g₂ : g₁ = g₂) (eq_f₁f₂ : f₁ = f₂)
    (comp_g₁f₁ : sc_is_tg i g₁ f₁) (comp_g₂f₂ : sc_is_tg i g₂ f₂) :
    g₁ ♯[i] f₁ ← comp_g₁f₁ = g₂ ♯[i] f₂ ← comp_g₂f₂ := by
  have pcomp_eq : g₁ ♯.[i] f₁ = g₂ ♯.[i] f₂ :=
    congrArg₂ (· ♯.[i] ·) eq_g₁g₂ eq_f₁f₂
  let comp_g₁f₁_dom := get_dom_of_sc_is_tg comp_g₁f₁
  let comp_g₂f₂_dom := get_dom_of_sc_is_tg comp_g₂f₂
  apply (Part.eq_iff_of_dom comp_g₁f₁_dom comp_g₂f₂_dom).mpr pcomp_eq

class SingleSortedCategoryFamily (Obj : Type u) (index : Type) [NatIndex index]
    extends SingleSortedStruct Obj index where
  sc_sc_is_sc : ∀ {i : index} {f : Obj}, sc i (sc i f) = sc i f := by intros; rfl
  tg_sc_is_sc : ∀ {i : index} {f : Obj}, tg i (sc i f) = sc i f := by intros; rfl
  sc_tg_is_tg : ∀ {i : index} {f : Obj}, sc i (tg i f) = tg i f := by intros; rfl
  tg_tg_is_tg : ∀ {i : index} {f : Obj}, tg i (tg i f) = tg i f := by intros; rfl
  sc_comp_is_sc : ∀ {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f),
      sc i (g ♯[i] f ← comp_gf) = sc i f := by intros; rfl
  tg_comp_is_tg : ∀ {i : index} {f g : Obj} (comp_gf : sc_is_tg i g f),
      tg i (g ♯[i] f ← comp_gf) = tg i g := by intros; rfl
  comp_sc_is_id : ∀ {i : index} {f : Obj}, f ♯[i] (sc i f) ← tg_sc_is_sc.symm = f := by intros; rfl
  comp_tg_is_id : ∀ {i : index} {f : Obj}, (tg i f) ♯[i] f ← sc_tg_is_tg = f := by intros; rfl
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
      ((h ♯[i] g ← comp_hg) ♯[i] f ← (compl_assoc comp_gf comp_hg)) := by
      intros; rfl

class SingleSorted2CategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedCategoryFamily Obj index where
  sck_scj_is_scj : ∀ {k : index} {j : Fin k} {f : Obj}, sc k (sc j f) = sc j f := by intros; rfl
  scj_sck_is_scj : ∀ {k : index} {j : Fin k} {f : Obj}, sc j (sc k f) = sc j f := by intros; rfl
  scj_tgk_is_scj : ∀ {k : index} {j : Fin k} {f : Obj}, sc j (tg k f) = sc j f := by intros; rfl
  tgk_tgj_is_tgj : ∀ {k : index} {j : Fin k} {f : Obj}, tg k (tg j f) = tg j f := by intros; rfl
  tgj_tgk_is_tgj : ∀ {k : index} {j : Fin k} {f : Obj}, tg j (tg k f) = tg j f := by intros; rfl
  tgj_sck_is_tgj : ∀ {k : index} {j : Fin k} {f : Obj}, tg j (sc k f) = tg j f := by intros; rfl
  comp_j_sc {k : index} {j : Fin k} {f g : Obj} (comp_j_gf : sc_is_tg j g f) :
      sc_is_tg j (sc k g) (sc k f) :=
    (scj_sck_is_scj.trans comp_j_gf).trans tgj_sck_is_tgj.symm
  comp_j_tg {k : index} {j : Fin k} {f g : Obj} (comp_j_gf : sc_is_tg j g f) :
      sc_is_tg j (tg k g) (tg k f) :=
    (scj_tgk_is_scj.trans comp_j_gf).trans tgj_tgk_is_tgj.symm
  sck_compj_is_compj_sck : ∀ {k : index} {j : Fin k} {f g : Obj}
      (comp_j_gf : sc_is_tg j g f),
      sc k (g ♯[j] f ← comp_j_gf) =
      (sc k g) ♯[j] (sc k f) ← (comp_j_sc comp_j_gf) := by intros; rfl
  tgk_compj_is_compj_tgk : ∀ {k : index} {j : Fin k} {f g : Obj}
      (comp_j_gf : sc_is_tg j g f),
      tg k (g ♯[j] f ← comp_j_gf) =
      (tg k g) ♯[j] (tg k f) ← (comp_j_tg comp_j_gf) := by intros; rfl
  comp_k_exchange {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (comp_k_g₂g₁ : sc_is_tg k g₂ g₁) (comp_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (comp_j_g₂f₂ : sc_is_tg j g₂ f₂) (comp_j_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg k (g₂ ♯[j] f₂ ← comp_j_g₂f₂) (g₁ ♯[j] f₁ ← comp_j_g₁f₁) := calc
    sc k (g₂ ♯[j] f₂ ← comp_j_g₂f₂)
    _ = (sc k g₂) ♯[j] (sc k f₂) ← (comp_j_sc comp_j_g₂f₂) := sck_compj_is_compj_sck comp_j_g₂f₂
    _ = (tg k g₁) ♯[j] (tg k f₁) ← (comp_j_tg comp_j_g₁f₁) :=
      congr_pcomp comp_k_g₂g₁ comp_k_f₂f₁ (comp_j_sc comp_j_g₂f₂) (comp_j_tg comp_j_g₁f₁)
    _ = tg k (g₁ ♯[j] f₁ ← comp_j_g₁f₁) := (tgk_compj_is_compj_tgk comp_j_g₁f₁).symm
  comp_j_exchange {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (comp_k_g₂g₁ : sc_is_tg k g₂ g₁) (comp_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (comp_j_g₂f₂ : sc_is_tg j g₂ f₂) (comp_j_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg j (g₂ ♯[k] g₁ ← comp_k_g₂g₁) (f₂ ♯[k] f₁ ← comp_k_f₂f₁) := calc
    sc j (g₂ ♯[k] g₁ ← comp_k_g₂g₁)
    _ = sc j (sc k (g₂ ♯[k] g₁ ← comp_k_g₂g₁)) := scj_sck_is_scj.symm
    _ = sc j (sc k g₁) := congrArg (fun x => sc j x) (sc_comp_is_sc comp_k_g₂g₁)
    _ = sc j g₁ := scj_sck_is_scj
    _ = tg j f₁ := comp_j_g₁f₁
    _ = tg j (sc k f₁) := tgj_sck_is_tgj.symm
    _ = tg j (sc k (f₂ ♯[k] f₁ ← comp_k_f₂f₁)) :=
      congrArg (fun x => tg j x) (sc_comp_is_sc comp_k_f₂f₁).symm
    _ = tg j (f₂ ♯[k] f₁ ← comp_k_f₂f₁) := tgj_sck_is_tgj
  exchange : ∀ {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (comp_k_g₂g₁ : sc_is_tg k g₂ g₁) (comp_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (comp_j_g₂f₂ : sc_is_tg j g₂ f₂) (comp_j_g₁f₁ : sc_is_tg j g₁ f₁),
      (g₂ ♯[j] f₂ ← comp_j_g₂f₂) ♯[k] (g₁ ♯[j] f₁ ← comp_j_g₁f₁) ←
        (comp_k_exchange comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁) =
      (g₂ ♯[k] g₁ ← comp_k_g₂g₁) ♯[j] (f₂ ♯[k] f₁ ← comp_k_f₂f₁) ←
        (comp_j_exchange comp_k_g₂g₁ comp_k_f₂f₁ comp_j_g₂f₂ comp_j_g₁f₁) := by intros; rfl

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
