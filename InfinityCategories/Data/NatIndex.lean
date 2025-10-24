/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/

/-!
# Natural-like index types

This file defines the `NatIndex` typeclass, which allows arbitrary types to be
used as index families that behave like natural numbers.

This is particularly useful when defining concepts in single-sorted categories
that depend on an index family. When each index requires types parameterized by
natural numbers (such as `Fin`), any type instantiating `NatIndex` can be used
in place of the natural numbers themselves.
-/

/--
A typeclass for types that can serve as index families similar to natural
numbers.
-/
class NatIndex (index : Type) where
  /-- Coerces an `index` to a `Nat`, considered its natural presentation. -/
  coeIndexNat : index → Nat
  /-- Coerces a `Fin k` to a `index`, where `k` is an element of `index`. -/
  coeFinIndex : (k : index) → Fin (coeIndexNat k) → index

namespace NatIndex


/-- Coercion from any `NatIndex` type to `Nat`. -/
instance {index : Type} [NatIndex index] : CoeOut index Nat :=
  ⟨NatIndex.coeIndexNat⟩

/-- Coercion from `Fin k` to any `NatIndex` type, where `k` is of that type. -/
instance {index : Type} [NatIndex index] {k : index} :
    CoeOut (Fin k) index :=
  ⟨NatIndex.coeFinIndex k⟩

/--
For any `n : Nat`, `Fin n` is a `NatIndex` via `Fin.val` and `Fin.castLE`.
-/
instance (n : Nat) : NatIndex (Fin n) where
  coeIndexNat := Fin.val
  coeFinIndex k := Fin.castLE (Nat.le_of_lt k.isLt)

/-- `Nat` is a `NatIndex` via the identity function. -/
instance : NatIndex Nat where
  coeIndexNat := id
  coeFinIndex := fun _ j ↦ j

end NatIndex
