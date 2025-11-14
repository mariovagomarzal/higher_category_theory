/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Nat.Notation

/-!
# Natural-like index types

This file defines the `NatIndex` typeclass, which allows arbitrary types to be used as index
families that behave like natural numbers.

This is particularly useful when defining concepts in single-sorted categories that depend on an
index family. When each index requires types parameterized by natural numbers (such as `Fin` or
`ℕ` itself), any type instantiating `NatIndex` can be used in place of the natural numbers
themselves.
-/

/-- A typeclass for types that can serve as index families similar to natural numbers. -/
class NatIndex (index : Type) where
  /-- Coerces an `index` to a `ℕ`, considered its natural presentation. -/
  coeIndexNat : index → ℕ

/-- Any `NatIndex` type has a _less-than_ relation induced by the natural numbers. -/
instance LT.instNatIndex {index : Type} [I : NatIndex index] : LT index :=
  ⟨fun i j ↦ I.coeIndexNat i < I.coeIndexNat j⟩

/-- Any `NatIndex` type has a _less-than-or-equal_ relation induced by the natural numbers. -/
instance LE.instNatIndex {index : Type} [I : NatIndex index] : LE index :=
  ⟨fun i j ↦ I.coeIndexNat i ≤ I.coeIndexNat j⟩

namespace NatIndex

/-- Coercion from any `NatIndex` type to `ℕ`. -/
instance instCoeOutNat {index : Type} [NatIndex index] : CoeOut index ℕ :=
  ⟨coeIndexNat⟩

/-- For any `n : ℕ`, `Fin n` is a `NatIndex` via `Fin.val` and `Fin.castLE`. -/
instance instFin (n : ℕ) : NatIndex (Fin n) where
  coeIndexNat i := i.val

/-- `ℕ` is a `NatIndex` via the identity function. -/
instance instNat : NatIndex ℕ where
  coeIndexNat := id

end NatIndex
