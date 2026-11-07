module

public import Iris.Std.Positives

/-! Upstream candidate (Iris-Lean): computable `Pos.Countable` instances for products, sums and
options, and instances transported along an injection with a left inverse, for
`Iris/Std/Positives.lean`. The latter are named after Mathlib's `Encodable.ofLeftInjection` and
`Encodable.ofLeftInverse`. -/

@[expose] public section

namespace Pos.Countable

/-- Countability along an injection with a computable partial inverse. -/
abbrev ofLeftInjection {α β : Type} [Countable β] (f : α → β) (g : β → Option α)
    (h : ∀ a, g (f a) = some a) : Countable α where
  encode a := encode (f a)
  decode p := (decode p).bind g
  decode_encode a := by simp [decode_encode, h]

/-- Countability along an injection with a computable inverse. -/
abbrev ofLeftInverse {α β : Type} [Countable β] (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) : Countable α :=
  ofLeftInjection f (some ∘ g) (by simp [h])

instance {α β : Type} [Countable α] [Countable β] : Countable (α × β) where
  encode x := flatten [encode x.1, encode x.2]
  decode p := match unflatten p with
    | some [p₁, p₂] => return (← decode p₁, ← decode p₂)
    | _ => none
  decode_encode x := by simp [unflatten_flatten, decode_encode]

instance {α β : Type} [Countable α] [Countable β] : Countable (α ⊕ β) where
  encode
    | .inl a => (encode a)~0
    | .inr b => (encode b)~1
  decode
    | p~0 => (decode p).map .inl
    | p~1 => (decode p).map .inr
    | .xH => none
  decode_encode x := by cases x <;> simp [decode_encode]

instance {α : Type} [Countable α] : Countable (Option α) where
  encode
    | none => .xH
    | some a => (encode a)~0
  decode
    | p~0 => (decode p).map some
    | _ => some none
  decode_encode x := by cases x <;> simp [decode_encode]

end Pos.Countable
