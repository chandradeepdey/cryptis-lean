module

public import Iris.HeapLang.Notation

/-! Encodings of Lean data as HeapLang values.

Option and list encodings follow HeapLang's conventions: `none` is `none()`, and a list is a
chain of `some((x, tail))` cells ending in `none()`. -/

@[expose] public section

namespace Cryptis

open Iris.HeapLang

/-- Types whose elements can be encoded as HeapLang values. -/
@[rocq_alias cryptis.Repr]
class Encode (α : Type _) where
  /-- The HeapLang value representing an element. -/
  encode : α → Val

attribute [rocq_alias cryptis.repr] Encode.encode

export Encode (encode)

variable {α β : Type _} [Encode α] [Encode β]

@[rocq_alias cryptis.repr_val]
instance : Encode Val := ⟨id⟩

@[rocq_alias cryptis.repr_Z]
instance : Encode Int := ⟨fun n => hl_val(#n)⟩

@[rocq_alias cryptis.repr_bool]
instance : Encode Bool := ⟨fun b => hl_val(#b)⟩

@[rocq_alias cryptis.repr_option]
instance : Encode (Option α) where
  encode
    | some x => hl_val(some(&(encode x)))
    | none => hl_val(none())

/-- The encoding of lists. -/
protected def Encode.list : List α → Val
  | [] => hl_val(none())
  | x :: xs => hl_val(some((&(encode x), &(Encode.list xs))))

@[rocq_alias cryptis.repr_list]
instance : Encode (List α) := ⟨Encode.list⟩

@[rocq_alias cryptis.repr_prod]
instance : Encode (α × β) := ⟨fun p => hl_val((&(encode p.1), &(encode p.2)))⟩

@[simp] theorem encode_val (v : Val) : encode v = v := rfl

@[simp] theorem encode_int (n : Int) : encode n = hl_val(#n) := rfl

@[simp] theorem encode_bool (b : Bool) : encode b = hl_val(#b) := rfl

@[simp] theorem encode_some (x : α) : encode (some x) = hl_val(some(&(encode x))) := rfl

@[simp] theorem encode_none : encode (none : Option α) = hl_val(none()) := rfl

@[simp] theorem encode_nil : encode ([] : List α) = hl_val(none()) := rfl

@[simp] theorem encode_cons (x : α) (xs : List α) :
    encode (x :: xs) = hl_val(some((&(encode x), &(encode xs)))) := rfl

#rocq_ignore cryptis.repr_listE "The simp lemmas `encode_nil` and `encode_cons`."

@[simp] theorem encode_prod (p : α × β) : encode p = hl_val((&(encode p.1), &(encode p.2))) :=
  rfl

/-- `encode_prod` for a pair literal. It does not apply to a variable, so it can be in the simp
set of the WP tactics. -/
theorem encode_pair (a : α) (b : β) : encode (a, b) = hl_val((&(encode a), &(encode b))) := rfl

/-- List encodings are injective on lists whose elements are encoded injectively. -/
theorem eq_of_encode_list_eq {xs ys : List α} (h : ∀ x ∈ xs, ∀ y, encode x = encode y → x = y)
    (e : encode xs = encode ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | rfl | cases e
  | cons x xs ih =>
    cases ys with
    | nil => cases e
    | cons y ys =>
      simp only [encode_cons, Val.injR.injEq, Val.pair.injEq] at e
      rw [h x (by simp) y e.1, ih (fun x hx => h x (by simp [hx])) e.2]

@[simp, rocq_alias cryptis.repr_list_val]
theorem encode_map_encode (xs : List α) : encode (xs.map encode) = encode xs := by
  induction xs <;> simp_all

end Cryptis
