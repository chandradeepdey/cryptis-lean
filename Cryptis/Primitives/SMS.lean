module

public import Mathlib.Data.Multiset.Sort
public import Cryptis.Lib.List
public import Cryptis.Lib.SMS

/-! HeapLang implementations of signed-multiset operations, parameterized by closures that
compare elements: an equality test `eq` and an order `le`.

A signed multiset over a linear order is encoded as its sorted positive and negative parts.
`HL.smsTo` computes this encoding for `SMS.make X Y` from the lists `X` and `Y`: it cancels their
common elements with `HL.smsCancel`, then sorts both sides. -/

@[expose] public section

namespace Cryptis

open Iris Iris.HeapLang BI ProgramLogic

namespace SMS

variable {T : Type _}

/-- Signed multisets over a linear order are encoded as their sorted positive and negative
parts. -/
@[rocq_alias cryptis.repr_sms]
instance [LinearOrder T] [Encode T] : Encode (SMS T) :=
  ⟨fun s => encode (s.posPart.sort, s.negPart.sort)⟩

@[rocq_alias cryptis.repr_smsE]
theorem encode_eq [LinearOrder T] [Encode T] (s : SMS T) :
    encode s = encode (s.posPart.sort, s.negPart.sort) := rfl

variable [DecidableEq T]

/-- Cancel `x` against an occurrence in the second list, or add it to the first one. -/
def cancelStep (x : T) (A : List T × List T) : List T × List T :=
  if x ∈ A.2 then (A.1, A.2.erase x) else (x :: A.1, A.2)

/-- Cancel the common elements of two lists, as the program `smsCancel` does. -/
def cancel (A : List T × List T) : List T × List T := A.1.foldr cancelStep ([], A.2)

theorem count_cancel (A : List T × List T) (z : T) :
    (cancel A).1.count z = A.1.count z - A.2.count z ∧
      (cancel A).2.count z = A.2.count z - A.1.count z := by
  obtain ⟨X, Y⟩ := A
  induction X generalizing z with
  | nil => simp [cancel]
  | cons x X ih =>
    simp only [cancel, List.foldr_cons] at ih ⊢
    generalize X.foldr cancelStep ([], Y) = B at ih
    have hx : x ∈ B.2 ↔ X.count x < Y.count x := by
      rw [← List.count_pos_iff, (ih x).2]; omega
    have := ih z
    unfold cancelStep
    split_ifs with h <;> rw [hx] at h <;>
      simp only [List.count_erase, List.count_cons, beq_iff_eq] <;>
      split_ifs <;> subst_vars <;> omega

@[simp]
theorem coe_cancel_fst (A : List T × List T) :
    ((cancel A).1 : Multiset T) = (make A.1 A.2).posPart :=
  Multiset.ext.mpr fun z => by
    rw [posPart_make, Multiset.count_sub, Multiset.coe_count, Multiset.coe_count,
      Multiset.coe_count, (count_cancel A z).1]

@[simp]
theorem coe_cancel_snd (A : List T × List T) :
    ((cancel A).2 : Multiset T) = (make A.1 A.2).negPart :=
  Multiset.ext.mpr fun z => by
    rw [negPart_make, Multiset.count_sub, Multiset.coe_count, Multiset.coe_count,
      Multiset.coe_count, (count_cancel A z).2]

/-- Binding the signed multiset of a pair of lists binds the pairs of lists of its elements. -/
theorem make_flatMap {U : Type _} [DecidableEq U] {f : T → List U × List U} {F : T → SMS U}
    {A : List T × List T}
    (h : ∀ x ∈ A.1 ++ A.2,
      ((f x).1 : Multiset U) = (F x).posPart ∧ ((f x).2 : Multiset U) = (F x).negPart) :
    make (A.1.flatMap (fun x => (f x).1) ++ A.2.flatMap (fun x => (f x).2) : List U)
        (A.1.flatMap (fun x => (f x).2) ++ A.2.flatMap (fun x => (f x).1) : List U) =
      (make A.1 A.2).bind F := by
  have h₁ x (hx : x ∈ A.1) := h x (List.mem_append_left _ hx)
  have h₂ x (hx : x ∈ A.2) := h x (List.mem_append_right _ hx)
  rw [bind_make, ← Multiset.coe_add, ← Multiset.coe_add]
  simp only [← Multiset.coe_bind]
  congr 2 <;> refine Multiset.bind_congr fun x hx => ?_
  exacts [(h₁ x hx).1, (h₂ x hx).2, (h₁ x hx).2, (h₂ x hx).1]

end SMS

namespace HL

/-! ## Programs -/

/-- Cancel `x` against an occurrence in the second list, or add it to the first one. -/
@[rocq_alias cryptis.sms_cancel_step]
def smsCancelStep : Val := hl_val%
  λ eq x A,
    if &memList eq x (snd(A)) then (fst(A), &remList eq x (snd(A)))
    else (x :: fst(A), snd(A))

/-- Cancel the common elements of a pair of lists. -/
@[rocq_alias cryptis.sms_cancel]
def smsCancel : Val := hl_val%
  λ eq A, &foldrList (λ x acc, &smsCancelStep eq x acc) ([], snd(A)) (fst(A))

/-- The encoding of the signed multiset with the occurrences in a pair of lists. -/
@[rocq_alias cryptis.sms_to]
def smsTo : Val := hl_val%
  λ le eq A,
    let B := &smsCancel eq A;
    (&insertionSort le (fst(B)), &insertionSort le (snd(B)))

end HL

/-! ## Specifications -/

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {T : Type _} [Encode T]
local bi (IProp GF)

namespace HL

section Eq

variable [DecidableEq T] (eqv : Val)
  (heqv : ∀ (x y : T) (Ψ : Val → IProp GF),
    Ψ hl_val(#(decide (x = y))) ⊢ WP hl(&eqv &(encode x) &(encode y)) @ s; E [{ Ψ }])
include heqv

@[rocq_alias cryptis.twp_sms_cancel_step]
theorem twp_smsCancelStep (x : T) (A : List T × List T) (Ψ : Val → IProp GF) :
    Ψ (encode (SMS.cancelStep x A)) ⊢
      WP hl(&smsCancelStep &eqv &(encode x) &(encode A)) @ s; E [{ Ψ }] := by
  have heq x y := triple_of_twp (heqv x y)
  iintro H
  twp_rec
  rw [encode_prod A]
  twp_pures
  twp_apply twp_memList eqv x A.2 heq $$ [//] with -
  unfold SMS.cancelStep
  by_cases h : x ∈ A.2
  · simp only [h, decide_true, ite_true]
    twp_pures
    twp_apply twp_remList eqv x A.2 heq $$ [//] with -
    twp_pures
    iexact H
  · simp only [h, decide_false, ite_false]
    twp_pures
    twp_apply twp_cons
    twp_pures
    iexact H

@[rocq_alias cryptis.twp_sms_cancel]
theorem twp_smsCancel (A : List T × List T) (Ψ : Val → IProp GF) :
    Ψ (encode (SMS.cancel A)) ⊢ WP hl(&smsCancel &eqv &(encode A)) @ s; E [{ Ψ }] := by
  have hf (x : T) (B : List T × List T) :
      [{ True }] hl(v(λ x acc, &smsCancelStep &eqv x acc) &(encode x) &(encode B)) @ s; E
        [{ RET encode (SMS.cancelStep x B); True }] := by
    iintro %Φ - HΦ
    twp_pures
    twp_apply twp_smsCancelStep eqv heqv
    iapply HΦ $$ [//]
  iintro H
  twp_rec
  rw [encode_prod A]
  twp_pures
  rw [show hl_val((none(), &(encode A.2))) = encode (([] : List T), A.2) from rfl]
  twp_apply twp_foldrList SMS.cancelStep _ A.1 ([], A.2) hf $$ [//] with -
  rw [SMS.cancel]
  iexact H

end Eq

section Order

variable [LinearOrder T] (eqv lev : Val)
  (heqv : ∀ (x y : T) (Ψ : Val → IProp GF),
    Ψ hl_val(#(decide (x = y))) ⊢ WP hl(&eqv &(encode x) &(encode y)) @ s; E [{ Ψ }])
  (hlev : ∀ (x y : T) (Ψ : Val → IProp GF),
    Ψ hl_val(#(decide (x ≤ y))) ⊢ WP hl(&lev &(encode x) &(encode y)) @ s; E [{ Ψ }])
include heqv hlev

@[rocq_alias cryptis.twp_sms_to]
theorem twp_smsTo (A : List T × List T) (Ψ : Val → IProp GF) :
    Ψ (encode (SMS.make (A.1 : Multiset T) A.2)) ⊢
      WP hl(&smsTo &lev &eqv &(encode A)) @ s; E [{ Ψ }] := by
  have sort (l : List T) :=
    twp_insertionSort (fun a b => decide (a ≤ b))
      (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact le_trans h₁ h₂)
      (fun a b => by simpa using le_total a b)
      (fun _ _ h₁ h₂ => le_antisymm (by simpa using h₁) (by simpa using h₂))
      lev l fun x y => triple_of_twp (hlev x y)
  iintro H
  twp_rec
  twp_pures
  twp_apply twp_smsCancel eqv heqv
  rw [encode_prod (SMS.cancel A)]
  twp_pures
  twp_apply sort $$ [//] with -
  twp_pures
  twp_apply sort $$ [//] with -
  twp_pures
  rw [SMS.encode_eq, ← SMS.coe_cancel_fst, ← SMS.coe_cancel_snd, Multiset.coe_sort,
    Multiset.coe_sort]
  iexact H

end Order

end HL

end Cryptis
