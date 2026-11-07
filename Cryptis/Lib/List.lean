module

public import Cryptis.Lib.Encode
public import Cryptis.Lib.Ord
public import Cryptis.Lib.TwpTactics
public import Iris.HeapLang.PrimitiveLaws

/-! HeapLang list functions and their specifications.

Lists are encoded as in `Cryptis.Lib.Encode`. Most specifications come in a total version
(`twp_`) and a partial one (`wp_`). -/

@[expose] public section

namespace List

@[rocq_alias cryptis.find_if_in]
theorem decide_mem_eq_isSome_find? {α : Type _} [DecidableEq α] (v : α) (l : List α) :
    decide (v ∈ l) = (l.find? (fun x => decide (v = x))).isSome := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.find?_isSome]; simp

@[rocq_alias cryptis.bool_decide_lexico_le]
theorem isLE_compare_cons_cons {α : Type _} [Ord α] [Std.LawfulEqOrd α] [DecidableEq α]
    (x₁ x₂ : α) (l₁ l₂ : List α) :
    (compare (x₁ :: l₁) (x₂ :: l₂)).isLE =
      if x₁ = x₂ then (compare l₁ l₂).isLE else (compare x₁ x₂).isLE := by
  rw [List.compare_eq_compareLex, List.compareLex_cons_cons, ← List.compare_eq_compareLex]
  exact isLE_compare_then x₁ x₂ _

end List

/-! The WP tactics unfold the encodings of option and pair literals, so that `match` and the
projections compute on them. Encodings of variables, lists and terms stay folded, so that specs
about `encode ?x` keep matching. -/
attribute [wp_expr_simp] Cryptis.encode_none Cryptis.encode_some Cryptis.encode_pair

namespace Cryptis

open Iris Iris.HeapLang BI ProgramLogic

/-! ## Notation -/

/-- The empty HeapLang list. -/
@[rocq_alias cryptis.NILV]
abbrev nilV : Val := hl_val(none())

/-- A HeapLang list cell. -/
@[rocq_alias cryptis.CONSV]
abbrev consV (hd tl : Val) : Val := hl_val(some((&hd, &tl)))

/-- The expression that evaluates to the empty list. -/
@[rocq_alias cryptis.NIL]
abbrev nilE : Exp := hl(none())

/-- The function that adds an element in front of a list. -/
@[rocq_alias cryptis.CONS]
def cons : Val := hl_val% λ hd tl, some((hd, tl))

/-- List values `[v₁, v₂]`. -/
syntax:max "[" hl_val,* "]" : hl_val
/-- The list value `v :: vs`. -/
syntax:60 hl_val:61 " :: " hl_val:60 : hl_val

/-- List expressions `[e₁, e₂]`, built with `cons`. -/
syntax:max "[" hl_exp,* "]" : hl_exp
/-- The list expression `e :: es`, built with `cons`. -/
syntax:60 hl_exp:61 " :: " hl_exp:60 : hl_exp

macro_rules
  | `(hl_val([])) => `(nilV)
  | `(hl_val([$x])) => `(hl_val($x :: []))
  | `(hl_val([$x, $xs,*])) => `(hl_val($x :: [$xs,*]))
  | `(hl_val($x :: $xs)) => `(consV hl_val($x) hl_val($xs))
  | `(hl([])) => `(nilE)
  | `(hl([$x])) => `(hl($x :: []))
  | `(hl([$x, $xs,*])) => `(hl($x :: [$xs,*]))
  | `(hl($x :: $xs)) => `(hl(v(&cons) $x $xs))

/-! ## Programs -/

/-- The `n`-th element of a list, as an option. -/
@[rocq_alias cryptis.get_list]
def getList : Val := hl_val%
  rec loop l n :=
    match l with
    | none() => none()
    | some(p) => if n = #0 then some(fst(p)) else loop (snd(p)) (n - #1)

/-- Equality of lists, given an equality test on elements. -/
@[rocq_alias cryptis.eq_list]
def eqList : Val := hl_val%
  rec loop eq l1 l2 :=
    match l1 with
    | some(l1) =>
      (match l2 with
       | some(l2) =>
         let v1 := fst(l1);
         let l1 := snd(l1);
         let v2 := fst(l2);
         let l2 := snd(l2);
         eq v1 v2 && loop eq l1 l2
       | none() => #false)
    | none() =>
      (match l2 with
       | some(_) => #false
       | none() => #true)

/-- The first `some` result of `f` on the elements of a list. -/
@[rocq_alias cryptis.scan_list]
def scanList : Val := hl_val%
  rec loop f l :=
    match l with
    | some(p) =>
      let head := fst(p);
      let tail := snd(p);
      (match f head with
       | some(res) => some(res)
       | none() => loop f tail)
    | none() => none()

/-- The first element of a list that satisfies `f`. -/
@[rocq_alias cryptis.find_list]
def findList : Val := hl_val%
  rec loop f l :=
    match l with
    | some(p) =>
      let head := fst(p);
      let tail := snd(p);
      if f head then some(head) else loop f tail
    | none() => none()

/-- Membership in a list, given an equality test. -/
@[rocq_alias cryptis.mem_list]
def memList : Val := hl_val%
  λ eq v l,
    match &findList (λ m, eq v m) l with
    | some(_) => #true
    | none() => #false

/-- Remove the first occurrence of an element from a list, given an equality test. -/
@[rocq_alias cryptis.rem_list]
def remList : Val := hl_val%
  rec loop eq v l :=
    match l with
    | some(p) =>
      let head := fst(p);
      let tail := snd(p);
      if eq head v then tail else some((head, loop eq v tail))
    | none() => none()

/-- The elements of a list that satisfy `f`. -/
@[rocq_alias cryptis.filter_list]
def filterList : Val := hl_val%
  rec loop f l :=
    match l with
    | some(p) =>
      let head := fst(p);
      let tail := snd(p);
      let tail := loop f tail;
      if f head then some((head, tail)) else tail
    | none() => none()

/-- List concatenation. -/
@[rocq_alias cryptis.append_lists]
def appendLists : Val := hl_val%
  rec loop l1 l2 :=
    match l1 with
    | some(p) =>
      let head := fst(p);
      let tail := snd(p);
      some((head, loop tail l2))
    | none() => l2

/-- Apply `f` to every element of a list. -/
@[rocq_alias cryptis.map_list]
def mapList : Val := hl_val%
  rec loop f l :=
    match l with
    | some(p) =>
      let h := fst(p);
      let l' := snd(p);
      some((f h, loop f l'))
    | none() => none()

/-- Right fold over a list. -/
@[rocq_alias cryptis.foldr_list]
def foldrList : Val := hl_val%
  rec loop f seed l :=
    match l with
    | some(p) =>
      let head := fst(p);
      let tail := snd(p);
      f head (loop f seed tail)
    | none() => seed

/-- Insert an element into a list sorted by `le`. -/
@[rocq_alias cryptis.insert_sorted]
def insertSorted : Val := hl_val%
  rec loop le x l :=
    match l with
    | none() => some((x, none()))
    | some(l) =>
      let y := fst(l);
      let l := snd(l);
      if le x y then some((x, some((y, l)))) else some((y, loop le x l))

/-- Sort a list by `le`. -/
@[rocq_alias cryptis.insertion_sort]
def insertionSort : Val := hl_val%
  rec loop le l :=
    match l with
    | none() => none()
    | some(l) =>
      let y := fst(l);
      let l' := snd(l);
      &insertSorted le y (loop le l')

/-- Lexicographic comparison of lists, given an equality test and a comparison of elements. -/
@[rocq_alias cryptis.leq_list]
def leqList : Val := hl_val%
  rec loop eq le l1 l2 :=
    match l1 with
    | none() => #true
    | some(l1) =>
      (match l2 with
       | none() => #false
       | some(l2) =>
         let x1 := fst(l1);
         let x2 := fst(l2);
         let l1 := snd(l1);
         let l2 := snd(l2);
         if eq x1 x2 then loop eq le l1 l2 else le x1 x2)

/-- The head of a list, or `none()`. -/
@[rocq_alias cryptis.list_hd]
def listHd : Val := hl_val%
  λ l, match l with
    | none() => none()
    | some(l) => fst(l)

/-- The tail of a list, or `none()`. -/
@[rocq_alias cryptis.list_tl]
def listTl : Val := hl_val%
  λ l, match l with
    | none() => none()
    | some(l) => snd(l)

/-- Run `f` until it returns `some(v)`, and return `v`. -/
@[rocq_alias cryptis.do_until]
def doUntil : Val := hl_val%
  rec loop f :=
    match f #() with
    | none() => loop f
    | some(v) => v

/-- The expression that builds the encoding of a list with `cons`. -/
@[rocq_alias cryptis.list_to_expr]
def listToExp {α : Type _} [Encode α] (l : List α) : Exp :=
  l.foldr (fun x e => hl(v(&(encode x)) :: &e)) (nilV : Exp)

/-! ## Specifications -/

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {α β : Type _} [Encode α] [Encode β]
local bi (IProp GF)

@[rocq_alias cryptis.twp_get_list]
theorem twp_getList (l : List α) (n : Nat) (Ψ : Val → IProp GF) :
    Ψ (encode l[n]?) ⊢ WP hl(&getList &(encode l) #n) @ s; E [{ Ψ }] := by
  iintro H
  iinduction l generalizing %n H with
  | nil => twp_rec; simp only [encode_nil, List.getElem?_nil, encode_none]; twp_pures; iexact H
  | cons x l ih =>
    twp_rec; simp only [encode_cons]; twp_pures
    cases n with
    | zero => simp; twp_pures; imodintro; iexact H
    | succ n =>
      simp [Bool.beq_eq_decide_eq, show (n : Int) + 1 ≠ 0 by omega]
      twp_pures
      rw [show (n : Int) + 1 - 1 = n by omega]
      iapply ih $$ H

@[rocq_alias cryptis.wp_get_list]
theorem wp_getList (l : List α) (n : Nat) (Ψ : Val → IProp GF) :
    Ψ (encode l[n]?) ⊢ WP hl(&getList &(encode l) #n) @ s; E {{ Ψ }} :=
  (twp_getList l n Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_nil]
theorem twp_nil (Ψ : Val → IProp GF) :
    Ψ (encode ([] : List α)) ⊢ WP hl(v([])) @ s; E [{ Ψ }] := by
  simp only [encode_nil]; iintro H; twp_pures; iexact H

@[rocq_alias cryptis.twp_cons]
theorem twp_cons (x : α) (xs : List α) (Ψ : Val → IProp GF) :
    Ψ (encode (x :: xs)) ⊢ WP hl(v(&(encode x)) :: v(&(encode xs))) @ s; E [{ Ψ }] := by
  simp only [encode_cons]; iintro H; unfold cons; twp_pures; iexact H

@[rocq_alias cryptis.wp_nil]
theorem wp_nil (Ψ : Val → IProp GF) :
    Ψ (encode ([] : List α)) ⊢ WP hl(v([])) @ s; E {{ Ψ }} :=
  (twp_nil Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.wp_cons]
theorem wp_cons (x : α) (xs : List α) (Ψ : Val → IProp GF) :
    Ψ (encode (x :: xs)) ⊢ WP hl(v(&(encode x)) :: v(&(encode xs))) @ s; E {{ Ψ }} :=
  (twp_cons x xs Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_eq_list]
theorem twp_eqList [DecidableEq α] (f : Val) (l₁ l₂ : List α) (Φ : Val → IProp GF)
    (hf : ∀ x₁ ∈ l₁, ∀ x₂ (Ψ : Val → IProp GF),
      Ψ hl_val(#(decide (x₁ = x₂))) ⊢ WP hl(&f &(encode x₁) &(encode x₂)) @ s; E [{ Ψ }]) :
    Φ hl_val(#(decide (l₁ = l₂))) ⊢
      WP hl(&eqList &f &(encode l₁) &(encode l₂)) @ s; E [{ Φ }] := by
  induction l₁ generalizing l₂ Φ with
  | nil => cases l₂ <;> iintro H <;> twp_rec <;> simp <;> twp_pures <;> iexact H
  | cons x₁ l₁ ih =>
    cases l₂ with
    | nil => iintro H; twp_rec; simp; twp_pures; iexact H
    | cons x₂ l₂ =>
      iintro H; twp_rec; simp only [encode_cons]; twp_pures
      twp_apply hf x₁ List.mem_cons_self x₂
      by_cases h : x₁ = x₂
      · subst h; simp only [decide_true]; twp_pures
        simp only [List.cons.injEq, true_and]
        iapply ih _ _ (fun x hx => hf x (List.mem_cons_of_mem _ hx)) $$ H
      · simp [h]; twp_pures; iexact H

@[rocq_alias cryptis.wp_scan_list]
theorem wp_scanList (φ : α → IProp GF) (ψ : Val → IProp GF) (f : Val) (l : List α) :
    ⊢ (□ ∀ x, {{ ψ hl_val(none()) ∗ φ x }} hl(&f &(encode x)) @ s; E
        {{ (r : Option Val), RET encode r; ψ (encode r) }}) -∗
      ψ hl_val(none()) ∗ ([∗list] x ∈ l, φ x) -∗
      WP hl(&scanList &f &(encode l)) @ s; E {{ ψ }} := by
  iintro #Hf
  iloeb as IH generalizing %l
  iintro ⟨Hψ, Hφ⟩
  wp_rec
  cases l with
  | nil => simp only [encode_nil]; wp_pures; iexact Hψ
  | cons x l =>
    simp only [encode_cons]; wp_pures
    icases BigSepL.bigSepL_cons.1 $$ Hφ with ⟨Hx, Hφ⟩
    wp_apply Hf $$ [$Hψ $Hx] with %r Hψ
    cases r with
    | none => simp only [encode_none]; wp_pures; iapply IH $$ [$Hψ $Hφ]
    | some r => simp only [encode_some, encode_val]; wp_pures; iexact Hψ

@[rocq_alias cryptis.wp_scan_list']
theorem wp_scanList' (φ : List α → IProp GF) (ψ : Val → IProp GF) (f : Val) :
    ⊢ (□ ∀ x xs, {{ φ (x :: xs) }} hl(&f &(encode x)) @ s; E
        {{ (r : Option Val), RET encode r;
           match r with | some r => ψ hl_val(some(&r)) | none => φ xs }}) -∗
      (φ [] -∗ ψ hl_val(none())) -∗
      ∀ xs, φ xs -∗ WP hl(&scanList &f &(encode xs)) @ s; E {{ ψ }} := by
  iintro #Hf Hend %xs Hφ
  iloeb as IH generalizing %xs
  wp_rec
  cases xs with
  | nil => simp only [encode_nil]; wp_pures; iapply Hend $$ Hφ
  | cons x xs =>
    simp only [encode_cons]; wp_pures
    wp_apply Hf $$ Hφ with %r Hφ
    cases r with
    | none => simp only [encode_none]; wp_pures; iapply IH $$ Hend Hφ
    | some r => simp only [encode_some, encode_val]; wp_pures; iexact Hφ

@[rocq_alias cryptis.twp_find_list]
theorem twp_findList (f : α → Bool) (fimpl : Val) (l : List α)
    (hf : ∀ x : α, [{ True }] hl(&fimpl &(encode x)) @ s; E [{ RET hl_val(#(f x)); True }]) :
    [{ True }] hl(&findList &fimpl &(encode l)) @ s; E [{ RET encode (l.find? f); True }] := by
  iintro %Φ - HΦ
  iinduction l generalizing %Φ HΦ with
  | nil =>
    twp_rec; simp only [encode_nil, List.find?_nil, encode_none]; twp_pures; iapply HΦ $$ [//]
  | cons x l ih =>
    twp_rec; simp only [encode_cons]; twp_pures
    twp_apply hf x $$ [//] with -
    cases h : f x <;> simp [h] <;> twp_pures
    · iapply ih $$ HΦ
    · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_find_list]
theorem wp_findList (f : α → Bool) (fimpl : Val) (l : List α)
    (hf : ∀ x : α, {{ True }} hl(&fimpl &(encode x)) @ s; E {{ RET hl_val(#(f x)); True }}) :
    {{ True }} hl(&findList &fimpl &(encode l)) @ s; E {{ RET encode (l.find? f); True }} := by
  iintro %Φ - HΦ
  iloeb as IH generalizing %l %Φ
  wp_rec
  cases l with
  | nil => simp only [encode_nil, List.find?_nil, encode_none]; wp_pures; iapply HΦ $$ [//]
  | cons x l =>
    simp only [encode_cons]; wp_pures
    wp_apply hf x $$ [//] with -
    cases h : f x <;> simp [h] <;> wp_pures
    · iapply IH $$ HΦ
    · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_filter_list]
theorem wp_filterList (f : α → Bool) (fimpl : Val) (l : List α)
    (hf : ∀ x : α, {{ True }} hl(&fimpl &(encode x)) @ s; E {{ RET hl_val(#(f x)); True }}) :
    {{ True }} hl(&filterList &fimpl &(encode l)) @ s; E
      {{ RET encode (l.filter f); True }} := by
  iintro %Φ - HΦ
  iloeb as IH generalizing %l %Φ
  wp_rec
  cases l with
  | nil => simp only [encode_nil, List.filter_nil]; wp_pures; iapply HΦ $$ [//]
  | cons x l =>
    simp only [encode_cons]; wp_pures
    wp_apply IH with -
    wp_pures
    wp_apply hf x $$ [//] with -
    cases h : f x <;> simp [h] <;> wp_pures <;> iapply HΦ $$ [//]

@[rocq_alias cryptis.twp_append_lists]
theorem twp_appendLists (l₁ l₂ : List α) (Ψ : Val → IProp GF) :
    Ψ (encode (l₁ ++ l₂)) ⊢ WP hl(&appendLists &(encode l₁) &(encode l₂)) @ s; E [{ Ψ }] := by
  induction l₁ generalizing Ψ with
  | nil => iintro H; twp_rec; simp only [encode_nil, List.nil_append]; twp_pures; iexact H
  | cons x l₁ ih =>
    iintro H; twp_rec; simp only [List.cons_append, encode_cons]; twp_pures
    twp_apply ih
    twp_pures
    imodintro
    iexact H

@[rocq_alias cryptis.twp_map_list]
theorem twp_mapList (f : α → β) (fimpl : Val) (xs : List α)
    (hf : ∀ y ∈ xs, [{ True }] hl(&fimpl &(encode y)) @ s; E [{ RET encode (f y); True }]) :
    [{ True }] hl(&mapList &fimpl &(encode xs)) @ s; E [{ RET encode (xs.map f); True }] := by
  induction xs with
  | nil =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_nil, List.map_nil]; twp_pures; iapply HΦ $$ [//]
  | cons x xs ih =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_cons]; twp_pures
    twp_apply ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) $$ [//] with -
    twp_apply hf x List.mem_cons_self $$ [//] with -
    twp_pures
    simp only [List.map_cons, encode_cons]
    iapply HΦ $$ [//]

@[rocq_alias cryptis.twp_foldr_list]
theorem twp_foldrList (f : β → α → α) (fimpl : Val) (l : List β) (x : α)
    (hf : ∀ b a, [{ True }] hl(&fimpl &(encode b) &(encode a)) @ s; E
      [{ RET encode (f b a); True }]) :
    [{ True }] hl(&foldrList &fimpl &(encode x) &(encode l)) @ s; E
      [{ RET encode (l.foldr f x); True }] := by
  induction l with
  | nil =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_nil, List.foldr_nil]; twp_pures; iapply HΦ $$ [//]
  | cons b l ih =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_cons]; twp_pures
    twp_apply ih $$ [//] with -
    twp_apply hf $$ [//] with -
    simp only [List.foldr_cons]
    iapply HΦ $$ [//]

@[rocq_alias cryptis.twp_mem_list]
theorem twp_memList [DecidableEq α] (eqImpl : Val) (v : α) (l : List α)
    (heq : ∀ x y : α, [{ True }] hl(&eqImpl &(encode x) &(encode y)) @ s; E
      [{ RET hl_val(#(decide (x = y))); True }]) :
    [{ True }] hl(&memList &eqImpl &(encode v) &(encode l)) @ s; E
      [{ RET hl_val(#(decide (v ∈ l))); True }] := by
  iintro %Φ - HΦ
  twp_lam; twp_pures
  have hf (x : α) : [{ True }] hl(v(λ m, v(&eqImpl) v(&(encode v)) m) &(encode x)) @ s; E
      [{ RET hl_val(#(decide (v = x))); True }] := by
    iintro %Ψ - HΨ; twp_pures; twp_apply heq $$ [//] HΨ
  twp_apply twp_findList (fun x => decide (v = x)) _ l hf $$ [//] with -
  rw [List.decide_mem_eq_isSome_find?]
  cases List.find? (fun x => decide (v = x)) l <;>
    simp only [encode_none, encode_some, Option.isSome_none, Option.isSome_some] <;>
    twp_pures <;> iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_mem_list]
theorem wp_memList [DecidableEq α] (eqImpl : Val) (v : α) (l : List α)
    (heq : ∀ x y : α, {{ True }} hl(&eqImpl &(encode x) &(encode y)) @ s; E
      {{ RET hl_val(#(decide (x = y))); True }}) :
    {{ True }} hl(&memList &eqImpl &(encode v) &(encode l)) @ s; E
      {{ RET hl_val(#(decide (v ∈ l))); True }} := by
  iintro %Φ - HΦ
  wp_lam; wp_pures
  have hf (x : α) : {{ True }} hl(v(λ m, v(&eqImpl) v(&(encode v)) m) &(encode x)) @ s; E
      {{ RET hl_val(#(decide (v = x))); True }} := by
    iintro %Ψ - HΨ; wp_pures; wp_apply heq $$ [//] HΨ
  wp_apply wp_findList (fun x => decide (v = x)) _ l hf $$ [//] with -
  rw [List.decide_mem_eq_isSome_find?]
  cases List.find? (fun x => decide (v = x)) l <;>
    simp only [encode_none, encode_some, Option.isSome_none, Option.isSome_some] <;>
    wp_pures <;> iapply HΦ $$ [//]

@[rocq_alias cryptis.twp_rem_list]
theorem twp_remList [DecidableEq α] (eqImpl : Val) (v : α) (l : List α)
    (heq : ∀ x y : α, [{ True }] hl(&eqImpl &(encode x) &(encode y)) @ s; E
      [{ RET hl_val(#(decide (x = y))); True }]) :
    [{ True }] hl(&remList &eqImpl &(encode v) &(encode l)) @ s; E
      [{ RET encode (l.erase v); True }] := by
  induction l with
  | nil =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_nil, List.erase_nil]; twp_pures; iapply HΦ $$ [//]
  | cons x l ih =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_cons]; twp_pures
    twp_apply heq $$ [//] with -
    by_cases h : x = v
    · subst h; simp; twp_pures; iapply HΦ $$ [//]
    · simp [h]; twp_pures
      twp_apply ih $$ [//] with -
      twp_pures
      iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_rem_list]
theorem wp_remList [DecidableEq α] (eqImpl : Val) (v : α) (l : List α)
    (heq : ∀ x y : α, {{ True }} hl(&eqImpl &(encode x) &(encode y)) @ s; E
      {{ RET hl_val(#(decide (x = y))); True }}) :
    {{ True }} hl(&remList &eqImpl &(encode v) &(encode l)) @ s; E
      {{ RET encode (l.erase v); True }} := by
  iintro %Φ - HΦ
  iloeb as IH generalizing %l %Φ
  wp_rec
  cases l with
  | nil => simp only [encode_nil, List.erase_nil]; wp_pures; iapply HΦ $$ [//]
  | cons x l =>
    simp only [encode_cons]; wp_pures
    wp_apply heq $$ [//] with -
    by_cases h : x = v
    · subst h; simp; wp_pures; iapply HΦ $$ [//]
    · simp [h]; wp_pures
      wp_apply IH with -
      wp_pures
      iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_do_until]
theorem wp_doUntil (f : Val) (φ : IProp GF) (Ψ : Val → IProp GF) :
    ⊢ (□ (φ -∗ WP hl(&f #()) @ s; E {{ v, ⌜v = hl_val(none())⌝ ∗ φ ∨
        ∃ v', ⌜v = hl_val(some(&v'))⌝ ∗ Ψ v' }})) -∗
      φ -∗ WP hl(&doUntil &f) @ s; E {{ Ψ }} := by
  iintro #Hf Hφ
  iloeb as IH
  wp_rec
  ihave Hwp := Hf $$ Hφ
  wp_apply wp_wand $$ Hwp with %v (⟨%rfl, Hφ⟩ | ⟨%v, %rfl, HΨ⟩)
  · wp_pures; iapply IH $$ Hφ
  · wp_pures; iexact HΨ

@[rocq_alias cryptis.wp_do_until']
theorem wp_doUntil' (f : Val) (φ : Val → IProp GF) :
    ⊢ (□ WP hl(&f #()) @ s; E {{ v, ⌜v = hl_val(none())⌝ ∨
        ∃ v', ⌜v = hl_val(some(&v'))⌝ ∗ φ v' }}) -∗
      WP hl(&doUntil &f) @ s; E {{ φ }} := by
  iintro #Hf
  iapply wp_doUntil f iprop(True) φ $$ [] [//]
  iintro !> -
  iapply wp_wand $$ Hf
  iintro %v (%h | H)
  · ileft; isplit <;> ipureintro <;> trivial
  · iright; iexact H

section Ordered

variable (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
  (total : ∀ a b, le a b || le b a)

include trans total in
@[rocq_alias cryptis.twp_insert_sorted]
theorem twp_insertSorted (f : Val) (x : α) (l : List α) (hl : l.Pairwise (le · ·))
    (hf : ∀ y z, [{ True }] hl(&f &(encode y) &(encode z)) @ s; E
      [{ RET hl_val(#(le y z)); True }]) :
    [{ True }] hl(&insertSorted &f &(encode x) &(encode l)) @ s; E
      [{ (l' : List α), RET encode l'; ⌜l'.Pairwise (le · ·)⌝ ∗ ⌜l'.Perm (x :: l)⌝ }] := by
  induction l with
  | nil =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_nil]; twp_pures
    rw [← encode_nil (α := α), ← encode_cons]
    iapply HΦ $$ %([x]); imodintro; isplit <;> ipureintro <;> simp
  | cons y l ih =>
    iintro %Φ - HΦ
    obtain ⟨hy, hl⟩ := List.pairwise_cons.1 hl
    twp_rec; simp only [encode_cons]; twp_pures
    twp_apply hf $$ [//] with -
    cases hxy : le x y
    · twp_pures
      twp_apply ih hl $$ [//] with %l' ⟨%hs, %hp⟩
      twp_pures
      rw [← encode_cons]; iapply HΦ $$ %(y :: l'); imodintro; isplit <;> ipureintro
      · refine List.pairwise_cons.2 ⟨fun z hz => ?_, hs⟩
        rcases List.mem_cons.1 (hp.mem_iff.1 hz) with rfl | hz
        · simpa [hxy] using total z y
        · exact hy z hz
      · exact (hp.cons y).trans (.swap x y l)
    · twp_pures
      rw [← encode_cons, ← encode_cons]
      iapply HΦ $$ %(x :: y :: l); imodintro; isplit <;> ipureintro
      · refine List.pairwise_cons.2 ⟨fun z hz => ?_, List.pairwise_cons.2 ⟨hy, hl⟩⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hxy
        · exact trans _ _ _ hxy (hy z hz)
      · exact .refl _

include trans total in
@[rocq_alias cryptis.twp_insertion_sort]
theorem twp_insertionSort (antisymm : ∀ a b, le a b → le b a → a = b) (f : Val) (l : List α)
    (hf : ∀ x y, [{ True }] hl(&f &(encode x) &(encode y)) @ s; E
      [{ RET hl_val(#(le x y)); True }]) :
    [{ True }] hl(&insertionSort &f &(encode l)) @ s; E
      [{ RET encode (l.mergeSort le); True }] := by
  induction l with
  | nil =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_nil, List.mergeSort_nil]; twp_pures; iapply HΦ $$ [//]
  | cons y l ih =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_cons]; twp_pures
    twp_apply ih $$ [//] with -
    twp_apply twp_insertSorted le trans total f y _ (List.pairwise_mergeSort trans total l) hf
      $$ [//] with %l' ⟨%hs, %hp⟩
    rw [List.Perm.eq_of_pairwise (fun a b _ _ => antisymm a b)
      (List.pairwise_mergeSort trans total _) hs
      ((List.mergeSort_perm _ _).trans (hp.trans ((List.mergeSort_perm _ _).cons y)).symm)]
    iapply HΦ $$ [//]

end Ordered

@[rocq_alias cryptis.twp_leq_list]
theorem twp_leqList [Ord α] [Std.LawfulEqOrd α] [DecidableEq α] (feq fle : Val)
    (l₁ l₂ : List α)
    (hfeq : ∀ x₁ x₂ : α, [{ True }] hl(&feq &(encode x₁) &(encode x₂)) @ s; E
      [{ RET hl_val(#(decide (x₁ = x₂))); True }])
    (hfle : ∀ x₁ ∈ l₁, ∀ x₂ : α, [{ True }] hl(&fle &(encode x₁) &(encode x₂)) @ s; E
      [{ RET hl_val(#((compare x₁ x₂).isLE)); True }]) :
    [{ True }] hl(&leqList &feq &fle &(encode l₁) &(encode l₂)) @ s; E
      [{ RET hl_val(#((compare l₁ l₂).isLE)); True }] := by
  induction l₁ generalizing l₂ with
  | nil =>
    iintro %Φ - HΦ
    twp_rec; simp only [encode_nil]; twp_pures
    cases l₂ <;> simp <;> iapply HΦ $$ [//]
  | cons x₁ l₁ ih =>
    iintro %Φ - HΦ
    cases l₂ with
    | nil =>
      twp_rec; simp only [encode_nil, encode_cons]; twp_pures
      simp
      iapply HΦ $$ [//]
    | cons x₂ l₂ =>
      twp_rec; simp only [encode_cons]; twp_pures
      twp_apply hfeq $$ [//] with -
      rw [List.isLE_compare_cons_cons]
      by_cases h : x₁ = x₂ <;> simp only [h, decide_true, decide_false, ite_true, ite_false] <;>
        twp_pures
      · twp_apply ih _ (fun x hx => hfle x (List.mem_cons_of_mem _ hx)) $$ [//] HΦ
      · twp_apply hfle x₁ List.mem_cons_self $$ [//] HΦ

end Cryptis
