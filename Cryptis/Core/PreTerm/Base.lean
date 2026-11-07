module

public import Iris.HeapLang.Syntax
public import Cryptis.Lib.Ord

/-! Pre-terms: the raw syntax of Cryptis messages.

A pre-term is a tree of operators. Integers and nonces are the leaves; keys and hashes take one
argument; pairs, sealed messages and exponentials take two; and the two kinds of product, of
exponents and of Diffie–Hellman values, take a list of positive factors and a list of negative
ones. Pre-terms may contain products and exponentials that are not simplified; terms are the
pre-terms in normal form (see `Cryptis.Core.PreTerm.Normalize`).

Every type here is ordered lexicographically: first by constructor, then by fields from left
to right, with lists compared by `List.compareLex`. Normal forms use this order to sort the
factors of products. -/

@[expose] public section
namespace Cryptis

open Iris.HeapLang

/-- A nonce: a fresh value, represented by the heap location allocated for it. -/
@[ext, rocq_alias cryptis.nonce]
structure Nonce where
  loc : Loc
deriving DecidableEq, Inhabited, Repr

instance : Ord Nonce := ⟨fun a b => compare a.loc b.loc⟩

instance : Std.TransOrd Nonce where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := (compare : Loc → Loc → Ordering))
  isLE_trans := Std.TransCmp.isLE_trans (cmp := (compare : Loc → Loc → Ordering))

instance : Std.LawfulEqOrd Nonce where
  eq_of_compare h :=
    Nonce.ext (Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Loc → Loc → Ordering)) h)

/-- Nullary operators: integers and nonces. -/
@[rocq_alias cryptis.term_op0]
inductive TermOp0 where
  | int (n : Int)
  | nonce (a : Nonce)
deriving DecidableEq, Inhabited, Repr, Ord

instance : Std.TransOrd TermOp0 where
  eq_swap {a b} := by
    show instOrdTermOp0.ord a b = (instOrdTermOp0.ord b a).swap
    cases a <;> cases b <;> simp only [instOrdTermOp0.ord, Ordering.then_eq] <;>
      first | rfl | exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    show (instOrdTermOp0.ord a b).isLE → (instOrdTermOp0.ord b c).isLE →
      (instOrdTermOp0.ord a c).isLE
    cases a <;> cases b <;> cases c <;> simp only [instOrdTermOp0.ord, Ordering.then_eq] <;>
      first | exact Std.TransCmp.isLE_trans | simp

instance : Std.LawfulEqOrd TermOp0 where
  eq_of_compare {a b} := by
    show instOrdTermOp0.ord a b = .eq → a = b
    cases a <;> cases b <;> simp only [instOrdTermOp0.ord, Ordering.then_eq] <;>
      first | exact congrArg _ ∘ Std.LawfulEqCmp.eq_of_compare | simp

/-- Key types: encryption and decryption keys, signing and verification keys, and symmetric
keys. -/
@[rocq_alias cryptis.key_type]
inductive KeyType where
  | aenc | adec | sign | verify | senc
deriving DecidableEq, Inhabited, Repr, Ord

instance : Std.TransOrd KeyType where
  eq_swap {a b} := by cases a <;> cases b <;> decide
  isLE_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd KeyType where
  eq_of_compare {a b} := by cases a <;> cases b <;> decide

/-- Unary operators: the key of a given type derived from a seed, and hashing. -/
@[rocq_alias cryptis.term_op1]
inductive TermOp1 where
  | key (kt : KeyType)
  | hash
deriving DecidableEq, Inhabited, Repr, Ord

instance : Std.TransOrd TermOp1 where
  eq_swap {a b} := by
    show instOrdTermOp1.ord a b = (instOrdTermOp1.ord b a).swap
    cases a <;> cases b <;> simp only [instOrdTermOp1.ord, Ordering.then_eq] <;>
      first | rfl | exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    show (instOrdTermOp1.ord a b).isLE → (instOrdTermOp1.ord b c).isLE →
      (instOrdTermOp1.ord a c).isLE
    cases a <;> cases b <;> cases c <;> simp only [instOrdTermOp1.ord, Ordering.then_eq] <;>
      first | exact Std.TransCmp.isLE_trans | simp

instance : Std.LawfulEqOrd TermOp1 where
  eq_of_compare {a b} := by
    show instOrdTermOp1.ord a b = .eq → a = b
    cases a <;> cases b <;> simp only [instOrdTermOp1.ord, Ordering.then_eq] <;>
      first | exact congrArg _ ∘ Std.LawfulEqCmp.eq_of_compare | simp

/-- Binary operators. `sealed` covers encryption and signatures alike: the key decides which. -/
@[rocq_alias cryptis.term_op2]
inductive TermOp2 where
  | pair | sealed | exp
deriving DecidableEq, Inhabited, Repr, Ord

instance : Std.TransOrd TermOp2 where
  eq_swap {a b} := by cases a <;> cases b <;> decide
  isLE_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd TermOp2 where
  eq_of_compare {a b} := by cases a <;> cases b <;> decide

/-- Variadic operators: the product of exponents and the product of Diffie–Hellman values. -/
@[rocq_alias cryptis.term_opN]
inductive TermOpN where
  | mul | gmul
deriving DecidableEq, Inhabited, Repr, Ord

instance : Std.TransOrd TermOpN where
  eq_swap {a b} := by cases a <;> cases b <;> decide
  isLE_trans {a b c} := by cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd TermOpN where
  eq_of_compare {a b} := by cases a <;> cases b <;> decide

/-- Pre-terms. -/
@[rocq_alias cryptis.PreTerm.pre_term]
inductive PreTerm where
  | op0 (o : TermOp0)
  | op1 (o : TermOp1) (t : PreTerm)
  | op2 (o : TermOp2) (t₁ t₂ : PreTerm)
  | opN (o : TermOpN) (ps ns : List PreTerm)
deriving Inhabited, Repr

namespace PreTerm

/-- The exponential `b ^ e`. -/
@[match_pattern, rocq_alias cryptis.PreTerm.PTExp]
abbrev ptExp (b e : PreTerm) : PreTerm := op2 .exp b e

/-- A product of exponents: its positive factors, then its negative ones. -/
@[match_pattern, rocq_alias cryptis.PreTerm.PTMul]
abbrev ptMul (ps ns : List PreTerm) : PreTerm := opN .mul ps ns

/-- A product of Diffie–Hellman values: its positive factors, then its negative ones. -/
@[match_pattern, rocq_alias cryptis.PreTerm.PTGMul]
abbrev ptGMul (ps ns : List PreTerm) : PreTerm := opN .gmul ps ns

/-- Induction with a hypothesis for every element of the lists under `opN`. -/
@[elab_as_elim, induction_eliminator, rocq_alias cryptis.PreTerm.pre_term_ind]
theorem ind {motive : PreTerm → Prop}
    (op0 : ∀ o, motive (.op0 o))
    (op1 : ∀ o t, motive t → motive (.op1 o t))
    (op2 : ∀ o t₁ t₂, motive t₁ → motive t₂ → motive (.op2 o t₁ t₂))
    (opN : ∀ o ps ns, (∀ t ∈ ps, motive t) → (∀ t ∈ ns, motive t) → motive (.opN o ps ns)) :
    ∀ t, motive t
  | .op0 o => op0 o
  | .op1 o t => op1 o t (ind op0 op1 op2 opN t)
  | .op2 o t₁ t₂ => op2 o t₁ t₂ (ind op0 op1 op2 opN t₁) (ind op0 op1 op2 opN t₂)
  | .opN o ps ns =>
    opN o ps ns (fun t _ => ind op0 op1 op2 opN t) (fun t _ => ind op0 op1 op2 opN t)

#rocq_ignore cryptis.PreTerm.pre_term_rect
  "Lean defines functions on PreTerm by structural recursion; PreTerm.ind covers proofs"
#rocq_ignore cryptis.PreTerm.pre_term_rect' "See PreTerm.ind"
#rocq_ignore cryptis.PreTerm.list_pre_term_rect' "See PreTerm.ind"
#rocq_ignore cryptis.PreTerm.pre_term_list_pre_term_rect "See PreTerm.ind"
#rocq_ignore cryptis.PreTerm.seq_pre_term "Only used to derive the list order in mathcomp"
#rocq_ignore cryptis.PreTerm.cons_num "The order compares constructors with PreTerm.ctorIdx"

mutual

/-- The order on pre-terms, written by hand because a derived `Ord` on a nested inductive is
opaque. -/
def cmp : PreTerm → PreTerm → Ordering
  | op0 o₁, op0 o₂ => compare o₁ o₂
  | op1 o₁ t₁, op1 o₂ t₂ => (compare o₁ o₂).then (cmp t₁ t₂)
  | op2 o₁ t₁ u₁, op2 o₂ t₂ u₂ => (compare o₁ o₂).then ((cmp t₁ t₂).then (cmp u₁ u₂))
  | opN o₁ ps₁ ns₁, opN o₂ ps₂ ns₂ =>
    (compare o₁ o₂).then ((cmpList ps₁ ps₂).then (cmpList ns₁ ns₂))
  | t₁, t₂ => compare t₁.ctorIdx t₂.ctorIdx

/-- `List.compareLex cmp`, spelled out so that `cmp` is structurally recursive. -/
def cmpList : List PreTerm → List PreTerm → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | t₁ :: ts₁, t₂ :: ts₂ => (cmp t₁ t₂).then (cmpList ts₁ ts₂)

end

theorem cmpList_eq_compareLex (ps qs : List PreTerm) : cmpList ps qs = ps.compareLex cmp qs := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp [cmpList, List.compareLex_nil_nil, List.compareLex_nil_cons]
  | cons t ts ih =>
    cases qs <;> simp [cmpList, List.compareLex_cons_nil, List.compareLex_cons_cons, ih]

theorem cmp_of_ctorIdx_ne {t₁ t₂ : PreTerm} (h : t₁.ctorIdx ≠ t₂.ctorIdx) :
    cmp t₁ t₂ = compare t₁.ctorIdx t₂.ctorIdx := by
  cases t₁ <;> cases t₂ <;> simp_all [cmp, PreTerm.ctorIdx]

theorem ctorIdx_eq_of_cmp {t₁ t₂ : PreTerm} (h : cmp t₁ t₂ = .eq) : t₁.ctorIdx = t₂.ctorIdx := by
  by_cases ht : t₁.ctorIdx = t₂.ctorIdx
  · exact ht
  · rw [cmp_of_ctorIdx_ne ht] at h
    exact absurd (Std.LawfulEqCmp.eq_of_compare h) ht

theorem ctorIdx_le_of_cmp {t₁ t₂ : PreTerm} (h : (cmp t₁ t₂).isLE) :
    t₁.ctorIdx ≤ t₂.ctorIdx := by
  by_cases ht : t₁.ctorIdx = t₂.ctorIdx
  · exact Nat.le_of_eq ht
  · rwa [cmp_of_ctorIdx_ne ht, Nat.isLE_compare] at h

theorem cmp_swap_of_ctorIdx_ne {t₁ t₂ : PreTerm} (h : t₁.ctorIdx ≠ t₂.ctorIdx) :
    cmp t₁ t₂ = (cmp t₂ t₁).swap := by
  rw [cmp_of_ctorIdx_ne h, cmp_of_ctorIdx_ne (Ne.symm h)]
  exact Std.OrientedCmp.eq_swap

/-- Transitivity reduces to the case where all three terms have the same constructor. -/
theorem cmp_trans_of_ctorIdx {t₁ t₂ t₃ : PreTerm}
    (h : t₁.ctorIdx = t₂.ctorIdx → t₂.ctorIdx = t₃.ctorIdx →
      (cmp t₁ t₂).isLE → (cmp t₂ t₃).isLE → (cmp t₁ t₃).isLE) :
    (cmp t₁ t₂).isLE → (cmp t₂ t₃).isLE → (cmp t₁ t₃).isLE := by
  intro h₁₂ h₂₃
  have l₁₂ := ctorIdx_le_of_cmp h₁₂
  have l₂₃ := ctorIdx_le_of_cmp h₂₃
  by_cases h₁₃ : t₁.ctorIdx = t₃.ctorIdx
  · exact h (by omega) (by omega) h₁₂ h₂₃
  · rw [cmp_of_ctorIdx_ne h₁₃, Nat.isLE_compare]
    omega

theorem cmpList_swap_of {ps : List PreTerm} (ih : ∀ t ∈ ps, ∀ u, cmp t u = (cmp u t).swap) :
    ∀ qs, cmpList ps qs = (cmpList qs ps).swap := by
  induction ps with
  | nil => intro qs; cases qs <;> rfl
  | cons t ts ih' =>
    intro qs
    cases qs with
    | nil => rfl
    | cons u us =>
      simp only [cmpList, Ordering.swap_then]
      rw [ih t (by simp) u, ih' (fun t' h => ih t' (by simp [h])) us]

theorem cmp_swap (t₁ t₂ : PreTerm) : cmp t₁ t₂ = (cmp t₂ t₁).swap := by
  induction t₁ generalizing t₂ with
  | op0 o =>
    cases t₂
    case op0 => exact Std.OrientedCmp.eq_swap (cmp := compare)
    all_goals exact cmp_swap_of_ctorIdx_ne nofun
  | op1 o t ih =>
    cases t₂
    case op1 => simp only [cmp, Ordering.swap_then, ← ih, ← Std.OrientedCmp.eq_swap]
    all_goals exact cmp_swap_of_ctorIdx_ne nofun
  | op2 o t u iht ihu =>
    cases t₂
    case op2 => simp only [cmp, Ordering.swap_then, ← iht, ← ihu, ← Std.OrientedCmp.eq_swap]
    all_goals exact cmp_swap_of_ctorIdx_ne nofun
  | opN o ps ns ihp ihn =>
    cases t₂
    case opN =>
      simp only [cmp, Ordering.swap_then, ← cmpList_swap_of ihp, ← cmpList_swap_of ihn,
        ← Std.OrientedCmp.eq_swap]
    all_goals exact cmp_swap_of_ctorIdx_ne nofun

theorem cmpList_eq_of {ps : List PreTerm} (ih : ∀ t ∈ ps, ∀ u, cmp t u = .eq → t = u) :
    ∀ qs, cmpList ps qs = .eq → ps = qs := by
  induction ps with
  | nil => intro qs; cases qs <;> simp [cmpList]
  | cons t ts ih' =>
    intro qs
    cases qs with
    | nil => simp [cmpList]
    | cons u us =>
      simp only [cmpList, Ordering.then_eq_eq, List.cons.injEq]
      exact fun ⟨h₁, h₂⟩ =>
        ⟨ih t (by simp) u h₁, ih' (fun t' h => ih t' (by simp [h])) us h₂⟩

theorem eq_of_cmp {t₁ t₂ : PreTerm} : cmp t₁ t₂ = .eq → t₁ = t₂ := by
  intro h
  have ht := ctorIdx_eq_of_cmp h
  induction t₁ generalizing t₂ with
  | op0 o =>
    cases t₂ <;> simp [PreTerm.ctorIdx] at ht
    simp only [cmp] at h
    rw [Std.LawfulEqCmp.eq_of_compare h]
  | op1 o t ih =>
    cases t₂ <;> simp [PreTerm.ctorIdx] at ht
    simp only [cmp, Ordering.then_eq_eq] at h
    rw [Std.LawfulEqCmp.eq_of_compare h.1, ih h.2 (ctorIdx_eq_of_cmp h.2)]
  | op2 o t u iht ihu =>
    cases t₂ <;> simp [PreTerm.ctorIdx] at ht
    simp only [cmp, Ordering.then_eq_eq] at h
    rw [Std.LawfulEqCmp.eq_of_compare h.1, iht h.2.1 (ctorIdx_eq_of_cmp h.2.1),
      ihu h.2.2 (ctorIdx_eq_of_cmp h.2.2)]
  | opN o ps ns ihp ihn =>
    cases t₂ <;> simp [PreTerm.ctorIdx] at ht
    simp only [cmp, Ordering.then_eq_eq] at h
    rw [Std.LawfulEqCmp.eq_of_compare h.1,
      cmpList_eq_of (fun t ht u h => ihp t ht h (ctorIdx_eq_of_cmp h)) _ h.2.1,
      cmpList_eq_of (fun t ht u h => ihn t ht h (ctorIdx_eq_of_cmp h)) _ h.2.2]

theorem cmpList_trans_of {ps : List PreTerm}
    (ih : ∀ t ∈ ps, ∀ u v, (cmp t u).isLE → (cmp u v).isLE → (cmp t v).isLE) :
    ∀ qs rs, (cmpList ps qs).isLE → (cmpList qs rs).isLE → (cmpList ps rs).isLE := by
  induction ps with
  | nil => intro qs rs; cases rs <;> simp [cmpList]
  | cons t ts ih' =>
    intro qs rs
    cases qs with
    | nil => simp [cmpList]
    | cons u us =>
      cases rs with
      | nil => simp [cmpList]
      | cons v vs =>
        exact Ordering.then_isLE_trans (cmp_swap _ _) eq_of_cmp (ih t (by simp) u v)
          (ih' (fun t' h => ih t' (by simp [h])) us vs)

theorem cmp_trans (t₁ t₂ t₃ : PreTerm) :
    (cmp t₁ t₂).isLE → (cmp t₂ t₃).isLE → (cmp t₁ t₃).isLE := by
  refine cmp_trans_of_ctorIdx fun e₁₂ e₂₃ => ?_
  induction t₁ generalizing t₂ t₃ with
  | op0 o =>
    cases t₂ <;> cases t₃ <;> simp [PreTerm.ctorIdx] at e₁₂ e₂₃
    exact Std.TransCmp.isLE_trans (cmp := (compare : TermOp0 → TermOp0 → Ordering))
  | op1 o t ih =>
    cases t₂ <;> cases t₃ <;> simp [PreTerm.ctorIdx] at e₁₂ e₂₃
    exact Ordering.compare_then_isLE_trans (cmp_trans_of_ctorIdx (ih _ _))
  | op2 o t u iht ihu =>
    cases t₂ <;> cases t₃ <;> simp [PreTerm.ctorIdx] at e₁₂ e₂₃
    exact Ordering.compare_then_isLE_trans <|
      Ordering.then_isLE_trans (cmp_swap _ _) eq_of_cmp (cmp_trans_of_ctorIdx (iht _ _))
        (cmp_trans_of_ctorIdx (ihu _ _))
  | opN o ps ns ihp ihn =>
    cases t₂ <;> cases t₃ <;> simp [PreTerm.ctorIdx] at e₁₂ e₂₃
    have hswap ps qs := cmpList_swap_of (ps := ps) (fun t _ u => cmp_swap t u) qs
    have heq {ps qs} := cmpList_eq_of (ps := ps) (fun _ _ _ => eq_of_cmp) qs
    exact Ordering.compare_then_isLE_trans <|
      Ordering.then_isLE_trans (hswap _ _) heq
        (cmpList_trans_of (fun t h u v => cmp_trans_of_ctorIdx (ihp t h u v)) _ _)
        (cmpList_trans_of (fun t h u v => cmp_trans_of_ctorIdx (ihn t h u v)) _ _)

instance : Ord PreTerm := ⟨cmp⟩

@[rocq_alias cryptis.PreTerm.pre_term_isOrder]
instance : Std.TransOrd PreTerm where
  eq_swap := cmp_swap _ _
  isLE_trans := cmp_trans _ _ _

instance : Std.LawfulEqOrd PreTerm where
  eq_of_compare := eq_of_cmp

@[rocq_alias cryptis.PreTerm.pre_term_hasDecEq]
instance : DecidableEq PreTerm := fun t₁ t₂ =>
  decidable_of_iff (compare t₁ t₂ = .eq) Std.LawfulEqCmp.compare_eq_iff_eq

/-- Products compare their factor lists with the standard order on lists. -/
theorem compare_opN {o₁ o₂ : TermOpN} {ps₁ ns₁ ps₂ ns₂ : List PreTerm} :
    compare (opN o₁ ps₁ ns₁) (opN o₂ ps₂ ns₂) =
      (compare o₁ o₂).then ((compare ps₁ ps₂).then (compare ns₁ ns₂)) := by
  show cmp _ _ = _
  rw [cmp, cmpList_eq_compareLex, cmpList_eq_compareLex]
  rfl

#rocq_ignore cryptis.PreTerm.le_alt "mathcomp order lemma; core Lean orders compare to Ordering"
#rocq_ignore cryptis.PreTerm.op0_leqE "The derived order on TermOp0 unfolds to this equation"
#rocq_ignore cryptis.PreTerm.op1_leqE "The derived order on TermOp1 unfolds to this equation"
#rocq_ignore cryptis.PreTerm.leqE "PreTerm.cmp is defined by this equation"

end PreTerm
end Cryptis
