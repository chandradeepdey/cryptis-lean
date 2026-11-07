module

public import Cryptis.Primitives.Simple
public import Cryptis.Upstream.Iris.HeapLangAssert
public import Iris.HeapLang.Lib.Assert
public import Iris.HeapLang.Lib.TicketLock

/-! Mutable sets of terms in HeapLang.

A term set is a reference to the list of its elements, each of which satisfies a persistent
predicate `φ`. A term is added only if it is fresh, that is, if `φ` does not hold of it yet but can
be made to hold, so the elements are distinct. A locked term set pairs a term set with a ticket
lock, and its insertion checks that the term is not in the set. -/

@[expose] public section

namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode

namespace HL

/-- A new empty term set. -/
@[rocq_alias cryptis.new_term_set]
def newTermSet : Val := hl_val% λ _, ref([])

/-- Add a term to a term set. -/
@[rocq_alias cryptis.add_term_set]
def addTermSet : Val := hl_val% λ x set, set ← x :: !set

/-- Membership in a term set. -/
@[rocq_alias cryptis.mem_term_set]
def memTermSet : Val := hl_val% λ x set, &memList &eqTerm x (!set)

/-- A new term set with a lock. -/
@[rocq_alias cryptis.new_lock_term_set]
def newLockTermSet : Val := hl_val%
  λ _,
    let set := &newTermSet #();
    let lock := &TicketLock.newlock #();
    (set, lock)

/-- Add a term to a locked term set, failing if it is already there. -/
@[rocq_alias cryptis.add_fresh_lock_term_set]
def addFreshLockTermSet : Val := hl_val%
  λ x set,
    &TicketLock.acquire (snd(set));
    let xs := fst(set);
    assert(~ (&memTermSet x xs));
    &addTermSet x xs;
    &TicketLock.release (snd(set))

end HL

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

/-- `v` is a term set with elements `xs`, all of which satisfy `φ`. -/
@[rocq_alias cryptis.is_term_set]
def isTermSet (φ : Term → IProp GF) (v : Val) (xs : List Term) : IProp GF :=
  iprop(∃ l : Loc, ⌜v = hl_val(#l)⌝ ∗ l ↦ some (encode xs) ∗ [∗list] x ∈ xs, □ φ x)

/-- `φ` does not hold of `x`, but can be made to hold. -/
@[rocq_alias cryptis.fresh_term]
def freshTerm (φ : Term → IProp GF) (x : Term) : IProp GF :=
  iprop((□ φ x → False) ∧ |==> □ φ x)

/-- `v` is a term set with elements satisfying `φ`, protected by a ticket lock. -/
@[rocq_alias cryptis.is_lock_term_set]
def isLockTermSet [TicketLock.TicketLockG GF] (φ : Term → IProp GF) (v : Val) : IProp GF :=
  iprop(∃ (vset vlock : Val) (γ : GName), ⌜v = hl_val((&vset, &vlock))⌝ ∗
    TicketLock.isLock γ vlock (∃ xs, isTermSet φ vset xs))

@[rocq_alias cryptis.is_lock_term_set_persistent]
instance isLockTermSet_persistent [TicketLock.TicketLockG GF] (φ : Term → IProp GF) (v : Val) :
    Persistent (isLockTermSet φ v) := by
  unfold isLockTermSet; infer_instance

@[rocq_alias cryptis.is_term_set_fresh]
theorem isTermSet_fresh {φ : Term → IProp GF} {v : Val} {x : Term} {xs : List Term} :
    isTermSet φ v xs -∗ freshTerm φ x -∗ ⌜x ∉ xs⌝ := by
  unfold isTermSet freshTerm
  iintro ⟨%l, -, -, #Hxs⟩ ⟨Hf, -⟩ %hx
  iapply Hf
  iapply BigSepL.bigSepL_mem hx $$ Hxs

namespace HL

@[rocq_alias cryptis.wp_new_term_set]
theorem wp_newTermSet (φ : Term → IProp GF) :
    {{ True }} hl(&newTermSet #()) {{ v, RET v; isTermSet φ v [] }} := by
  iintro %Φ - HΦ
  wp_rec
  wp_pures
  wp_alloc l with Hl
  imodintro
  iapply HΦ
  unfold isTermSet
  iexists l
  isplitr
  · ipureintro; rfl
  simp only [encode_nil]
  iframe Hl
  iapply BigSepL.bigSepL_nil.mpr
  iempintro

@[rocq_alias cryptis.wp_add_term_set]
theorem wp_addTermSet (φ : Term → IProp GF) (v : Val) (x : Term) (xs : List Term) :
    {{ isTermSet φ v xs ∗ freshTerm φ x }} hl(&addTermSet &(encode x) &v)
      {{ RET hl_val(#()); isTermSet φ v (x :: xs) }} := by
  unfold isTermSet freshTerm
  iintro %Φ ⟨⟨%l, %rfl, Hl, #Hxs⟩, ⟨-, >#Hx⟩⟩ HΦ
  wp_rec
  wp_pures
  wp_load
  wp_apply wp_cons x xs
  wp_store
  iapply HΦ
  iexists l
  isplitr
  · ipureintro; rfl
  iframe Hl
  iapply BigSepL.bigSepL_cons.mpr
  iframe Hx Hxs

@[rocq_alias cryptis.wp_mem_term_set]
theorem wp_memTermSet (φ : Term → IProp GF) (x : Term) (xs : List Term) (v : Val) :
    {{ isTermSet φ v xs }} hl(&memTermSet &(encode x) &v)
      {{ RET hl_val(#(decide (x ∈ xs))); isTermSet φ v xs }} := by
  have heq (y z : Term) : [{ True }] hl(&eqTerm &(encode y) &(encode z))
      [{ RET hl_val(#(decide (y = z))); True }] := by
    iintro %Ψ - HΨ; twp_apply HL.twp_eqTerm; iapply HΨ $$ [//]
  unfold isTermSet
  iintro %Φ ⟨%l, %rfl, Hl, #Hxs⟩ HΦ
  wp_rec
  wp_pures
  wp_load
  iapply twp.to_wp
  twp_apply twp_memList eqTerm x xs heq $$ [//] with -
  iapply HΦ
  iexists l
  isplitr
  · ipureintro; rfl
  iframe Hl Hxs

@[rocq_alias cryptis.wp_new_lock_term_set]
theorem wp_newLockTermSet [TicketLock.TicketLockG GF] (φ : Term → IProp GF) :
    {{ True }} hl(&newLockTermSet #()) {{ v, RET v; isLockTermSet φ v }} := by
  iintro %Φ - HΦ
  wp_rec
  wp_apply wp_newTermSet φ $$ [//] with %vset Hset
  wp_pures
  wp_apply TicketLock.newlock_spec $$ [//] with %lk %γ Hinit
  imod Hinit $$ %(iprop(∃ xs, isTermSet φ vset xs)) %⊤ [Hset] with #Hlk
  · iexists []; iexact Hset
  wp_pures
  iapply HΦ
  unfold isLockTermSet
  iexists vset, lk, γ
  isplitr
  · ipureintro; rfl
  iexact Hlk

@[rocq_alias cryptis.wp_add_fresh_lock_term_set]
theorem wp_addFreshLockTermSet [TicketLock.TicketLockG GF] (φ : Term → IProp GF) (x : Term)
    (v : Val) :
    {{ isLockTermSet φ v ∗ freshTerm φ x }} hl(&addFreshLockTermSet &(encode x) &v)
      {{ RET hl_val(#()); True }} := by
  unfold isLockTermSet
  iintro %Φ ⟨⟨%vset, %vlock, %γ, %rfl, #Hlk⟩, Hx⟩ HΦ
  wp_rec
  wp_pures
  wp_apply TicketLock.acquire_spec γ vlock _ $$ Hlk with ⟨Hlocked, ⟨%xs, Hset⟩⟩
  wp_pures
  wp_apply Assert.wp_assert
  wp_apply wp_memTermSet φ x xs $$ Hset with Hset
  icases isTermSet_fresh $$ Hset Hx with %hx
  simp only [hx, decide_false]
  wp_pures
  imodintro
  isplit
  · ipureintro; rfl
  inext
  wp_pures
  wp_apply wp_addTermSet φ vset x xs $$ [Hset Hx] with Hset
  · iframe Hset Hx
  wp_pures
  wp_apply TicketLock.release_spec γ vlock _ $$ [Hlocked Hset] with -
  · iframe Hlk Hlocked
    iexists x :: xs
    iexact Hset
  iapply HΦ $$ [//]

end HL

end Cryptis
