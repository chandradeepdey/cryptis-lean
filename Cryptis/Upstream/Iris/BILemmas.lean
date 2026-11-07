module

public import Iris.BI.BigOp
public import Iris.BI.LaterCredits
public import Iris.BI.Updates
import Iris.ProofMode

/-! Upstream candidate (Iris-Lean): lemmas valid in any BI.

- `Connectives`: disjunctions against separating conjunctions, connectives under a pure guard,
  updates of a disjunction, later credits and laters of persistent propositions, and quantifiers
  over pure conditions.
- `BigSepL`: congruence of big separating conjunctions over lists, `attach`, and two-element
  lists.
- `BigSepS`: big separating conjunctions of persistent propositions over sets, which turn unions
  into conjunctions. -/

@[expose] public section

namespace Iris.BI

open BIBase

section Connectives

variable {PROP : Type _} [BI PROP]
local bi PROP

@[rocq_alias cryptis.or_sep1]
theorem or_sep_merge [BIAffine PROP] (P Q R : PROP) : (P ∨ Q) ∗ (P ∨ R) ⊢ P ∨ Q ∗ R := by
  iintro ⟨HP | HQ, HP' | HR⟩
  · ileft; iexact HP
  · ileft; iexact HP
  · ileft; iexact HP'
  · iright; isplitl [HQ] <;> iassumption

@[rocq_alias cryptis.or_sep2]
theorem or_sep_split [BIAffine PROP] (P Q R : PROP) [Persistent P] :
    P ∨ Q ∗ R ⊢ (P ∨ Q) ∗ (P ∨ R) := by
  iintro (#HP | ⟨HQ, HR⟩)
  · isplitl [] <;> ileft <;> iexact HP
  · isplitl [HQ]
    · iright; iexact HQ
    · iright; iexact HR

@[rocq_alias cryptis.and_proper_L]
theorem pure_and_congr {φ : Prop} {P Q : PROP} (h : φ → (P ⊣⊢ Q)) : ⌜φ⌝ ∧ P ⊣⊢ ⌜φ⌝ ∧ Q :=
  ⟨pure_elim_left fun hφ => and_intro (pure_intro hφ) (h hφ).1,
   pure_elim_left fun hφ => and_intro (pure_intro hφ) (h hφ).2⟩

theorem pure_imp_congr {φ : Prop} {P Q : PROP} (h : φ → (P ⊣⊢ Q)) : (⌜φ⌝ → P) ⊣⊢ (⌜φ⌝ → Q) :=
  ⟨imp_intro <| pure_elim_right fun hφ => (pure_imp_elim hφ).trans (h hφ).1,
   imp_intro <| pure_elim_right fun hφ => (pure_imp_elim hφ).trans (h hφ).2⟩

@[rocq_alias cryptis.if_persistent]
instance persistent_ite {c : Prop} [Decidable c] {P Q : PROP} [Persistent P] [Persistent Q] :
    Persistent (if c then P else Q) := by
  split <;> infer_instance

@[rocq_alias cryptis.fupd_or']
theorem fupd_or_right [BIAffine PROP] [BIFUpdate PROP] (E : CoPset) (P Q R : PROP) :
    (Q ={E}=∗ R) -∗ P ∨ Q ={E}=∗ P ∨ R := by
  iintro HQR (HP | HQ)
  · imodintro; ileft; iexact HP
  · imod HQR $$ HQ with HR
    imodintro; iright; iexact HR

@[rocq_alias cryptis.lc_fupd_elim_later_pers]
theorem lc_fupd_elim_later_intuitionistically [BIFUpdate PROP] [BILaterCredits PROP]
    [BIFUpdLaterCredits PROP] (E : CoPset) (P : PROP) : £ 1 -∗ □ ▷ P ={E}=∗ □ P := by
  iintro Hlc #HP
  iapply lc_fupd_elim_later $$ Hlc
  inext
  imodintro
  iexact HP

/-- The `□` under a later is redundant on a persistent affine proposition. As an equation, it
rewrites only `▷ □ P`, so `simp` keeps an outer `□`, as in `□ (Q ↔ ▷ □ P)`. -/
theorem later_intuitionistically_eq (P : PROP) [Affine P] [Persistent P] :
    iprop(▷ □ P) = iprop(▷ P) :=
  (later_congr intuitionistically_of_intuitionistic).to_eq

theorem exists_prop {φ : Prop} {P : PROP} : (∃ _ : φ, P) ⊣⊢ ⌜φ⌝ ∧ P :=
  ⟨exists_elim fun h => and_intro (pure_intro h) .rfl,
   pure_elim_left fun h => exists_intro (Ψ := fun _ => P) h⟩

theorem forall_pure_eq_imp {α : Type _} (a : α) (Φ : α → PROP) : (∀ x, ⌜x = a⌝ → Φ x) ⊣⊢ Φ a :=
  ⟨(forall_elim a).trans (pure_imp_elim rfl),
   forall_intro fun _ => imp_intro <| pure_elim_right fun h => h ▸ .rfl⟩

theorem forall_pure_or_imp {α : Type _} (p q : α → Prop) (Φ : α → PROP) :
    (∀ x, ⌜p x ∨ q x⌝ → Φ x) ⊣⊢ (∀ x, ⌜p x⌝ → Φ x) ∧ (∀ x, ⌜q x⌝ → Φ x) := by
  constructor
  · iintro H
    isplit <;> iintro %x %h <;> iapply H $$ %x <;> ipureintro <;> simp [h]
  · iintro H %x %h
    rcases h with h | h
    · icases H with ⟨H, -⟩; iapply H $$ %x %h
    · icases H with ⟨-, H⟩; iapply H $$ %x %h

end Connectives

namespace BigSepL

variable {PROP : Type _} [BI PROP] {A : Type _}
local bi PROP

theorem bigSepL_congr_of_mem {Φ Ψ : A → PROP} {l : List A} (h : ∀ x ∈ l, Φ x ⊣⊢ Ψ x) :
    ([∗list] x ∈ l, Φ x) ⊣⊢ [∗list] x ∈ l, Ψ x :=
  ⟨bigSepL_mono fun hx => (h _ (List.mem_of_getElem? hx)).1,
   bigSepL_mono fun hx => (h _ (List.mem_of_getElem? hx)).2⟩

theorem bigSepL_attach {Φ : Nat → A → PROP} {l : List A} :
    ([∗list] k ↦ x ∈ l.attach, Φ k x.1) = [∗list] k ↦ x ∈ l, Φ k x := by
  rw [← bigSepL_map Subtype.val, List.attach_map_subtype_val]

theorem bigSepL_pair {Φ : A → PROP} {a b : A} : ([∗list] x ∈ [a, b], Φ x) ⊣⊢ Φ a ∗ Φ b :=
  bigSepL_cons.trans (sep_congr .rfl bigSepL_singleton)

end BigSepL

namespace BigSepS

open Iris.Std

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {S A : Type _} [LawfulFiniteSet S A]
variable {Φ : A → PROP} [∀ x, Persistent (Φ x)]
local bi PROP

@[rocq_alias cryptis.big_sepS_union_pers]
theorem bigSepS_union_and (X Y : S) :
    ([∗set] x ∈ X ∪ Y, Φ x) ⊣⊢ ([∗set] x ∈ X, Φ x) ∧ ([∗set] x ∈ Y, Φ x) :=
  bigSepS_forall.trans <| by
    simp only [LawfulSet.mem_union]
    exact (forall_pure_or_imp _ _ _).trans (and_congr bigSepS_forall bigSepS_forall).symm

@[rocq_alias cryptis.big_sepS_union_list_pers]
theorem bigSepS_foldr_union (Xs : List S) :
    ([∗set] x ∈ Xs.foldr (· ∪ ·) ∅, Φ x) ⊣⊢ [∗list] X ∈ Xs, [∗set] x ∈ X, Φ x := by
  induction Xs with
  | nil => exact bigSepS_empty
  | cons X Xs ih =>
    exact (bigSepS_union_and X _).trans <| (and_congr .rfl ih).trans persistent_and_sep

end BigSepS

end Iris.BI
