module

public import Mathlib.Order.Std
public import Mathlib.Data.Finset.Basic
public import Cryptis.Core.PreTerm.Base
public import Cryptis.Lib.Encode
public import Cryptis.Upstream.Iris.Countable

/-! Pre-terms as ordinary data: their encoding as HeapLang values, which tags each constructor
and operator with an integer, the `Countable` instances, the nonces of a pre-term, and the linear
order on pre-terms that sorts the factors of products. -/

@[expose] public section
namespace Cryptis

open Iris Iris.HeapLang

/-! ### Tags of the HeapLang encoding -/

namespace Tag

@[rocq_alias cryptis.TInt_tag] abbrev int : Int := 0
@[rocq_alias cryptis.TNonce_tag] abbrev nonce : Int := 1
@[rocq_alias cryptis.TKey_tag] abbrev key : Int := 0
@[rocq_alias cryptis.THash_tag] abbrev hash : Int := 1
@[rocq_alias cryptis.TPair_tag] abbrev pair : Int := 0
@[rocq_alias cryptis.TSeal_tag] abbrev sealed : Int := 1
@[rocq_alias cryptis.TExp_tag] abbrev exp : Int := 2
@[rocq_alias cryptis.TMul_tag] abbrev mul : Int := 0
@[rocq_alias cryptis.TGMul_tag] abbrev gmul : Int := 1
@[rocq_alias cryptis.TOp0_tag] abbrev op0 : Int := 0
@[rocq_alias cryptis.TOp1_tag] abbrev op1 : Int := 1
@[rocq_alias cryptis.TOp2_tag] abbrev op2 : Int := 2
@[rocq_alias cryptis.TOpN_tag] abbrev opN : Int := 3

end Tag

/-! ### Key types as integers -/

namespace KeyType

/-- The integer that encodes a key type. -/
@[rocq_alias cryptis.int_of_key_type]
def toInt : KeyType → Int
  | aenc => 0
  | adec => 1
  | sign => 2
  | verify => 3
  | senc => 4

/-- The key type encoded by an integer; out-of-range integers encode `senc`. -/
@[rocq_alias cryptis.key_type_of_int]
def ofInt : Int → KeyType
  | 0 => aenc
  | 1 => adec
  | 2 => sign
  | 3 => verify
  | _ => senc

@[simp, rocq_alias cryptis.int_of_key_typeK]
theorem ofInt_toInt (kt : KeyType) : ofInt kt.toInt = kt := by
  cases kt <;> rfl

@[rocq_alias cryptis.int_of_key_type_inj]
theorem toInt_injective : Function.Injective toInt :=
  Function.LeftInverse.injective ofInt_toInt

@[simp]
theorem toInt_inj {kt₁ kt₂ : KeyType} : kt₁.toInt = kt₂.toInt ↔ kt₁ = kt₂ :=
  toInt_injective.eq_iff

end KeyType

/-! ### Decidable equality and inhabitants -/

attribute [rocq_alias cryptis.term_op0_eq_dec] instDecidableEqTermOp0
attribute [rocq_alias cryptis.key_type_eq_dec] instDecidableEqKeyType
attribute [rocq_alias cryptis.term_op1_eq_dec] instDecidableEqTermOp1
attribute [rocq_alias cryptis.term_op2_eq_dec] instDecidableEqTermOp2
attribute [rocq_alias cryptis.term_opN_eq_dec] instDecidableEqTermOpN
attribute [rocq_alias cryptis.nonce_eq_dec] instDecidableEqNonce
attribute [rocq_alias cryptis.nonce_inhabited] instInhabitedNonce
attribute [rocq_alias cryptis.pre_term_eq_dec] PreTerm.instDecidableEq
attribute [rocq_alias cryptis.pre_term_inhabited] instInhabitedPreTerm

#rocq_ignore cryptis.term_op0O "Leibniz OFEs are built on demand with OFE.ofDiscrete"
#rocq_ignore cryptis.key_typeO "Leibniz OFEs are built on demand with OFE.ofDiscrete"
#rocq_ignore cryptis.term_op1O "Leibniz OFEs are built on demand with OFE.ofDiscrete"
#rocq_ignore cryptis.term_op2O "Leibniz OFEs are built on demand with OFE.ofDiscrete"
#rocq_ignore cryptis.term_opNO "Leibniz OFEs are built on demand with OFE.ofDiscrete"

/-! ### The HeapLang encoding

A pre-term is encoded as its constructor tag paired with its arguments. The operator and
arguments of a binary or variadic constructor are nested to the left, so that the operator of `x`
is `fst(fst(snd(x)))`. -/

@[rocq_alias cryptis.repr_term_op0]
instance : Encode TermOp0 where
  encode
    | .int n => hl_val((#Tag.int, #n))
    | .nonce a => hl_val((#Tag.nonce, #a.loc))

@[rocq_alias cryptis.repr_key_type]
instance : Encode KeyType := ⟨fun kt => hl_val(#kt.toInt)⟩

@[rocq_alias cryptis.repr_term_op1]
instance : Encode TermOp1 where
  encode
    | .key kt => hl_val((#Tag.key, &(encode kt)))
    | .hash => hl_val((#Tag.hash, #()))

@[rocq_alias cryptis.repr_term_op2]
instance : Encode TermOp2 where
  encode
    | .pair => hl_val(#Tag.pair)
    | .sealed => hl_val(#Tag.sealed)
    | .exp => hl_val(#Tag.exp)

@[rocq_alias cryptis.repr_term_opN]
instance : Encode TermOpN where
  encode
    | .mul => hl_val(#Tag.mul)
    | .gmul => hl_val(#Tag.gmul)

@[simp] theorem TermOp0.encode_int (n : Int) : encode (int n) = hl_val((#Tag.int, #n)) := rfl

@[simp] theorem TermOp0.encode_nonce (a : Nonce) :
    encode (nonce a) = hl_val((#Tag.nonce, #a.loc)) := rfl

theorem KeyType.encode_eq (kt : KeyType) : encode kt = hl_val(#kt.toInt) := rfl

@[simp] theorem TermOp1.encode_key (kt : KeyType) :
    encode (key kt) = hl_val((#Tag.key, &(encode kt))) := rfl

@[simp] theorem TermOp1.encode_hash : encode hash = hl_val((#Tag.hash, #())) := rfl

@[simp] theorem TermOp2.encode_pair : encode pair = hl_val(#Tag.pair) := rfl

@[simp] theorem TermOp2.encode_sealed : encode sealed = hl_val(#Tag.sealed) := rfl

@[simp] theorem TermOp2.encode_exp : encode exp = hl_val(#Tag.exp) := rfl

@[simp] theorem TermOpN.encode_mul : encode mul = hl_val(#Tag.mul) := rfl

@[simp] theorem TermOpN.encode_gmul : encode gmul = hl_val(#Tag.gmul) := rfl

theorem TermOp2.encode_eq (o : TermOp2) : encode o = hl_val(#(o.ctorIdx : Int)) := by
  cases o <;> rfl

theorem TermOpN.encode_eq (o : TermOpN) : encode o = hl_val(#(o.ctorIdx : Int)) := by
  cases o <;> rfl

mutual

/-- The encoding of pre-terms. -/
@[rocq_alias cryptis.val_of_pre_term]
protected def Encode.preTerm : PreTerm → Val
  | .op0 o => hl_val((#Tag.op0, &(encode o)))
  | .op1 o t => hl_val((#Tag.op1, (&(encode o), &(Encode.preTerm t))))
  | .op2 o t₁ t₂ =>
    hl_val((#Tag.op2, ((&(encode o), &(Encode.preTerm t₁)), &(Encode.preTerm t₂))))
  | .opN o ps ns =>
    hl_val((#Tag.opN, ((&(encode o), &(Encode.preTerms ps)), &(Encode.preTerms ns))))

/-- `Encode.list` at `Encode.preTerm`, spelled out so that `Encode.preTerm` is structurally
recursive. -/
protected def Encode.preTerms : List PreTerm → Val
  | [] => hl_val(none())
  | t :: ts => hl_val(some((&(Encode.preTerm t), &(Encode.preTerms ts))))

end

instance : Encode PreTerm := ⟨Encode.preTerm⟩

theorem Encode.preTerms_eq_encode (ts : List PreTerm) : Encode.preTerms ts = encode ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [Encode.preTerms, ih]; rfl

namespace PreTerm

variable {o₀ : TermOp0} {o₁ : TermOp1} {o₂ : TermOp2} {oₙ : TermOpN} {t t₁ t₂ : PreTerm}
  {ps ns : List PreTerm}

@[simp] theorem encode_op0 : encode (op0 o₀) = hl_val((#Tag.op0, &(encode o₀))) := rfl

@[simp] theorem encode_op1 : encode (op1 o₁ t) = hl_val((#Tag.op1, (&(encode o₁), &(encode t)))) :=
  rfl

@[simp] theorem encode_op2 :
    encode (op2 o₂ t₁ t₂) = hl_val((#Tag.op2, ((&(encode o₂), &(encode t₁)), &(encode t₂)))) :=
  rfl

@[simp] theorem encode_opN :
    encode (opN oₙ ps ns) = hl_val((#Tag.opN, ((&(encode oₙ), &(encode ps)), &(encode ns)))) := by
  simp only [encode, Encode.preTerm, Encode.preTerms_eq_encode]

end PreTerm

@[rocq_alias cryptis.repr_term_op0_inj]
theorem TermOp0.encode_injective : Function.Injective (encode : TermOp0 → Val) := by
  rintro (_ | ⟨_⟩) (_ | ⟨_⟩) h <;> simp_all [encode, Nonce.ext_iff]

theorem KeyType.encode_injective : Function.Injective (encode : KeyType → Val) := fun _ _ h =>
  KeyType.toInt_injective (by simpa [encode] using h)

@[rocq_alias cryptis.repr_term_op1_inj]
theorem TermOp1.encode_injective : Function.Injective (encode : TermOp1 → Val) := by
  rintro (_ | _) (_ | _) h <;> simp_all [encode, ← KeyType.toInt_inj]

@[rocq_alias cryptis.repr_term_op2_inj]
theorem TermOp2.encode_injective : Function.Injective (encode : TermOp2 → Val) := by
  rintro (_ | _ | _) (_ | _ | _) h <;> simp_all +decide

@[rocq_alias cryptis.repr_term_opN_inj]
theorem TermOpN.encode_injective : Function.Injective (encode : TermOpN → Val) := by
  rintro (_ | _) (_ | _) h <;> simp_all +decide

@[simp] theorem TermOp0.encode_inj {o o' : TermOp0} : encode o = encode o' ↔ o = o' :=
  encode_injective.eq_iff

@[simp] theorem KeyType.encode_inj {kt kt' : KeyType} : encode kt = encode kt' ↔ kt = kt' :=
  encode_injective.eq_iff

@[simp] theorem TermOp1.encode_inj {o o' : TermOp1} : encode o = encode o' ↔ o = o' :=
  encode_injective.eq_iff

@[simp] theorem TermOp2.encode_inj {o o' : TermOp2} : encode o = encode o' ↔ o = o' :=
  encode_injective.eq_iff

@[simp] theorem TermOpN.encode_inj {o o' : TermOpN} : encode o = encode o' ↔ o = o' :=
  encode_injective.eq_iff

@[rocq_alias cryptis.val_of_pre_term_inj]
theorem PreTerm.encode_injective : Function.Injective (encode : PreTerm → Val) := by
  intro t₁
  induction t₁ with (rintro (_ | _ | _ | _) h <;> simp +decide at h ⊢)
  | op0 o => exact h
  | op1 o t ih => exact ⟨h.1, ih h.2⟩
  | op2 o t u iht ihu => exact ⟨h.1.1, iht h.1.2, ihu h.2⟩
  | opN o ps ns ihp ihn =>
    exact ⟨h.1.1, eq_of_encode_list_eq ihp h.1.2, eq_of_encode_list_eq ihn h.2⟩

@[simp]
theorem PreTerm.encode_inj {t₁ t₂ : PreTerm} : encode t₁ = encode t₂ ↔ t₁ = t₂ :=
  encode_injective.eq_iff

/-! ### Countability -/

@[rocq_alias cryptis.nonce_countable]
instance : Pos.Countable Nonce where
  encode a := Pos.Countable.encode a.loc
  decode p := (Pos.Countable.decode p).map Nonce.mk
  decode_encode _ := by simp [Pos.Countable.decode_encode]

@[rocq_alias cryptis.int_of_key_type_countable]
instance : Pos.Countable KeyType where
  encode kt := Pos.Countable.encode kt.toInt
  decode p := (Pos.Countable.decode p).map KeyType.ofInt
  decode_encode _ := by simp [Pos.Countable.decode_encode]

/-! A pre-term is countable through the list of its operators in postfix order, which a stack
machine decodes. This encoding is computable. -/

instance : Pos.Countable TermOp0 :=
  .ofLeftInverse (fun | .int n => .inl n | .nonce a => .inr a) (Sum.elim .int .nonce)
    (by rintro (_ | _) <;> rfl)

instance : Pos.Countable TermOp1 :=
  .ofLeftInverse (fun | .key kt => some kt | .hash => none) (Option.elim · .hash .key)
    (by rintro (_ | _) <;> rfl)

instance : Pos.Countable TermOp2 :=
  .ofLeftInverse TermOp2.ctorIdx (fun | 0 => .pair | 1 => .sealed | _ => .exp)
    (by rintro (_ | _ | _) <;> rfl)

instance : Pos.Countable TermOpN :=
  .ofLeftInverse TermOpN.ctorIdx (fun | 0 => .mul | _ => .gmul) (by rintro (_ | _) <;> rfl)

namespace PreTerm

/-- The symbols of the postfix encoding of pre-terms: the operators, with the lengths of the
factor lists of products. -/
abbrev Symbol := TermOp0 ⊕ TermOp1 ⊕ TermOp2 ⊕ (TermOpN × ℕ × ℕ)

mutual

/-- A pre-term in postfix order. -/
def toSymbols : PreTerm → List Symbol
  | op0 o => [.inl o]
  | op1 o t => t.toSymbols ++ [.inr (.inl o)]
  | op2 o t₁ t₂ => t₁.toSymbols ++ t₂.toSymbols ++ [.inr (.inr (.inl o))]
  | opN o ps ns =>
    listToSymbols ps ++ listToSymbols ns ++ [.inr (.inr (.inr (o, ps.length, ns.length)))]

/-- A list of pre-terms in postfix order. -/
def listToSymbols : List PreTerm → List Symbol
  | [] => []
  | t :: ts => t.toSymbols ++ listToSymbols ts

end

/-- One step of the stack machine that decodes `toSymbols`. -/
def decodeStep : List PreTerm → Symbol → Option (List PreTerm)
  | s, .inl o => some (op0 o :: s)
  | t :: s, .inr (.inl o) => some (op1 o t :: s)
  | t₂ :: t₁ :: s, .inr (.inr (.inl o)) => some (op2 o t₁ t₂ :: s)
  | s, .inr (.inr (.inr (o, m, n))) =>
    some (opN o ((s.drop n).take m).reverse (s.take n).reverse :: s.drop (n + m))
  | _, _ => none

/-- The pre-term encoded by a list of symbols, if any. -/
def ofSymbols (l : List Symbol) : Option PreTerm :=
  match l.foldlM decodeStep [] with
  | some [t] => some t
  | _ => none

theorem foldlM_decodeStep_toSymbols (t : PreTerm) (s : List PreTerm) :
    t.toSymbols.foldlM decodeStep s = some (t :: s) := by
  induction t generalizing s with
  | op0 => rfl
  | op1 o t ih => simp [toSymbols, ih, decodeStep]
  | op2 o t₁ t₂ ih₁ ih₂ => simp [toSymbols, ih₁, ih₂, decodeStep]
  | opN o ps ns ihp ihn =>
    have h {ts : List PreTerm} (ih : ∀ t ∈ ts, ∀ s, t.toSymbols.foldlM decodeStep s = some (t :: s))
        (s : List PreTerm) : (listToSymbols ts).foldlM decodeStep s = some (ts.reverse ++ s) := by
      induction ts generalizing s with
      | nil => rfl
      | cons t ts iht => simp_all [listToSymbols]
    simp [toSymbols, h ihp, h ihn, decodeStep, List.drop_append]

theorem ofSymbols_toSymbols (t : PreTerm) : ofSymbols t.toSymbols = some t := by
  simp [ofSymbols, foldlM_decodeStep_toSymbols]

@[rocq_alias cryptis.pre_term_countable]
instance : Pos.Countable PreTerm := .ofLeftInjection toSymbols ofSymbols ofSymbols_toSymbols

end PreTerm

/-! ### Comparisons -/

theorem Nonce.compare_eq (a b : Nonce) : compare a b = compare a.loc.n b.loc.n := rfl

@[simp] theorem TermOp0.compare_int_int (n m : Int) : compare (int n) (int m) = compare n m :=
  Ordering.then_eq

@[simp] theorem TermOp0.compare_nonce_nonce (a b : Nonce) :
    compare (nonce a) (nonce b) = compare a b :=
  Ordering.then_eq

@[simp] theorem TermOp0.compare_int_nonce (n : Int) (a : Nonce) :
    compare (int n) (nonce a) = .lt := rfl

@[simp] theorem TermOp0.compare_nonce_int (a : Nonce) (n : Int) :
    compare (nonce a) (int n) = .gt := rfl

theorem KeyType.compare_eq (kt₁ kt₂ : KeyType) : compare kt₁ kt₂ = compare kt₁.toInt kt₂.toInt := by
  cases kt₁ <;> cases kt₂ <;> rfl

@[simp] theorem TermOp1.compare_key_key (kt₁ kt₂ : KeyType) :
    compare (key kt₁) (key kt₂) = compare kt₁ kt₂ :=
  Ordering.then_eq

@[simp] theorem TermOp1.compare_key_hash (kt : KeyType) : compare (key kt) hash = .lt := rfl

@[simp] theorem TermOp1.compare_hash_key (kt : KeyType) : compare hash (key kt) = .gt := rfl

@[simp] theorem TermOp1.compare_hash_hash : compare hash hash = .eq := rfl

theorem TermOp2.compare_eq (o₁ o₂ : TermOp2) : compare o₁ o₂ = compare o₁.ctorIdx o₂.ctorIdx :=
  rfl

theorem TermOpN.compare_eq (o₁ o₂ : TermOpN) : compare o₁ o₂ = compare o₁.ctorIdx o₂.ctorIdx :=
  rfl

namespace PreTerm

variable {o₀ o₀' : TermOp0} {o₁ o₁' : TermOp1} {o₂ o₂' : TermOp2} {t t' u u' : PreTerm}

theorem compare_op0 : compare (op0 o₀) (op0 o₀') = compare o₀ o₀' := rfl

theorem compare_op1 :
    compare (op1 o₁ t) (op1 o₁' t') = (compare o₁ o₁').then (compare t t') := rfl

theorem compare_op2 :
    compare (op2 o₂ t u) (op2 o₂' t' u') =
      (compare o₂ o₂').then ((compare t t').then (compare u u')) :=
  rfl

theorem compare_of_ctorIdx_ne {t₁ t₂ : PreTerm} (h : t₁.ctorIdx ≠ t₂.ctorIdx) :
    compare t₁ t₂ = compare t₁.ctorIdx t₂.ctorIdx :=
  cmp_of_ctorIdx_ne h

end PreTerm

/-! ### Nonces -/

/-- The nonce of a nullary operator, if any. -/
@[rocq_alias cryptis.nonces_of_term_op0]
def TermOp0.nonces : TermOp0 → Finset Nonce
  | .int _ => ∅
  | .nonce a => {a}

namespace PreTerm

/-- The nonces that occur in a pre-term. -/
@[rocq_alias cryptis.nonces_of_pre_term]
def nonces : PreTerm → Finset Nonce
  | op0 o => o.nonces
  | op1 _ t => t.nonces
  | op2 _ t₁ t₂ => t₁.nonces ∪ t₂.nonces
  | opN _ ps ns => ps.foldr (fun t s => t.nonces ∪ s) ∅ ∪ ns.foldr (fun t s => t.nonces ∪ s) ∅

theorem mem_foldr_nonces {a : Nonce} {ts : List PreTerm} :
    a ∈ ts.foldr (fun t s => t.nonces ∪ s) ∅ ↔ ∃ t ∈ ts, a ∈ t.nonces := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih, or_and_right, exists_or]

@[simp]
theorem mem_nonces_opN {a : Nonce} {o : TermOpN} {ps ns : List PreTerm} :
    a ∈ (opN o ps ns).nonces ↔ (∃ t ∈ ps, a ∈ t.nonces) ∨ ∃ t ∈ ns, a ∈ t.nonces := by
  rw [nonces, Finset.mem_union, mem_foldr_nonces, mem_foldr_nonces]

/-! ### The linear order on pre-terms -/

/-- The order of `Ord PreTerm` as a Mathlib linear order, used to sort the factors of
products. -/
@[rocq_alias cryptis.pt_order, rocq_alias cryptis.pt_order_dec, rocq_alias cryptis.pt_order_refl,
  rocq_alias cryptis.pt_order_trans, rocq_alias cryptis.pt_order_total,
  rocq_alias cryptis.pt_order_antisymm, rocq_alias cryptis.pre_term_lexico,
  rocq_alias cryptis.pre_term_lexico_irrefl, rocq_alias cryptis.pre_term_lexico_trans,
  rocq_alias cryptis.pre_term_lexico_strict, rocq_alias cryptis.pre_term_lexico_trichotomyT]
instance : LinearOrder PreTerm := .ofStd PreTerm

theorem le_iff_compare_isLE {t₁ t₂ : PreTerm} : t₁ ≤ t₂ ↔ (compare t₁ t₂).isLE := .rfl

attribute [rocq_alias cryptis.pt_order_lexico] le_iff_eq_or_lt

#rocq_ignore cryptis.bool_decide_pt_order "PreTerm's order is a single Mathlib LinearOrder"
#rocq_ignore cryptis.seqlexi_lexico "List orders are List.compareLex; see PreTerm.compare_opN"
#rocq_ignore cryptis.pt_order_N "PreTerm.compare_opN"
#rocq_ignore cryptis.int_of_term_op2
  "Only used by op2_le; the HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.int_of_term_opN
  "Only used by opN_le; the HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.kt_le "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.op0_le "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.op1_le "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.op2_le "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.opN_le "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.kt_leE "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.op0_leE "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.op1_leE "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.op2_leE "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.opN_leE "The HeapLang comparison specs can state compare directly"
#rocq_ignore cryptis.pt_orderE "PreTerm.cmp is defined by this equation"
#rocq_ignore cryptis.sorted_StronglySorted "Bridge between mathcomp and stdpp sortedness"
#rocq_ignore cryptis.sort_merge_sort "Bridge between mathcomp and stdpp sorting"

end PreTerm
end Cryptis
