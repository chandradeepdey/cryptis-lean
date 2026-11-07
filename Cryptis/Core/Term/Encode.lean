module

public import Mathlib.Data.Fintype.EquivFin
public import Cryptis.Core.Term.Base

/-! The HeapLang encoding of terms: a term is encoded as the pre-term it stands for, so HeapLang
code inspects terms with the functions on pre-terms of `Cryptis.Primitives.PreTerm`. -/

@[expose] public section
namespace Cryptis

open Iris Iris.HeapLang

/-- Terms are encoded as their pre-terms. -/
@[rocq_alias cryptis.repr_term, rocq_alias cryptis.val_of_term]
instance : Encode Term := ⟨fun t => encode t.unfold⟩

#rocq_ignore cryptis.val_of_term_rec "The instance `Encode Term`, through `Term.unfold`"

/-- Keys are encoded as terms. -/
@[rocq_alias cryptis.repr_aenc_key, rocq_alias cryptis.repr_senc_key,
  rocq_alias cryptis.repr_sign_key]
instance {F : Functionality} : Encode (Key F) := ⟨fun k => encode (k : Term)⟩

namespace Term

variable {t₁ t₂ : Term}

@[simp, rocq_alias cryptis.val_of_pre_term_unfold]
theorem encode_unfold (t : Term) : encode t.unfold = encode t := rfl

@[simp] theorem encode_int (n : Int) : encode (int n) = hl_val((#Tag.op0, (#Tag.int, #n))) := rfl

@[simp] theorem encode_pair (t₁ t₂ : Term) :
    encode (pair t₁ t₂) =
      hl_val((#Tag.op2, ((#Tag.pair, &(encode t₁)), &(encode t₂)))) := rfl

@[simp] theorem encode_nonce (a : Nonce) :
    encode (nonce a) = hl_val((#Tag.op0, (#Tag.nonce, #a.loc))) := rfl

@[simp] theorem encode_key (kt : KeyType) (t : Term) :
    encode (key kt t) = hl_val((#Tag.op1, ((#Tag.key, &(encode kt)), &(encode t)))) := rfl

@[simp] theorem encode_sealed (k t : Term) :
    encode (sealed k t) = hl_val((#Tag.op2, ((#Tag.sealed, &(encode k)), &(encode t)))) := rfl

@[simp] theorem encode_hash (t : Term) :
    encode (hash t) = hl_val((#Tag.op1, ((#Tag.hash, #()), &(encode t)))) := rfl

@[simp] theorem encode_nonFree (pt : PreTerm) (wf : pt.wf) (nf : pt.isNonFree) :
    encode (nonFree pt wf nf) = encode pt := rfl

@[rocq_alias cryptis.val_of_term_inj]
theorem encode_injective : Function.Injective (encode : Term → Val) := fun _ _ h =>
  unfold_injective (PreTerm.encode_injective h)

@[simp]
theorem encode_inj : encode t₁ = encode t₂ ↔ t₁ = t₂ := encode_injective.eq_iff

@[rocq_alias cryptis.infinite_term]
instance : Infinite Term := .of_injective int fun _ _ h => by cases h; rfl

/-- The height of a term, as a pre-term. -/
@[rocq_alias cryptis.term_height]
def height (t : Term) : Nat := t.unfold.height

end Term

@[simp]
theorem Key.encode_eq {F : Functionality} (k : Key F) : encode k = encode (k : Term) := rfl

end Cryptis
