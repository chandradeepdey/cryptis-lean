module

public import Cryptis.Core.Term.Subterms

/-! The functions that protocols use to build and inspect messages.

Protocols tag their messages with the namespace of the protocol step that produced them, so that
a message made for one step cannot be mistaken for one made for another. `Term.ofNamespace N` is
the tag of the namespace `N`, an integer.

- Keys: key pairs, and the key that opens what a key seals: the decryption key of an encryption
  key, the verification key of a signing key, and a symmetric key itself.
- Tags: a tagged message is a pair of the tag and the payload.
- Integers, pairs and lists: a list of terms is a chain of nested pairs.
- Sealing: `enc` tags a payload and seals it with a key; `dec` opens a sealed message with a key
  and removes the tag. Encryption and signatures are both sealing, with different keys. -/

@[expose] public section
namespace Cryptis

namespace Term

/-- The tag of a namespace: the integer that encodes it. -/
@[rocq_alias cryptis.Tag]
def ofNamespace (N : Namespace) : Term := .int (Pos.Countable.encode N).toNat

@[rocq_alias cryptis.Tag_inj]
theorem ofNamespace_injective : Function.Injective ofNamespace := by
  intro N₁ N₂ h
  simp only [ofNamespace, int.injEq] at h
  exact Pos.encode_inj (Pos.Pos_toNat_inj (by exact_mod_cast h))

@[simp]
theorem ofNamespace_inj {N₁ N₂ : Namespace} : ofNamespace N₁ = ofNamespace N₂ ↔ N₁ = N₂ :=
  ofNamespace_injective.eq_iff

end Term

namespace Spec

open Term

variable {c c₁ c₂ k k' k₁ k₂ t t' t₁ t₂ : Term} {ts : List Term}

/-! ### Keys -/

/-- Keys that can seal: encryption, signing and symmetric keys. -/
@[rocq_alias cryptis.Spec.is_seal_key]
def isSealKey : Term → Bool
  | key .aenc _ | key .sign _ | key .senc _ => true
  | _ => false

/-- The key types that can be made public without compromising their pair. -/
@[rocq_alias cryptis.Spec.public_key_type]
def publicKeyType : KeyType → Bool
  | .aenc | .verify => true
  | _ => false

/-- The secret key of a key pair, given its public key. -/
@[rocq_alias cryptis.Spec.skey]
def skey : Term → Term
  | key .aenc t => key .adec t
  | key .verify t => key .sign t
  | t => t

/-- The public key of a key pair, given its secret key. -/
@[rocq_alias cryptis.Spec.pkey]
def pkey : Term → Term
  | key .adec t => key .aenc t
  | key .sign t => key .verify t
  | t => t

@[rocq_alias cryptis.Spec.aenc_pkey_inj, rocq_alias cryptis.Spec.sign_pkey_inj,
  rocq_alias cryptis.Spec.senc_pkey_inj]
theorem _root_.Cryptis.Key.pkey_injective {F : Functionality} :
    Function.Injective fun sk : Key F => pkey sk := by
  rintro ⟨_⟩ ⟨_⟩ h
  cases F <;> simpa [pkey, Key.toTerm] using h

/-- The key type and seed of a key. -/
@[rocq_alias cryptis.Spec.to_key]
def toKey : Term → Option (KeyType × Term)
  | key kt t => some (kt, t)
  | _ => none

/-- The key that opens what a key seals, if it can seal. -/
@[rocq_alias cryptis.Spec.open_key]
def openKey : Term → Option Term
  | key .aenc t => some (key .adec t)
  | key .sign t => some (key .verify t)
  | key .senc t => some (key .senc t)
  | _ => none

@[simp, rocq_alias cryptis.Spec.open_key_aenc]
theorem openKey_pkey_aenc (sk : Key .aenc) : openKey (pkey sk) = some (sk : Term) := rfl

@[simp, rocq_alias cryptis.Spec.open_key_sign]
theorem openKey_sign (sk : Key .sign) : openKey sk = some (pkey sk) := rfl

@[simp, rocq_alias cryptis.Spec.open_key_senc]
theorem openKey_senc (sk : Key .senc) : openKey sk = some (sk : Term) := rfl

@[rocq_alias cryptis.Spec.open_key_aencK]
theorem eq_pkey_of_openKey_eq_aenc {sk : Key .aenc} (h : openKey k = some (sk : Term)) :
    k = pkey sk := by
  rcases k with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp_all [openKey, Key.toTerm, pkey]

@[rocq_alias cryptis.Spec.open_key_signK]
theorem eq_of_openKey_eq_sign {sk : Key .sign} (h : openKey k = some (pkey sk)) : k = sk := by
  rcases k with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp_all [openKey, Key.toTerm, pkey]

@[rocq_alias cryptis.Spec.open_key_sencK]
theorem eq_of_openKey_eq_senc {sk : Key .senc} (h : openKey k = some (sk : Term)) : k = sk := by
  rcases k with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp_all [openKey, Key.toTerm]

@[rocq_alias cryptis.Spec.open_key_tsize]
theorem tsize_eq_of_openKey_eq_some (h : openKey k = some k') : k'.tsize = k.tsize := by
  rcases k with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp_all [openKey] <;> subst h <;> simp

theorem eq_of_openKey_eq (h₁ : openKey k₁ = some k) (h₂ : openKey k₂ = some k) : k₁ = k₂ := by
  rcases k₁ with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp [openKey] at h₁ <;> subst h₁ <;>
    rcases k₂ with _ | _ | _ | ⟨_ | _ | _ | _ | _, _⟩ <;> simp_all [openKey]

/-- The key type of a key. -/
@[rocq_alias cryptis.Spec.is_key]
def isKey : Term → Option KeyType
  | key kt _ => some kt
  | _ => none

@[rocq_alias cryptis.Spec.is_keyP]
theorem isKey_eq_some_iff {kt : KeyType} : isKey t = some kt ↔ ∃ k, t = key kt k := by
  cases t <;> simp [isKey, eq_comm]

theorem isKey_eq_none_iff : isKey t = none ↔ ∀ kt k, t ≠ key kt k := by
  cases t <;> simp [isKey]

#rocq_ignore cryptis.Spec.is_key_spec "Spec.isKey_eq_some_iff and Spec.isKey_eq_none_iff"
#rocq_ignore cryptis.Spec.IsKeySome "Spec.isKey_eq_some_iff and Spec.isKey_eq_none_iff"
#rocq_ignore cryptis.Spec.IsKeyNone "Spec.isKey_eq_some_iff and Spec.isKey_eq_none_iff"

/-- `t` is a key of type `kt`. -/
@[rocq_alias cryptis.Spec.has_key_type]
def hasKeyType (kt : KeyType) (t : Term) : Bool := isKey t = some kt

/-! ### Tags -/

/-- Tag `t` with `c`. -/
@[rocq_alias cryptis.Spec.tag]
def tag (c t : Term) : Term := .pair c t

/-- Remove the tag `c` from `t`, if `t` has it. -/
@[rocq_alias cryptis.Spec.untag]
def untag (c : Term) : Term → Option Term
  | pair c' t => if c = c' then some t else none
  | _ => none

@[simp, rocq_alias cryptis.Spec.is_nonce_tag]
theorem isNonce_tag (c t : Term) : (tag c t).isNonce = false := rfl

@[simp, rocq_alias cryptis.Spec.is_exp_tag]
theorem isExp_tag (c t : Term) : (tag c t).isExp = false := rfl

@[simp, rocq_alias cryptis.Spec.tag_inj]
theorem tag_inj : tag c₁ t₁ = tag c₂ t₂ ↔ c₁ = c₂ ∧ t₁ = t₂ := by simp [tag]

@[simp, rocq_alias cryptis.Spec.tagK]
theorem untag_tag (c t : Term) : untag c (tag c t) = some t := by simp [untag, tag]

@[rocq_alias cryptis.Spec.untag_tag_ne]
theorem untag_tag_of_ne (h : c₁ ≠ c₂) : untag c₁ (tag c₂ t) = none := by simp [untag, tag, h]

@[rocq_alias cryptis.Spec.untagK, rocq_alias cryptis.Spec.untagP]
theorem untag_eq_some_iff : untag c t₁ = some t₂ ↔ t₁ = tag c t₂ := by
  cases t₁ <;> simp [untag, tag, eq_comm]

theorem untag_eq_none_iff : untag c t = none ↔ ∀ t', t ≠ tag c t' := by
  simp [Option.eq_none_iff_forall_ne_some, untag_eq_some_iff]

#rocq_ignore cryptis.Spec.untag_spec "Spec.untag_eq_some_iff and Spec.untag_eq_none_iff"
#rocq_ignore cryptis.Spec.UntagSome "Spec.untag_eq_some_iff and Spec.untag_eq_none_iff"
#rocq_ignore cryptis.Spec.UntagNone "Spec.untag_eq_some_iff and Spec.untag_eq_none_iff"

/-! ### Integers, pairs and lists -/

/-- The integer that a term is, if any. -/
@[rocq_alias cryptis.Spec.to_int]
def toInt : Term → Option Int
  | int n => some n
  | _ => none

@[rocq_alias cryptis.Spec.to_intP]
theorem toInt_eq_some_iff {n : Int} : toInt t = some n ↔ t = int n := by
  cases t <;> simp [toInt, eq_comm]

theorem toInt_eq_none_iff : toInt t = none ↔ ∀ n, t ≠ int n := by
  cases t <;> simp [toInt]

#rocq_ignore cryptis.Spec.to_int_spec "Spec.toInt_eq_some_iff and Spec.toInt_eq_none_iff"
#rocq_ignore cryptis.Spec.AsIntSome "Spec.toInt_eq_some_iff and Spec.toInt_eq_none_iff"
#rocq_ignore cryptis.Spec.AsIntNone "Spec.toInt_eq_some_iff and Spec.toInt_eq_none_iff"

/-- The components of a pair. -/
@[rocq_alias cryptis.Spec.untuple]
def untuple : Term → Option (Term × Term)
  | pair t₁ t₂ => some (t₁, t₂)
  | _ => none

/-- The `n`-th component of a list of terms. -/
@[rocq_alias cryptis.Spec.proj]
def proj : Term → Nat → Option Term
  | pair t _, 0 => some t
  | pair _ t, n + 1 => proj t n
  | _, _ => none

/-- A list of terms as nested pairs, ending with `int 0`. -/
@[rocq_alias cryptis.Spec.of_list]
def ofList (ts : List Term) : Term := ts.foldr pair (int 0)

/-- The list of terms that a term encodes, if any. -/
@[rocq_alias cryptis.Spec.to_list]
def toList : Term → Option (List Term)
  | int n => if n = 0 then some [] else none
  | pair t₁ t₂ => (toList t₂).map (t₁ :: ·)
  | _ => none

@[simp] theorem ofList_nil : ofList [] = int 0 := rfl

@[simp] theorem ofList_cons (t : Term) (ts : List Term) : ofList (t :: ts) = pair t (ofList ts) :=
  rfl

@[rocq_alias cryptis.Spec.of_list_tsize]
theorem tsize_lt_ofList (h : t ∈ ts) : t.tsize < (ofList ts).tsize := by
  induction ts with
  | nil => simp at h
  | cons t' ts ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp; omega
    · simp; have := ih h; omega

@[simp, rocq_alias cryptis.Spec.is_nonce_of_list]
theorem isNonce_ofList (ts : List Term) : (ofList ts).isNonce = false := by cases ts <;> rfl

@[simp, rocq_alias cryptis.Spec.is_exp_of_list]
theorem isExp_ofList (ts : List Term) : (ofList ts).isExp = false := by cases ts <;> rfl

@[simp, rocq_alias cryptis.Spec.of_listK]
theorem toList_ofList (ts : List Term) : toList (ofList ts) = some ts := by
  induction ts <;> simp_all [toList]

@[rocq_alias cryptis.Spec.to_listK, rocq_alias cryptis.Spec.to_listP]
theorem toList_eq_some_iff : toList t = some ts ↔ t = ofList ts := by
  refine ⟨fun h => ?_, fun h => h ▸ toList_ofList ts⟩
  induction t using Term.rec generalizing ts with
  | int n => by_cases hn : n = 0 <;> simp_all [toList]
  | pair t₁ t₂ _ ih =>
    obtain ⟨ts', h', rfl⟩ := Option.map_eq_some_iff.mp h
    simp [ih h']
  | _ => simp [toList] at h

#rocq_ignore cryptis.Spec.to_list_spec "Spec.toList_eq_some_iff"
#rocq_ignore cryptis.Spec.ToListSome "Spec.toList_eq_some_iff"
#rocq_ignore cryptis.Spec.ToListNone "Spec.toList_eq_some_iff"

@[rocq_alias cryptis.Spec.of_list_inj]
theorem ofList_injective : Function.Injective ofList := fun ts₁ ts₂ h =>
  Option.some_injective _ (by rw [← toList_ofList, h, toList_ofList])

@[simp]
theorem ofList_inj {ts₁ ts₂ : List Term} : ofList ts₁ = ofList ts₂ ↔ ts₁ = ts₂ :=
  ofList_injective.eq_iff

/-- The term `int 0`. -/
@[rocq_alias cryptis.Spec.zero]
def zero : Term := int 0

/-! ### Sealing -/

/-- The payload of `t` if it is sealed with a key that `k` opens. -/
@[rocq_alias cryptis.Spec.open]
def opened (k : Term) : Term → Option Term
  | sealed kt t => if openKey kt = some k then some t else none
  | _ => none

@[rocq_alias cryptis.Spec.openP]
theorem opened_eq_some_iff :
    opened k t = some t' ↔ ∃ kt, openKey kt = some k ∧ t = sealed kt t' := by
  cases t <;> simp [opened, eq_comm]

#rocq_ignore cryptis.Spec.open_spec "Spec.opened_eq_some_iff"
#rocq_ignore cryptis.Spec.OpenSome "Spec.opened_eq_some_iff"
#rocq_ignore cryptis.Spec.OpenNone "Spec.opened_eq_some_iff"

/-- Seal `t` with `k`, tagged with `c`. -/
@[rocq_alias cryptis.Spec.enc]
def enc (k c t : Term) : Term := sealed k (tag c t)

/-- Open `t` with `k` and remove the tag `c`. -/
@[rocq_alias cryptis.Spec.dec]
def dec (k c t : Term) : Option Term := (opened k t).bind (untag c)

@[rocq_alias cryptis.Spec.decP]
theorem dec_eq_some_iff : dec k c t = some t' ↔ ∃ kt, openKey kt = some k ∧ t = enc kt c t' := by
  simp [dec, Option.bind_eq_some_iff, opened_eq_some_iff, untag_eq_some_iff, enc]

#rocq_ignore cryptis.Spec.dec_spec "Spec.dec_eq_some_iff"
#rocq_ignore cryptis.Spec.DecSome "Spec.dec_eq_some_iff"
#rocq_ignore cryptis.Spec.DecNone "Spec.dec_eq_some_iff"

@[rocq_alias cryptis.Spec.decK]
theorem eq_enc_of_dec_eq_some (hk : openKey k₁ = some k₂) (h : dec k₂ c t = some t') :
    t = enc k₁ c t' := by
  obtain ⟨kt, hkt, rfl⟩ := dec_eq_some_iff.mp h
  rw [eq_of_openKey_eq hkt hk]

end Spec

@[rocq_alias cryptis.subterm_tag]
theorem Term.Subterm.tag {c t₁ t₂ : Term} (h : t₁.Subterm t₂) : t₁.Subterm (Spec.tag c t₂) :=
  .pairRight h

end Cryptis
