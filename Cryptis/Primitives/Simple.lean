module

public import Cryptis.Primitives.Notations
public import Cryptis.Primitives.Comp

/-! HeapLang programs that build and inspect terms, with specs saying that each one computes the
corresponding function of `Spec` on term encodings: integers, pairs, lists, tags, keys, sealing,
hashing, and the encryption and signature schemes built from them. Encryption and signatures
are the same program, `HL.enc`, on different keys, and so are decryption and verification,
`HL.dec`. -/

@[expose] public section

namespace Cryptis

open Iris Iris.HeapLang BI ProgramLogic

namespace HL

/-! ## Programs -/

/-- The integer term `n`. -/
@[rocq_alias cryptis.tint]
def tint : Val := hl_val% λ n, (#Tag.op0, (#Tag.int, n))

/-- `Spec.toInt`. -/
@[rocq_alias cryptis.to_int]
def toInt : Val := hl_val%
  λ t, if (fst(t) = #Tag.op0) && (fst(snd(t)) = #Tag.int) then some(snd(snd(t))) else none()

/-- The pair of two terms. -/
@[rocq_alias cryptis.tuple]
def tuple : Val := hl_val% λ t1 t2, (#Tag.op2, ((#Tag.pair, t1), t2))

/-- `Spec.untuple`. -/
@[rocq_alias cryptis.untuple]
def untuple : Val := hl_val%
  λ t,
    if fst(t) = #Tag.op2 then
      let t := snd(t);
      if fst(fst(t)) = #Tag.pair then some((snd(fst(t)), snd(t))) else none()
    else none()

/-- `Spec.toList`. -/
@[rocq_alias cryptis.list_of_term]
def listOfTerm : Val := hl_val%
  rec loop t :=
    if &eqTerm t &(encode (Term.int 0)) then some([])
    else
      bind: t := &untuple t in
      bind: l := loop (snd(t)) in
      some(fst(t) :: l)

/-- `Spec.ofList`. -/
@[rocq_alias cryptis.term_of_list]
def termOfList : Val := hl_val%
  rec loop l :=
    match l with
    | none() => &(encode (Term.int 0))
    | some(p) => &tuple (fst(p)) (loop (snd(p)))

/-- `Spec.tag`. -/
@[rocq_alias cryptis.tag]
def tag : Val := hl_val% λ c t, &tuple c t

/-- `Spec.untag`. -/
@[rocq_alias cryptis.untag]
def untag : Val := hl_val%
  λ c t,
    bind: t := &untuple t in
    let c' := fst(t);
    if &eqTerm c c' then some(snd(t)) else none()

/-- The key of type `kt` with a given seed. -/
@[rocq_alias cryptis.key]
def key (kt : KeyType) : Val := hl_val% λ k, (#Tag.op1, ((#Tag.key, &(encode kt)), k))

/-- `Spec.toKey`. -/
@[rocq_alias cryptis.to_key]
def toKey : Val := hl_val%
  λ t,
    if fst(t) = #Tag.op1 then
      let o := fst(snd(t));
      let t := snd(snd(t));
      if fst(o) = #Tag.key then some((snd(o), t)) else none()
    else none()

/-- `Spec.isKey`. -/
@[rocq_alias cryptis.is_key]
def isKey : Val := hl_val% λ t, bind: r := &toKey t in some(fst(r))

/-- The term `k` seals `t`. -/
@[rocq_alias cryptis.seal]
def sealed : Val := hl_val% λ k t, (#Tag.op2, ((#Tag.sealed, k), t))

/-- The hash of a term. -/
@[rocq_alias cryptis.hash]
def hash : Val := hl_val% λ t, (#Tag.op1, ((#Tag.hash, #()), t))

/-- The secret key for public-key encryption with a given seed. -/
@[rocq_alias cryptis.derive_aenc_key]
def deriveAEncKey : Val := hl_val% λ seed, &(key .adec) seed

/-- The key for symmetric encryption with a given seed. -/
@[rocq_alias cryptis.derive_senc_key]
def deriveSEncKey : Val := hl_val% λ seed, &(key .senc) seed

/-- The signing key with a given seed. -/
@[rocq_alias cryptis.derive_sign_key]
def deriveSignKey : Val := hl_val% λ seed, &(key .sign) seed

/-- `Spec.openKey`. -/
@[rocq_alias cryptis.open_key]
def openKey : Val := hl_val%
  λ k,
    bind: r := &toKey k in
    let kt := fst(r);
    let seed := snd(r);
    if kt = #(KeyType.aenc.toInt) then some(&(key .adec) seed)
    else if kt = #(KeyType.sign.toInt) then some(&(key .verify) seed)
    else if kt = #(KeyType.senc.toInt) then some(&(key .senc) seed)
    else none()

/-- `Spec.opened`. -/
@[rocq_alias cryptis.open]
def opened : Val := hl_val%
  λ k t,
    if fst(t) = #Tag.op2 then
      let t := snd(t);
      if fst(fst(t)) = #Tag.sealed then
        let kt := snd(fst(t));
        let t := snd(t);
        match &openKey kt with
        | some(k') => if &eqTerm k' k then some(t) else none()
        | none() => none()
      else none()
    else none()

/-- `Spec.enc`. -/
@[rocq_alias cryptis.enc]
def enc : Val := hl_val% λ k c t, &sealed k (&tag c t)

/-- `Spec.dec`. -/
@[rocq_alias cryptis.dec]
def dec : Val := hl_val% λ k c t, bind: t := &opened k t in &untag c t

/-- `Spec.pkey`. -/
@[rocq_alias cryptis.pkey]
def pkey : Val := hl_val%
  λ k,
    match &toKey k with
    | none() => k
    | some(r) =>
      let kt := fst(r);
      let seed := snd(r);
      if kt = #(KeyType.adec.toInt) then &(key .aenc) seed
      else if kt = #(KeyType.sign.toInt) then &(key .verify) seed
      else k

/-- Public-key encryption. -/
@[rocq_alias cryptis.aenc]
def aenc : Val := hl_val% λ pk c t, &enc pk c t

/-- Public-key decryption. -/
@[rocq_alias cryptis.adec]
def adec : Val := hl_val% λ sk c t, &dec sk c t

/-- Symmetric encryption. -/
@[rocq_alias cryptis.senc]
def senc : Val := hl_val% λ k c t, &enc k c t

/-- Symmetric decryption. -/
@[rocq_alias cryptis.sdec]
def sdec : Val := hl_val% λ k c t, &dec k c t

/-- Signing. -/
@[rocq_alias cryptis.sign]
def sign : Val := hl_val% λ sk c t, &enc sk c t

/-- Signature verification. -/
@[rocq_alias cryptis.verify]
def verify : Val := hl_val% λ pk c t, &dec pk c t

/-- `Spec.hasKeyType`. -/
@[rocq_alias cryptis.has_key_type]
def hasKeyType : Val := hl_val%
  λ kt t,
    match &isKey t with
    | some(kt') => kt = kt'
    | none() => #false

/-- The term is a public encryption key. -/
@[rocq_alias cryptis.is_aenc_key]
def isAEncKey : Val := hl_val% λ t, &hasKeyType #(KeyType.aenc.toInt) t

/-- The term is a decryption key. -/
@[rocq_alias cryptis.is_adec_key]
def isADecKey : Val := hl_val% λ t, &hasKeyType #(KeyType.adec.toInt) t

/-- The term is a signing key. -/
@[rocq_alias cryptis.is_sign_key]
def isSignKey : Val := hl_val% λ t, &hasKeyType #(KeyType.sign.toInt) t

/-- The term is a verification key. -/
@[rocq_alias cryptis.is_verify_key]
def isVerifyKey : Val := hl_val% λ t, &hasKeyType #(KeyType.verify.toInt) t

/-- The term is a symmetric key. -/
@[rocq_alias cryptis.is_senc_key]
def isSEncKey : Val := hl_val% λ t, &hasKeyType #(KeyType.senc.toInt) t

end HL

/-! ## Specifications -/

namespace WpEncode

attribute [scoped wp_expr_simp] KeyType.encode_eq KeyType.toInt.eq_1 KeyType.toInt.eq_2
  KeyType.toInt.eq_3 KeyType.toInt.eq_4 KeyType.toInt.eq_5

end WpEncode

open scoped WpLit WpEncode

set_option hygiene false in
/-- Split a term into its constructors, and a non-free term into an exponential or a
product. -/
local macro "term_cases " t:term : tactic =>
  `(tactic| (rcases $t:term with _ | ⟨_, _⟩ | _ | ⟨_, _⟩ | ⟨_, _⟩ | _ | ⟨_, _, h⟩ <;>
    try obtain ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ := PreTerm.isNonFree_iff.mp h))

/-- Unfold the encodings of terms, options, pairs and lists, evaluate the resulting tests, and
unfold the given definitions. -/
local macro "simp_encode" " [" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [Term.encode_int, Term.encode_pair, Term.encode_nonce, Term.encode_key,
    Term.encode_sealed, Term.encode_hash, Term.encode_nonFree, PreTerm.encode_op2,
    PreTerm.encode_opN, TermOp2.encode_exp, encode_some, encode_none, encode_prod, encode_int,
    encode_nil, encode_cons, KeyType.encode_eq, KeyType.toInt.eq_1, KeyType.toInt.eq_2,
    KeyType.toInt.eq_3, KeyType.toInt.eq_4, KeyType.toInt.eq_5, Option.some.injEq,
    eq_self_iff_true, _root_.decide_true, _root_.decide_false, ite_true, ite_false, reduceCtorEq,
    $ids,*])

set_option hygiene false in
/-- Close a goal `Ψ v` with the hypothesis `H : Ψ v'`, after `simp_encode`. -/
local macro "ifinish" " [" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ((try simp_encode [$ids,*]); iexact H))

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset}
local bi (IProp GF)

namespace HL

@[rocq_alias cryptis.twp_tint]
theorem twp_tint (n : Int) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.int n)) ⊢ WP hl(&tint #n) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; ifinish []

@[rocq_alias cryptis.wp_tint]
theorem wp_tint (n : Int) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.int n)) ⊢ WP hl(&tint #n) @ s; E {{ Ψ }} :=
  (twp_tint n Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_to_int]
theorem twp_toInt (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.toInt t)) ⊢ WP hl(&toInt &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  term_cases t <;> simp_encode [] <;> twp_rec <;> twp_pures <;> ifinish [Spec.toInt]

@[rocq_alias cryptis.wp_to_int]
theorem wp_toInt (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.toInt t)) ⊢ WP hl(&toInt &(encode t)) @ s; E {{ Ψ }} :=
  (twp_toInt t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tuple]
theorem twp_tuple (t₁ t₂ : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.pair t₁ t₂)) ⊢ WP hl(&tuple &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; ifinish []

@[rocq_alias cryptis.wp_tuple]
theorem wp_tuple (t₁ t₂ : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.pair t₁ t₂)) ⊢ WP hl(&tuple &(encode t₁) &(encode t₂)) @ s; E {{ Ψ }} :=
  (twp_tuple t₁ t₂ Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_untuple]
theorem twp_untuple (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.untuple t)) ⊢ WP hl(&untuple &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  term_cases t <;> simp_encode [] <;> twp_rec <;> twp_pures <;> ifinish [Spec.untuple]

@[rocq_alias cryptis.wp_untuple]
theorem wp_untuple (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.untuple t)) ⊢ WP hl(&untuple &(encode t)) @ s; E {{ Ψ }} :=
  (twp_untuple t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_term_of_list]
theorem twp_termOfList (ts : List Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.ofList ts)) ⊢ WP hl(&termOfList &(encode ts)) @ s; E [{ Ψ }] := by
  induction ts generalizing Ψ with
  | nil => iintro H; twp_rec; simp_encode []; twp_pures; ifinish [Spec.ofList_nil]
  | cons t ts ih =>
    iintro H
    twp_rec
    simp_encode []
    twp_pures
    twp_apply ih
    twp_smart_apply twp_tuple
    ifinish [Spec.ofList_cons]

@[rocq_alias cryptis.wp_term_of_list]
theorem wp_termOfList (ts : List Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.ofList ts)) ⊢ WP hl(&termOfList &(encode ts)) @ s; E {{ Ψ }} :=
  (twp_termOfList ts Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_list_of_term]
theorem twp_listOfTerm (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.toList t)) ⊢ WP hl(&listOfTerm &(encode t)) @ s; E [{ Ψ }] := by
  induction t using Term.tsize_induction generalizing Ψ with | _ t ih => ?_
  iintro H
  twp_rec
  twp_apply twp_eqTerm
  by_cases h0 : t = .int 0
  · subst h0; simp_encode []; twp_pures; ifinish [Spec.toList]
  simp only [h0, decide_false]
  twp_pures
  twp_apply twp_untuple
  cases t
  case pair t₁ t₂ =>
    simp_encode [Spec.untuple]
    twp_pures
    twp_apply ih t₂ (by simp; omega)
    cases h : Spec.toList t₂ with
    | none => simp_encode []; twp_pures; ifinish [Spec.toList, h, Option.map_none]
    | some ts =>
      simp_encode []
      twp_pures
      twp_apply twp_cons
      twp_pures
      ifinish [Spec.toList, h, Option.map_some]
  case int n =>
    have hn : n ≠ 0 := by rintro rfl; exact h0 rfl
    simp_encode [Spec.untuple]
    twp_pures
    ifinish [Spec.toList, hn]
  all_goals simp_encode [Spec.untuple]; twp_pures; ifinish [Spec.toList]

@[rocq_alias cryptis.wp_list_of_term]
theorem wp_listOfTerm (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.toList t)) ⊢ WP hl(&listOfTerm &(encode t)) @ s; E {{ Ψ }} :=
  (twp_listOfTerm t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_list]
theorem twp_listToExp {α : Type _} [Encode α] (xs : List α) (Ψ : Val → IProp GF) :
    Ψ (encode xs) ⊢ WP (listToExp xs) @ s; E [{ Ψ }] := by
  induction xs generalizing Ψ with
  | nil => exact twp_nil Ψ
  | cons x xs ih =>
    rw [show listToExp (x :: xs) = hl(v(&(encode x)) :: &(listToExp xs)) from rfl]
    iintro H
    twp_apply ih
    twp_apply twp_cons
    iexact H

@[rocq_alias cryptis.wp_list]
theorem wp_listToExp {α : Type _} [Encode α] (xs : List α) (Ψ : Val → IProp GF) :
    Ψ (encode xs) ⊢ WP (listToExp xs) @ s; E {{ Ψ }} :=
  (twp_listToExp xs Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tag]
theorem twp_tag (c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.tag c t)) ⊢ WP hl(&tag &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; twp_apply twp_tuple; ifinish [Spec.tag]

@[rocq_alias cryptis.wp_tag]
theorem wp_tag (c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.tag c t)) ⊢ WP hl(&tag &(encode c) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_tag c t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_untag]
theorem twp_untag (c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.untag c t)) ⊢ WP hl(&untag &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  twp_apply twp_untuple
  cases t
  case pair c' t =>
    simp_encode [Spec.untuple]
    twp_pures
    twp_apply twp_eqTerm
    by_cases h : c = c' <;> simp_encode [h] <;> twp_pures <;> ifinish [Spec.untag, h]
  all_goals simp_encode [Spec.untuple]; twp_pures; ifinish [Spec.untag]

@[rocq_alias cryptis.wp_untag]
theorem wp_untag (c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.untag c t)) ⊢ WP hl(&untag &(encode c) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_untag c t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_key]
theorem twp_key (kt : KeyType) (k : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.key kt k)) ⊢ WP hl(&(key kt) &(encode k)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; ifinish []

@[rocq_alias cryptis.wp_key]
theorem wp_key (kt : KeyType) (k : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.key kt k)) ⊢ WP hl(&(key kt) &(encode k)) @ s; E {{ Ψ }} :=
  (twp_key kt k Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_seal]
theorem twp_sealed (k t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.sealed k t)) ⊢ WP hl(&sealed &(encode k) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; ifinish []

@[rocq_alias cryptis.wp_seal]
theorem wp_sealed (k t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.sealed k t)) ⊢ WP hl(&sealed &(encode k) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_sealed k t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_hash]
theorem twp_hash (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.hash t)) ⊢ WP hl(&hash &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; ifinish []

@[rocq_alias cryptis.wp_hash]
theorem wp_hash (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Term.hash t)) ⊢ WP hl(&hash &(encode t)) @ s; E {{ Ψ }} :=
  (twp_hash t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.wp_derive_aenc_key]
theorem wp_deriveAEncKey (t : Term) (Ψ : Val → IProp GF) :
    ▷ Ψ (encode (⟨t⟩ : Key .aenc)) ⊢ WP hl(&deriveAEncKey &(encode t)) @ s; E {{ Ψ }} := by
  change ▷ Ψ (encode (Term.key .adec t)) ⊢ _
  iintro H; wp_rec; iapply wp_key .adec t $$ H

@[rocq_alias cryptis.wp_derive_senc_key]
theorem wp_deriveSEncKey (t : Term) (Ψ : Val → IProp GF) :
    ▷ Ψ (encode (⟨t⟩ : Key .senc)) ⊢ WP hl(&deriveSEncKey &(encode t)) @ s; E {{ Ψ }} := by
  change ▷ Ψ (encode (Term.key .senc t)) ⊢ _
  iintro H; wp_rec; iapply wp_key .senc t $$ H

@[rocq_alias cryptis.wp_derive_sign_key]
theorem wp_deriveSignKey (t : Term) (Ψ : Val → IProp GF) :
    ▷ Ψ (encode (⟨t⟩ : Key .sign)) ⊢ WP hl(&deriveSignKey &(encode t)) @ s; E {{ Ψ }} := by
  change ▷ Ψ (encode (Term.key .sign t)) ⊢ _
  iintro H; wp_rec; iapply wp_key .sign t $$ H

@[rocq_alias cryptis.twp_to_key]
theorem twp_toKey (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.toKey t)) ⊢ WP hl(&toKey &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  term_cases t <;> simp_encode [] <;> twp_rec <;> twp_pures <;> ifinish [Spec.toKey]

@[rocq_alias cryptis.twp_open_key]
theorem twp_openKey (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.openKey t)) ⊢ WP hl(&openKey &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_toKey
  rcases t with _ | _ | _ | ⟨kt, k⟩ | _ | _ | _
  case key =>
    cases kt <;> simp_encode [Spec.toKey] <;> twp_pures <;>
      (try (twp_apply twp_key; twp_pures)) <;> ifinish [Spec.openKey]
  all_goals simp_encode [Spec.toKey]; twp_pures; ifinish [Spec.openKey]

@[rocq_alias cryptis.twp_open]
theorem twp_opened (k t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.opened k t)) ⊢ WP hl(&opened &(encode k) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  term_cases t
  case sealed kt t =>
    simp_encode []
    twp_rec
    twp_pures
    twp_apply twp_openKey
    cases h : Spec.openKey kt with
    | none => simp_encode []; twp_pures; ifinish [Spec.opened, h]
    | some k' =>
      simp_encode []
      twp_pures
      twp_apply twp_eqTerm
      by_cases hk : k' = k <;> simp_encode [hk] <;> twp_pures <;> ifinish [Spec.opened, h, hk]
  all_goals simp_encode []; twp_rec; twp_pures; ifinish [Spec.opened]

@[rocq_alias cryptis.wp_open]
theorem wp_opened (k t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.opened k t)) ⊢ WP hl(&opened &(encode k) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_opened k t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_enc]
theorem twp_enc (k c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.enc k c t)) ⊢
      WP hl(&enc &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; twp_apply twp_tag; twp_apply twp_sealed; ifinish [Spec.enc]

@[rocq_alias cryptis.wp_enc]
theorem wp_enc (k c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.enc k c t)) ⊢
      WP hl(&enc &(encode k) &(encode c) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_enc k c t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_dec]
theorem twp_dec (k c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.dec k c t)) ⊢
      WP hl(&dec &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  twp_apply twp_opened
  cases h : Spec.opened k t with
  | none => simp_encode []; twp_pures; ifinish [Spec.dec, h, Option.bind_none]
  | some t' =>
    simp_encode []
    twp_pures
    twp_apply twp_untag
    ifinish [Spec.dec, h, Option.bind_some]

@[rocq_alias cryptis.wp_dec]
theorem wp_dec (k c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.dec k c t)) ⊢
      WP hl(&dec &(encode k) &(encode c) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_dec k c t Ψ).trans (wand_entails twp.to_wp)

/-! ### Encryption and signatures -/

/-- The postcondition of decrypting `t` with `k`, when `k` opens what `k'` seals. -/
abbrev decPost (k' k c t : Term) (Ψ : Val → IProp GF) : IProp GF :=
  iprop((∀ t', ⌜t = .sealed k' (Spec.tag c t')⌝ -∗ ⌜Spec.dec k c t = some t'⌝ -∗
      Ψ hl_val(some(&(encode t')))) ∧
    (⌜Spec.dec k c t = none⌝ → Ψ hl_val(none())))

theorem twp_dec_of_openKey {k' k : Term} (hk : Spec.openKey k' = some k) (c t : Term)
    (Ψ : Val → IProp GF) :
    decPost k' k c t Ψ ⊢ WP hl(&dec &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_apply twp_dec
  cases h : Spec.dec k c t with
  | none => icases H with ⟨-, H⟩; iapply H $$ %h
  | some t' =>
    icases H with ⟨H, -⟩
    iapply H $$ %t' %(Spec.eq_enc_of_dec_eq_some hk h) %h

@[rocq_alias cryptis.twp_aenc']
theorem twp_aenc' (pk c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.enc pk c t)) ⊢
      WP hl(&aenc &(encode pk) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; twp_apply twp_enc; iexact H

@[rocq_alias cryptis.wp_aenc']
theorem wp_aenc' (pk c t : Term) (Ψ : Val → IProp GF) :
    ▷ Ψ (encode (Spec.enc pk c t)) ⊢
      WP hl(&aenc &(encode pk) &(encode c) &(encode t)) @ s; E {{ Ψ }} := by
  iintro H; wp_rec; wp_pures; wp_apply wp_enc; iexact H

@[rocq_alias cryptis.twp_adec']
theorem twp_adec' (sk : Key .aenc) (c t : Term) (Ψ : Val → IProp GF) :
    decPost (Spec.pkey sk) sk c t Ψ ⊢
      WP hl(&adec &(encode sk) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; iapply twp_dec_of_openKey (Spec.openKey_pkey_aenc sk) $$ H

@[rocq_alias cryptis.wp_adec']
theorem wp_adec' (sk : Key .aenc) (c t : Term) (Ψ : Val → IProp GF) :
    ▷ decPost (Spec.pkey sk) sk c t Ψ ⊢
      WP hl(&adec &(encode sk) &(encode c) &(encode t)) @ s; E {{ Ψ }} := by
  iintro H; wp_rec; wp_pures
  iapply twp.to_wp
  iapply twp_dec_of_openKey (Spec.openKey_pkey_aenc sk) $$ H

@[rocq_alias cryptis.twp_senc']
theorem twp_senc' (k c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.enc k c t)) ⊢
      WP hl(&senc &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; twp_apply twp_enc; iexact H

@[rocq_alias cryptis.wp_senc']
theorem wp_senc' (k c t : Term) (Ψ : Val → IProp GF) :
    ▷ Ψ (encode (Spec.enc k c t)) ⊢
      WP hl(&senc &(encode k) &(encode c) &(encode t)) @ s; E {{ Ψ }} := by
  iintro H; wp_rec; wp_pures; wp_apply wp_enc; iexact H

@[rocq_alias cryptis.twp_sdec']
theorem twp_sdec' (k : Key .senc) (c t : Term) (Ψ : Val → IProp GF) :
    decPost k k c t Ψ ⊢
      WP hl(&sdec &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; iapply twp_dec_of_openKey (Spec.openKey_senc k) $$ H

@[rocq_alias cryptis.wp_sdec']
theorem wp_sdec' (k : Key .senc) (c t : Term) (Ψ : Val → IProp GF) :
    ▷ decPost k k c t Ψ ⊢
      WP hl(&sdec &(encode k) &(encode c) &(encode t)) @ s; E {{ Ψ }} := by
  iintro H; wp_rec; wp_pures
  iapply twp.to_wp
  iapply twp_dec_of_openKey (Spec.openKey_senc k) $$ H

@[rocq_alias cryptis.twp_sign']
theorem twp_sign' (k c t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.enc k c t)) ⊢
      WP hl(&sign &(encode k) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; twp_apply twp_enc; iexact H

@[rocq_alias cryptis.wp_sign']
theorem wp_sign' (k c t : Term) (Ψ : Val → IProp GF) :
    ▷ Ψ (encode (Spec.enc k c t)) ⊢
      WP hl(&sign &(encode k) &(encode c) &(encode t)) @ s; E {{ Ψ }} := by
  iintro H; wp_rec; wp_pures; wp_apply wp_enc; iexact H

@[rocq_alias cryptis.twp_verify']
theorem twp_verify' (sk : Key .sign) (c t : Term) (Ψ : Val → IProp GF) :
    decPost sk (Spec.pkey sk) c t Ψ ⊢
      WP hl(&verify &(encode (Spec.pkey sk)) &(encode c) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H; twp_rec; twp_pures; iapply twp_dec_of_openKey (Spec.openKey_sign sk) $$ H

@[rocq_alias cryptis.wp_verify']
theorem wp_verify' (sk : Key .sign) (c t : Term) (Ψ : Val → IProp GF) :
    ▷ decPost sk (Spec.pkey sk) c t Ψ ⊢
      WP hl(&verify &(encode (Spec.pkey sk)) &(encode c) &(encode t)) @ s; E {{ Ψ }} := by
  iintro H; wp_rec; wp_pures
  iapply twp.to_wp
  iapply twp_dec_of_openKey (Spec.openKey_sign sk) $$ H

@[rocq_alias cryptis.twp_pkey]
theorem twp_pkey (k : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.pkey k)) ⊢ WP hl(&pkey &(encode k)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_toKey
  rcases k with _ | _ | _ | ⟨kt, k⟩ | _ | _ | _
  case key =>
    cases kt <;> simp_encode [Spec.toKey] <;> twp_pures <;> (try twp_apply twp_key) <;>
      ifinish [Spec.pkey]
  all_goals simp_encode [Spec.toKey]; twp_pures; ifinish [Spec.pkey]

@[rocq_alias cryptis.wp_pkey]
theorem wp_pkey (k : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.pkey k)) ⊢ WP hl(&pkey &(encode k)) @ s; E {{ Ψ }} :=
  (twp_pkey k Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_is_key]
theorem twp_isKey (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.isKey t)) ⊢ WP hl(&isKey &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_toKey
  cases t <;> simp_encode [Spec.toKey] <;> twp_pures <;> ifinish [Spec.isKey]

@[rocq_alias cryptis.wp_is_key]
theorem wp_isKey (t : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (Spec.isKey t)) ⊢ WP hl(&isKey &(encode t)) @ s; E {{ Ψ }} :=
  (twp_isKey t Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_has_key_type]
theorem twp_hasKeyType (kt : KeyType) (t : Term) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(Spec.hasKeyType kt t)) ⊢
      WP hl(&hasKeyType &(encode kt) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  twp_apply twp_isKey
  unfold Spec.hasKeyType
  cases h : Spec.isKey t with
  | none => simp_encode []; twp_pures; ifinish []
  | some kt' => cases kt <;> cases kt' <;> simp_encode [] <;> twp_pures <;> ifinish []

@[rocq_alias cryptis.wp_has_key_type]
theorem wp_hasKeyType (kt : KeyType) (t : Term) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(Spec.hasKeyType kt t)) ⊢
      WP hl(&hasKeyType &(encode kt) &(encode t)) @ s; E {{ Ψ }} :=
  (twp_hasKeyType kt t Ψ).trans (wand_entails twp.to_wp)

end HL

end Cryptis
