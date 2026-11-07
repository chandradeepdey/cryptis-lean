module

public import Cryptis.Primitives.WithCryptis

/-! The Dolev–Yao attacker: threads that read public terms from the network, combine them with
every operation available to protocol code, and send the results back. These include the
operations of both groups, which a real attacker on Diffie–Hellman values also has.

`HL.initNetwork` creates a channel and starts the attacker on it; `HL.wp_initNetwork` shows that
every term on the channel stays public. -/

@[expose] public section

namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode ProgramLogic Term.ProdGroup

namespace HL

/-! ## Programs -/

/-- Send an arbitrary integer. -/
@[rocq_alias cryptis.add_int]
def addInt : Val := hl_val% λ c, let n := &nondetInt #(); &send c (&tint n)

/-- Pair two received terms. -/
@[rocq_alias cryptis.add_pair]
def addPair : Val := hl_val%
  λ c, let t1 := &recv c; let t2 := &recv c; &send c (&tuple t1 t2)

/-- Split a received pair. -/
@[rocq_alias cryptis.add_proj]
def addProj : Val := hl_val%
  λ c,
    let t := &recv c;
    match &untuple t with
    | none() => #()
    | some(v) => &send c (fst(v)); &send c (snd(v))

/-- Send a fresh nonce. -/
@[rocq_alias cryptis.add_nonce]
def addNonce : Val := hl_val% λ c, &send c (&mkNonce #())

/-- Turn a received term into keys of every type. -/
@[rocq_alias cryptis.add_keys]
def addKeys : Val := hl_val%
  λ c,
    let t := &recv c;
    &send c (&(key .aenc) t);
    &send c (&(key .adec) t);
    &send c (&(key .sign) t);
    &send c (&(key .verify) t);
    &send c (&(key .senc) t);
    &send c (&pkey t)

/-- Seal a received term with another one. -/
@[rocq_alias cryptis.add_seal]
def addSeal : Val := hl_val%
  λ c, let t1 := &recv c; let t2 := &recv c; &send c (&sealed t1 t2)

/-- Open a received term with another one. -/
@[rocq_alias cryptis.add_open]
def addOpen : Val := hl_val%
  λ c,
    let t1 := &recv c;
    let t2 := &recv c;
    match &opened t1 t2 with
    | none() => #()
    | some(t) => &send c t

/-- Hash a received term. -/
@[rocq_alias cryptis.add_hash]
def addHash : Val := hl_val% λ c, let t := &recv c; &send c (&hash t)

/-- Exponentiate a received term by another one. -/
@[rocq_alias cryptis.add_exp]
def addExp : Val := hl_val%
  λ c, let t1 := &recv c; let t2 := &recv c; &send c (&texp t1 t2)

/-- Send the unit of scalar products. -/
@[rocq_alias cryptis.add_mul_unit]
def addMulUnit : Val := hl_val% λ c, &send c (&tone #())

/-- Multiply two received terms. -/
@[rocq_alias cryptis.add_mul]
def addMul : Val := hl_val%
  λ c, let t1 := &recv c; let t2 := &recv c; &send c (&tmul t1 t2)

/-- Invert a received term. -/
@[rocq_alias cryptis.add_inv]
def addInv : Val := hl_val% λ c, let t := &recv c; &send c (&tinv t)

/-- Send the unit of group products. -/
@[rocq_alias cryptis.add_gmul_unit]
def addGMulUnit : Val := hl_val% λ c, &send c (&tgone #())

/-- Multiply two received terms in the group. -/
@[rocq_alias cryptis.add_gmul]
def addGMul : Val := hl_val%
  λ c, let t1 := &recv c; let t2 := &recv c; &send c (&tgmul t1 t2)

/-- Invert a received term in the group. -/
@[rocq_alias cryptis.add_ginv]
def addGInv : Val := hl_val% λ c, let t := &recv c; &send c (&tginv t)

/-- Run every attacker step in a new thread, forever. -/
@[rocq_alias cryptis.init_attacker]
def initAttacker : Val := hl_val%
  rec loop c :=
    fork(
      &addInt c; &addPair c; &addProj c; &addNonce c; &addKeys c; &addSeal c; &addOpen c;
      &addHash c; &addExp c; &addMulUnit c; &addMul c; &addInv c; &addGMulUnit c; &addGMul c;
      &addGInv c; loop c)

/-- A channel with an attacker on it. -/
@[rocq_alias cryptis.init_network]
def initNetwork : Val := hl_val% λ _, let c := &mkChannel #(); &initAttacker c; c

/-- Run a protocol on a network with an attacker. -/
@[rocq_alias cryptis.run_network]
def runNetwork : Val := hl_val% λ f, f (&initNetwork #())

/-! ## Specifications -/

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- `wp_send`, for a term known to be public. -/
theorem wp_send_of_isPublic {c : Val} {t : Term} {Ψ : Val → IProp GF} :
    channel c -∗ isPublic t -∗ Ψ hl_val(#()) -∗ WP hl(&send &c &(encode t)) {{ Ψ }} := by
  iintro #Hc #Ht HΨ
  iapply wp_send c t Ψ $$ Hc [] HΨ
  inext
  iexact Ht

@[rocq_alias cryptis.wp_add_int]
theorem wp_addInt (c : Val) :
    {{ channel c }} hl(&addInt &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_nondetInt with %n
  wp_pures
  wp_apply wp_tint
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply (isPublic_int n).mpr $$ [//]
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_pair]
theorem wp_addPair (c : Val) :
    {{ channel c }} hl(&addPair &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t₁ #H₁
  wp_pures
  wp_apply wp_recv $$ Hc with %t₂ #H₂
  wp_pures
  wp_apply wp_tuple
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply (isPublic_pair t₁ t₂).mpr
    isplit
    · iexact H₁
    · iexact H₂
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_proj]
theorem wp_addProj (c : Val) :
    {{ channel c }} hl(&addProj &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t #Ht
  wp_pures
  wp_apply wp_untuple
  cases t
  case pair t₁ t₂ =>
    icases (isPublic_pair t₁ t₂).mp $$ Ht with ⟨#H₁, #H₂⟩
    simp only [Spec.untuple, encode_some, encode_prod]
    wp_pures
    wp_apply wp_send_of_isPublic $$ Hc H₁
    wp_pures
    iapply wp_send_of_isPublic $$ Hc H₂ [HΦ]
    iapply HΦ $$ [//]
  all_goals simp only [Spec.untuple, encode_none]; wp_pures; iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_nonce]
theorem wp_addNonce (c : Val) :
    {{ cryptisCtx ∗ channel c }} hl(&addNonce &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hctx, #Hc⟩ HΦ
  wp_rec
  wp_apply wp_mkNonce (fun _ => iprop(True)) (fun _ => iprop(True)) $$ Hctx
    with %a - #Hp - - -
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · icases Hp with ⟨-, H⟩
    iapply H
    inext
    iintro !>
    itrivial
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_keys]
theorem wp_addKeys (c : Val) :
    {{ channel c }} hl(&addKeys &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t #Ht
  ihave #Hk : ∀ kt, isPublic (Term.key kt t) $$ [#]
  · iintro %kt
    iapply (isPublic_key kt t).mpr
    ileft
    iexact Ht
  ihave #Hae := Hk $$ %.aenc
  ihave #Had := Hk $$ %.adec
  ihave #Hsg := Hk $$ %.sign
  ihave #Hvf := Hk $$ %.verify
  ihave #Hse := Hk $$ %.senc
  wp_pures
  wp_apply wp_key
  wp_apply wp_send_of_isPublic $$ Hc Hae
  wp_pures
  wp_apply wp_key
  wp_apply wp_send_of_isPublic $$ Hc Had
  wp_pures
  wp_apply wp_key
  wp_apply wp_send_of_isPublic $$ Hc Hsg
  wp_pures
  wp_apply wp_key
  wp_apply wp_send_of_isPublic $$ Hc Hvf
  wp_pures
  wp_apply wp_key
  wp_apply wp_send_of_isPublic $$ Hc Hse
  wp_pures
  wp_apply wp_pkey
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_pkey $$ Ht
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_seal]
theorem wp_addSeal (c : Val) :
    {{ channel c }} hl(&addSeal &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t₁ #H₁
  wp_pures
  wp_apply wp_recv $$ Hc with %t₂ #H₂
  wp_pures
  wp_apply wp_sealed
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_sealed_of_isPublic $$ H₁ H₂
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_open]
theorem wp_addOpen (c : Val) :
    {{ channel c }} hl(&addOpen &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t₁ #H₁
  wp_pures
  wp_apply wp_recv $$ Hc with %t₂ #H₂
  wp_pures
  wp_apply wp_opened
  cases h : Spec.opened t₁ t₂ with
  | none => simp only [encode_none]; wp_pures; iapply HΦ $$ [//]
  | some t =>
    simp only [encode_some]
    wp_pures
    iapply wp_send_of_isPublic $$ Hc [] [HΦ]
    · iapply isPublic_opened h $$ H₁ H₂
    · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_hash]
theorem wp_addHash (c : Val) :
    {{ channel c }} hl(&addHash &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t #Ht
  wp_pures
  wp_apply wp_hash
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply (isPublic_hash t).mpr
    ileft
    iexact Ht
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_exp]
theorem wp_addExp (c : Val) :
    {{ channel c }} hl(&addExp &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t₁ #H₁
  wp_pures
  wp_apply wp_recv $$ Hc with %t₂ #H₂
  wp_pures
  wp_apply wp_texp (Term.E.ofTerm t₂) (Term.G.ofTerm t₁)
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_coe_smul $$ H₁ H₂
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_mul_unit]
theorem wp_addMulUnit (c : Val) :
    {{ channel c }} hl(&addMulUnit &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_tone
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_coe_one
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_mul]
theorem wp_addMul (c : Val) :
    {{ channel c }} hl(&addMul &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t₁ #H₁
  wp_pures
  wp_apply wp_recv $$ Hc with %t₂ #H₂
  wp_pures
  wp_apply wp_tmul (Term.E.ofTerm t₁) (Term.E.ofTerm t₂)
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_coe_mul $$ H₁ H₂
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_inv]
theorem wp_addInv (c : Val) :
    {{ channel c }} hl(&addInv &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t #Ht
  wp_pures
  wp_apply wp_tinv (Term.E.ofTerm t)
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply (isPublic_coe_inv (Term.E.ofTerm t)).mpr $$ Ht
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_gmul_unit]
theorem wp_addGMulUnit (c : Val) :
    {{ channel c }} hl(&addGMulUnit &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_tgone
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_coe_one
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_gmul]
theorem wp_addGMul (c : Val) :
    {{ channel c }} hl(&addGMul &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t₁ #H₁
  wp_pures
  wp_apply wp_recv $$ Hc with %t₂ #H₂
  wp_pures
  wp_apply wp_tgmul (Term.G.ofTerm t₁) (Term.G.ofTerm t₂)
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply isPublic_coe_mul $$ H₁ H₂
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_add_ginv]
theorem wp_addGInv (c : Val) :
    {{ channel c }} hl(&addGInv &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ #Hc HΦ
  wp_rec
  wp_apply wp_recv $$ Hc with %t #Ht
  wp_pures
  wp_apply wp_tginv (Term.G.ofTerm t)
  iapply wp_send_of_isPublic $$ Hc [] [HΦ]
  · iapply (isPublic_coe_inv (Term.G.ofTerm t)).mpr $$ Ht
  · iapply HΦ $$ [//]

@[rocq_alias cryptis.wp_init_attacker]
theorem wp_initAttacker (c : Val) :
    {{ cryptisCtx ∗ channel c }} hl(&initAttacker &c) {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hctx, #Hc⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_apply wp_fork $$ [HΦ]
  · iapply HΦ $$ [//]
  wp_apply wp_addInt $$ Hc with -
  wp_pures
  wp_apply wp_addPair $$ Hc with -
  wp_pures
  wp_apply wp_addProj $$ Hc with -
  wp_pures
  wp_apply wp_addNonce $$ [Hctx Hc] with -
  · iframe Hctx Hc
  wp_pures
  wp_apply wp_addKeys $$ Hc with -
  wp_pures
  wp_apply wp_addSeal $$ Hc with -
  wp_pures
  wp_apply wp_addOpen $$ Hc with -
  wp_pures
  wp_apply wp_addHash $$ Hc with -
  wp_pures
  wp_apply wp_addExp $$ Hc with -
  wp_pures
  wp_apply wp_addMulUnit $$ Hc with -
  wp_pures
  wp_apply wp_addMul $$ Hc with -
  wp_pures
  wp_apply wp_addInv $$ Hc with -
  wp_pures
  wp_apply wp_addGMulUnit $$ Hc with -
  wp_pures
  wp_apply wp_addGMul $$ Hc with -
  wp_pures
  wp_apply wp_addGInv $$ Hc with -
  wp_pures
  iapply IH
  iintro !> -
  itrivial

@[rocq_alias cryptis.wp_init_network]
theorem wp_initNetwork :
    {{ cryptisCtx }} hl(&initNetwork #()) {{ c, RET c; channel c }} := by
  iintro %Φ #Hctx HΦ
  wp_rec
  wp_apply wp_mkChannel with %c #Hc
  wp_pures
  wp_apply wp_initAttacker $$ [Hctx Hc] with -
  · iframe Hctx Hc
  wp_pures
  iapply HΦ $$ Hc

@[rocq_alias cryptis.wp_run_network]
theorem wp_runNetwork (f : Val) (φ : Val → IProp GF) :
    (∀ c, cryptisCtx -∗ channel c -∗ WP hl(&f &c) {{ φ }}) -∗
    cryptisCtx -∗ WP hl(&runNetwork &f) {{ φ }} := by
  iintro Hwp #Hctx
  wp_rec
  wp_apply wp_initNetwork $$ Hctx with %c #Hc
  iapply Hwp $$ Hctx Hc

end HL

end Cryptis
