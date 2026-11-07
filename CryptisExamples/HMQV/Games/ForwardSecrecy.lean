module

public import Cryptis.Adequacy
public import Cryptis.Upstream.Iris.HeapLangAssert
public import Iris.HeapLang.Lib.Assert
public import CryptisExamples.HMQV.Proofs

/-! The forward secrecy game of HMQV.

The initiator and the responder run any number of sessions with each other, while the attacker
may at any time obtain both long-term private keys. A session completed before the compromise
keeps its key secret: the attacker may guess its key after the compromise, and an assertion checks
that the guess is wrong. `hmqv_secure` shows that the game never gets stuck, so these assertions
hold.

- An invariant ties the flag `compromised` to the long-term keys: they are secret while it is
  false and public once it is true.
- The game uses the protocol with no resources exchanged and no session ever released. Since
  ephemeral keys never leak, a session completed while the long-term keys were secret keeps its
  key secret (`wp_checkKeySecrecy`).
- The remaining lemmas follow the structure of the program, and `hmqv_secure` concludes by
  adequacy. -/

@[expose] public section

namespace CryptisExamples.HMQV.ForwardSecrecy

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Iris.ProgramLogic Language.Notation Term

/-- The namespace of the game. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.gameN]
def gameN : Namespace := nroot.@"game"

/-- Record the compromise and leak both long-term private keys. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.compromise_long_term_keys]
def compromiseLongTermKeys : Val := hl_val%
  λ c compromised pa pb,
    compromised ← #true;
    &HL.send c pa;
    &HL.send c pb

/-- Wait until the long-term keys are compromised. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wait_for_compromise]
def waitForCompromise : Val := hl_val%
  rec loop compromised := if !compromised then #() else loop compromised

/-- If the long-term keys have not leaked yet, wait for their compromise, then receive a guess for
the key `sk` and check that it is wrong. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.check_key_secrecy]
def checkKeySecrecy : Val := hl_val%
  λ c compromised sk,
    if ~ !compromised then
      (&waitForCompromise compromised;
       let guess := &HL.recv c;
       assert(~ (&HL.eqTerm sk guess)))
    else #()

/-- Run initiator sessions with `Pb`, and check the secrecy of the key of each one that
completes. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.do_init]
def doInit : Val := hl_val%
  rec loop c compromised pa Pa Pb :=
    fork(loop c compromised pa Pa Pb);
    (bind: sk := &initiator c pa Pa Pb &(encode (ofNamespace gameN)) in
     &checkKeySecrecy c compromised sk);
    #()

/-- Run responder sessions, answering only first messages that claim the identity `Pa`, and check
the secrecy of the key of each one that completes. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.do_resp]
def doResp : Val := hl_val%
  rec loop c compromised pb Pb Pa :=
    fork(loop c compromised pb Pb Pa);
    let res := &responderListen c;
    let Xa := fst(res);
    let Pa' := snd(res);
    (guard: &HL.eqTerm Pa Pa' in
     bind: sk := &responderConfirm c pb Pb Xa Pa' &(encode (ofNamespace gameN)) in
     &checkKeySecrecy c compromised sk);
    #()

/-- Create the long-term keys, run both parties, and let the attacker compromise the keys. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.game]
def game : Val := hl_val%
  λ c,
    let ka := &mkLtKey #();
    let kb := &mkLtKey #();
    let pa := fst(ka);
    let Pa := snd(ka);
    let pb := fst(kb);
    let Pb := snd(kb);
    let compromised := ref(#false);
    &HL.send c Pa;
    &HL.send c Pb;
    fork(&doInit c compromised pa Pa Pb);
    fork(&doResp c compromised pb Pb Pa);
    fork(&compromiseLongTermKeys c compromised pa pb)

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- The flag `l` records whether both long-term private keys are public or secret. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.game_inv]
abbrev gameInv (l : Loc) (pa pb : Nonce) : IProp GF :=
  iprop(∃ b : Bool, l ↦ some hl_val(#b) ∗
    if b then isPublic (pa : Term) ∗ isPublic (pb : Term)
    else secret (pa : Term) ∗ secret (pb : Term))

@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wp_compromise_long_term_keys]
theorem wp_compromiseLongTermKeys (c : Val) (l : Loc) (pa pb : Nonce) :
    {{ cryptisCtx ∗ channel c ∗ inv gameN (gameInv l pa pb) }}
      hl(&compromiseLongTermKeys &c #l &(encode (pa : Term)) &(encode (pb : Term)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨-, #Hc, #Hinv⟩ HΦ
  wp_rec
  wp_pures
  wp_bind (_ ← _)
  iinv Hinv with ⟨%b, >Hl, Hb⟩
  wp_store
  ihave Hp : |={⊤ \ ↑gameN}=> isPublic (pa : Term) ∗ isPublic (pb : Term) $$ [Hb]
  · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · icases Hb with ⟨Hspa, Hspb⟩
      imod secret_isPublic _ $$ Hspa with #Hppa
      imod secret_isPublic _ $$ Hspb with #Hppb
      imodintro
      iframe Hppa Hppb
    · imodintro
      iexact Hb
  imod Hp with ⟨#Hppa, #Hppb⟩
  imodintro
  isplitl [Hl]
  · inext
    iexists true
    simp only [↓reduceIte]
    iframe Hl Hppa Hppb
  wp_pures
  wp_apply HL.wp_send $$ Hc Hppa
  wp_pures
  wp_apply HL.wp_send $$ Hc Hppb
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wp_wait_for_compromise]
theorem wp_waitForCompromise (l : Loc) (pa pb : Nonce) :
    {{ cryptisCtx ∗ inv gameN (gameInv l pa pb) }}
      hl(&waitForCompromise #l)
    {{ RET hl_val(#()); isPublic (pa : Term) ∗ isPublic (pb : Term) }} := by
  iintro %Φ ⟨-, #Hinv⟩ HΦ
  iloeb as IH
  wp_rec
  wp_bind (! _)
  iinv Hinv with ⟨%b, >Hl, Hb⟩
  wp_load
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · imodintro
    isplitl [Hl Hb]
    · inext
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hl Hb
    wp_pures
    iapply IH $$ HΦ
  · icases Hb with ⟨#Hppa, #Hppb⟩
    imodintro
    isplitl [Hl]
    · inext
      iexists true
      simp only [↓reduceIte]
      iframe Hl Hppa Hppb
    wp_pures
    iapply HΦ
    iframe Hppa Hppb

/-- Ephemerals never leak and the game never releases a session, so a session completed while
the long-term keys were secret keeps its key secret. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wp_check_key_secrecy]
theorem wp_checkKeySecrecy (c : Val) (l : Loc) (pa pb : Nonce) (rl : Role) (si : SessInfo)
    (ha : si.init = g.exp pa) (hb : si.resp = g.exp pb) :
    {{ cryptisCtx ∗ channel c ∗ inv gameN (gameInv l pa pb) ∗ hmqvKey pa ∗ hmqvKey pb ∗
        session (fun _ => iprop(False)) rl si }}
      hl(&checkKeySecrecy &c #l &(encode (si.key : Term)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hctx, #Hc, #Hinv, #Hpa, #Hpb, #Hsess⟩ HΦ
  wp_rec
  wp_pures
  wp_bind (! _)
  iinv Hinv with ⟨%b, >Hl, Hb⟩
  wp_load
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  on_goal 2 =>
    imodintro
    isplitl [Hl Hb]
    · inext
      iexists true
      simp only [↓reduceIte]
      iframe Hl Hb
    wp_pures
    iapply HΦ $$ [//]
  icases Hb with ⟨Hspa, Hspb⟩
  -- The secret long-term key of the peer rules out compromise.
  ihave H : ◇ □ (¬ compromised rl si) ∧ secret (pa : Term) ∗ secret (pb : Term) $$ [Hspa Hspb]
  · isplit
    · cases rl
      · iapply secret_session (rl := .init) pb hb $$ Hpb Hspb Hsess
      · iapply secret_session (rl := .resp) pa ha $$ Hpa Hspa Hsess
    · iframe Hspa Hspb
  icases H with ⟨#Hnc, Hspa, Hspb⟩
  imod Hnc with #Hnc
  ihave #Hok := session_ok $$ Hsess Hnc
  imodintro
  isplitl [Hl Hspa Hspb]
  · inext
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hl Hspa Hspb
  wp_pures
  wp_apply wp_waitForCompromise l pa pb $$ [] with -
  · iframe Hctx Hinv
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %guess #Hg
  -- The key is public only two laters later, so the case split comes before the pure steps.
  by_cases e : (si.key : Term) = guess
  · subst e
    ihave Hf := Hok $$ Hg
    wp_pures
    wp_apply Assert.wp_assert
    wp_apply HL.wp_eqTerm
    wp_pures
    iexfalso
    iexact Hf
  · wp_pures
    wp_apply Assert.wp_assert
    wp_apply HL.wp_eqTerm
    wp_pures
    imodintro
    isplit
    · ipureintro; simp [e]
    · inext
      iapply HΦ $$ [//]

variable [HmqvGS GF]

/-- The usage of the protocol in the game: no gifts, and no session is released. -/
abbrev gamePred : IProp GF := hmqvPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False))

@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wp_do_init]
theorem wp_doInit (c : Val) (l : Loc) (pa pb : Nonce) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ gamePred ∗ hmqvKey pa ∗ hmqvKey pb ∗
        inv gameN (gameInv l pa pb) }}
      hl(&doInit &c #l &(encode (pa : Term)) &(encode (g.exp pa)) &(encode (g.exp pb)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hhmqv, #Hφ, #Hpa, #Hpb, #Hinv⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply wp_initiator c pa (g.exp pb) gameN _ _ (fun _ => iprop(True)) iprop(True) $$ []
    with %r (⟨%rfl, -⟩ | ⟨%xa, %Xb, %rfl, #Hsess, -⟩)
  · iframe Hc Hctx Hhmqv Hφ Hpa
    isplit
    · iapply isPublic_of_hmqvKey $$ Hpb
    isplit
    · itrivial
    · iintro %xa %Xb - !>
      isplit <;> itrivial
  · wp_expr_simp
    wp_pures
    iapply HΦ $$ [//]
  wp_expr_simp
  wp_pures
  wp_apply wp_checkKeySecrecy c l pa pb .init (initSI pa xa (g.exp pb) Xb) rfl rfl $$ [] with -
  · iframe Hctx Hc Hinv Hpa Hpb Hsess
  wp_pures
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wp_do_resp]
theorem wp_doResp (c : Val) (l : Loc) (pa pb : Nonce) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ gamePred ∗ hmqvKey pa ∗ hmqvKey pb ∗
        inv gameN (gameInv l pa pb) }}
      hl(&doResp &c #l &(encode (pb : Term)) &(encode (g.exp pb)) &(encode (g.exp pa)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hhmqv, #Hφ, #Hpa, #Hpb, #Hinv⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply wp_responderListen c $$ [] with %Xa %Pa' ⟨#HXa, #HPa'⟩
  · iframe Hc Hctx
  wp_pures
  wp_eq_term e
  on_goal 2 => (wp_pures; iapply HΦ $$ [//])
  subst e
  wp_pures
  wp_apply wp_responderConfirm c (g.exp pa) Xa pb gameN _ _ (fun _ => iprop(True)) $$ []
    with %r (%rfl | ⟨%xb, %rfl, #Hsess, -⟩)
  · iframe Hc Hctx Hhmqv Hφ HXa Hpb HPa'
    iintro %xb - !>
    isplit <;> itrivial
  · wp_expr_simp
    wp_pures
    iapply HΦ $$ [//]
  wp_expr_simp
  wp_pures
  wp_apply wp_checkKeySecrecy c l pa pb .resp (respSI (g.exp pa) Xa pb xb) rfl rfl $$ [] with -
  · iframe Hctx Hc Hinv Hpa Hpb Hsess
  wp_pures
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.wp_game]
theorem wp_game (c : Val) :
    cryptisCtx -∗ channel c -∗ hmqvCtx -∗ gamePred -∗ WP hl(&game &c) {{ _v, True }} := by
  iintro #Hctx #Hc #Hhmqv #Hφ
  wp_rec
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pa ⟨#Hpa, Hspa, #HPa, -⟩
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pb ⟨#Hpb, Hspb, #HPb, -⟩
  wp_pures
  wp_alloc l with Hl
  imod inv_alloc gameN ⊤ (gameInv l pa pb) $$ [Hl Hspa Hspb] with #Hinv
  · inext
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hl Hspa Hspb
  wp_pures
  wp_apply HL.wp_send $$ Hc HPa
  wp_pures
  wp_apply HL.wp_send $$ Hc HPb
  wp_pures
  wp_apply wp_fork $$ []
  · wp_pures
    wp_apply wp_fork $$ []
    · wp_pures
      wp_apply wp_fork $$ []
      · itrivial
      wp_apply wp_compromiseLongTermKeys c l pa pb $$ [] with -
      · iframe Hctx Hc Hinv
      itrivial
    wp_apply wp_doResp c l pa pb $$ [] with -
    · iframe Hc Hctx Hhmqv Hφ Hpa Hpb Hinv
    itrivial
  wp_apply wp_doInit c l pa pb $$ [] with -
  · iframe Hc Hctx Hhmqv Hφ Hpa Hpb Hinv
  itrivial

#rocq_ignore cryptis.examples.hmqv.games.forward_secrecy.F
  "Subsumed by BundledGFunctors typeclass synthesis: the theorem holds for any suitable GF"

/-- The game never gets stuck: the keys of the sessions completed before the compromise stay
secret. -/
@[rocq_alias cryptis.examples.hmqv.games.forward_secrecy.hmqv_secure]
theorem hmqv_secure {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] [CryptisGpreS GF]
    [HmqvGpreS GF] {σ₁ σ₂ : State} {t₂ : List Exp} {e₂ : Exp}
    (h : ([hl(&HL.runNetwork &game)], σ₁) -·->ₜₚ* (t₂, σ₂)) (he : e₂ ∈ t₂) :
    PrimStep.NotStuck (e₂, σ₂) := by
  refine (cryptis_adequacy (GF := GF) game σ₁ (fun _ => True) fun c => ?_).adequate_not_stuck
    t₂ σ₂ e₂ rfl h he
  iintro #Hctx #Hc ⟨-, -, -, Htok⟩
  imod hmqvGS_alloc CoPset.subseteq_top $$ Htok with ⟨%_, #Hhmqv, Htok, -⟩
  imod hmqvPred_set gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) CoPset.subseteq_top
    $$ Htok with ⟨#Hφ, -⟩
  iapply wp_game $$ Hctx Hc Hhmqv Hφ

end CryptisExamples.HMQV.ForwardSecrecy
