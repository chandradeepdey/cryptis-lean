module

public import Cryptis.Adequacy
public import Cryptis.Upstream.Iris.HeapLangAssert
public import Iris.HeapLang.Lib.Assert
public import CryptisExamples.HMQV.Proofs

/-! The key independence game of HMQV.

The initiator and the responder run any number of sessions with each other, and their long-term
keys never leak. Each time the responder completes a session, it checks that the attacker cannot
guess the key, and then leaks the key. So the keys of some sessions do not help the attacker guess
the keys of the others. `hmqv_key_independence` shows that the game never gets stuck, so the
checks succeed.

- The game uses the protocol with no resources exchanged, and a session counts as released once
  the responder has marked it, which it does right after checking its key.
- `wp_checkKeySecrecy` shows that the guess is wrong as long as the responder holds the token
  that marking the session would use up.
- `wp_doResp` then marks the session released, which allows the responder to leak its key. The
  remaining lemmas follow the structure of the program, and `hmqv_key_independence` concludes by
  adequacy. -/

@[expose] public section

namespace CryptisExamples.HMQV.KeyIndependence

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Iris.ProgramLogic Language.Notation Term

/-- The namespace of the game. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.gameN]
def gameN : Namespace := nroot.@"game"

/-- Receive a guess for the key `sk` and check that it is wrong. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.check_key_secrecy]
def checkKeySecrecy : Val := hl_val%
  λ c sk, let guess := &HL.recv c; assert(~ (&HL.eqTerm sk guess))

/-- Run initiator sessions with `Pb`. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.do_init]
def doInit : Val := hl_val%
  rec loop c pa Pa Pb :=
    fork(loop c pa Pa Pb);
    &initiator c pa Pa Pb &(encode (ofNamespace gameN));
    #()

/-- Run responder sessions with `Pa`, check the secrecy of each key and leak it. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.do_resp]
def doResp : Val := hl_val%
  rec loop c pb Pb Pa :=
    fork(loop c pb Pb Pa);
    let m1 := &responderListen c;
    (guard: &HL.eqTerm (snd(m1)) Pa in
     bind: sk := &responderConfirm c pb Pb (fst(m1)) Pa &(encode (ofNamespace gameN)) in
     &checkKeySecrecy c sk;
     &HL.send c sk);
    #()

/-- Create the long-term keys and run both parties. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.game]
def game : Val := hl_val%
  λ c,
    let ka := &mkLtKey #();
    let kb := &mkLtKey #();
    let pa := fst(ka);
    let Pa := snd(ka);
    let pb := fst(kb);
    let Pb := snd(kb);
    &HL.send c Pa;
    &HL.send c Pb;
    fork(&doInit c pa Pa Pb);
    &doResp c pb Pb Pa

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- The responder releases a session once it has checked its key. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.released]
abbrev released (si : SessInfo) : IProp GF := termMeta si.respShare gameN ()

@[rocq_alias cryptis.examples.hmqv.games.key_independence.wp_check_key_secrecy]
theorem wp_checkKeySecrecy (c : Val) (si : SessInfo) :
    {{ channel c ∗ termToken si.respShare ↑gameN ∗ □ (isPublic si.key → ▷ ▷ □ released si) }}
      hl(&checkKeySecrecy &c &(encode (si.key : Term)))
    {{ RET hl_val(#()); termToken si.respShare ↑gameN }} := by
  iintro %Φ ⟨#Hc, Htok, #Hk⟩ HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %guess #Hg
  -- The key is public only two laters later, so the case split comes before the pure steps.
  by_cases e : (si.key : Term) = guess
  · subst e
    ihave Hrel := Hk $$ Hg
    wp_pures
    wp_apply Assert.wp_assert
    wp_apply HL.wp_eqTerm
    wp_pures
    iexfalso
    iapply termMeta_token Std.LawfulSet.subset_refl $$ Htok Hrel
  · wp_pures
    wp_apply Assert.wp_assert
    wp_apply HL.wp_eqTerm
    wp_pures
    imodintro
    isplit
    · ipureintro; simp [e]
    · inext
      iapply HΦ $$ Htok

variable [HmqvGS GF]

/-- The usage of the protocol in the game: no gifts, and a session is released once checked. -/
abbrev gamePred : IProp GF := hmqvPred gameN (fun _ _ => iprop(True)) released

@[rocq_alias cryptis.examples.hmqv.games.key_independence.wp_do_init]
theorem wp_doInit (c : Val) (pa pb : Nonce) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ gamePred ∗ hmqvKey pa ∗ hmqvKey pb }}
      hl(&doInit &c &(encode (pa : Term)) &(encode (g.exp pa)) &(encode (g.exp pb)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hhmqv, #Hφ, #Hpa, #Hpb⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply wp_initiator c pa (g.exp pb) gameN _ _ (fun _ => iprop(True)) iprop(True) $$ []
    with %r -
  · iframe Hc Hctx Hhmqv Hφ Hpa
    isplit
    · iapply isPublic_of_hmqvKey $$ Hpb
    isplit
    · itrivial
    · iintro %xa %Xb - !>
      isplit <;> itrivial
  wp_pures
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.key_independence.wp_do_resp]
theorem wp_doResp (c : Val) (pa pb : Nonce) :
    {{ channel c ∗ cryptisCtx ∗ hmqvCtx ∗ gamePred ∗ hmqvKey pa ∗ hmqvKey pb ∗
        □ (isPublic (pa : Term) ↔ ▷ False) }}
      hl(&doResp &c &(encode (pb : Term)) &(encode (g.exp pb)) &(encode (g.exp pa)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hhmqv, #Hφ, #Hpa, #Hpb, #Hspa⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply wp_responderListen c $$ [] with %Xa %Pa' ⟨#HXa, -⟩
  · iframe Hc Hctx
  wp_pures
  wp_eq_term e
  on_goal 2 => (wp_pures; iapply HΦ $$ [//])
  subst e
  wp_pures
  wp_apply wp_responderConfirm c (g.exp pa) Xa pb gameN _ _
      (fun si => termToken si.respShare (⊤ \ ↑hmqvN)) $$ []
    with %r (%rfl | ⟨%xb, %rfl, #Hsess, Htok, -⟩)
  · iframe Hc Hctx Hhmqv Hφ HXa Hpb
    isplit
    · iapply isPublic_of_hmqvKey $$ Hpa
    · iintro %xb Htok !>
      iframe Htok
  · wp_expr_simp
    wp_pures
    iapply HΦ $$ [//]
  wp_expr_simp
  ihave #Hsk : ◇ □ (isPublic (respSI (g.exp pa) Xa pb xb).key →
      ▷ ▷ □ released (respSI (g.exp pa) Xa pb xb)) $$ []
  · icases Hsess with ⟨-, -, (⟨-, -, #Hl⟩ | ⟨-, #Hok⟩)⟩
    · imod Hl $$ %pa %rfl Hpa with #Hp
      ihave Hf := Hspa $$ Hp
      imod Hf with ⟨⟩
    · imodintro
      iexact Hok
  imod Hsk with #Hsk
  ihave Htok := termToken_drop (E1 := ↑gameN) (by solve_ndisj) $$ Htok
  wp_pures
  wp_apply wp_checkKeySecrecy c (respSI (g.exp pa) Xa pb xb) $$ [Htok] with Htok
  · iframe Hc Htok Hsk
  imod termMeta_set () Std.LawfulSet.subset_refl $$ Htok with #Hrel
  ihave #Hpk : isPublic (respSI (g.exp pa) Xa pb xb).key $$ []
  · iapply session_release $$ Hsess
    inext
    iintro !>
    iexact Hrel
  wp_pures
  wp_apply HL.wp_send $$ Hc Hpk
  wp_pures
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.key_independence.wp_game]
theorem wp_game (c : Val) :
    cryptisCtx -∗ channel c -∗ hmqvCtx -∗ gamePred -∗ WP hl(&game &c) {{ _v, True }} := by
  iintro #Hctx #Hc #Hhmqv #Hφ
  wp_rec
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pa ⟨#Hpa, Hspa, #HPa, -⟩
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pb ⟨#Hpb, -, #HPb, -⟩
  imod freeze_secret _ $$ Hspa with #Hspa
  wp_pures
  wp_apply HL.wp_send $$ Hc HPa
  wp_pures
  wp_apply HL.wp_send $$ Hc HPb
  wp_pures
  wp_apply wp_fork $$ []
  · wp_pures
    wp_apply wp_doResp c pa pb $$ [] with -
    · iframe Hc Hctx Hhmqv Hφ Hpa Hpb Hspa
    itrivial
  wp_apply wp_doInit c pa pb $$ [] with -
  · iframe Hc Hctx Hhmqv Hφ Hpa Hpb
  itrivial

#rocq_ignore cryptis.examples.hmqv.games.key_independence.F
  "Subsumed by BundledGFunctors typeclass synthesis: the theorem holds for any suitable GF"

/-- The game never gets stuck: the attacker cannot guess a key from the keys of other sessions. -/
@[rocq_alias cryptis.examples.hmqv.games.key_independence.hmqv_key_independence]
theorem hmqv_key_independence {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF]
    [CryptisGpreS GF] [HmqvGpreS GF] {σ₁ σ₂ : State} {t₂ : List Exp} {e₂ : Exp}
    (h : ([hl(&HL.runNetwork &game)], σ₁) -·->ₜₚ* (t₂, σ₂)) (he : e₂ ∈ t₂) :
    PrimStep.NotStuck (e₂, σ₂) := by
  refine (cryptis_adequacy (GF := GF) game σ₁ (fun _ => True) fun c => ?_).adequate_not_stuck
    t₂ σ₂ e₂ rfl h he
  iintro #Hctx #Hc ⟨-, -, -, Htok⟩
  imod hmqvGS_alloc CoPset.subseteq_top $$ Htok with ⟨%_, #Hhmqv, Htok, -⟩
  imod hmqvPred_set gameN (fun _ _ => iprop(True)) released CoPset.subseteq_top
    $$ Htok with ⟨#Hφ, -⟩
  iapply wp_game $$ Hctx Hc Hhmqv Hφ

end CryptisExamples.HMQV.KeyIndependence
