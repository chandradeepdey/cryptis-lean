module

public import Cryptis.Adequacy
public import Cryptis.Upstream.Iris.HeapLangAssert
public import Iris.HeapLang.Lib.Assert
public import Iris.HeapLang.Lib.Par
public import CryptisExamples.HMQV.Proofs

/-! The key-compromise impersonation game of HMQV.

An attacker who learns a party's long-term key can impersonate that party, but should not be able
to impersonate anybody else to it. In this game, the attacker picks whose long-term key leaks, the
initiator's or the responder's. One initiator and one responder session then run in parallel,
each party accepting only the other as its peer, and the key returned by the party whose
long-term key leaked must stay unguessable. `hmqv_kci_secure` shows that the game never gets
stuck, so this holds.

- `kci_key_secrecy` is the heart of the proof: the key of a session is public only if the peer's
  long-term key is, whatever happens to the party's own long-term key.
- `wp_kci_initiator` and `wp_kci_responder` give this guarantee for the result of each party, and
  `wp_checkKeySecrecy` turns it into a wrong guess.
- `wp_game` puts them together, and `hmqv_kci_secure` concludes by adequacy. -/

@[expose] public section

namespace CryptisExamples.HMQV.KCI

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Iris.ProgramLogic Language.Notation Term

/-- The namespace of the game. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.gameN]
def gameN : Namespace := nroot.@"game"

/-- The responder, which only answers the initiator `Pa`. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.responder]
def responder : Val := hl_val%
  λ c pb Pb Pa N,
    let m1 := &responderListen c;
    guard: &HL.eqTerm (snd(m1)) Pa in
    &responderConfirm c pb Pb (fst(m1)) Pa N

/-- Receive a guess for the key returned in `r`, if any, and check that it is wrong. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.check_key_secrecy]
def checkKeySecrecy : Val := hl_val%
  λ c r,
    bind: sk := r in
    let guess := &HL.recv c;
    assert(~ (&HL.eqTerm sk guess))

/-- Create the long-term keys, leak the one chosen by the attacker, and run one session of each
party. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.game]
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
    let leakInit := &HL.eqTerm (&HL.recv c) &(encode (Term.int 0));
    &HL.send c (if leakInit then pa else pb);
    let rs := (&initiator c pa Pa Pb &(encode (ofNamespace gameN)) ‖
      &responder c pb Pb Pa &(encode (ofNamespace gameN)));
    &checkKeySecrecy c (if leakInit then fst(rs) else snd(rs))

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- The key of a session is public only if the long-term private key `p` of the peer is, whatever
happens to the party's own long-term key. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.kci_key_secrecy]
theorem kci_key_secrecy (rl : Role) (si : SessInfo) (p : Nonce)
    (h : si.staticOf rl.swap = g.exp p) :
    session (fun _ => iprop(False)) rl si -∗ hmqvKey p -∗
      □ (isPublic si.key → ▷ ▷ ◇ isPublic (p : Term)) := by
  iintro ⟨-, -, (⟨-, -, #Hl⟩ | ⟨-, #Hok⟩)⟩ #Hkey !> #Hpk
  · inext
    inext
    iapply Hl $$ %p %h Hkey
  · ihave H := Hok $$ Hpk
    inext
    inext
    iexfalso
    iexact H

/-- The result of a session of a party whose peer has long-term private key `p`: its key, if
any, is public only if `p` is. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.kci_res]
abbrev kciRes (p : Nonce) (v : Val) : IProp GF :=
  iprop(⌜v = encode (none : Option Term)⌝ ∨ ∃ sk : Key .senc, ⌜v = encode (some (sk : Term))⌝ ∗
    □ (isPublic sk → ▷ ▷ ◇ isPublic (p : Term)))

@[rocq_alias cryptis.examples.hmqv.games.kci.wp_check_key_secrecy]
theorem wp_checkKeySecrecy (c v : Val) (p : Nonce) :
    channel c -∗ □ (isPublic (p : Term) ↔ ▷ False) -∗ kciRes p v -∗
      WP hl(&checkKeySecrecy &c &v) {{ _v, True }} := by
  iintro #Hc #Hsp (%rfl | ⟨%sk, %rfl, #Hsk⟩) <;> wp_expr_simp
  · wp_rec
    wp_pures
    itrivial
  wp_rec
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %guess #Hg
  -- The key is public only two laters later, so the case split comes before the pure steps.
  by_cases e : (sk : Term) = guess
  · subst e
    ihave Hf : ▷ ▷ ▷ False $$ []
    · ihave H := Hsk $$ Hg
      inext
      inext
      iapply except0_later
      imod H with #H
      imodintro
      iapply Hsp $$ H
    wp_pures
    wp_apply Assert.wp_assert
    wp_apply HL.wp_eqTerm
    wp_pures
    icases Hf with ⟨⟩
  · wp_pures
    wp_apply Assert.wp_assert
    wp_apply HL.wp_eqTerm
    wp_pures
    imodintro
    isplit
    · ipureintro; simp [e]
    · inext
      itrivial

variable [HmqvGS GF]

/-- The usage of the protocol in the game: no gifts, and no session is released. -/
abbrev gamePred : IProp GF := hmqvPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False))

@[rocq_alias cryptis.examples.hmqv.games.kci.wp_kci_initiator]
theorem wp_kci_initiator (c : Val) (pa pb : Nonce) :
    channel c -∗ cryptisCtx -∗ hmqvCtx -∗ gamePred -∗ hmqvKey pa -∗ hmqvKey pb -∗
      WP hl(&initiator &c &(encode (pa : Term)) &(encode (g.exp pa)) &(encode (g.exp pb))
        &(encode (ofNamespace gameN))) {{ kciRes pb }} := by
  iintro #Hc #Hctx #Hhmqv #Hφ #Hpa #Hpb
  wp_apply wp_initiator c pa (g.exp pb) gameN _ _ (fun _ => iprop(True)) iprop(True) $$ []
    with %r (⟨%rfl, -⟩ | ⟨%xa, %Xb, %rfl, #Hsess, -⟩)
  · iframe Hc Hctx Hhmqv Hφ Hpa
    isplit
    · iapply isPublic_of_hmqvKey $$ Hpb
    isplit
    · itrivial
    · iintro %xa %Xb - !>
      isplit <;> itrivial
  · ileft
    ipureintro; rfl
  · iright
    iexists _
    isplit
    · ipureintro; rfl
    · iapply kci_key_secrecy .init _ pb rfl $$ Hsess Hpb

@[rocq_alias cryptis.examples.hmqv.games.kci.wp_kci_responder]
theorem wp_kci_responder (c : Val) (pa pb : Nonce) :
    channel c -∗ cryptisCtx -∗ hmqvCtx -∗ gamePred -∗ hmqvKey pa -∗ hmqvKey pb -∗
      WP hl(&responder &c &(encode (pb : Term)) &(encode (g.exp pb)) &(encode (g.exp pa))
        &(encode (ofNamespace gameN))) {{ kciRes pa }} := by
  iintro #Hc #Hctx #Hhmqv #Hφ #Hpa #Hpb
  wp_rec
  wp_pures
  wp_apply wp_responderListen c $$ [] with %Xa %Pa' ⟨#HXa, -⟩
  · iframe Hc Hctx
  wp_pures
  wp_eq_term e
  on_goal 2 => (wp_pures; ileft; ipureintro; rfl)
  subst e
  wp_pures
  wp_apply wp_responderConfirm c (g.exp pa) Xa pb gameN _ _ (fun _ => iprop(True)) $$ []
    with %r (%rfl | ⟨%xb, %rfl, #Hsess, -⟩)
  · iframe Hc Hctx Hhmqv Hφ HXa Hpb
    isplit
    · iapply isPublic_of_hmqvKey $$ Hpa
    · iintro %xb - !>
      isplit <;> itrivial
  · ileft
    ipureintro; rfl
  · iright
    iexists _
    isplit
    · ipureintro; rfl
    · iapply kci_key_secrecy .resp _ pa rfl $$ Hsess Hpa

variable [Spawn.SpawnG GF]

@[rocq_alias cryptis.examples.hmqv.games.kci.wp_game]
theorem wp_game (c : Val) :
    cryptisCtx -∗ channel c -∗ hmqvCtx -∗ gamePred -∗ WP hl(&game &c) {{ _v, True }} := by
  iintro #Hctx #Hc #Hhmqv #Hφ
  wp_rec
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pa ⟨#Hpa, Hspa, #HPa, -⟩
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pb ⟨#Hpb, Hspb, #HPb, -⟩
  wp_pures
  wp_apply HL.wp_send $$ Hc HPa
  wp_pures
  wp_apply HL.wp_send $$ Hc HPb
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %m -
  wp_eq_term e
  · imod secret_isPublic _ $$ Hspa with #Hppa
    imod freeze_secret _ $$ Hspb with #Hspb
    wp_pures
    wp_apply HL.wp_send $$ Hc Hppa
    wp_pures
    wp_apply Par.wp_par (kciRes pb) (kciRes pa) $$ [] [] with %va %vb ⟨Hres, -⟩
    · iapply wp_kci_initiator $$ Hc Hctx Hhmqv Hφ Hpa Hpb
    · iapply wp_kci_responder $$ Hc Hctx Hhmqv Hφ Hpa Hpb
    inext
    wp_pures
    iapply wp_checkKeySecrecy $$ Hc Hspb Hres
  · imod secret_isPublic _ $$ Hspb with #Hppb
    imod freeze_secret _ $$ Hspa with #Hspa
    wp_pures
    wp_apply HL.wp_send $$ Hc Hppb
    wp_pures
    wp_apply Par.wp_par (kciRes pb) (kciRes pa) $$ [] [] with %va %vb ⟨-, Hres⟩
    · iapply wp_kci_initiator $$ Hc Hctx Hhmqv Hφ Hpa Hpb
    · iapply wp_kci_responder $$ Hc Hctx Hhmqv Hφ Hpa Hpb
    inext
    wp_pures
    iapply wp_checkKeySecrecy $$ Hc Hspa Hres

#rocq_ignore cryptis.examples.hmqv.games.kci.F
  "Subsumed by BundledGFunctors typeclass synthesis: hmqv_kci_secure holds for any suitable GF"

/-- The game never gets stuck: the key of the party whose long-term key leaked stays secret. -/
@[rocq_alias cryptis.examples.hmqv.games.kci.hmqv_kci_secure]
theorem hmqv_kci_secure {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] [CryptisGpreS GF]
    [Spawn.SpawnG GF] [HmqvGpreS GF] {σ₁ σ₂ : State} {t₂ : List Exp} {e₂ : Exp}
    (h : ([hl(&HL.runNetwork &game)], σ₁) -·->ₜₚ* (t₂, σ₂)) (he : e₂ ∈ t₂) :
    PrimStep.NotStuck (e₂, σ₂) := by
  refine (cryptis_adequacy (GF := GF) game σ₁ (fun _ => True) fun c => ?_).adequate_not_stuck
    t₂ σ₂ e₂ rfl h he
  iintro #Hctx #Hc ⟨-, -, -, Htok⟩
  imod hmqvGS_alloc CoPset.subseteq_top $$ Htok with ⟨%_, #Hhmqv, Htok, -⟩
  imod hmqvPred_set gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) CoPset.subseteq_top
    $$ Htok with ⟨#Hφ, -⟩
  iapply wp_game $$ Hctx Hc Hhmqv Hφ

end CryptisExamples.HMQV.KCI
