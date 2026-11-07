module

public import Cryptis.Adequacy
public import Cryptis.Lib.TermSet
public import Cryptis.Role
public import CryptisExamples.NSL.Proofs

/-! The secrecy game of NSL.

Two honest participants run any number of sessions against the attacker, which chooses the peer
of each initiator session. When an honest session completes with the honest peer, the attacker may
guess its key, and an assertion checks that the guess is wrong. Each session key is added to a set
that must not already contain it, so keys are never reused. `nsl_secure` shows that this program
never gets stuck, so all these assertions hold.

- The keys in the set of a role are the keys of sessions whose nonce from that role has been
  marked. The token of the nonce allows marking it only once, so a key enters the set only once.
- `wp_checkKeySecrecy` shows that a guess for a key that stays secret is wrong.
- The remaining lemmas follow the structure of the program, and `nsl_secure` concludes by
  adequacy. -/

@[expose] public section

namespace CryptisExamples.NSL

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Iris.ProgramLogic Language.Notation

/-- Receive a guess for the key `sk` and check that it is wrong. -/
@[rocq_alias cryptis.examples.nsl.check_key_secrecy]
def checkKeySecrecy : Val := hl_val%
  λ c sk, let guess := &HL.recv c; assert(~ (&HL.eqTerm sk guess))

/-- Run initiator sessions with the peers chosen by the attacker, and check the secrecy of the
keys of the sessions with `pkR`. -/
@[rocq_alias cryptis.examples.nsl.do_init_loop]
def doInitLoop : Val := hl_val%
  rec loop c set skI pkR :=
    fork(loop c set skI pkR);
    let pkR' := &HL.recv c;
    (guard: &HL.isAEncKey pkR' in
     bind: sk := &init c skI pkR' in
     &HL.addFreshLockTermSet sk set;
     if &HL.eqTerm pkR pkR' then &checkKeySecrecy c sk else #());
    #()

/-- `doInitLoop` with a new set of keys. -/
@[rocq_alias cryptis.examples.nsl.do_init]
def doInit : Val := hl_val%
  λ c skI pkR, let set := &HL.newLockTermSet #(); &doInitLoop c set skI pkR

/-- Run responder sessions, and check the secrecy of the keys of the sessions with `pkI`. -/
@[rocq_alias cryptis.examples.nsl.do_resp_loop]
def doRespLoop : Val := hl_val%
  rec loop c set skR pkI :=
    fork(loop c set skR pkI);
    (bind: res := &resp c skR in
     let pkI' := fst(res);
     let sk := snd(res);
     &HL.addFreshLockTermSet sk set;
     if &HL.eqTerm pkI pkI' then &checkKeySecrecy c sk else #());
    #()

/-- `doRespLoop` with a new set of keys. -/
@[rocq_alias cryptis.examples.nsl.do_resp]
def doResp : Val := hl_val%
  λ c skR pkI, let set := &HL.newLockTermSet #(); &doRespLoop c set skR pkI

/-- Create the keys of both participants, publish their public keys and run both. -/
@[rocq_alias cryptis.examples.nsl.game]
def game : Val := hl_val%
  λ c,
    let skI := &HL.mkAEncKey #();
    let skR := &HL.mkAEncKey #();
    let pkI := &HL.pkey skI;
    let pkR := &HL.pkey skR;
    &HL.send c pkI;
    &HL.send c pkR;
    fork(&doInit c skI pkR);
    fork(&doResp c skR pkI)

/-- The nonce that the participant `rl` contributes to a session. -/
@[rocq_alias cryptis.examples.nsl.si_share_of]
abbrev SessInfo.shareOf : Role → SessInfo → Term
  | .init => SessInfo.initShare
  | .resp => SessInfo.respShare

section

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- The keys in the set of `rl` are the keys of sessions whose nonce of `rl` is marked. -/
@[rocq_alias cryptis.examples.nsl.nsl_game_inv]
abbrev nslGameInv (rl : Role) (t : Term) : IProp GF :=
  iprop(∃ si : SessInfo, ⌜t = ↑si.key⌝ ∧ termMeta (si.shareOf rl) (nroot.@"fresh") ())

@[rocq_alias cryptis.examples.nsl.nsl_game_inv_fresh]
theorem nslGameInv_fresh (rl : Role) (si : SessInfo) {E : CoPset} (h : ↑(nroot.@"fresh") ⊆ E) :
    termToken (si.shareOf rl) E -∗ freshTerm (nslGameInv (GF := GF) rl) si.key := by
  unfold freshTerm
  iintro Htok
  isplit
  · iintro ⟨%si', %e, #Hm⟩
    obtain rfl := SessInfo.key_injective (Key.toTerm_injective e)
    iapply termMeta_token h $$ Htok Hm
  · imod termMeta_set () h $$ Htok with #Hm
    iintro !> !>
    iexists si
    iframe Hm
    ipureintro; rfl

@[rocq_alias cryptis.examples.nsl.wp_check_key_secrecy]
theorem wp_checkKeySecrecy (c : Val) (k : Term) :
    {{ channel c ∗ cryptisCtx ∗ □ (isPublic k → ▷ ▷ False) }}
      hl(&checkKeySecrecy &c &(encode k))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, -, #Hk⟩ HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %guess #Hg
  wp_pures
  wp_apply Assert.wp_assert
  wp_eq_term e
  · subst e
    ihave Hcontra := Hk $$ Hg
    wp_pures
    imod Hcontra with ⟨⟩
  · wp_pures
    imodintro
    isplit
    · ipureintro; rfl
    · inext
      iapply HΦ $$ [//]

variable [TicketLock.TicketLockG GF]

@[rocq_alias cryptis.examples.nsl.wp_do_init_loop]
theorem wp_doInitLoop (c vset : Val) (skI skR : Key .aenc) :
    {{ channel c ∗ cryptisCtx ∗ nslCtx ∗ minted skI ∗ □ (isPublic skI ↔ ▷ False) ∗
        □ (isPublic skR ↔ ▷ False) ∗ isLockTermSet (nslGameInv .init) vset }}
      hl(&doInitLoop &c &vset &(encode skI) &(encode (Spec.pkey skR)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hnsl, #HmI, #HsI, #HsR, #Hset⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %pkR' #HpkR'
  wp_pures
  wp_apply HL.wp_isAEncKey pkR' $$ []
  · iapply isPublic_minted $$ HpkR'
  isplit
  on_goal 2 => (wp_pures; iapply HΦ $$ [//])
  iintro %skR' %rfl #HmR'
  wp_pures
  wp_apply wp_init c skI skR' $$ [] with %r Hr
  · iframe Hc Hctx Hnsl HmI HmR'
  icases Hr with (%rfl | ⟨%si, %rfl, ⟨-, -, -, #Hsk⟩, Htok⟩) <;> wp_expr_simp
  · wp_pures
    iapply HΦ $$ [//]
  ihave Hfresh := nslGameInv_fresh .init si (E := ⊤) (by solve_ndisj) $$ Htok
  wp_pures
  wp_apply HL.wp_addFreshLockTermSet (nslGameInv .init) ↑si.key vset $$ [Hfresh] with -
  · iframe Hset Hfresh
  wp_pures
  wp_eq_term e
  · obtain rfl := Key.pkey_injective e
    wp_pures
    wp_apply wp_checkKeySecrecy c ↑si.key $$ [] with -
    · iframe Hc Hctx
      iintro !> #Hfail
      ihave #Hfail := Hsk $$ Hfail
      inext
      icases Hfail with (#H | #H)
      · iapply HsI $$ H
      · iapply HsR $$ H
    wp_pures
    iapply HΦ $$ [//]
  · wp_pures
    iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.nsl.wp_do_init]
theorem wp_doInit (c : Val) (skI skR : Key .aenc) :
    {{ channel c ∗ cryptisCtx ∗ nslCtx ∗ minted skI ∗ □ (isPublic skI ↔ ▷ False) ∗
        □ (isPublic skR ↔ ▷ False) }}
      hl(&doInit &c &(encode skI) &(encode (Spec.pkey skR)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hnsl, #HmI, #HsI, #HsR⟩ HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_newLockTermSet (nslGameInv .init) $$ [//] with %vset #Hset
  wp_pures
  iapply wp_doInitLoop c vset skI skR $$ [] HΦ
  iframe Hc Hctx Hnsl HmI HsI HsR Hset

@[rocq_alias cryptis.examples.nsl.wp_do_resp_loop]
theorem wp_doRespLoop (c vset : Val) (skI skR : Key .aenc) :
    {{ channel c ∗ cryptisCtx ∗ nslCtx ∗ minted skR ∗ □ (isPublic skR ↔ ▷ False) ∗
        □ (isPublic skI ↔ ▷ False) ∗ isLockTermSet (nslGameInv .resp) vset }}
      hl(&doRespLoop &c &vset &(encode skR) &(encode (Spec.pkey skI)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hnsl, #HmR, #HsR, #HsI, #Hset⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply wp_resp c skR $$ [] with %r Hr
  · iframe Hc Hctx Hnsl HmR
  icases Hr with (%rfl | ⟨%skI', %si, %rfl, ⟨-, -, -, #Hsk⟩, Htok⟩) <;> wp_expr_simp
  · wp_pures
    iapply HΦ $$ [//]
  ihave Hfresh := nslGameInv_fresh .resp si (E := ⊤) (by solve_ndisj) $$ Htok
  wp_pures
  wp_apply HL.wp_addFreshLockTermSet (nslGameInv .resp) ↑si.key vset $$ [Hfresh] with -
  · iframe Hset Hfresh
  wp_pures
  wp_eq_term e
  · obtain rfl := Key.pkey_injective e
    wp_pures
    wp_apply wp_checkKeySecrecy c ↑si.key $$ [] with -
    · iframe Hc Hctx
      iintro !> #Hfail
      ihave #Hfail := Hsk $$ Hfail
      inext
      icases Hfail with (#H | #H)
      · iapply HsI $$ H
      · iapply HsR $$ H
    wp_pures
    iapply HΦ $$ [//]
  · wp_pures
    iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.nsl.wp_do_resp]
theorem wp_doResp (c : Val) (skI skR : Key .aenc) :
    {{ channel c ∗ cryptisCtx ∗ nslCtx ∗ minted skR ∗ □ (isPublic skR ↔ ▷ False) ∗
        □ (isPublic skI ↔ ▷ False) }}
      hl(&doResp &c &(encode skR) &(encode (Spec.pkey skI)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hnsl, #HmR, #HsR, #HsI⟩ HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_newLockTermSet (nslGameInv .resp) $$ [//] with %vset #Hset
  wp_pures
  iapply wp_doRespLoop c vset skI skR $$ [] HΦ
  iframe Hc Hctx Hnsl HmR HsR HsI Hset

@[rocq_alias cryptis.examples.nsl.wp_game]
theorem wp_game (c : Val) :
    cryptisCtx -∗ channel c -∗ sealPredToken .aenc ⊤ -∗ WP hl(&game &c) {{ _v, True }} := by
  iintro #Hctx #Hc Htok
  wp_rec
  wp_pures
  wp_apply HL.wp_mkAEncKey $$ Hctx with %skI #HmI HsecI -
  wp_pures
  wp_apply HL.wp_mkAEncKey $$ Hctx with %skR #HmR HsecR -
  wp_pures
  wp_apply HL.wp_pkey
  wp_pures
  wp_apply HL.wp_pkey
  imod freeze_secret _ $$ HsecI with #HsI
  imod freeze_secret _ $$ HsecR with #HsR
  wp_pures
  wp_apply HL.wp_send $$ Hc []
  · iapply (isPublic_pkey_aenc skI).mpr $$ HmI
  wp_pures
  wp_apply HL.wp_send $$ Hc []
  · iapply (isPublic_pkey_aenc skR).mpr $$ HmR
  wp_pures
  imod nslCtx_alloc (E₂ := ⊤) CoPset.subseteq_top $$ Htok with ⟨#Hnsl, -⟩
  wp_apply wp_fork $$ []
  · wp_pures
    wp_apply wp_fork $$ []
    · itrivial
    wp_apply wp_doResp c skI skR $$ [] with -
    · iframe Hc Hctx Hnsl HmR HsR HsI
    itrivial
  wp_apply wp_doInit c skI skR $$ [] with -
  · iframe Hc Hctx Hnsl HmI HsI HsR
  itrivial

end

#rocq_ignore cryptis.examples.nsl.F
  "Subsumed by BundledGFunctors typeclass synthesis: nsl_secure holds for any suitable GF"

/-- The game never gets stuck: the assertions of `checkKeySecrecy` and of the key sets hold. -/
@[rocq_alias cryptis.examples.nsl.nsl_secure]
theorem nsl_secure {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] [CryptisGpreS GF]
    {σ₁ σ₂ : State} {t₂ : List Exp} {e₂ : Exp}
    (h : ([hl(&HL.runNetwork &game)], σ₁) -·->ₜₚ* (t₂, σ₂)) (he : e₂ ∈ t₂) :
    PrimStep.NotStuck (e₂, σ₂) := by
  let := CryptisGpreS.tlock (GF := GF)
  refine (cryptis_adequacy (GF := GF) game σ₁ (fun _ => True) fun c => ?_).adequate_not_stuck
    t₂ σ₂ e₂ rfl h he
  iintro #Hctx #Hc ⟨Htok, -⟩
  iapply wp_game $$ Hctx Hc Htok

end CryptisExamples.NSL
