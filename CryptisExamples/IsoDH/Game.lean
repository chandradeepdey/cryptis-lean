module

public import Cryptis.Adequacy
public import Cryptis.Lib.TermSet
public import CryptisExamples.IsoDH

/-! The forward secrecy game of ISO-DH.

Two honest participants run any number of sessions against the attacker, which chooses the peer
of each initiator session, and may at any time leak both long-term keys. When an honest session
completes with the honest peer before the leak, the attacker may guess its key once the keys have
leaked, and an assertion checks that the guess is wrong. Each session key is added to a set that
must not already contain it, so keys are never reused. `iso_dh_secure` shows that this program
never gets stuck, so all these assertions hold.

- An invariant ties the flag `compromised` to the long-term keys: they are secret while it is
  false and public once it is true.
- The game uses the protocol with no resources exchanged and no session ever released, so a
  session completed before the leak keeps its key secret (`wp_checkKeySecrecy`).
- The keys in the set of a role are the keys of sessions whose share from that role has been
  marked, which the token of the share allows only once.
- The remaining lemmas follow the structure of the program, and `iso_dh_secure` concludes by
  adequacy. -/

@[expose] public section

namespace CryptisExamples.IsoDH

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Iris.ProgramLogic Language.Notation Term

/-- The namespace of the game. -/
@[rocq_alias cryptis.examples.iso_dh.gameN]
def gameN : Namespace := nroot.@"game"

/-- Leak both long-term keys, after recording it in `compromised`. -/
@[rocq_alias cryptis.examples.iso_dh.compromise_long_term_keys]
def compromiseLongTermKeys : Val := hl_val%
  λ c compromised skI skR,
    compromised ← #true;
    &HL.send c skI;
    &HL.send c skR

/-- Wait until the long-term keys have leaked. -/
@[rocq_alias cryptis.examples.iso_dh.wait_for_compromise]
def waitForCompromise : Val := hl_val%
  rec loop compromised := if !compromised then #() else loop compromised

/-- If the long-term keys have not leaked yet, wait until they have, receive a guess for the key
`sk` and check that it is wrong. -/
@[rocq_alias cryptis.examples.iso_dh.check_key_secrecy]
def checkKeySecrecy : Val := hl_val%
  λ c compromised sk,
    if ~ !compromised then
      (&waitForCompromise compromised;
       let guess := &HL.recv c;
       assert(~ (&HL.eqTerm sk guess)))
    else #()

/-- Run initiator sessions with the peers chosen by the attacker, and check the secrecy of the
keys of the sessions with `pkR`. -/
@[rocq_alias cryptis.examples.iso_dh.do_init_loop]
def doInitLoop : Val := hl_val%
  rec loop c compromised set skI pkR :=
    fork(loop c compromised set skI pkR);
    let pkR' := &HL.recv c;
    (guard: &HL.isVerifyKey pkR' in
     bind: sk := &initiator c skI pkR' &(encode (ofNamespace gameN)) in
     &HL.addFreshLockTermSet sk set;
     if &HL.eqTerm pkR pkR' then &checkKeySecrecy c compromised sk else #());
    #()

/-- `doInitLoop` with a new set of keys. -/
@[rocq_alias cryptis.examples.iso_dh.do_init]
def doInit : Val := hl_val%
  λ c compromised skI pkR,
    let set := &HL.newLockTermSet #();
    &doInitLoop c compromised set skI pkR

/-- Run responder sessions, and check the secrecy of the keys of the sessions with `pkI`. -/
@[rocq_alias cryptis.examples.iso_dh.do_resp_loop]
def doRespLoop : Val := hl_val%
  rec loop c compromised set skR pkI :=
    fork(loop c compromised set skR pkI);
    (bind: res := &responder c skR &(encode (ofNamespace gameN)) in
     let pkI' := fst(res);
     let sk := snd(res);
     &HL.addFreshLockTermSet sk set;
     if &HL.eqTerm pkI pkI' then &checkKeySecrecy c compromised sk else #());
    #()

/-- `doRespLoop` with a new set of keys. -/
@[rocq_alias cryptis.examples.iso_dh.do_resp]
def doResp : Val := hl_val%
  λ c compromised skR pkI,
    let set := &HL.newLockTermSet #();
    &doRespLoop c compromised set skR pkI

/-- Create the keys of both participants, publish their public keys, run both, and leak the
long-term keys at some point. -/
@[rocq_alias cryptis.examples.iso_dh.game]
def game : Val := hl_val%
  λ c,
    let skI := &HL.mkSignKey #();
    let skR := &HL.mkSignKey #();
    let pkI := &HL.pkey skI;
    let pkR := &HL.pkey skR;
    let compromised := ref(#false);
    &HL.send c pkI;
    &HL.send c pkR;
    fork(&doInit c compromised skI pkR);
    fork(&doResp c compromised skR pkI);
    fork(&compromiseLongTermKeys c compromised skI skR)

section

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- The long-term keys are secret until `lcomp` records that they leaked. -/
@[rocq_alias cryptis.examples.iso_dh.game_inv]
abbrev gameInv (lcomp : Loc) (skI skR : Key .sign) : IProp GF :=
  iprop(∃ b : Bool, lcomp ↦ some hl_val(#b) ∗
    if b then iprop(isPublic skI ∗ isPublic skR) else iprop(secret skI ∗ secret skR))

@[rocq_alias cryptis.examples.iso_dh.wp_compromise_long_term_keys]
theorem wp_compromiseLongTermKeys (c : Val) (lcomp : Loc) (skI skR : Key .sign) :
    {{ cryptisCtx ∗ channel c ∗ inv gameN (gameInv lcomp skI skR) }}
      hl(&compromiseLongTermKeys &c #lcomp &(encode skI) &(encode skR))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨-, #Hc, #Hinv⟩ HΦ
  wp_rec
  wp_pures
  wp_bind (_ ← _)
  iinv Hinv with ⟨%b, >Hl, Hb⟩
  wp_store
  ihave H : |==> (isPublic skI ∗ isPublic skR) $$ [Hb]
  · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · icases Hb with ⟨HsI, HsR⟩
      imod secret_isPublic _ $$ HsI with #HpI
      imod secret_isPublic _ $$ HsR with #HpR
      imodintro
      iframe HpI HpR
    · imodintro
      iexact Hb
  imod H with ⟨#HpI, #HpR⟩
  imodintro
  isplitl [Hl]
  · inext
    iexists true
    simp only [↓reduceIte]
    iframe Hl HpI HpR
  wp_pures
  wp_apply HL.wp_send $$ Hc HpI
  wp_pures
  wp_apply HL.wp_send $$ Hc HpR
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.iso_dh.wp_wait_for_compromise]
theorem wp_waitForCompromise (lcomp : Loc) (skI skR : Key .sign) :
    {{ cryptisCtx ∗ inv gameN (gameInv lcomp skI skR) }}
      hl(&waitForCompromise #lcomp)
    {{ RET hl_val(#()); isPublic skI ∗ isPublic skR }} := by
  iintro %Φ ⟨-, #Hinv⟩ HΦ
  iloeb as IH generalizing %Φ
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
  · icases Hb with ⟨#HpI, #HpR⟩
    imodintro
    isplitl [Hl]
    · inext
      iexists true
      simp only [↓reduceIte]
      iframe Hl HpI HpR
    wp_pures
    iapply HΦ
    iframe HpI HpR

/-- The game never releases a session, so a session completed while the long-term keys were
secret keeps its key secret. -/
@[rocq_alias cryptis.examples.iso_dh.wp_check_key_secrecy]
theorem wp_checkKeySecrecy (c : Val) (lcomp : Loc) (rl : Role) (si : SessInfo) :
    {{ cryptisCtx ∗ channel c ∗ inv gameN (gameInv lcomp si.init si.resp) ∗
        session (fun _ => iprop(False)) rl si }}
      hl(&checkKeySecrecy &c #lcomp &(encode (si.key : Term)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hctx, #Hc, #Hinv, #Hsess⟩ HΦ
  wp_rec
  wp_pures
  wp_bind (! _)
  iinv Hinv with ⟨%b, >Hl, Hb⟩
  wp_load
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · icases Hb with ⟨HsI, HsR⟩
    ihave #Hnc : ◇ □ (compromised rl si → False) $$ [#]
    · iapply secret_session $$ HsI HsR Hsess
    imod Hnc with #Hnc
    ihave #Hok := session_ok $$ Hsess Hnc
    imodintro
    isplitl [Hl HsI HsR]
    · inext
      iexists false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hl HsI HsR
    wp_pures
    wp_apply wp_waitForCompromise lcomp si.init si.resp $$ [] with -
    · iframe Hctx Hinv
    wp_pures
    wp_apply HL.wp_recv $$ Hc with %guess #Hg
    wp_pures
    wp_apply Assert.wp_assert
    wp_eq_term e
    · subst e
      ihave Hcontra := Hok $$ Hg
      wp_pures
      iexfalso
      iexact Hcontra
    · wp_pures
      imodintro
      isplit
      · ipureintro; rfl
      · inext
        iapply HΦ $$ [//]
  · imodintro
    isplitl [Hl Hb]
    · inext
      iexists true
      simp only [↓reduceIte]
      iframe Hl Hb
    wp_pures
    iapply HΦ $$ [//]

variable [IsoDHGS GF]

/-- The keys in the set of `rl` are the keys of sessions whose share of `rl` is marked. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dh_game_inv]
abbrev isoDHGameInv (rl : Role) (x : Term) : IProp GF :=
  iprop(∃ si : SessInfo, ⌜(si.key : Term) = x⌝ ∧ termMeta (si.shareOf rl) (gameN.@"fresh") ())

omit [IsoDHGS GF] in
@[rocq_alias cryptis.examples.iso_dh.iso_dh_game_fresh]
theorem isoDHGameInv_fresh (rl : Role) (si : SessInfo) {E : CoPset} (h : ↑(gameN.@"fresh") ⊆ E) :
    termToken (si.shareOf rl) E -∗
      freshTerm (isoDHGameInv (GF := GF) rl) si.key ∗
        termToken (si.shareOf rl) (E \ ↑(gameN.@"fresh")) := by
  iintro Htok
  icases (termToken_difference h).mp $$ Htok with ⟨Htok, Htok'⟩
  iframe Htok'
  unfold freshTerm
  isplit
  · iintro ⟨%si', %e, #Hm⟩
    obtain rfl := SessInfo.key_injective (Key.toTerm_injective e)
    iapply termMeta_token Std.LawfulSet.subset_refl $$ Htok Hm
  · imod termMeta_set () Std.LawfulSet.subset_refl $$ Htok with #Hm
    iintro !> !>
    iexists si
    iframe Hm
    ipureintro; rfl

variable [TicketLock.TicketLockG GF]

@[rocq_alias cryptis.examples.iso_dh.wp_do_init_loop]
theorem wp_doInitLoop (c : Val) (lcomp : Loc) (vset : Val) (skI skR : Key .sign) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗
        isoDHPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) ∗ minted skI ∗
        minted skR ∗ inv gameN (gameInv lcomp skI skR) ∗ isLockTermSet (isoDHGameInv .init) vset }}
      hl(&doInitLoop &c #lcomp &vset &(encode skI) &(encode (Spec.pkey skR)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hiso, #HNφ, #HmI, #HmR, #Hinv, #Hset⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %pkR' #HpkR'
  wp_pures
  wp_apply HL.wp_isVerifyKey pkR' $$ []
  · iapply isPublic_minted $$ HpkR'
  isplit
  on_goal 2 => (wp_pures; iapply HΦ $$ [//])
  iintro %skR' %rfl #HmR'
  wp_pures
  wp_apply wp_initiator c skI skR' gameN (fun _ _ => iprop(True)) (fun _ => iprop(False))
      (fun si => termToken si.initShare (⊤ \ ↑isoDHN)) iprop(True) $$ [] with %r Hr
  · iframe Hc Hctx Hiso HNφ HmI HmR'
    isplit
    · itrivial
    · iintro %a %gb Htok !>
      iframe Htok
  icases Hr with (⟨%rfl, -⟩ | ⟨%a, %gb, %rfl, #Hsess, Htok, -⟩) <;> wp_expr_simp
  · wp_pures
    iapply HΦ $$ [//]
  let si : SessInfo := ⟨skI, skR', (int 0).exp a, gb, gb.exp a⟩
  icases isoDHGameInv_fresh .init si (E := ⊤ \ ↑isoDHN) (by solve_ndisj) $$ Htok with ⟨Hfresh, -⟩
  wp_pures
  wp_apply HL.wp_addFreshLockTermSet (isoDHGameInv .init) ↑si.key vset $$ [Hfresh] with -
  · iframe Hset Hfresh
  wp_pures
  wp_eq_term e
  · obtain rfl := Key.pkey_injective e
    wp_pures
    wp_apply wp_checkKeySecrecy c lcomp .init si $$ [] with -
    · iframe Hctx Hc Hinv Hsess
    wp_pures
    iapply HΦ $$ [//]
  · wp_pures
    iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.iso_dh.wp_do_init]
theorem wp_doInit (c : Val) (lcomp : Loc) (skI skR : Key .sign) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗
        isoDHPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) ∗ minted skI ∗
        minted skR ∗ inv gameN (gameInv lcomp skI skR) }}
      hl(&doInit &c #lcomp &(encode skI) &(encode (Spec.pkey skR)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hiso, #HNφ, #HmI, #HmR, #Hinv⟩ HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_newLockTermSet (isoDHGameInv .init) $$ [//] with %vset #Hset
  wp_pures
  iapply wp_doInitLoop c lcomp vset skI skR $$ [] HΦ
  iframe Hc Hctx Hiso HNφ HmI HmR Hinv Hset

@[rocq_alias cryptis.examples.iso_dh.wp_do_resp_loop]
theorem wp_doRespLoop (c : Val) (lcomp : Loc) (vset : Val) (skI skR : Key .sign) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗
        isoDHPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) ∗ minted skI ∗
        minted skR ∗ inv gameN (gameInv lcomp skI skR) ∗ isLockTermSet (isoDHGameInv .resp) vset }}
      hl(&doRespLoop &c #lcomp &vset &(encode skR) &(encode (Spec.pkey skI)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hiso, #HNφ, #HmI, #HmR, #Hinv, #Hset⟩ HΦ
  iloeb as IH generalizing %Φ
  wp_rec
  wp_pures
  wp_apply wp_fork $$ [HΦ]
  on_goal 2 => iapply IH $$ %(fun _ => iprop(True)) [//]
  wp_pures
  wp_apply wp_responder c skR gameN (fun _ _ => iprop(True)) (fun _ => iprop(False))
      (fun si => termToken si.respShare (⊤ \ ↑isoDHN)) $$ [] with %r Hr
  · iframe Hc Hctx Hiso HNφ HmR
    iintro %skI' %ga %b Htok !>
    iframe Htok
  icases Hr with (%rfl | ⟨%skI', %ga, %b, %rfl, #Hsess, Htok, -⟩) <;> wp_expr_simp
  · wp_pures
    iapply HΦ $$ [//]
  let si : SessInfo := ⟨skI', skR, ga, (int 0).exp b, ga.exp b⟩
  wp_pures
  icases isoDHGameInv_fresh .resp si (E := ⊤ \ ↑isoDHN) (by solve_ndisj) $$ Htok with ⟨Hfresh, -⟩
  wp_apply HL.wp_addFreshLockTermSet (isoDHGameInv .resp) ↑si.key vset $$ [Hfresh] with -
  · iframe Hset Hfresh
  wp_pures
  wp_eq_term e
  · obtain rfl := Key.pkey_injective e
    wp_pures
    wp_apply wp_checkKeySecrecy c lcomp .resp si $$ [] with -
    · iframe Hctx Hc Hinv Hsess
    wp_pures
    iapply HΦ $$ [//]
  · wp_pures
    iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.iso_dh.wp_do_resp]
theorem wp_doResp (c : Val) (lcomp : Loc) (skI skR : Key .sign) :
    {{ channel c ∗ cryptisCtx ∗ isoDHCtx ∗
        isoDHPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) ∗ minted skI ∗
        minted skR ∗ inv gameN (gameInv lcomp skI skR) }}
      hl(&doResp &c #lcomp &(encode skR) &(encode (Spec.pkey skI)))
    {{ RET hl_val(#()); True }} := by
  iintro %Φ ⟨#Hc, #Hctx, #Hiso, #HNφ, #HmI, #HmR, #Hinv⟩ HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_newLockTermSet (isoDHGameInv .resp) $$ [//] with %vset #Hset
  wp_pures
  iapply wp_doRespLoop c lcomp vset skI skR $$ [] HΦ
  iframe Hc Hctx Hiso HNφ HmI HmR Hinv Hset

@[rocq_alias cryptis.examples.iso_dh.wp_game]
theorem wp_game (c : Val) :
    cryptisCtx -∗ channel c -∗ isoDHCtx -∗
      isoDHPred gameN (fun _ _ => iprop(True)) (fun _ => iprop(False)) -∗
      WP hl(&game &c) {{ _v, True }} := by
  iintro #Hctx #Hc #Hiso #HNφ
  wp_rec
  wp_pures
  wp_apply HL.wp_mkSignKey $$ Hctx with %skI #HmI HsecI -
  wp_pures
  wp_apply HL.wp_mkSignKey $$ Hctx with %skR #HmR HsecR -
  wp_pures
  wp_apply HL.wp_pkey
  wp_pures
  wp_apply HL.wp_pkey
  wp_pures
  wp_alloc lcomp with Hl
  imod inv_alloc gameN ⊤ (gameInv lcomp skI skR) $$ [Hl HsecI HsecR] with #Hinv
  · inext
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hl HsecI HsecR
  wp_pures
  wp_apply HL.wp_send $$ Hc []
  · iapply (isPublic_pkey_sign skI).mpr $$ HmI
  wp_pures
  wp_apply HL.wp_send $$ Hc []
  · iapply (isPublic_pkey_sign skR).mpr $$ HmR
  wp_pures
  wp_apply wp_fork $$ []
  · wp_pures
    wp_apply wp_fork $$ []
    · wp_pures
      wp_apply wp_fork $$ []
      · itrivial
      wp_apply wp_compromiseLongTermKeys c lcomp skI skR $$ [] with -
      · iframe Hctx Hc Hinv
      itrivial
    wp_apply wp_doResp c lcomp skI skR $$ [] with -
    · iframe Hc Hctx Hiso HNφ HmI HmR Hinv
    itrivial
  wp_apply wp_doInit c lcomp skI skR $$ [] with -
  · iframe Hc Hctx Hiso HNφ HmI HmR Hinv
  itrivial

end

#rocq_ignore cryptis.examples.iso_dh.F
  "Subsumed by BundledGFunctors typeclass synthesis: iso_dh_secure holds for any suitable GF"

/-- The game never gets stuck: the assertions of `checkKeySecrecy` and of the key sets hold. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dh_secure]
theorem iso_dh_secure {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] [CryptisGpreS GF]
    [IsoDHGpreS GF] {σ₁ σ₂ : State} {t₂ : List Exp} {e₂ : Exp}
    (h : ([hl(&HL.runNetwork &game)], σ₁) -·->ₜₚ* (t₂, σ₂)) (he : e₂ ∈ t₂) :
    PrimStep.NotStuck (e₂, σ₂) := by
  let := CryptisGpreS.tlock (GF := GF)
  refine (cryptis_adequacy (GF := GF) game σ₁ (fun _ => True) fun c => ?_).adequate_not_stuck
    t₂ σ₂ e₂ rfl h he
  iintro #Hctx #Hc ⟨-, Htok, -⟩
  imod isoDHGS_alloc (E := ⊤) CoPset.subseteq_top $$ Htok with ⟨%_, #Hiso, HisoTok, -⟩
  imod isoDHPred_set gameN (fun _ _ => iprop(True)) (fun _ => iprop(False))
    CoPset.subseteq_top $$ HisoTok with ⟨#HNφ, -⟩
  iapply wp_game $$ Hctx Hc Hiso HNφ

end CryptisExamples.IsoDH
