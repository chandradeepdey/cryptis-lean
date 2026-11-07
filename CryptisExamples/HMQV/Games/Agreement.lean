module

public import Cryptis.Adequacy
public import Cryptis.Upstream.Iris.HeapLangAssert
public import Iris.Algebra.Lib.FracAuth
public import Iris.Algebra.LeibnizSet
public import Iris.HeapLang.Lib.Assert
public import Iris.HeapLang.Lib.Par
public import Iris.Std.GenSetsInstances
public import CryptisExamples.HMQV.Proofs

/-! The injective agreement game of HMQV.

Alice, the initiator, and Bob, the responder, run sessions in parallel until the attacker tells
each of them to stop. Each talks to whatever peer the attacker picks (Alice connects to the
identity that the attacker names, Bob answers the identity that the first message claims) and
only keeps track of the sessions with the other: Alice records the key of each session with Bob,
and Bob records the key of each session with Alice as soon as he has answered, noting whether
Alice confirmed it. Once all sessions are over, every key that Bob saw confirmed must be one of
Alice's keys, each of Alice's keys must be one that Bob recorded, and no list may repeat a key.
So each session that Bob completes with Alice matches one of hers, no two of his match the same
one, and the keys that Alice has but Bob did not see confirmed come from sessions that Bob did run
with her, but whose last message never reached him. `hmqv_agreement` shows that the game never
gets stuck, so these assertions hold.

- Ledgers: each session of a party commits the party to its key, and anyone may keep a witness of
  that commitment. Once the shares of all sessions are back, the committed keys are exactly the
  keys that the party recorded.
- Sessions: the programs of the game and the list functions that check the records.
- Proofs: in each session with the other, a party receives its peer's commitment to the key, which
  gives the inclusions between the lists of keys. Each key is owned through the share of its
  session, so no list repeats a key. `hmqv_agreement` concludes by adequacy. -/

@[expose] public section

namespace CryptisExamples.HMQV.Agreement

open Cryptis Iris Iris.BI Iris.HeapLang Iris.ProofMode Iris.ProgramLogic Language.Notation Term
  Iris.Std

/-! ### Ledgers -/

/-- The sets of keys that the parties commit to. -/
abbrev KeySet : Type := Std.ExtTreeSet Term compare

/-- The camera of the commitments of a party, split among its sessions. -/
abbrev CommitsF : COFE.OFunctorPre := constOF (FracAuth (A := LeibnizSet KeySet))

/-- The camera of the witnesses of the commitments of a party. -/
abbrev CommittedF : COFE.OFunctorPre := constOF (Auth (LeibnizSet KeySet))

/-- The ghost state of the ledgers. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.commitG]
class CommitG (GF : BundledGFunctors) where
  commits : ElemG GF CommitsF
  committed : ElemG GF CommittedF

attribute [reducible, instance] CommitG.commits CommitG.committed

#rocq_ignore cryptis.examples.hmqv.games.agreement.«commitΣ»
  "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore cryptis.examples.hmqv.games.agreement.subG_commitG
  "Subsumed by BundledGFunctors typeclass synthesis"

/-- The namespace of the game. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.gameN]
def gameN : Namespace := nroot.@"game"

section Ledger

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CommitG GF]
local bi (IProp GF)

/-- A party committed to the key `k`. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.committed]
def committed (γw : GName) (k : Term) : IProp GF :=
  iOwn (F := CommittedF) γw (◯ (.valid {k} : LeibnizSet KeySet))

instance committed_persistent (γw : GName) (k : Term) :
    Persistent (committed (GF := GF) γw k) := by
  unfold committed; infer_instance

/-- The share `q` of the commitments of a party, to the keys `X`. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.commits]
def commits (γ : GName) (q : Qp) (X : KeySet) : IProp GF :=
  iOwn (F := CommitsF) γ (◯F{q} (.valid X : LeibnizSet KeySet))

/-- The ledger of a party: once all shares of its commitments are back, the committed keys are
those of the shares. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.ledger]
def ledger (N : Namespace) (γ γw : GName) : IProp GF :=
  inv N iprop(∃ X : KeySet, iOwn (F := CommitsF) γ (●F (.valid X : LeibnizSet KeySet)) ∗
    iOwn (F := CommittedF) γw (● (.valid X : LeibnizSet KeySet)))

instance ledger_persistent (N : Namespace) (γ γw : GName) :
    Persistent (ledger (GF := GF) N γ γw) := by
  unfold ledger; infer_instance

@[rocq_alias cryptis.examples.hmqv.games.agreement.ledger_alloc]
theorem ledger_alloc (N : Namespace) :
    ⊢ |={⊤}=> ∃ γ γw, ledger (GF := GF) N γ γw ∗ commits γ 1 ∅ := by
  imod iOwn_alloc (F := CommitsF)
    ((●F (.valid ∅ : LeibnizSet KeySet)) • ◯F (.valid ∅ : LeibnizSet KeySet))
    (FracAuth.valid trivial) with ⟨%γ, H⟩
  icases iOwn_op.mp $$ H with ⟨Ha, Hf⟩
  imod iOwn_alloc (F := CommittedF) (● (.valid ∅ : LeibnizSet KeySet))
    (Auth.auth_valid.mpr trivial) with ⟨%γw, Hw⟩
  imod inv_alloc N ⊤ iprop(∃ X : KeySet,
      iOwn (F := CommitsF) γ (●F (.valid X : LeibnizSet KeySet)) ∗
      iOwn (F := CommittedF) γw (● (.valid X : LeibnizSet KeySet))) $$ [Ha Hw] with #Hinv
  · inext
    iexists ∅
    iframe Ha Hw
  imodintro
  iexists γ, γw
  unfold ledger commits
  iframe Hinv Hf

@[rocq_alias cryptis.examples.hmqv.games.agreement.commits_split]
theorem commits_split (γ : GName) (q : Qp) :
    commits (GF := GF) γ q ∅ ⊢ commits γ q.half ∅ ∗ commits γ q.half ∅ := by
  unfold commits
  refine .trans (.of_eq ?_) iOwn_op.mp
  rw [← FracAuth.frag_op, LeibnizSet.op_union, LawfulSet.union_empty_left, Qp.half_add_half]

@[rocq_alias cryptis.examples.hmqv.games.agreement.commits_join]
theorem commits_join (γ : GName) (q : Qp) (X₁ X₂ : KeySet) :
    commits (GF := GF) γ q.half X₁ ∗ commits γ q.half X₂ ⊢ commits γ q (X₁ ∪ X₂) := by
  unfold commits
  refine iOwn_op.mpr.trans (.of_eq ?_)
  rw [← FracAuth.frag_op, LeibnizSet.op_union, Qp.half_add_half]

#rocq_ignore cryptis.examples.hmqv.games.agreement.commit_update
  "Inlined in commit, as LocalUpdate.op_discrete"

@[rocq_alias cryptis.examples.hmqv.games.agreement.commit]
theorem commit (N : Namespace) (γ γw : GName) (q : Qp) (k : Term) :
    ledger N γ γw -∗ commits (GF := GF) γ q ∅ ={⊤}=∗ commits γ q {k} ∗ committed γw k := by
  unfold ledger commits committed
  iintro #Hinv Hf
  iinv Hinv with ⟨%X, >Ha, >Hw⟩
  have hup := LocalUpdate.op_discrete (.valid X : LeibnizSet KeySet) (.valid ∅) (.valid {k})
    fun _ => trivial
  rw [LeibnizSet.op_union, LeibnizSet.op_union, LawfulSet.union_empty_right] at hup
  imod iOwn_update (F := CommitsF) (FracAuth.update hup) $$ [Ha Hf] with H
  · iapply iOwn_op.mpr
    iframe Ha Hf
  icases iOwn_op.mp $$ H with ⟨Ha, Hf⟩
  imod iOwn_update (F := CommittedF) (Auth.auth_update_alloc hup) $$ Hw with H
  icases iOwn_op.mp $$ H with ⟨Hw, #Hk⟩
  imodintro
  isplitl [Ha Hw]
  · inext
    iexists {k} ∪ X
    iframe Ha Hw
  iframe Hf Hk

@[rocq_alias cryptis.examples.hmqv.games.agreement.commits_full]
theorem commits_full (N : Namespace) (γ γw : GName) (X : KeySet) (ks : List Term) :
    ledger N γ γw -∗ commits (GF := GF) γ 1 X -∗ ([∗list] k ∈ ks, committed γw k) ={⊤}=∗
      ⌜∀ k ∈ ks, k ∈ X⌝ := by
  unfold ledger commits
  iintro #Hinv Hf #Hks
  iinv Hinv with ⟨%X', >Ha, >Hw⟩
  icombine Ha Hf gives %h
  obtain rfl : X' = X := LeibnizSet.valid.inj (FracAuth.agree h)
  ihave %hks : ⌜∀ k ∈ ks, k ∈ X'⌝ $$ [Hw]
  · iintro %k %hk
    ihave #Hk := BigSepL.bigSepL_mem hk $$ Hks
    unfold committed
    icombine Hw Hk gives %h
    ipureintro
    exact (LeibnizSet.included_iff_subset _ _).mp (Auth.auth_both_valid_discrete.mp h).1 k
      (mem_singleton.mpr rfl)
  imodintro
  isplitl [Ha Hw]
  · inext
    iexists X'
    iframe Ha Hw
  ipureintro
  exact hks

@[rocq_alias cryptis.examples.hmqv.games.agreement.committed_confirmed]
theorem committed_confirmed (γw : GName) (rs : List (Term × Bool)) :
    ([∗list] r ∈ rs, if r.2 then committed (GF := GF) γw r.1 else True) -∗
      [∗list] k ∈ (rs.filter Prod.snd).map Prod.fst, committed γw k := by
  induction rs with
  | nil =>
    iintro -
    simp only [List.filter_nil, List.map_nil]
    iapply BigSepL.bigSepL_nil.mpr
    itrivial
  | cons r rs ih =>
    obtain ⟨k, b⟩ := r
    iintro ⟨Hr, Hrs⟩
    cases b
    · simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]
      iapply ih $$ Hrs
    · simp only [List.filter_cons, ↓reduceIte, List.map_cons]
      isplitl [Hr]
      · iexact Hr
      · iapply ih $$ Hrs

end Ledger

/-- The set of the keys of a list. -/
def keySet (ks : List Term) : KeySet := ks.foldr (fun k X => {k} ∪ X) ∅

@[simp]
theorem keySet_nil : keySet [] = ∅ := rfl

@[simp]
theorem keySet_singleton (k : Term) : keySet [k] = {k} := LawfulSet.union_empty_right

theorem keySet_append (ks₁ ks₂ : List Term) : keySet (ks₁ ++ ks₂) = keySet ks₁ ∪ keySet ks₂ := by
  induction ks₁ with
  | nil => exact LawfulSet.union_empty_left.symm
  | cons k ks ih =>
    simp only [List.cons_append, keySet, List.foldr_cons] at ih ⊢
    rw [ih, LawfulSet.union_assoc]

theorem mem_keySet {k : Term} {ks : List Term} : k ∈ keySet ks ↔ k ∈ ks := by
  induction ks with
  | nil => simp [LawfulSet.mem_empty]
  | cons k' ks ih =>
    simp only [keySet, List.foldr_cons, LawfulSet.mem_union, LawfulSet.mem_singleton, List.mem_cons]
      at ih ⊢
    rw [ih]

/-! ### Sessions -/

/-- What each party receives from its peer in the game: the peer's commitment to the key. Each
party only commits in the sessions that it runs with the other. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.agree_pred]
abbrev agreePred {GF : BundledGFunctors} [CommitG GF] (γaw γbw : GName) (Pa Pb : Term)
    (si : SessInfo) : Role → IProp GF
  | .resp => iprop(⌜si.resp = Pb⌝ → committed γaw si.key)
  | .init => iprop(⌜si.init = Pa⌝ → committed γbw si.key)

/-- Run sessions `f` in parallel until the attacker sends `0`, and return the list of the results
of the sessions that return one. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.sessions]
def sessions : Val := hl_val%
  rec loop c f :=
    if &HL.eqTerm (&HL.recv c) &(encode (Term.int 0)) then none()
    else
      let r := (f #() ‖ loop c f);
      match fst(r) with
      | none() => snd(r)
      | some(k) => some((k, snd(r)))

/-- Alice contacts whatever identity the attacker names, but only records the sessions with
Bob. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.alice_session]
def aliceSession : Val := hl_val%
  λ c pa Pa Pb,
    let P := &HL.recv c;
    if &HL.eqTerm P Pb then &initiator c pa Pa Pb &(encode (ofNamespace gameN))
    else (&initiator c pa Pa P &(encode (ofNamespace gameN)); none())

/-- Bob answers any identity, but only records the sessions with Alice, along with whether she
confirmed them. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.bob_session]
def bobSession : Val := hl_val%
  λ c pb Pb Pa,
    let m1 := &responderListen c;
    let X := fst(m1);
    let P := snd(m1);
    if &HL.eqTerm P Pa then
      (bind: σ := &responderAccept c pb Pb X Pa &(encode (ofNamespace gameN)) in
       let k := &sessionKey σ;
       let r := &responderFinish c σ &(encode (ofNamespace gameN));
       some((k, match r with | none() => #false | some(_x) => #true)))
    else (&responderConfirm c pb Pb X P &(encode (ofNamespace gameN)); none())

/-- An equality test that takes a step, as `wp_memList` wants. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.teq]
def teq : Val := hl_val% λ x y, &HL.eqTerm x y

/-- Whether every element of `xs` is in `ys`. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.all_in]
def allIn : Val := hl_val%
  rec loop xs ys :=
    match xs with
    | none() => #true
    | some(p) => &memList &teq (fst(p)) ys && loop (snd(p)) ys

/-- Whether `xs` has no duplicates. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.no_dups]
def noDups : Val := hl_val%
  rec loop xs :=
    match xs with
    | none() => #true
    | some(p) => (~ (&memList &teq (fst(p)) (snd(p)))) && loop (snd(p))

/-- The key of one of Bob's records. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.rec_key]
def recKey : Val := hl_val% λ r, fst(r)

/-- Whether Alice confirmed one of Bob's records. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.rec_confirmed]
def recConfirmed : Val := hl_val% λ r, snd(r)

/-- The keys of Bob's records. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.answered]
def answered : Val := hl_val% λ rs, &mapList &recKey rs

/-- The keys of Bob's records that Alice confirmed. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.confirmed]
def confirmed : Val := hl_val% λ rs, &mapList &recKey (&filterList &recConfirmed rs)

/-- Create the long-term keys, run Alice's and Bob's sessions, and check their records. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.game]
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
    let res := (&sessions c (λ _, &aliceSession c pa Pa Pb) ‖
      &sessions c (λ _, &bobSession c pb Pb Pa));
    let ksa := fst(res);
    let ansb := &answered (snd(res));
    let confb := &confirmed (snd(res));
    assert(&allIn confb ksa && &allIn ksa ansb && &noDups ksa && &noDups ansb && &noDups confb)

section Lists

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_teq]
theorem wp_teq (t₁ t₂ : Term) :
    {{ True }} hl(&teq &(encode t₁) &(encode t₂)) {{ RET hl_val(#(decide (t₁ = t₂))); True }} := by
  iintro %Φ - HΦ
  wp_rec
  wp_pures
  wp_apply HL.wp_eqTerm
  iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_all_in]
theorem wp_allIn (ks₁ ks₂ : List Term) (h : ∀ k ∈ ks₁, k ∈ ks₂) :
    {{ True }} hl(&allIn &(encode ks₁) &(encode ks₂)) {{ RET hl_val(#true); True }} := by
  induction ks₁ with
  | nil =>
    iintro %Φ - HΦ
    wp_rec
    simp only [encode_nil]
    wp_pures
    iapply HΦ $$ [//]
  | cons k ks ih =>
    iintro %Φ - HΦ
    wp_rec
    simp only [encode_cons]
    wp_pures
    wp_apply wp_memList teq k ks₂ wp_teq $$ [//] with -
    rw [decide_eq_true (h k List.mem_cons_self)]
    wp_pures
    wp_apply ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) $$ [//] with -
    iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_no_dups]
theorem wp_noDups (ks : List Term) (h : ks.Nodup) :
    {{ True }} hl(&noDups &(encode ks)) {{ RET hl_val(#true); True }} := by
  induction ks with
  | nil =>
    iintro %Φ - HΦ
    wp_rec
    simp only [encode_nil]
    wp_pures
    iapply HΦ $$ [//]
  | cons k ks ih =>
    obtain ⟨hk, hks⟩ := List.nodup_cons.mp h
    iintro %Φ - HΦ
    wp_rec
    simp only [encode_cons]
    wp_pures
    wp_apply wp_memList teq k ks wp_teq $$ [//] with -
    rw [decide_eq_false hk]
    wp_pures
    wp_apply ih hks $$ [//] with -
    iapply HΦ $$ [//]

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_answered]
theorem wp_answered (rs : List (Term × Bool)) :
    {{ True }} hl(&answered &(encode rs)) {{ RET encode (rs.map Prod.fst); True }} := by
  have hf (r : Term × Bool) (_ : r ∈ rs) :
      [{ True }] hl(&recKey &(encode r)) [{ RET encode r.1; True }] := by
    iintro %Ψ - HΨ
    twp_rec
    simp only [encode_prod]
    twp_pures
    iapply HΨ $$ [//]
  iintro %Φ - HΦ
  wp_rec
  iapply twp.to_wp
  iapply twp_mapList Prod.fst recKey rs hf $$ [//]
  iexact HΦ

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_confirmed]
theorem wp_confirmed (rs : List (Term × Bool)) :
    {{ True }} hl(&confirmed &(encode rs))
    {{ RET encode ((rs.filter Prod.snd).map Prod.fst); True }} := by
  have hf (r : Term × Bool) :
      {{ True }} hl(&recConfirmed &(encode r)) {{ RET hl_val(#r.2); True }} := by
    iintro %Ψ - HΨ
    wp_rec
    simp only [encode_prod]
    wp_pures
    iapply HΨ $$ [//]
  have hg (r : Term × Bool) (_ : r ∈ rs.filter Prod.snd) :
      [{ True }] hl(&recKey &(encode r)) [{ RET encode r.1; True }] := by
    iintro %Ψ - HΨ
    twp_rec
    simp only [encode_prod]
    twp_pures
    iapply HΨ $$ [//]
  iintro %Φ - HΦ
  wp_rec
  wp_apply wp_filterList Prod.snd recConfirmed rs hf $$ [//] with -
  iapply twp.to_wp
  iapply twp_mapList Prod.fst recKey _ hg $$ [//]
  iexact HΦ

@[rocq_alias cryptis.examples.hmqv.games.agreement.NoDup_confirmed]
theorem nodup_confirmed {rs : List (Term × Bool)} (h : (rs.map Prod.fst).Nodup) :
    ((rs.filter Prod.snd).map Prod.fst).Nodup :=
  h.sublist ((List.filter_sublist).map _)

end Lists

section Proofs

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
local bi (IProp GF)

/-- A key of a session of role `rl`, owned through the session's share. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.owned]
abbrev owned (rl : Role) (k : Term) : IProp GF :=
  iprop(∃ si : SessInfo, ⌜k = ↑si.key⌝ ∗ ⌜sessionOf rl si⌝ ∗ termToken (si.shareOf rl) ↑gameN)

@[rocq_alias cryptis.examples.hmqv.games.agreement.owned_excl]
theorem owned_excl (rl : Role) (k : Term) : owned (GF := GF) rl k -∗ owned rl k -∗ False := by
  iintro ⟨%si₁, %rfl, %h₁, Htok₁⟩ ⟨%si₂, %e, %h₂, Htok₂⟩
  obtain rfl := sessionOf_key_inj h₁ h₂ (Key.toTerm_injective e)
  icases termToken_disj $$ Htok₁ Htok₂ with %h
  ipureintro
  exact (nclose_non_empty gameN) (LawfulSet.ext fun x => ⟨fun hx => absurd ⟨hx, hx⟩ (h x),
    fun hx => absurd hx LawfulSet.mem_empty⟩)

@[rocq_alias cryptis.examples.hmqv.games.agreement.owned_NoDup]
theorem owned_nodup (rl : Role) (ks : List Term) :
    ([∗list] k ∈ ks, owned (GF := GF) rl k) -∗ ⌜ks.Nodup⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; exact List.nodup_nil
  | cons k ks ih =>
    iintro ⟨Hk, Hks⟩
    ihave %hk : ⌜k ∉ ks⌝ $$ [Hk Hks]
    · iintro %hk
      icases BigSepL.bigSepL_mem_acc hk $$ Hks with ⟨Hk', -⟩
      iapply owned_excl $$ Hk Hk'
    ihave %hks := ih $$ Hks
    ipureintro
    exact List.nodup_cons.mpr ⟨hk, hks⟩

/-- The result of a session: its record, if any, with `Q` of it, and `R` of the list of its
records. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.session_res]
abbrev sessionRes {A : Type} [Encode A] (R : List A → IProp GF) (Q : A → IProp GF) (v : Val) :
    IProp GF :=
  iprop(∃ o : Option A, ⌜v = encode o⌝ ∗ match o with
    | some x => R [x] ∗ Q x
    | none => R [])

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_sessions]
theorem wp_sessions [Spawn.SpawnG GF] {A : Type} [Encode A] (c f : Val)
    (R : Qp → List A → IProp GF) (Q : A → IProp GF) (q : Qp) :
    channel c -∗ □ (∀ q, R q [] -∗ R q.half [] ∗ R q.half []) -∗
      □ (∀ q xs₁ xs₂, R q.half xs₁ -∗ R q.half xs₂ -∗ R q (xs₁ ++ xs₂)) -∗
      □ (∀ q, R q [] -∗ WP hl(&f #()) {{ sessionRes (R q) Q }}) -∗ R q [] -∗
      WP hl(&sessions &c &f)
        {{ v, ∃ xs : List A, ⌜v = encode xs⌝ ∗ R q xs ∗ [∗list] x ∈ xs, Q x }} := by
  iintro #Hc #Hsplit #Hjoin #Hf
  iloeb as IH generalizing %q
  iintro Hr
  wp_rec
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %t -
  wp_eq_term e
  · wp_pures
    imodintro
    iexists []
    iframe Hr
    isplit
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.mpr; itrivial
  icases Hsplit $$ Hr with ⟨Hr₁, Hr₂⟩
  wp_pures
  wp_apply Par.wp_par (sessionRes (R q.half) Q)
      (fun v => iprop(∃ xs : List A, ⌜v = encode xs⌝ ∗ R q.half xs ∗ [∗list] x ∈ xs, Q x))
    $$ [Hr₁] [Hr₂] with %v₁ %v₂ ⟨⟨%o, %rfl, Hr₁⟩, ⟨%xs, %rfl, Hr₂, HQ⟩⟩
  · iapply Hf $$ Hr₁
  · iapply IH $$ Hr₂
  inext
  cases o with
  | none =>
    wp_pures
    ihave Hr := Hjoin $$ %q %([] : List A) %xs Hr₁ Hr₂
    rw [List.nil_append]
    imodintro
    iexists xs
    iframe Hr HQ
    ipureintro; rfl
  | some x =>
    icases Hr₁ with ⟨Hr₁, Hx⟩
    wp_pures
    ihave Hr := Hjoin $$ %q %([x] : List A) %xs Hr₁ Hr₂
    rw [List.singleton_append]
    imodintro
    iexists x :: xs
    iframe Hr Hx HQ
    ipureintro; rfl

@[rocq_alias cryptis.examples.hmqv.games.agreement.owned_answered]
theorem owned_answered (rs : List (Term × Bool)) :
    ([∗list] r ∈ rs, owned (GF := GF) .resp r.1) -∗ [∗list] k ∈ rs.map Prod.fst, owned .resp k := by
  rw [BigSepL.bigSepL_map]
  iintro H
  iexact H

variable [CommitG GF] [HmqvGS GF]

/-- The usage of the protocol in the game: each party receives its peer's commitment to the key,
and no session is released. -/
abbrev gamePred (γaw γbw : GName) (pa pb : Nonce) : IProp GF :=
  hmqvPred gameN (agreePred γaw γbw (g.exp pa) (g.exp pb)) (fun _ => iprop(False))

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_alice_session]
theorem wp_aliceSession (c : Val) (γa γaw γbw : GName) (pa pb : Nonce) (q : Qp) :
    channel c -∗ cryptisCtx -∗ hmqvCtx -∗ gamePred γaw γbw pa pb -∗ hmqvKey pa -∗ hmqvKey pb -∗
      □ (isPublic (pa : Term) ↔ ▷ False) -∗ □ (isPublic (pb : Term) ↔ ▷ False) -∗
      ledger (gameN.@"alice") γa γaw -∗ commits γa q ∅ -∗
      WP hl(&aliceSession &c &(encode (pa : Term)) &(encode (g.exp pa)) &(encode (g.exp pb)))
        {{ sessionRes (fun ks => commits γa q (keySet ks))
            (fun k => iprop(owned .init k ∗ committed γbw k)) }} := by
  iintro #Hc #Hctx #Hhmqv #Hφ #Hpa #Hpb #Hspa #Hspb #Hled Hf
  wp_rec
  wp_pures
  wp_apply HL.wp_recv $$ Hc with %P #HP
  wp_eq_term e
  on_goal 2 =>
    wp_pures
    wp_apply wp_initiator c pa P gameN _ _ (fun _ => iprop(True)) iprop(True) $$ [] with %r -
    · iframe Hc Hctx Hhmqv Hφ Hpa HP
      isplit
      · itrivial
      · iintro %xa %Xb - !>
        isplit
        · iintro %h
          exact absurd h e
        · itrivial
    wp_pures
    imodintro
    iexists none
    isplit
    · ipureintro; rfl
    dsimp only
    rw [keySet_nil]
    iexact Hf
  subst e
  wp_pures
  iapply wp_fupd
  wp_apply wp_initiator c pa (g.exp pb) gameN _ _
      (fun si => iprop(commits γa q {(si.key : Term)} ∗ termToken si.initShare (⊤ \ ↑hmqvN)))
      (commits γa q ∅) $$ [Hf]
    with %r (⟨%rfl, Hf⟩ | ⟨%xa, %Xb, %rfl, #Hsess, ⟨Hf, Htok⟩, Hgift⟩)
  · iframe Hc Hctx Hhmqv Hφ Hpa HP
    isplit
    · iexact Hf
    · iintro %xa %Xb Htok
      imod commit _ γa γaw q ↑(initSI pa xa (g.exp pb) Xb).key $$ Hled Hf with ⟨Hf, #Hw⟩
      imodintro
      iframe Hf Htok
      iintro -
      iexact Hw
  · imodintro
    iexists none
    isplit
    · ipureintro; rfl
    dsimp only
    rw [keySet_nil]
    iexact Hf
  ihave #Hw : ◇ committed γbw (initSI pa xa (g.exp pb) Xb).key $$ [Hgift]
  · icases Hgift with (#Hcomp | Hw)
    · icases session_compromised $$ Hsess Hcomp with ⟨-, #Hl⟩
      imod Hl $$ %pb %rfl Hpb with #Hp
      ihave Hf := Hspb $$ Hp
      imod Hf with ⟨⟩
    · imodintro
      iapply Hw
      ipureintro; rfl
  imod Hw with #Hw
  imodintro
  iexists some ↑(initSI pa xa (g.exp pb) Xb).key
  isplit
  · ipureintro; rfl
  dsimp only
  rw [keySet_singleton]
  iframe Hf Hw
  iexists initSI pa xa (g.exp pb) Xb
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; exact initSession_initSI pa xa pb Xb
  iapply termToken_drop (by solve_ndisj) $$ Htok

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_bob_session]
theorem wp_bobSession (c : Val) (γb γaw γbw : GName) (pa pb : Nonce) (q : Qp) :
    channel c -∗ cryptisCtx -∗ hmqvCtx -∗ gamePred γaw γbw pa pb -∗ hmqvKey pa -∗ hmqvKey pb -∗
      □ (isPublic (pa : Term) ↔ ▷ False) -∗ □ (isPublic (pb : Term) ↔ ▷ False) -∗
      ledger (gameN.@"bob") γb γbw -∗ commits γb q ∅ -∗
      WP hl(&bobSession &c &(encode (pb : Term)) &(encode (g.exp pb)) &(encode (g.exp pa)))
        {{ sessionRes (fun rs : List (Term × Bool) => commits γb q (keySet (rs.map Prod.fst)))
            (fun r => iprop(owned .resp r.1 ∗ if r.2 then committed γaw r.1 else True)) }} := by
  iintro #Hc #Hctx #Hhmqv #Hφ #Hpa #Hpb #Hspa #Hspb #Hled Hf
  wp_rec
  wp_pures
  wp_apply wp_responderListen c $$ [] with %X %P ⟨#HX, #HP⟩
  · iframe Hc Hctx
  wp_pures
  wp_eq_term e
  on_goal 2 =>
    wp_pures
    wp_apply wp_responderConfirm c P X pb gameN _ _ (fun _ => iprop(True)) $$ [] with %r -
    · iframe Hc Hctx Hhmqv Hφ HP HX Hpb
      iintro %xb - !>
      isplit
      · iintro %h
        exact absurd h e
      · itrivial
    wp_pures
    imodintro
    iexists none
    isplit
    · ipureintro; rfl
    dsimp only
    rw [List.map_nil, keySet_nil]
    iexact Hf
  subst e
  wp_pures
  wp_apply wp_responderAccept c (g.exp pa) X pb gameN _ _
      (fun si => iprop(commits γb q {(si.key : Term)} ∗ termToken si.respShare (⊤ \ ↑hmqvN)))
      (commits γb q ∅) $$ [Hf]
    with %r (⟨%rfl, Hf⟩ | ⟨%xb, %rfl, Hstate, Hf, Htok⟩)
  · iframe Hc Hctx Hhmqv Hφ HP HX Hpb
    isplit
    · iexact Hf
    · iintro %xb Htok
      imod commit _ γb γbw q ↑(respSI (g.exp pa) X pb xb).key $$ Hled Hf with ⟨Hf, #Hw⟩
      imodintro
      iframe Hf Htok
      iintro -
      iexact Hw
  · wp_expr_simp
    wp_pures
    imodintro
    iexists none
    isplit
    · ipureintro; rfl
    dsimp only
    rw [List.map_nil, keySet_nil]
    iexact Hf
  wp_expr_simp
  ihave Hown : owned .resp ↑(respSI (g.exp pa) X pb xb).key $$ [Htok]
  · iexists respSI (g.exp pa) X pb xb
    isplit
    · ipureintro; rfl
    isplit
    · ipureintro; exact respSession_respSI pa X pb xb
    iapply termToken_drop (by solve_ndisj) $$ Htok
  wp_pures
  wp_apply wp_sessionKey
  wp_pures
  wp_apply wp_responderFinish c (g.exp pa) X pb xb gameN _ _ $$ [Hstate]
    with %r (%rfl | ⟨%rfl, #Hsess, Hgift⟩)
  · iframe Hc Hctx Hhmqv Hφ HP HX Hpb Hstate
  · wp_expr_simp
    wp_pures
    imodintro
    iexists some (↑(respSI (g.exp pa) X pb xb).key, false)
    isplit
    · ipureintro; rfl
    simp only [List.map_cons, List.map_nil, keySet_singleton, Bool.false_eq_true, ↓reduceIte]
    iframe Hf Hown
  ihave #Hw : ◇ committed γaw (respSI (g.exp pa) X pb xb).key $$ [Hgift]
  · icases Hgift with (#Hcomp | Hw)
    · icases session_compromised $$ Hsess Hcomp with ⟨-, #Hl⟩
      imod Hl $$ %pa %rfl Hpa with #Hp
      ihave Hf := Hspa $$ Hp
      imod Hf with ⟨⟩
    · imodintro
      iapply Hw
      ipureintro; rfl
  imod Hw with #Hw
  wp_expr_simp
  wp_pures
  imodintro
  iexists some (↑(respSI (g.exp pa) X pb xb).key, true)
  isplit
  · ipureintro; rfl
  simp only [List.map_cons, List.map_nil, keySet_singleton, ↓reduceIte]
  iframe Hf Hown Hw

@[rocq_alias cryptis.examples.hmqv.games.agreement.wp_game]
theorem wp_game [Spawn.SpawnG GF] (c : Val) :
    cryptisCtx -∗ channel c -∗ hmqvCtx -∗ hmqvToken ⊤ -∗ WP hl(&game &c) {{ _v, True }} := by
  iintro #Hctx #Hc #Hhmqv Htok
  wp_rec
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pa ⟨#Hpa, Hspa, #HPa, -⟩
  wp_pures
  wp_apply wp_mkLtKey $$ Hctx with %pb ⟨#Hpb, Hspb, #HPb, -⟩
  imod freeze_secret _ $$ Hspa with #Hspa
  imod freeze_secret _ $$ Hspb with #Hspb
  imod ledger_alloc (GF := GF) (gameN.@"alice") with ⟨%γa, %γaw, #Hleda, Hfa⟩
  imod ledger_alloc (GF := GF) (gameN.@"bob") with ⟨%γb, %γbw, #Hledb, Hfb⟩
  imod hmqvPred_set gameN (agreePred γaw γbw (g.exp pa) (g.exp pb)) (fun _ => iprop(False))
    CoPset.subseteq_top $$ Htok with ⟨#Hφ, -⟩
  wp_pures
  wp_apply HL.wp_send $$ Hc HPa
  wp_pures
  wp_apply HL.wp_send $$ Hc HPb
  wp_pures
  wp_apply Par.wp_par
      (fun v => iprop(∃ ks : List Term, ⌜v = encode ks⌝ ∗ commits γa 1 (keySet ks) ∗
        [∗list] k ∈ ks, owned .init k ∗ committed γbw k))
      (fun v => iprop(∃ rs : List (Term × Bool), ⌜v = encode rs⌝ ∗
        commits γb 1 (keySet (rs.map Prod.fst)) ∗
        [∗list] r ∈ rs, owned .resp r.1 ∗ if r.2 then committed γaw r.1 else True))
    $$ [Hfa] [Hfb] with %v₁ %v₂ ⟨⟨%ksa, %rfl, Hfa, Hownsa⟩, ⟨%rs, %rfl, Hfb, Hownsb⟩⟩
  · wp_pures
    iapply wp_sessions c _ (fun q ks => commits γa q (keySet ks))
      (fun k => iprop(owned .init k ∗ committed γbw k)) 1 $$ Hc [] [] [] [Hfa]
    · iintro !> %q Hf
      rw [keySet_nil]
      iapply commits_split $$ Hf
    · iintro !> %q %ks₁ %ks₂ H₁ H₂
      rw [keySet_append]
      iapply commits_join
      iframe H₁ H₂
    · iintro !> %q Hf
      rw [keySet_nil]
      wp_pures
      iapply wp_aliceSession $$ Hc Hctx Hhmqv Hφ Hpa Hpb Hspa Hspb Hleda Hf
    · rw [keySet_nil]
      iexact Hfa
  · wp_pures
    iapply wp_sessions c _
      (fun q (rs : List (Term × Bool)) => commits γb q (keySet (rs.map Prod.fst)))
      (fun r => iprop(owned .resp r.1 ∗ if r.2 then committed γaw r.1 else True)) 1
      $$ Hc [] [] [] [Hfb]
    · iintro !> %q Hf
      rw [List.map_nil, keySet_nil]
      iapply commits_split $$ Hf
    · iintro !> %q %rs₁ %rs₂ H₁ H₂
      rw [List.map_append, keySet_append]
      iapply commits_join
      iframe H₁ H₂
    · iintro !> %q Hf
      rw [List.map_nil, keySet_nil]
      wp_pures
      iapply wp_bobSession $$ Hc Hctx Hhmqv Hφ Hpa Hpb Hspa Hspb Hledb Hf
    · rw [List.map_nil, keySet_nil]
      iexact Hfb
  inext
  icases BigSepL.bigSepL_sep_eqv.mp $$ Hownsa with ⟨Hownsa, #Hwa⟩
  icases BigSepL.bigSepL_sep_eqv.mp $$ Hownsb with ⟨Hownsb, #Hwb⟩
  ihave %nda := owned_nodup .init ksa $$ Hownsa
  ihave Hownsb := owned_answered rs $$ Hownsb
  ihave %ndb := owned_nodup .resp _ $$ Hownsb
  ihave #Hwb := committed_confirmed γaw rs $$ Hwb
  imod commits_full _ γa γaw _ _ $$ Hleda Hfa Hwb with %suba
  imod commits_full _ γb γbw _ _ $$ Hledb Hfb Hwa with %subb
  wp_pures
  wp_apply wp_answered rs $$ [//] with -
  wp_pures
  wp_apply wp_confirmed rs $$ [//] with -
  wp_pures
  wp_apply Assert.wp_assert
  wp_apply wp_allIn _ _ (fun k hk => mem_keySet.mp (suba k hk)) $$ [//] with -
  wp_pures
  wp_apply wp_allIn _ _ (fun k hk => mem_keySet.mp (subb k hk)) $$ [//] with -
  wp_pures
  wp_apply wp_noDups _ nda $$ [//] with -
  wp_pures
  wp_apply wp_noDups _ ndb $$ [//] with -
  wp_pures
  wp_apply wp_noDups _ (nodup_confirmed ndb) $$ [//] with -
  isplit
  · ipureintro; rfl
  · inext
    itrivial

end Proofs

#rocq_ignore cryptis.examples.hmqv.games.agreement.F
  "Subsumed by BundledGFunctors typeclass synthesis: the theorem holds for any suitable GF"

/-- The game never gets stuck: the sessions that Bob completes with Alice match hers
injectively. -/
@[rocq_alias cryptis.examples.hmqv.games.agreement.hmqv_agreement]
theorem hmqv_agreement {GF : BundledGFunctors} [HeapLangGpreS .hasLC GF] [CryptisGpreS GF]
    [Spawn.SpawnG GF] [HmqvGpreS GF] [CommitG GF] {σ₁ σ₂ : State} {t₂ : List Exp} {e₂ : Exp}
    (h : ([hl(&HL.runNetwork &game)], σ₁) -·->ₜₚ* (t₂, σ₂)) (he : e₂ ∈ t₂) :
    PrimStep.NotStuck (e₂, σ₂) := by
  refine (cryptis_adequacy (GF := GF) game σ₁ (fun _ => True) fun c => ?_).adequate_not_stuck
    t₂ σ₂ e₂ rfl h he
  iintro #Hctx #Hc ⟨-, -, -, Htok⟩
  imod hmqvGS_alloc CoPset.subseteq_top $$ Htok with ⟨%_, #Hhmqv, Htok, -⟩
  iapply wp_game $$ Hctx Hc Hhmqv Htok

end CryptisExamples.HMQV.Agreement
