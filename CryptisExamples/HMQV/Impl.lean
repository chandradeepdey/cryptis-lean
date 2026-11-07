module

public import Cryptis.Lib.HMQV
public import Cryptis.Lib.ListMatch

/-! The HMQV-C protocol.

HMQV-C is the three-message variant of HMQV. Each party `i` has a long-term key pair
`pᵢ, Pᵢ = g^pᵢ`, and its public key is its identity:

```
A → B : g^a, P_A
B → A : g^b, H(σ, N)
A → B : H'(σ, N)
```

Both parties return `deriveSEncKey (H''(σ))`, where `σ` is the HMQV key `hmqvK` computed from
the long-term and ephemeral keys of the parties. The ephemeral private keys are deleted right
away. Checking the hashes `H(σ, N)` and `H'(σ, N)` shows each party that its peer could compute
`σ` too, so the key is authentic. The namespace `N` tags the use of the protocol. Each party aborts
if the long-term key it uses for its peer, or `σ`, is the unit of the group; otherwise `σ` binds
the peer's keys even when nobody vetted the peer's long-term key (`hmqvK_inj'`). -/

@[expose] public section

namespace CryptisExamples.HMQV

open Cryptis Iris Iris.HeapLang

/-- The namespace of the protocol. -/
@[rocq_alias cryptis.examples.hmqv.hmqvN]
def hmqvN : Namespace := nroot.@"hmqv"

/-- The hash of a list of terms, tagged with `hmqvN.@c`. -/
@[rocq_alias cryptis.examples.hmqv.H]
def tagHash (c : String) : Val := hl_val%
  λ xs, &HL.hash (&HL.tag &(encode (Term.ofNamespace (hmqvN.@c))) (&HL.termOfList xs))

/-- The generator of the Diffie–Hellman group. -/
@[rocq_alias cryptis.examples.hmqv.g]
def g : Term := .int 0

#rocq_ignore cryptis.examples.hmqv.one "The unit of the group, ↑(1 : Term.G)"

/-- A long-term key pair. -/
@[rocq_alias cryptis.examples.hmqv.mk_lt_key]
def mkLtKey : Val := hl_val%
  λ _, let p := &HL.mkNonce #(); (p, &HL.texp &(encode g) p)

/-- The session key derived from the HMQV key `σ`. -/
@[rocq_alias cryptis.examples.hmqv.session_key]
def sessionKey : Val := hl_val% λ σ, &HL.deriveSEncKey (&(tagHash "key") [σ])

/-- The initiator, with long-term key pair `pa`, `Pa`, talking to the peer with long-term public
key `Pb` for the usage `N`. It returns the session key, if the run succeeds. -/
@[rocq_alias cryptis.examples.hmqv.initiator]
def initiator : Val := hl_val%
  λ c pa Pa Pb N,
    guard: ~ (&HL.eqTerm Pb &(encode (↑(1 : Term.G) : Term))) in
    let xa := &HL.mkNonce #();
    let Xa := &HL.texp &(encode g) xa;
    &HL.send c (&HL.termOfList [Xa, Pa]);
    bind: m2 := &HL.listOfTerm (&HL.recv c) in
    list_match [Xb, Ab] := m2 in
    let σ := &(HL.hmqvKE hmqvN "init" "resp") pa xa Pa Xa Pb Xb;
    guard: ~ (&HL.eqTerm σ &(encode (↑(1 : Term.G) : Term))) in
    guard: &HL.eqTerm Ab (&(tagHash "m2") [σ, N]) in
    &HL.send c (&(tagHash "m3") [σ, N]);
    some(&sessionKey σ)

/-- Receive the first message: the ephemeral and long-term public keys of the initiator. Nothing
ties a claimed long-term key to its owner, so whether to answer it is the caller's decision. -/
@[rocq_alias cryptis.examples.hmqv.responder_listen]
def responderListen : Val := hl_val%
  λ c,
    &doUntil (λ _,
      bind: m1 := &HL.listOfTerm (&HL.recv c) in
      list_match [Xa, Pa] := m1 in
      some((Xa, Pa)))

/-- The responder, with long-term key pair `pb`, `Pb`, answering the initiator with public keys
`Xa`, `Pa`. It returns the HMQV key. The key is fixed once the responder has answered, and the last
message only confirms it, so a caller may use the key before `responderFinish`. -/
@[rocq_alias cryptis.examples.hmqv.responder_accept]
def responderAccept : Val := hl_val%
  λ c pb Pb Xa Pa N,
    guard: ~ (&HL.eqTerm Pa &(encode (↑(1 : Term.G) : Term))) in
    let xb := &HL.mkNonce #();
    let Xb := &HL.texp &(encode g) xb;
    let σ := &(HL.hmqvKE hmqvN "resp" "init") pb xb Pb Xb Pa Xa;
    guard: ~ (&HL.eqTerm σ &(encode (↑(1 : Term.G) : Term))) in
    &HL.send c (&HL.termOfList [Xb, &(tagHash "m2") [σ, N]]);
    some(σ)

/-- Receive the confirmation of the initiator for the HMQV key `σ`, and return the session key. -/
@[rocq_alias cryptis.examples.hmqv.responder_finish]
def responderFinish : Val := hl_val%
  λ c σ N,
    let Aa := &HL.recv c;
    guard: &HL.eqTerm Aa (&(tagHash "m3") [σ, N]) in
    some(&sessionKey σ)

/-- `responderAccept` followed by `responderFinish`. -/
@[rocq_alias cryptis.examples.hmqv.responder_confirm]
def responderConfirm : Val := hl_val%
  λ c pb Pb Xa Pa N,
    bind: σ := &responderAccept c pb Pb Xa Pa N in
    &responderFinish c σ N

end CryptisExamples.HMQV
