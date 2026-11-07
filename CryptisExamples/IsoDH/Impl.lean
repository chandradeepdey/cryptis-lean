module

public import Cryptis.Primitives
public import Cryptis.Lib.ListMatch

/-! The ISO Diffie–Hellman protocol.

An initiator `I` and a responder `R` agree on a session key by exchanging Diffie–Hellman key
shares, each signing both shares with its long-term key:

```
I → R : g^a, pkI
R → I : {g^a, g^b, pkI, N}@skR
I → R : {g^a, g^b, pkR}@skI
```

The generator `g` is the integer `0`, and `N` tags the use of the protocol that both sides agree
on. The session key is derived from both public keys, both shares and the shared secret `g^ab`. -/

@[expose] public section

namespace CryptisExamples.IsoDH

open Cryptis Iris Iris.HeapLang

/-- The namespace of the protocol. -/
@[rocq_alias cryptis.examples.iso_dh.iso_dhN]
def isoDHN : Namespace := nroot.@"iso_dh"

/-- The key share `g^k` of the exponent `k`. -/
@[rocq_alias cryptis.examples.iso_dh.mk_keyshare]
def mkKeyShare : Val := hl_val% λ k, &HL.texp (&HL.tint #(0 : Int)) k

/-- The initiator, with secret key `skI`, talking to the responder with public key `pkR` for
the usage tagged `N`. It returns the session key, if the run succeeds. -/
@[rocq_alias cryptis.examples.iso_dh.initiator]
def initiator : Val := hl_val%
  λ c skI pkR N,
    let pkI := &HL.pkey skI;
    let a := &HL.mkNonce #();
    let ga := &mkKeyShare a;
    let m1 := &HL.termOfList [ga, pkI];
    &HL.send c m1;
    bind: m2 := &HL.verify pkR &(encode (Term.ofNamespace (isoDHN.@"m2"))) (&HL.recv c) in
    bind: m2 := &HL.listOfTerm m2 in
    list_match [ga', gb, pkI', N'] := m2 in
    guard: &HL.eqTerm ga ga' && &HL.eqTerm pkI pkI' && &HL.eqTerm N N' in
    let gab := &HL.texp gb a;
    let secret := &HL.termOfList [pkI, pkR, ga, gb, gab];
    let m3Body := &HL.termOfList [ga, gb, pkR];
    let m3 := &HL.sign skI &(encode (Term.ofNamespace (isoDHN.@"m3"))) m3Body;
    &HL.send c m3;
    some(&HL.deriveSEncKey secret)

/-- Wait for a first message whose second component is a verification key. -/
@[rocq_alias cryptis.examples.iso_dh.responder_listen]
def responderListen : Val := hl_val%
  λ c,
    &doUntil (λ _,
      let m1 := &HL.recv c;
      bind: m1 := &HL.listOfTerm m1 in
      list_match [ga, pkI] := m1 in
      guard: &HL.isVerifyKey pkI in
      some((ga, pkI)))

/-- The responder, with secret key `skR`, answering the share `ga` of the initiator with public
key `pkI` for the usage tagged `N`. It returns the session key, if the run succeeds. -/
@[rocq_alias cryptis.examples.iso_dh.responder_confirm]
def responderConfirm : Val := hl_val%
  λ c skR ga pkI N,
    let pkR := &HL.pkey skR;
    let b := &HL.mkNonce #();
    let gb := &mkKeyShare b;
    let m2 := &HL.sign skR &(encode (Term.ofNamespace (isoDHN.@"m2")))
      (&HL.termOfList [ga, gb, pkI, N]);
    &HL.send c m2;
    bind: m3 := &HL.verify pkI &(encode (Term.ofNamespace (isoDHN.@"m3"))) (&HL.recv c) in
    bind: m3 := &HL.listOfTerm m3 in
    list_match [ga', gb', pkR'] := m3 in
    guard: &HL.eqTerm ga ga' && &HL.eqTerm gb gb' && &HL.eqTerm pkR pkR' in
    let gab := &HL.texp ga b;
    let secret := &HL.termOfList [pkI, pkR, ga, gb, gab];
    some(&HL.deriveSEncKey secret)

/-- The responder, with secret key `skR`, for the usage tagged `N`. It returns the public key of
its peer and the session key, if the run succeeds. -/
@[rocq_alias cryptis.examples.iso_dh.responder]
def responder : Val := hl_val%
  λ c skR N,
    let res := &responderListen c;
    let ga := fst(res);
    let pkI := snd(res);
    bind: kS := &responderConfirm c skR ga pkI N in
    some((pkI, kS))

end CryptisExamples.IsoDH
