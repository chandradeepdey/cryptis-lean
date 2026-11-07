module

public import Cryptis.Primitives
public import Cryptis.Lib.ListMatch

/-! The Needham–Schroeder–Lowe protocol.

An initiator `I` and a responder `R` agree on a session key by exchanging nonces, each encrypted
under the public key of its recipient:

```
I → R : {nI, pkI}@pkR
R → I : {nI, nR, pkR}@pkI
I → R : {nR}@pkR
```

Each message is encrypted with its own tag under `nslN`, and the session key is derived from both
public keys and both nonces. -/

@[expose] public section

namespace CryptisExamples.NSL

open Cryptis Iris Iris.HeapLang

/-- The namespace of the protocol. -/
@[rocq_alias cryptis.examples.nsl.nslN]
def nslN : Namespace := nroot.@"nsl"

/-- The initiator, with secret key `skI`, talking to the responder with public key `pkR`. It
returns the session key, if the run succeeds. -/
@[rocq_alias cryptis.examples.nsl.init]
def init : Val := hl_val%
  λ c skI pkR,
    let pkI := &HL.pkey skI;
    let nI := &HL.mkNonce #();
    let m1 := &HL.aenc pkR &(encode (Term.ofNamespace (nslN.@"m1"))) (&HL.termOfList [nI, pkI]);
    &HL.send c m1;
    bind: m2 := &HL.adec skI &(encode (Term.ofNamespace (nslN.@"m2"))) (&HL.recv c) in
    bind: m2 := &HL.listOfTerm m2 in
    list_match [nI', nR, pkR'] := m2 in
    guard: &HL.eqTerm nI' nI && &HL.eqTerm pkR' pkR in
    let m3 := &HL.aenc pkR &(encode (Term.ofNamespace (nslN.@"m3"))) nR;
    &HL.send c m3;
    let sessKey := &HL.deriveSEncKey (&HL.termOfList [pkI, pkR, nI, nR]);
    some(sessKey)

/-- The responder, with secret key `skR`. It returns the public key of its peer and the session
key, if the run succeeds. -/
@[rocq_alias cryptis.examples.nsl.resp]
def resp : Val := hl_val%
  λ c skR,
    let pkR := &HL.pkey skR;
    bind: m1 := &HL.adec skR &(encode (Term.ofNamespace (nslN.@"m1"))) (&HL.recv c) in
    bind: m1 := &HL.listOfTerm m1 in
    list_match [nI, pkI] := m1 in
    guard: &HL.isAEncKey pkI in
    let nR := &HL.mkNonce #();
    let m2 := &HL.aenc pkI &(encode (Term.ofNamespace (nslN.@"m2"))) (&HL.termOfList [nI, nR, pkR]);
    &HL.send c m2;
    bind: m3 := &HL.adec skR &(encode (Term.ofNamespace (nslN.@"m3"))) (&HL.recv c) in
    guard: &HL.eqTerm m3 nR in
    let sessKey := &HL.deriveSEncKey (&HL.termOfList [pkI, pkR, nI, nR]);
    some((pkI, sessKey))

end CryptisExamples.NSL
