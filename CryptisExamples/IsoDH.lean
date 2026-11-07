module

public import CryptisExamples.IsoDH.Impl
public import CryptisExamples.IsoDH.Proofs

/-! The ISO Diffie–Hellman case study.

An initiator `I` and a responder `R` agree on a session key by exchanging Diffie–Hellman key
shares, each signing the shares with its long-term key:

```
I → R : g^a, pkI
R → I : {g^a, g^b, pkI, N}@skR
I → R : {g^a, g^b, pkR}@skI
```

`N` tags the use of the protocol, and the session key is derived from both public keys, both
shares and `g^ab`. This module gathers the implementation and the specifications of both roles;
the secrecy game is in `CryptisExamples.IsoDH.Game`. -/
