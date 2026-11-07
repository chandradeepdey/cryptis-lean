module

public import CryptisExamples.HMQV.Impl
public import CryptisExamples.HMQV.Proofs

/-! The HMQV case study.

HMQV-C, an authenticated Diffie–Hellman exchange in three messages. Each party has a long-term
key pair `p, P = g^p`, and its public key is its identity:

```
A → B : g^a, P_A
B → A : g^b, H(σ, N)
A → B : H'(σ, N)
```

Both parties compute the HMQV key `σ` from their own long-term and ephemeral private keys and
the peer's public keys. The two hashes of `σ` prove to each party that its peer computed the same
key, and the session key is a third hash of `σ`. This module gathers the implementation and the
specifications of both roles. The games under `CryptisExamples.HMQV.Games` use them to prove
forward secrecy, key independence, resistance to key-compromise impersonation, and injective
agreement. -/
