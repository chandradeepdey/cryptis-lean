module

public import Cryptis.Primitives.Notations
public import Cryptis.Primitives.PreTerm
public import Cryptis.Primitives.Comp
public import Cryptis.Primitives.Simple
public import Cryptis.Primitives.WithCryptis
public import Cryptis.Primitives.Attacker

/-! The HeapLang primitives of Cryptis: programs that build and inspect terms, create nonces and
keys, encrypt and sign, and communicate over a network controlled by the attacker.

The programs and their specs live in the namespace `Cryptis.HL`, so that `HL.enc`, `HL.hash` or
`HL.mkNonce` do not clash with the functions of `Term` and `Spec`. -/
