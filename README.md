# Cryptis in Lean: Cryptographic Reasoning in Separation Logic

[Cryptis](https://github.com/arthuraa/cryptis) is a separation logic for proving cryptographic
protocols correct against a Dolev-Yao-style symbolic attacker. This repository is its Lean port,
built on [Iris-Lean](https://github.com/leanprover-community/iris-lean) and
[Mathlib](https://github.com/leanprover-community/mathlib4). It covers the core library and the
`nsl`, `iso_dh` and `hmqv` case studies of Cryptis. [PORTING.md](PORTING.md) relates every Rocq
file to its Lean module, describes the conventions and design of the port, and lists the
Iris-Lean deficiencies that Cryptis works around.

## Core library

In the `Cryptis` directory you will find:

- `Lib/*`: Signed multisets, encodings of Lean data as HeapLang values, HeapLang list programs,
  ghost state indexed by namespaces and attached to ghost names, replicated state, mutable term
  sets, total-WP tactics, and the adequacy of total WPs.
- `Lib/EExp`, `Lib/DH`, `Lib/HMQV`: Extended exponents, Diffie–Hellman key shares, and the HMQV
  key, with its injectivity and secrecy properties.
- `Core/PreTerm/*`, `Core/Term/*`: Cryptographic terms, with exponentials and products in normal
  form; the group of exponents acting on the Diffie–Hellman group; sizes, nonces and subterms;
  and the functions that protocols use to build and inspect messages (`Spec`).
- `Core/Minted`, `Core/TermMeta`, `Core/Public`: Minted terms, meta data attached to terms, and
  the predicate `isPublic`, which says that the attacker may know a term.
- `Logic`, `Role`: The ghost state of Cryptis and its invariant, and the roles of a session.
- `Primitives/*`: HeapLang functions for manipulating cryptographic terms, encryption,
  signatures and network channels, with their specifications. Definition of the attacker.
- `Tactics`: Tactics for symbolically executing the HeapLang functions on terms.
- `Adequacy`: A program verified against the Cryptis invariant is safe when run against the
  attacker.
- `Upstream/*`: Generic additions to Iris-Lean, meant to be upstreamed.

## Case studies

In the `CryptisExamples` directory you will find:

- `NSL`: Needham–Schroeder–Lowe public-key protocol: a session key is public only if a
  participant's secret key is, and in the secrecy game (`nsl_secure`) keys stay unguessable and
  are never reused.
- `IsoDH`: ISO protocol with Diffie–Hellman key exchange and digital signatures, with a secrecy
  game (`iso_dh_secure`) that includes forward secrecy.
- `HMQV`: The three-message HMQV authenticated key exchange, with four games: forward secrecy
  (`hmqv_secure`), resistance to key-compromise impersonation (`hmqv_kci_secure`), key
  independence (`hmqv_key_independence`) and injective agreement (`hmqv_agreement`).

## Building

The Lean version is pinned in `lean-toolchain`, and Iris-Lean and Mathlib are pinned in
`lakefile.toml`. With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get   # download Mathlib's compiled files
lake build
```

Without a global elan install, `nix shell nixpkgs#elan --command lake build` works too. Set
`ELAN_HOME` to keep the toolchain somewhere other than `~/.elan`. The first build compiles the
Iris-Lean modules it needs.
