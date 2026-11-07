# Porting Cryptis to Iris-Lean

This repository ports the core library of Cryptis (the opam package `rocq-cryptis`) and three of
its case studies, `nsl`, `iso_dh` and `hmqv` (from `rocq-cryptis-examples`), as of Cryptis
`master` at commit `21c72bc`. Later Cryptis commits are ported by diffing against `21c72bc`. The
session library `rocq-cryptis-session`, which is built on Actris, and the other case studies are
not ported.

The port builds on Lean `v4.35.0` (`lean-toolchain`), Mathlib `v4.35.0` and Iris-Lean at commit
`8293092f` (`lakefile.toml`, with the exact revisions in `lake-manifest.json`).

## What Lean and Mathlib bring

- **The term algebra is Mathlib algebra.** The exponents `Term.E` and the Diffie–Hellman values
  `Term.G` are Mathlib commutative groups, and exponentiation is a group action that distributes
  over the group product (`Core/Term/Algebra`). The group laws are Mathlib's lemmas, and `group`,
  `abel`, `simp` and `norm_cast` normalise Diffie–Hellman expressions that Rocq rewrites step by
  step.
- **Extended exponents form a ring.** `EExp` is the group ring of the exponents, an integral
  domain, and the Diffie–Hellman values form a module over it (`Lib/EExp`). The injectivity
  arguments of HMQV are equations in this ring, solved with `ring`, `linear_combination` and
  `mul_eq_zero` (`Lib/HMQV`).
- **Signed multisets come for free.** Built on Mathlib's multisets, a signed multiset has a
  canonical representation and is an additive group, so it needs neither an order on its elements
  nor a layer of sorting and cancellation (`Lib/SMS`).
- **One statement where Rocq has several.** The scalar and group products share one theory,
  parametrised by the kind of product, and the three kinds of keys are one type indexed by their
  functionality, so each pair or triple of Rocq lemmas is a single lemma.
- **Recursion and induction as the language provides them.** `isPublic` is defined by
  well-founded recursion on the size of terms, and Lean derives its unfolding equations
  (`Core/Public`). Terms and pre-terms register their own induction principles, so `induction t`
  recurses under exponentials and products. Orders and decidable equality come from core Lean's
  lawful `Ord` and Mathlib's `LinearOrder`.
- **Terms compute.** Equality and order on terms are decidable and the encodings into countable
  types are computable, so `decide` and `#eval` work on concrete terms.
- **Iris-Lean's libraries apply to Mathlib's data.** Big separating conjunctions over Mathlib's
  multisets and finite sets are Iris-Lean's own, with its lemmas and proof-mode support
  (`Upstream/Iris/BigSepMultiset`). Nonces and subterms are `Finset`s, and executions are
  Mathlib's reflexive-transitive closures.
- **Lean's metaprogramming.** The Cryptis tactics are macros over Iris-Lean's proof mode
  (`Tactics`), Cryptis extends the HeapLang linter with its own binding forms
  (`Lib/HeapLangLinter`), goals display the term groups as `E` and `G`, and every Rocq name
  resolves to its Lean counterpart through `rocq_alias`.

## Conventions

### Names and modules

- Each Rocq file `cryptis/a/b_c.v` is the module `Cryptis.A.BC`, with acronyms in capitals
  (`NSL`, `DH`, `HMQV`). The case studies of `examples/` are in the library `CryptisExamples`,
  which builds every module under `CryptisExamples/`.
- Every ported declaration carries `@[rocq_alias cryptis.<Rocq name>]`, Iris-Lean's porting
  attribute, which adds a deprecated alias `Rocq.cryptis.<Rocq name>` for the Lean name. Rocq
  `Module`s are part of the name and `Section`s are not, so `PreTerm.pre_term` keeps its module
  prefix. Where a core, Mathlib or Iris-Lean declaration already is the Rocq one, the alias is
  added with `attribute [rocq_alias cryptis.rem] List.erase`. `#rocq_ignore` records each Rocq
  declaration that has no counterpart, with the reason.
- Names follow Iris-Lean, which follows Mathlib: `UpperCamelCase` for types, `lowerCamelCase` for
  definitions and `snake_case` for lemmas. Constructors drop their Rocq prefix inside the
  namespace of their type: `PT1` is `PreTerm.op1` and `O2Pair` is `TermOp2.pair`.
- Rocq names that are Lean keywords get a new name: `public` is `isPublic`, sealing (`O2Seal`,
  `TSeal`, `seal`) is `sealed`, and `open` is `opened`.
- Proofs follow Iris-Lean's contribution guidelines (`docs/ai.md` there): each proof is short
  enough to explain and does not case-split more than its Rocq counterpart.

### Case studies

- Aliases are `cryptis.examples.<study>.<name>`, after the Rocq logical path, with no file
  component, as the library's aliases have none.
- A study with several games puts each in its own namespace, such as `CryptisExamples.HMQV.KCI`
  with aliases `cryptis.examples.hmqv.games.kci.<name>`, since their Rocq names collide.
- The persistent assumptions of a spec go in its precondition,
  `{{ channel c ∗ cryptisCtx ∗ … }} e {{ … }}`, as in the library. Rocq writes
  `P -∗ {{{ True }}} e {{{ … }}}`.
- Bundles of propositions (protocol contexts, message predicates, session and game invariants)
  are `abbrev`s, so that `icases`, `iexists`, `isplit` and `Persistent` see through them, as
  Rocq's type class search does. `iframe` and `simp` need an `unfold` first.
- A spec's result is chosen with a partial witness, `iapply Hpost $$ %(some (_, _))`, as Rocq's
  `iApply ("Hpost" $! (Some _))`; unification fills in the rest.
- The mintedness and publicity of a list literal are rewritten into conjunctions with
  `simp only [minted_ofList_cons_cons, minted_ofList_singleton]` (and the `isPublic_` versions).
  A nonce's `□ (isPublic a ↔ ▷ □ P a)` loses its inner `□` with
  `simp only [later_intuitionistically_eq]`.
- A later that Rocq eliminates with the credit of a pure step (`wp_pure _ credit:`) is stripped
  by a later pure step, which means splitting cases before that step (see the Iris-Lean
  deficiencies below).

## Organisation of the library

### Terms and their algebra

- **Pre-terms** (`Core/PreTerm/*`) are the raw syntax: a nested inductive `PreTerm` with
  constructors `op0`, `op1`, `op2` and `opN`, whose operator types (`TermOp0`, …, `TermOpN`)
  derive core Lean's `Ord`, with `Std.TransOrd` and `Std.LawfulEqOrd`, as Iris-Lean does for
  `Loc`. The order on `PreTerm` itself is `PreTerm.cmp`, written by hand: constructors are
  compared by `ctorIdx`, then fields from left to right, with lists compared by
  `List.compareLex`. It is the Rocq order, which the HeapLang comparison `leq_term` implements.
  `PreTerm` is a Mathlib `LinearOrder` (`LinearOrder.ofStd`), and its `DecidableEq` comes from
  this order. `PreTerm.ind` (Rocq `pre_term_ind`) is the default `induction` eliminator, with
  `∀ t ∈ ps` hypotheses for the subterm lists.
- **Normal forms.** A product stores its factors as lists sorted by `≤`: `toLists` sorts the parts
  of a signed multiset, and `IsCanonical` says that a pair of lists is sorted with no factor on
  both sides. `wf` is a structurally recursive `Bool`, so `wf pt = true` is decidable and
  proof-irrelevant. Recognisers are `Bool` functions (`isExp`, `isProd o`, …) with `_iff` lemmas.
- **One theory for both products.** The scalar product of exponents and the group product of
  Diffie–Hellman values share their theory, stated once for the operator `o : TermOpN`: Rocq's
  `is_mul`/`is_gmul`, `factors`/`gfactors`, `mul_aux`/`gmul_aux`, `mul`/`gmul` and
  `wf_factors`/`wf_gfactors` are `isProd o`, `factors o`, `prodAux o`, `prod o` and `WfFactors o`,
  and each pair of Rocq lemmas is one Lean lemma. The HeapLang programs follow (`HL.isProd o`,
  `HL.factors o`, `HL.prod o`).
- **Signed multisets** (`Lib/SMS`) are pairs of disjoint Mathlib `Multiset`s. The representation
  is canonical, so `SMS` needs no order on its elements and has no internal layer of sorting and
  cancellation. `SMS` is an `AddCommGroup`: Rocq's `∅`, `⊎`, `inv` and `{[+ x +]}` are `0`, `+`,
  `-` and `{x}`, and the positive and negative parts are `posPart` and `negPart`. Sorted lists
  appear only where pre-terms store products.
- **Terms** (`Core/Term/Base`) have the constructors `int`, `pair`, `nonce`, `key`, `sealed`,
  `hash` and `nonFree`, the last one holding a normal pre-term for exponentials and products.
  The smart constructors are `Term.exp b e` and `Term.prod o s` (Rocq `TExp`, `TMul`, `TGMul`).
  `Term.ind`, which recurses under exponentials and products with the cases `int`, `pair`,
  `nonce`, `key`, `sealed`, `hash`, `exp` and `prod`, is the default `induction` eliminator. Rocq
  lemmas that state a whole `match` (`fold_termE`, `tsize_eq`, `subtermsE'`) are one simp lemma
  per constructor. `LinearOrder Term` is pulled back from `PreTerm` along `unfold`.
- **Keys.** Rocq's three key records `aenc_key`, `sign_key` and `senc_key` are one structure
  `Key F`, indexed by the functionality `F` (`.aenc`, `.sign`, `.senc`). It holds the seed and
  coerces to the secret key `Term.key F.keyType seed`. Injectivity, the encoding,
  `minted_coe_key`, `isPublic_coe_key` and the predicates `aenc_pred`/`sign_pred`/`senc_pred`
  (`keyPred F`) are stated once for all `F`. Lemmas whose content depends on the functionality,
  such as the sealing rules, take `Key .aenc`, `Key .sign` or `Key .senc`.
- **The term algebra** (`Core/Term/Algebra`). The products form groups of terms:
  `Term.ProdGroup o` is a one-field structure around a term, coercing to `Term`, and a Mathlib
  `CommGroup`, free on the terms that are not products of kind `o`. `Term.E` (the exponents, Rocq
  `TMul`, `TInv`) and `Term.G` (the Diffie–Hellman group, Rocq `TGMul`, `TGInv`) are its two
  instances, and `Term.E.ofTerm t`, `Term.G.ofTerm t` view a term as a group element.
  Exponentiation is a `MulDistribMulAction Term.E Term.G`, so Rocq's `TExp (TExp g a) b` is
  `↑(b • a • g)` and `TExp g (TMul {x; y})` is `↑((x * y) • g)`. A group expression inside a term
  needs its coercion: `TPair (TExp g a) (TSeal k t)` is `.pair ↑(a • g) (.sealed k t)`. The simp
  lemmas `ProdGroup.coe_mul`, `coe_inv`, `coe_smul`, … push the coercion down to `Term.prod` and
  `Term.exp`, so simp normal forms are terms, and `norm_cast` lifts a goal back into the groups.
  Lemmas about Rocq's term functions are stated on terms (`TInv t` is `prod .mul (-{t})`), and
  those used with the group-valued HeapLang specs on coercions (`isPublic_coe_inv`). `Term`
  itself has no group structure. `group`, `abel` (on `Additive Term.G`) and `ring` apply.
- **Extended exponents** (`Lib/EExp`). `EExp` (Rocq `eexp`) is the group ring
  `MonoidAlgebra ℤ Term.E`, a domain because `Term.E` has unique products; `emul` is `*`.
  `Additive Term.G` is an `EExp`-module, so Rocq's `epow` is `•`, and `Term.log g` is a linear
  map. Rocq's cancellation lemmas are Mathlib's ring and module theory.
- **Diffie–Hellman and HMQV** (`Lib/DH`, `Lib/HMQV`). Shares and secrets are terms in simp normal
  form, `g.exp a` and `g.exp (prod .mul ({a} + {b}))`, and Rocq's `[a; b] ⊆+ SMS.pos (exps t)` is
  `{a, b} ≤ t.exps.posPart`. The HMQV base `hmqvY` and key `hmqvK` are elements of `Term.G`, so
  the case studies use the term `↑(hmqvK …)`, and the conditions `P ≠ TGMul ∅` are
  `G.ofTerm P ≠ 1`. The key is the scalar `hmqvS : EExp` acting on the base, so
  `log b K = hmqvS * log b Y`, and the injectivity arguments are equations in the domain `EExp`:
  Rocq's `hmqv_s_eq0` and `emul1_eq0` are `mul_eq_zero`, and computations with `emul` are `ring`
  and `linear_combination`. `hmqvK_eq_one` (Rocq `hmqv_K_unit`) is an equivalence, and
  `hmqvK_inj_counterexample` is stated existentially and also shows that the second claimed
  long-term key is not the unit. Rocq's `ephemeral` is `hmqvEphemeral`.
- **Sizes, nonces and subterms.** `isPublic` and other recursions on terms use `Term.tsizeRec`
  (Rocq `term_lt_rect`). The nonces of a term are a `Finset Nonce` and its subterms a
  `Finset Term`.
- **Tags.** `Tag N` is `Term.ofNamespace N`, the integer constant of `N`'s encoding. The integer
  tags of the HeapLang encoding (`TInt_tag`, `TSeal_tag`, …) are in `Core/PreTerm/WithStdpp`,
  where that encoding is defined; the order on pre-terms does not use them.

### The logic

- **Public terms** (`Core/Public`). Rocq's `public t` is `isPublic t` (`public_TPair` is
  `isPublic_pair`). It is defined by well-founded recursion on `Term.tsize`, so Rocq's fixpoint
  combinator `size_rec_pred` and the functional `public_pre_aux` have no counterpart. The
  recursive calls range over attached lists and multisets (`List.attach`, `Multiset.attach`) and
  under existentials over proofs, so that their arguments are known to be smaller; `isPublic_eq`
  (Rocq `public_eq`) states the definition with Rocq's pure guards, and `isPublic_persistent` is
  proved by induction on the size. The conditions on seals that Rocq writes as a `match` inside
  `public_TSeal` are the definitions `sealCond` and `openCond`. `Spec.open` is `Spec.opened`.
- **Ghost state.** Rocq's `inG Σ A` is Iris-Lean's `ElemG GF F` for a contractive functor `F`,
  and the `Σ` and `subG` declarations are subsumed by `BundledGFunctors` instance search. Cryptis
  uses Iris-Lean's classes where they exist: `SavedPropG`/`SavedPredG`, `GhostVarG` for
  replicas, `metaToken`/`metaInfo` from `GenHeap`, and `MetaUR` for `GMeta`. `namespace_map` is
  `ReservationMap.namespaceData` (`Upstream/Iris/NamespaceMap`), a reservation-map singleton.
- **The Cryptis ghost state** (`Logic`, Rocq `cryptis.v`). `CryptisGpreS` and `CryptisGS` hold
  the term-meta, public and lock ghost state as instance fields rather than parents, because the
  first two each contain a `MetaGS` and must be allocated separately. The case studies'
  `IsoDHGpreS` and `HmqvGpreS` hold their `MetaGS` and saved predicates as fields too.
- **General BIs.** Lemmas that do not need `IProp` are stated for any BI, with `BIAffine` where
  Rocq relies on `iProp` being affine. In Iris-Lean's BIs, bi-entailment implies equality
  (`BIBase.BiEntails.to_eq`), so Rocq lemmas about `≡` between propositions are stated with `=`.
- **Big operators** (`Upstream/Iris/BigSepMultiset`). Rocq's `[∗ mset]` and `[∗ set]` over
  Cryptis's multisets and sets are `[∗multiset] x ∈ s, Φ x` and `[∗finset] x ∈ s, Φ x` over
  Mathlib's `Multiset` and `Finset`, and `[∗ list] t ∈ elements s` over a signed multiset is
  `[∗multiset] t ∈ s.elements`. They are Iris-Lean's `[∗mset]` over the type synonym
  `Multiset.AsIris`: `[∗multiset] x ∈ s, Φ x` is `[∗mset] x ∈ s.toIris, Φ x`, and `[∗finset]` is
  the same over `s.val`. Like Rocq's, they need decidable equality on the elements, and they are
  computable. Iris-Lean's lemmas and proof-mode instances apply after the simp lemmas
  `Multiset.toIris_add`, `toIris_cons`, … rewrite Mathlib's operations into Iris-Lean's, and
  `bigSepMultiset_*`/`bigSepFinset_*` restate the common ones with Mathlib's operations. Rocq's
  `[∗ set] t ∈ dom m` is Iris-Lean's `[∗map] t ↦ _ ∈ m`.
- **Maps, sets and countability.** Iris-Lean's concrete maps and sets (`Std.ExtTreeMap`,
  `Std.ExtTreeSet`) need a lawful order on keys, so maps keyed by terms (`Core/TermMeta`) use
  `LinearOrder Term`, and the ledgers of the HMQV agreement game are `LeibnizSet` cameras over
  `Std.ExtTreeSet Term`. Iris-Lean's countability `Pos.Countable`, distinct from Mathlib's, is
  needed only for values stored in location meta data and for namespaces built from them
  (`N.@kR`). All instances are computable: a pre-term is encoded as the list of its operators in
  postfix order (`PreTerm.toSymbols`), which a stack machine decodes, and a term through its
  pre-term.
- **Adequacy** (`Lib/GenAdequacy`, `Lib/Adequacy`, `Adequacy`). Rocq's `thread_step` is
  `ThreadStep`, its reflexive-transitive closure is Mathlib's `Relation.ReflTransGen`, and
  `runsUntil` takes a mask.

### HeapLang code and specifications

- **Value encodings** (`Lib/Encode`). Lean's `Repr` is pretty-printing, so Cryptis's class `Repr`
  is `Cryptis.Encode` with the method `encode : α → Val`, and instances are named after the type
  (`Encode (List α)`). `Encode PreTerm` keeps Rocq's left-nested tuples, so it matches the
  HeapLang term functions, and a signed multiset is encoded as its sorted positive and negative
  parts. Keys are passed with their own encoding, `encode sk` for `sk : Key .aenc`, which the
  key-generation specs return; the simp lemma `Key.encode_eq` rewrites it to the encoding of the
  term `↑sk`.
- **The namespace `HL`.** The HeapLang functions of `primitives/` live in `Cryptis.HL`, so that
  calls read `HL.enc`, `HL.hash`, `HL.send` and do not clash with the functions of `Term` and
  `Spec`. They keep Rocq's names in Lean style (`HL.tint`, `HL.untuple`, `HL.sealed`,
  `HL.opened`, `HL.mkNonce`, …), without the `hl_` prefix of the Rocq pre-term programs (`hl_exp`
  is `HL.exp`). Their specs are in the same namespace, named after the program (`HL.twp_sealed`,
  `HL.wp_opened`). The generic list programs of `lib/list.v` and `lib/list_match.v` (`getList`,
  `mapList`, `list_match`) and `nondetNat` are in `Cryptis`, as library code with no Cryptis
  concept.
- **Specs** are stated for any stuckness and mask (`@ s; E`) and in continuation form,
  `Ψ (encode (Spec.f t)) ⊢ WP … [{ Ψ }]`, each `wp_` spec derived from its `twp_` spec. Channels
  and nonce and key creation are at `⊤`, as in Rocq. Decryption specs need no later credits, so
  they hold for any `hlc`. Sorting and lexicographic comparison in HeapLang are specified against
  core's `List.mergeSort` and the lexicographic `Ord (List α)`.
- **`list_match`** applies a closure to the list elements in a closed HeapLang loop, so it needs
  no free-variable metatheory. List literals are `hl_val([v₁, v₂])` and `hl(e :: es)`, and Rocq's
  `l !! n` is `&getList l n`, since `!!` would read as a double load.
- **`guard:` and `bind:`** (`Primitives/Notations`) are `hl_exp` syntax, and their body extends
  over `;`, as with `let` and the Rocq notations.
- **The WP simp set.** Term encodings are kept out of the `wp_expr_simp` set (the role of Rocq's
  `lock`), so that specs about `encode ?t` keep matching; `open scoped Cryptis.WpLit` and
  `Cryptis.WpEncode` add literal evaluation and pre-term encodings where wanted. The encodings of
  option and pair literals (`encode_none`, `encode_some`, `encode_pair`) and the negations of
  boolean literals are in the set, so that `match`, `~` and projections compute on results such
  as `encode none`.

### Tactics

The tactics of `tactics.v` (`Tactics`) are macros over Iris-Lean's `wp_pures`, `wp_apply`,
`isplit`, `iintro` and `wp_finish`, keep Rocq's names, and handle partial WPs. Rocq's tactic
lemmas, stated for an evaluation context `K`, are specs whose premise is the conjunction of the
success and the failure case (`HL.wp_untag_cases`, `wp_listMatch_cases`), since `wp_apply` finds
the context; where a spec is already in continuation form (`HL.wp_hash`) or splits the cases
itself (`HL.wp_adec'` with `HL.decPost`), the tactic applies it directly. A tactic that tests a
term takes the names of the success case and substitutes the decomposition of the tested term if
it is a variable; with `with h` it keeps the equation and names the failure case `h`, which covers
Rocq's `_eq` variants. `wp_list_match x y` names the elements of the list, and `wp_dec kt t` also
names the sealing key.

| Rocq | Lean |
|---|---|
| `wp_cons`, `wp_list`, `wp_term_of_list`, `wp_hash`, `wp_tag`, `wp_eq_term h` | the same |
| `wp_list_match => [x y ->\|h]` | `wp_list_match x y`, `wp_list_match x y with h` |
| `wp_list_match` | `wp_list_match` |
| `wp_untag t`, `wp_untag_eq t h` | `wp_untag t`, `wp_untag t with h` |
| `wp_list_of_term t`, `wp_list_of_term_eq t h` | `wp_list_of_term t`, `wp_list_of_term t with h` |
| `wp_is_key_eq kt k h` | `wp_is_key kt k`, `wp_is_key kt k with h` |
| `wp_lookup t h` | `wp_lookup t with h` |
| `wp_dec t`, `wp_dec_eq t h` | `wp_dec kt t`, `wp_dec kt t with hk h` |
| `wp_adec t`, `wp_adec_eq t h` (also `sdec`, `verify`) | `wp_adec t`, `wp_adec t with h` |

Rocq's `Hint Extern`s for `eauto` (`public_minted`, `public_TInt`) have no counterpart; the
lemmas `isPublic_minted` and `isPublic_int` state these facts.

## Iris-Lean deficiencies

These are limitations of Iris-Lean (and, in the last group, of Lean) that Cryptis works around.
Most of the workarounds are local and marked as upstream candidates.

### Proof mode

- **`iframe` does not unfold or reduce the goal.** It looks for the framed hypothesis in the goal
  as written, so it fails when the conjunct is hidden behind an `abbrev`, behind a `let` or a
  β-redex in the goal, in a `match` on a constructor, or in an `if` whose condition `cases` has
  made a literal (`if false = true then A else B`). For example, with
  `abbrev bundle A B := iprop(A ∗ B)`, `iframe HA HB` on the goal `bundle A B` fails with "cannot
  frame A", while `isplitl [HA]` works, since `isplit` finds the `∗` by instance search.
  Variables bound by a `let` in the local context are fine. Cryptis's protocol bundles are
  `abbrev`s, so the case studies write `unfold session`, `dsimp only` or
  `simp only [↓reduceIte]` before `iframe` (`CryptisExamples/HMQV/Proofs/Responder.lean`,
  `CryptisExamples/IsoDH/Game.lean`).
- **`icases H with ⟨⟩` does not destruct `H : □ False`.** It fails with "cannot destruct
  iprop(□ False) as an empty conjunct", where Rocq's `iDestruct "H" as "[]"` succeeds. Writing
  `icases H with #⟨⟩` moves `H` to the intuitionistic context first, and works.
- **A persistent `ihave` consumes the specialised hypothesis.** When the result is persistent,
  Rocq's `iDestruct ("H" with "HA") as "#H'"` keeps every hypothesis it used, since a persistent
  result can be derived without consuming anything. Iris-Lean's `ihave #H' := H $$ HA` keeps `HA`
  but consumes `H` when `H` is spatial. (With a lemma as head, `ihave #H' := lem $$ HA` keeps
  `HA`.) A proof that needs `H` again has to make it persistent first.
- **The functor of `iOwn` cannot be inferred from the camera element.** `iOwn_alloc` and its
  relatives take an element of `F.ap (IProp GF)`, from which Lean cannot recover `F`, so with
  several `ElemG` instances in scope, as in Cryptis's ghost state, the functor has to be named:
  `iOwn_alloc (F := DFracAgree.DFracAgreeRF …)` in `Cryptis/Core/Public.lean`,
  `termOwn_alloc (F := GhostVarF A)` in `Cryptis/Lib/Replica.lean`.
- **Missing proof-mode instances.** `iapply` and `ispecialize` do not use a hypothesis `P ↔ Q` as
  a wand (Rocq's type class search unfolds `bi_iff`), `icases` does not split an intuitionistic
  `[∗list]` over a list literal, and `iframe` leaves `[∗list] _ ∈ []` after framing the last
  element of a literal. `Cryptis/Upstream/Iris/ProofModeInstances.lean` adds the instances.

### HeapLang and the WP tactics

- **The HeapLang free-variable linter cannot be extended.** `linter.heapLang.freeVars` knows only
  the binders of core HeapLang, so it reports the variables bound by Cryptis's
  `list_match [x, y] := e in k` and `bind: x := e₁ in e₂` as unbound, and offers no way to
  register new binding forms. Cryptis turns it off in `lakefile.toml` and runs
  `linter.cryptis.heapLangFreeVars` (`Cryptis/Lib/HeapLangLinter.lean`), a copy of its analysis
  that also recognises these two syntax kinds.
- **The WP tactics handle only partial WPs.** Cryptis's specs come in a total version (`twp_`),
  from which the partial one is derived, but `wp_pure`, `wp_bind`, `wp_apply` and their
  relatives only accept `WP e {{ Φ }}`. Iris-Lean also lacks
  `twp_alloc`. `Cryptis/Lib/TwpTactics.lean` provides `twp_pure`, `twp_pures`, `twp_rec`,
  `twp_bind`, `twp_apply` and `twp_smart_apply`, copied from Iris-Lean's `ProofMode.lean`, with
  `twp_alloc` and `triple_of_twp`.
- **`wp_pures` looks for a redex before simplifying.** It takes pure steps while it finds a
  redex, and only when it finds none does it fall back to `wp_finish`, which simplifies the
  program and stops. After a case split substitutes a result such as `encode none` into
  `match r with …`, the `match` is a redex only once `encode none` is simplified to `none()`, so
  `wp_pures` alone simplifies and stops. The case studies write `wp_expr_simp` after such case
  splits (`… <;> wp_expr_simp`, then `wp_pures`).
- **Pure steps produce no later credits.** Iris-Lean's `wp_pure` strips one later from the
  hypotheses at each step, but has no `credit:` option producing `£ 1`, which Rocq proofs use to
  strip a later at a moment of their choosing, such as inside an invariant opening after the last
  step. The case studies arrange for a pure step to follow: in the HMQV games, where a session
  key is public only two laters later, the secrecy check splits cases before the pure steps of
  the assertion (`CryptisExamples/HMQV/Games/KCI.lean`, `ForwardSecrecy.lean`,
  `KeyIndependence.lean`), and the ISO-DH proofs strip the later of the escrowed resources with
  a following pure step. The decryption specs strip the later of the stored invariant with the
  program step.
- **`wp_expr_simp` does not substitute under `assert`.** Its simp set lacks the substitution
  lemma for `Exp.assert`, so a program that asserts a condition on a bound variable gets stuck
  under an `Exp.subst`. `Cryptis/Upstream/Iris/HeapLangAssert.lean` adds `subst_assert` to the
  set.

### Notation

- **`|==> A ∗ B` is `(|==> A) ∗ B`.** The update modality takes its argument at precedence 40 and
  `∗` is at 35, so the modality covers only `A`. Cryptis writes `|==> (A ∗ B)`.
- **`.@` does not associate.** Iris-Lean declares the namespace operator as a plain `infix:80`, so
  Rocq's `N.@"client".@kR` does not parse as intended and is written `(N.@"client").@kR`
  (`Cryptis/Lib/Replica.lean`). Declaring it `infixl` would remove the parentheses.
- **`•` is also the camera operation.** Iris-Lean writes the camera operation as `•` at
  precedence 60, below Mathlib's `•` (73) and `*` (70), so `a • x * b • y` parses as
  `a • (x * b • y)` and fails to typecheck. Expressions that mix the action of `Term.E` on
  `Term.G` with products write `(a • x) * (b • y)`.

### Libraries

- **Big operators cannot range over Mathlib's `Multiset` and `Finset`.** `[∗mset]` and `[∗set]`
  range over instances of Iris-Lean's classes `LawfulFiniteMultiSet` and `LawfulFiniteSet`, which
  bring their own `∈` and `⊆`. Instances for `Multiset` or `Finset` would clash with Mathlib's
  notation. Cryptis instantiates the class for the type synonym `Multiset.AsIris` and defines
  `[∗multiset]` and `[∗finset]` through it (`Cryptis/Upstream/Iris/BigSepMultiset.lean`). There is
  no lawful finite-set instance for a Mathlib type, so ghost sets of terms use
  `Std.ExtTreeSet Term`, the only instance Iris-Lean provides
  (`CryptisExamples/HMQV/Games/Agreement.lean`).
- **`Pos.ofNat` counts in unary.** Iris-Lean's `Pos.ofNat n` applies the successor `n` times, and
  `Pos.Countable Nat`, `Int`, `Char` and `Loc` go through it. Evaluating it by `decide` already
  exceeds the maximum recursion depth at `n = 100000`, so a countability instance that goes
  through large natural numbers, such as Mathlib's `Encodable` pairing, is impractical, and
  Iris-Lean's `Pos.Countable Val` is noncomputable. Cryptis encodes pre-terms directly as the
  list of their operators (`PreTerm.toSymbols` in `Cryptis/Core/PreTerm/WithStdpp.lean`), so the
  numbers involved stay small.
- **Missing pieces** that Cryptis supplies in `Cryptis/Upstream/Iris/`: Rocq Iris's
  `namespace_map` (`NamespaceMap.lean`); substitution under `assert` (`HeapLangAssert.lean`);
  countability of products, sums and options, and along a left inverse (`Countable.lean`); the
  injectivity of `.@` (`ndot_inj`), a `solve_ndisj` tactic and `Pos.Countable Unit`
  (`Namespaces.lean`); the proof-mode instances above (`ProofModeInstances.lean`); and BI lemmas
  about disjunctions, pure guards, updates, later credits and big separating conjunctions
  (`BILemmas.lean`). `twp_alloc` is in `Cryptis/Lib/TwpTactics.lean`.

### Lean

- **No derived instances or induction for nested inductives.** `PreTerm` nests `List PreTerm`.
  Lean cannot derive `DecidableEq` for it, a derived `Ord` does not unfold in proofs, and the
  `induction` tactic rejects the type. Cryptis writes `PreTerm.cmp` by hand, obtains decidable
  equality from the lawful order, and registers `PreTerm.ind` as the `induction_eliminator`
  (`Cryptis/Core/PreTerm/Base.lean`).

### Differences from Iris-Rocq worth knowing

- `wp_fork` takes the continuation first: `▷ Φ #() -∗ ▷ WP e {{ _, True }} -∗ WP fork e {{ Φ }}`,
  so `wp_apply wp_fork $$ [HΦ]` proves the continuation and leaves the forked thread as the goal.
- In Iris-Lean's BIs, bi-entailment implies equality (`BIBase.BiEntails.to_eq`), so equivalences
  of propositions are equalities and can be rewritten with `rw`. OFEs in general are not
  Leibniz.
- An entailment `h : ⊢ P` is passed to a wand premise as `%h`; a bare `h` after `$$` is read as
  a hypothesis name.
- Iris-Lean's HeapLang state interpretation ignores the step counter, so `Cryptis.Lib.Adequacy`
  needs no `mono_nat` ghost state.
- Iris-Lean has no concrete `gset` or `gmap`. It has the classes `Set`/`FiniteSet`
  (`Iris/Std/GenSets.lean`) and `PartialMap`/`FiniteMap` (`Iris/Std/PartialMap.lean`), with
  instances for `Std.ExtTreeSet` and `Std.ExtTreeMap`, and `Pos.Countable` in
  `Iris/Std/Positives.lean`.

## Upstream candidates

Generic code that belongs in Iris-Lean or Mathlib lives in separate files whose docstring starts
with `Upstream candidate (Iris-Lean): …` or `(Mathlib): …`, and which import nothing from
Cryptis.

| File | Target |
|---|---|
| `Cryptis/Upstream/Iris/BigSepMultiset.lean` | Iris-Lean (IrisMath, as it needs Mathlib) |
| `Cryptis/Upstream/Iris/BILemmas.lean` | Iris-Lean (`Iris/BI`) |
| `Cryptis/Upstream/Iris/Countable.lean` | Iris-Lean (`Iris/Std/Positives.lean`) |
| `Cryptis/Upstream/Iris/HeapLangAssert.lean` | Iris-Lean (`Iris/HeapLang/ProofMode.lean`) |
| `Cryptis/Upstream/Iris/Namespaces.lean` | Iris-Lean (`Iris/Std`) |
| `Cryptis/Upstream/Iris/NamespaceMap.lean` | Iris-Lean (`Iris/Algebra/ReservationMap`) |
| `Cryptis/Upstream/Iris/ProofModeInstances.lean` | Iris-Lean (`Iris/ProofMode/Instances.lean`) |

These Cryptis files also hold generic code:

- `Cryptis/Lib/TwpTactics.lean`: the total-WP proof-mode tactics, `twp_alloc` and
  `triple_of_twp` (Iris-Lean, `Iris/HeapLang/ProofMode.lean`).
- `Cryptis/Lib/Ord.lean`: all of it (Mathlib or Batteries).
- `Cryptis/Lib/ListSort.lean`: the `leOrd` sorting lemmas (Mathlib, `List.mergeSort`).
- `Cryptis/Lib/HeapLangLinter.lean`: the candidate is an extensible version of Iris-Lean's
  `linter.heapLang.freeVars`, to which this file would register its two binding forms.

## File map


### Library (`rocq-cryptis`): 45 files, 16461 lines

| Rocq file | Lines | Lean module | Status |
|---|---:|---|---|
| `cryptis/adequacy.v` | 26 | `Cryptis.Adequacy` | ported |
| `cryptis/core/minted.v` | 219 | `Cryptis.Core.Minted` | ported |
| `cryptis/core/pre_term.v` | 22 | `Cryptis.Core.PreTerm` | ported; umbrella module, defines `tsize` |
| `cryptis/core/pre_term/base.v` | 311 | `Cryptis.Core.PreTerm.Base` | ported |
| `cryptis/core/pre_term/normalize.v` | 648 | `Cryptis.Core.PreTerm.Normalize` | ported; factor lists sorted by `LinearOrder PreTerm`; products generic over `o : TermOpN` |
| `cryptis/core/pre_term/with_stdpp.v` | 468 | `Cryptis.Core.PreTerm.WithStdpp` | ported; `Encode` instances, computable `Pos.Countable` for nonces, key types, pre-terms (postfix encoding) |
| `cryptis/core/public.v` | 1547 | `Cryptis.Core.Public` | ported; `public` is `isPublic` |
| `cryptis/core/term.v` | 3 | `Cryptis.Core.Term` | ported; umbrella |
| `cryptis/core/term/algebra.v` | 701 | `Cryptis.Core.Term.Algebra` | ported; `Term.E`/`Term.G` are Mathlib `CommGroup`s of terms, with a `MulDistribMulAction` |
| `cryptis/core/term/base.v` | 732 | `Cryptis.Core.Term.Base` | ported; products are `Term.prod o`; `LinearOrder Term` via `unfold` |
| `cryptis/core/term/nonces.v` | 300 | `Cryptis.Core.Term.Nonces` | ported |
| `cryptis/core/term/repr.v` | 75 | `Cryptis.Core.Term.Encode` | ported; `Encode Term` goes through `Term.unfold` |
| `cryptis/core/term/spec.v` | 345 | `Cryptis.Core.Term.Spec` | ported; `Tag` is `Term.ofNamespace`, `Spec.open` is `Spec.opened` |
| `cryptis/core/term/subterms.v` | 482 | `Cryptis.Core.Term.Subterms` | ported; `subterms` is a `Finset Term` |
| `cryptis/core/term/tsize.v` | 370 | `Cryptis.Core.Term.TSize` | ported; `term_lt_rect` is `Term.tsizeRec` |
| `cryptis/core/term_meta.v` | 482 | `Cryptis.Core.TermMeta` | ported; ghost map keyed by `LinearOrder Term` |
| `cryptis/cryptis.v` | 70 | `Cryptis.Logic` | ported; `CryptisGS` holds its parts as instance fields |
| `cryptis/lib.v` | 608 | `Cryptis.Lib` | ported; umbrella; HeapLang part in `Misc`, Iris part in `BaseLogic` and `Upstream/Iris/*` |
| `cryptis/lib/adequacy.v` | 50 | `Cryptis.Lib.Adequacy` | ported |
| `cryptis/lib/dh.v` | 328 | `Cryptis.Lib.DH` | ported; `[a; b] ⊆+ SMS.pos (exps t)` is `{a, b} ≤ t.exps.posPart` |
| `cryptis/lib/eexp.v` | 582 | `Cryptis.Lib.EExp` | ported; `EExp` is `MonoidAlgebra ℤ Term.E`, acting on `Additive Term.G` |
| `cryptis/lib/gen_adequacy.v` | 72 | `Cryptis.Lib.GenAdequacy` | ported |
| `cryptis/lib/gmeta.v` | 124 | `Cryptis.Lib.GMeta` | ported; camera is Iris-Lean's `MetaUR` |
| `cryptis/lib/hmqv.v` | 1276 | `Cryptis.Lib.HMQV` | ported; `hmqvY`, `hmqvK` are elements of `Term.G`, `hmqvS` an `EExp`; `ephemeral` is `hmqvEphemeral`; programs in `HL` |
| `cryptis/lib/list.v` | 624 | `Cryptis.Lib.List` | ported; total and partial specs |
| `cryptis/lib/list_match.v` | 294 | `Cryptis.Lib.ListMatch` | ported; a closure-passing HeapLang loop |
| `cryptis/lib/list_sort.v` | 262 | `Cryptis.Lib.ListSort` | ported; mostly aliases to core Lean |
| `cryptis/lib/mathcomp_compat.v` | 115 | — | not ported: mathcomp/stdpp plumbing with no Lean meaning |
| `cryptis/lib/nown.v` | 137 | `Cryptis.Lib.NOwn` | ported; generic over `ElemG GF F` |
| `cryptis/lib/replica.v` | 173 | `Cryptis.Lib.Replica` | ported; the ghost state is Iris-Lean's `GhostVarG` |
| `cryptis/lib/repr.v` | 46 | `Cryptis.Lib.Encode` | ported; `Repr` is `Encode` |
| `cryptis/lib/saved_prop.v` | 113 | `Cryptis.Lib.SavedProp` | ported; on Iris-Lean's `SavedPropG`/`SavedPredG` |
| `cryptis/lib/size_rec_pred.v` | 52 | — | not ported: `isPublic` is defined by well-founded recursion |
| `cryptis/lib/sms.v` | 1203 | `Cryptis.Lib.SMS` | ported; pairs of disjoint Mathlib `Multiset`s |
| `cryptis/lib/term_set.v` | 150 | `Cryptis.Lib.TermSet` | ported; programs in `HL`; membership is `memList` with `HL.eqTerm` |
| `cryptis/primitives.v` | 2 | `Cryptis.Primitives` | ported; umbrella |
| `cryptis/primitives/attacker.v` | 328 | `Cryptis.Primitives.Attacker` | ported |
| `cryptis/primitives/comp.v` | 194 | `Cryptis.Primitives.Comp` | ported |
| `cryptis/primitives/notations.v` | 20 | `Cryptis.Primitives.Notations` | ported; `guard:` and `bind:` are `hl_exp` syntax |
| `cryptis/primitives/pre_term.v` | 871 | `Cryptis.Primitives.PreTerm` | ported; order specs state `compare` on `PreTerm`; programs on products take `o : TermOpN` |
| `cryptis/primitives/simple.v` | 634 | `Cryptis.Primitives.Simple` | ported; `seal`/`open`/`open_key` are `sealed`/`opened`/`openKey` |
| `cryptis/primitives/sms.v` | 98 | `Cryptis.Primitives.SMS` | ported; specified against the `SMS` encoding as sorted parts |
| `cryptis/primitives/with_cryptis.v` | 724 | `Cryptis.Primitives.WithCryptis` | ported; decryption specs need no later credits |
| `cryptis/role.v` | 63 | `Cryptis.Role` | ported |
| `cryptis/tactics.v` | 517 | `Cryptis.Tactics` | ported; tactic lemmas are specs by cases, `_eq` variants are `with h` |

### Case studies (`rocq-cryptis-examples`): 79 files, 15257 lines

| Rocq file | Lines | Lean module | Status |
|---|---:|---|---|
| `examples/alist.v` | 5 | — | not ported: out of scope |
| `examples/alist/impl.v` | 48 | — | not ported: out of scope |
| `examples/alist/proofs.v` | 168 | — | not ported: out of scope |
| `examples/challenge_response.v` | 237 | — | not ported: out of scope |
| `examples/composite_game.v` | 296 | — | not ported: out of scope |
| `examples/conn.v` | 9 | — | not ported: out of scope |
| `examples/conn/proofs.v` | 124 | — | not ported: out of scope |
| `examples/conn/proofs/base.v` | 114 | — | not ported: out of scope |
| `examples/counter.v` | 252 | — | not ported: out of scope |
| `examples/gen_conn.v` | 70 | — | not ported: out of scope |
| `examples/gen_conn/impl.v` | 74 | — | not ported: out of scope |
| `examples/gen_conn/proofs.v` | 383 | — | not ported: out of scope |
| `examples/gen_conn/proofs/base.v` | 580 | — | not ported: out of scope |
| `examples/hmqv.v` | 24 | `CryptisExamples.HMQV` | ported; umbrella |
| `examples/hmqv/games/agreement.v` | 542 | `CryptisExamples.HMQV.Games.Agreement` | ported; namespace `HMQV.Agreement`; ledgers are `LeibnizSet` cameras over `Std.ExtTreeSet Term` |
| `examples/hmqv/games/forward_secrecy.v` | 272 | `CryptisExamples.HMQV.Games.ForwardSecrecy` | ported; namespace `HMQV.ForwardSecrecy`; laters stripped by pure steps |
| `examples/hmqv/games/kci.v` | 189 | `CryptisExamples.HMQV.Games.KCI` | ported; namespace `HMQV.KCI`; laters stripped by pure steps |
| `examples/hmqv/games/key_independence.v` | 180 | `CryptisExamples.HMQV.Games.KeyIndependence` | ported; namespace `HMQV.KeyIndependence` |
| `examples/hmqv/impl.v` | 92 | `CryptisExamples.HMQV.Impl` | ported; `H` is `tagHash` |
| `examples/hmqv/proofs.v` | 1 | `CryptisExamples.HMQV.Proofs` | ported; umbrella |
| `examples/hmqv/proofs/base.v` | 556 | `CryptisExamples.HMQV.Proofs.Base` | ported; `SessInfo.secret` is an element of `Term.G`; `HmqvGpreS` holds its `MetaGS` and saved predicates as fields |
| `examples/hmqv/proofs/initiator.v` | 144 | `CryptisExamples.HMQV.Proofs.Initiator` | ported |
| `examples/hmqv/proofs/responder.v` | 213 | `CryptisExamples.HMQV.Proofs.Responder` | ported |
| `examples/iso_dh.v` | 17 | `CryptisExamples.IsoDH` | ported; umbrella |
| `examples/iso_dh/game.v` | 355 | `CryptisExamples.IsoDH.Game` | ported; `iso_dh_secure` holds for any `GF` with the HeapLang, Cryptis and ISO-DH ghost state |
| `examples/iso_dh/impl.v` | 73 | `CryptisExamples.IsoDH.Impl` | ported |
| `examples/iso_dh/proofs.v` | 1 | `CryptisExamples.IsoDH.Proofs` | ported; umbrella |
| `examples/iso_dh/proofs/base.v` | 278 | `CryptisExamples.IsoDH.Proofs.Base` | ported; `IsoDHGpreS` holds its `MetaGS` and saved predicates as fields |
| `examples/iso_dh/proofs/initiator.v` | 214 | `CryptisExamples.IsoDH.Proofs.Initiator` | ported; laters stripped by pure steps |
| `examples/iso_dh/proofs/responder.v` | 213 | `CryptisExamples.IsoDH.Proofs.Responder` | ported; laters stripped by pure steps |
| `examples/nsl/game.v` | 255 | `CryptisExamples.NSL.Game` | ported; `nsl_secure` holds for any `GF` with the HeapLang and Cryptis ghost state |
| `examples/nsl/impl.v` | 54 | `CryptisExamples.NSL.Impl` | ported |
| `examples/nsl/proofs.v` | 229 | `CryptisExamples.NSL.Proofs` | ported; the persistent assumptions of `wp_init`/`wp_resp` are in their preconditions |
| `examples/nsl_auth.v` | 367 | — | not ported: out of scope |
| `examples/nsl_dh.v` | 1 | — | not ported: out of scope |
| `examples/nsl_dh/game.v` | 358 | — | not ported: out of scope |
| `examples/nsl_dh/impl.v` | 110 | — | not ported: out of scope |
| `examples/nsl_dh/proofs.v` | 1 | — | not ported: out of scope |
| `examples/nsl_dh/proofs/base.v` | 472 | — | not ported: out of scope |
| `examples/nsl_dh/proofs/initiator.v` | 292 | — | not ported: out of scope |
| `examples/nsl_dh/proofs/responder.v` | 289 | — | not ported: out of scope |
| `examples/nsl_secr.v` | 333 | — | not ported: out of scope |
| `examples/opaque.v` | 1 | — | not ported: out of scope |
| `examples/opaque/client_proofs.v` | 341 | — | not ported: out of scope |
| `examples/opaque/game.v` | 490 | — | not ported: out of scope |
| `examples/opaque/impl.v` | 120 | — | not ported: out of scope |
| `examples/opaque/server_proofs.v` | 361 | — | not ported: out of scope |
| `examples/opaque/shared.v` | 564 | — | not ported: out of scope |
| `examples/permanent.v` | 182 | — | not ported: out of scope |
| `examples/rpc.v` | 14 | — | not ported: out of scope |
| `examples/rpc/impl.v` | 65 | — | not ported: out of scope |
| `examples/rpc/proofs.v` | 393 | — | not ported: out of scope |
| `examples/rpc/proofs/base.v` | 310 | — | not ported: out of scope |
| `examples/store.v` | 3 | — | not ported: out of scope |
| `examples/store/game.v` | 163 | — | not ported: out of scope |
| `examples/store/impl.v` | 103 | — | not ported: out of scope |
| `examples/store/proofs.v` | 1 | — | not ported: out of scope |
| `examples/store/proofs/base.v` | 413 | — | not ported: out of scope |
| `examples/store/proofs/client.v` | 2 | — | not ported: out of scope |
| `examples/store/proofs/client/close.v` | 51 | — | not ported: out of scope |
| `examples/store/proofs/client/connect.v` | 55 | — | not ported: out of scope |
| `examples/store/proofs/client/create.v` | 53 | — | not ported: out of scope |
| `examples/store/proofs/client/load.v` | 56 | — | not ported: out of scope |
| `examples/store/proofs/client/store.v` | 51 | — | not ported: out of scope |
| `examples/store/proofs/db.v` | 194 | — | not ported: out of scope |
| `examples/store/proofs/server.v` | 179 | — | not ported: out of scope |
| `examples/store/proofs/server/create.v` | 62 | — | not ported: out of scope |
| `examples/store/proofs/server/load.v` | 54 | — | not ported: out of scope |
| `examples/store/proofs/server/store.v` | 56 | — | not ported: out of scope |
| `examples/tls13.v` | 12 | — | not ported: out of scope |
| `examples/tls13/impl.v` | 811 | — | not ported: out of scope |
| `examples/tls13/proofs.v` | 1 | — | not ported: out of scope |
| `examples/tls13/proofs/base.v` | 76 | — | not ported: out of scope |
| `examples/tls13/proofs/cparams.v` | 188 | — | not ported: out of scope |
| `examples/tls13/proofs/cshare.v` | 242 | — | not ported: out of scope |
| `examples/tls13/proofs/meth.v` | 107 | — | not ported: out of scope |
| `examples/tls13/proofs/protocol.v` | 278 | — | not ported: out of scope |
| `examples/tls13/proofs/sparams.v` | 299 | — | not ported: out of scope |
| `examples/tls13/proofs/sshare.v` | 421 | — | not ported: out of scope |

### Sessions (`rocq-cryptis-session`): 19 files, 3796 lines, built on Actris

| Rocq file | Lines | Lean module | Status |
|---|---:|---|---|
| `session/examples/basic.v` | 398 | — | not ported: built on Actris |
| `session/examples/store/game.v` | 166 | — | not ported: built on Actris |
| `session/examples/store/impl.v` | 124 | — | not ported: built on Actris |
| `session/examples/store/proofs.v` | 1 | — | not ported: built on Actris |
| `session/examples/store/proofs/base.v` | 432 | — | not ported: built on Actris |
| `session/examples/store/proofs/client.v` | 2 | — | not ported: built on Actris |
| `session/examples/store/proofs/client/close.v` | 92 | — | not ported: built on Actris |
| `session/examples/store/proofs/client/connect.v` | 89 | — | not ported: built on Actris |
| `session/examples/store/proofs/client/create.v` | 80 | — | not ported: built on Actris |
| `session/examples/store/proofs/client/load.v` | 98 | — | not ported: built on Actris |
| `session/examples/store/proofs/client/store.v` | 73 | — | not ported: built on Actris |
| `session/examples/store/proofs/server.v` | 527 | — | not ported: built on Actris |
| `session/impl.v` | 38 | — | not ported: built on Actris |
| `session/proofmode.v` | 492 | — | not ported: built on Actris |
| `session/proofs.v` | 364 | — | not ported: built on Actris |
| `session/proofs/base.v` | 265 | — | not ported: built on Actris |
| `session/sess.v` | 11 | — | not ported: built on Actris |
| `session/tag.v` | 263 | — | not ported: built on Actris |
| `session/trusted.v` | 281 | — | not ported: built on Actris |
