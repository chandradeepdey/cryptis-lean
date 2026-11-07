module

public import Cryptis.Core.PreTerm

/-! Terms: the messages of Cryptis.

A term is a message that protocols exchange: an integer, a nonce, a pair, a key derived from a
seed, a sealed message (a payload encrypted or signed with a key), a hash, or one of the algebraic
terms of Diffie–Hellman key exchange. These are exponentials, which raise a base to an exponent,
and products in two commutative groups: the scalar product of exponents and the group product of
Diffie–Hellman values. Terms are kept in normal form for the laws of these groups, so messages
that are equal by these laws are equal terms.

The free operators are constructors of `Term`. An exponential or a product is held by the
constructor `nonFree` as its normal pre-term, and is built with the smart constructors `exp` and
`prod`, which normalize their results.

- Keys: the three functionalities of keys (public-key encryption, signatures and symmetric
  encryption), and secret keys, given by their seeds.
- Terms as normal pre-terms: `unfold` and `fold` translate between terms and normal pre-terms,
  and terms are ordered by their pre-terms.
- Exponentials and products: `exp` and `prod`. A single `prod o` covers both products, chosen by
  the operator `o`.
- Recognisers, and the base and exponent of an exponential.
- Factors: `factors o` reads a term as a signed multiset of factors, the positive and negative
  occurrences of the terms that are not themselves products of kind `o`. It determines the term,
  so the laws of products follow by comparing factors, or their multiplicities (`count`).
- Induction: `Term.ind`, the default induction principle, recurses under exponentials and
  products. -/

@[expose] public section
namespace Cryptis

/-- Terms. Exponentials and products are held by `nonFree` as normal pre-terms. -/
@[rocq_alias cryptis.term]
inductive Term where
  | int (n : Int)
  | pair (t₁ t₂ : Term)
  | nonce (a : Nonce)
  | key (kt : KeyType) (t : Term)
  | sealed (k t : Term)
  | hash (t : Term)
  | nonFree (pt : PreTerm) (wf : pt.wf) (nf : pt.isNonFree)
deriving DecidableEq, Inhabited, Repr

attribute [rocq_alias cryptis.TInt] Term.int
attribute [rocq_alias cryptis.TPair] Term.pair
attribute [rocq_alias cryptis.TNonce] Term.nonce
attribute [rocq_alias cryptis.TKey] Term.key
attribute [rocq_alias cryptis.TSeal] Term.sealed
attribute [rocq_alias cryptis.THash] Term.hash
attribute [rocq_alias cryptis.TNonFree] Term.nonFree
attribute [rocq_alias cryptis.term_ind'] Term.rec
attribute [rocq_alias cryptis.term_eq_dec] instDecidableEqTerm
attribute [rocq_alias cryptis.term_inhabited] instInhabitedTerm
attribute [coe] Term.nonce

instance : Coe Nonce Term := ⟨Term.nonce⟩

#rocq_ignore cryptis.is_non_free "PreTerm.isNonFree"
#rocq_ignore cryptis.TNonFree_irr "Proof irrelevance is definitional in Lean"
#rocq_ignore cryptis.termO "Leibniz OFEs are built on demand with OFE.ofDiscrete"
#rocq_ignore cryptis.tsms "SMS Term"

/-! ### Keys -/

/-- The functionality of a key: public-key encryption, signatures or symmetric encryption. -/
@[rocq_alias cryptis.functionality]
inductive Functionality where
  | aenc | sign | senc
deriving DecidableEq, Inhabited, Repr

/-- The functionality a key type belongs to. -/
@[rocq_alias cryptis.func_of_key_type]
def KeyType.functionality : KeyType → Functionality
  | .aenc | .adec => .aenc
  | .sign | .verify => .sign
  | .senc => .senc

/-- The functionality of a key, if the term is one. -/
@[rocq_alias cryptis.func_of_term]
def Term.functionality : Term → Option Functionality
  | .key kt _ => some kt.functionality
  | _ => none

/-- The key type of the secret keys of a functionality: decryption, signing and symmetric keys. -/
def Functionality.keyType : Functionality → KeyType
  | .aenc => .adec
  | .sign => .sign
  | .senc => .senc

attribute [simp] Functionality.keyType.eq_1 Functionality.keyType.eq_2 Functionality.keyType.eq_3

@[simp]
theorem Functionality.functionality_keyType (F : Functionality) : F.keyType.functionality = F := by
  cases F <;> rfl

/-- A secret key of functionality `F`, given by its seed: a decryption key for `.aenc`, a signing
key for `.sign` and a symmetric key for `.senc`. -/
@[ext, rocq_alias cryptis.aenc_key, rocq_alias cryptis.sign_key, rocq_alias cryptis.senc_key]
structure Key (F : Functionality) where
  seed : Term
deriving DecidableEq, Inhabited, Repr

attribute [rocq_alias cryptis.AEncKey, rocq_alias cryptis.SignKey, rocq_alias cryptis.SEncKey]
  Key.mk
attribute [rocq_alias cryptis.seed_of_aenc_key, rocq_alias cryptis.seed_of_sign_key,
  rocq_alias cryptis.seed_of_senc_key] Key.seed
attribute [rocq_alias cryptis.aenc_key_eq_dec, rocq_alias cryptis.sign_key_eq_dec,
  rocq_alias cryptis.senc_key_eq_dec] instDecidableEqKey
attribute [rocq_alias cryptis.aenc_key_inhabited, rocq_alias cryptis.sign_key_inhabited,
  rocq_alias cryptis.senc_key_inhabited] instInhabitedKey

namespace Key

variable {F : Functionality}

/-- A secret key, as a term. -/
@[coe, rocq_alias cryptis.term_of_aenc_key, rocq_alias cryptis.term_of_sign_key,
  rocq_alias cryptis.term_of_senc_key]
def toTerm (k : Key F) : Term := .key F.keyType k.seed

instance : CoeOut (Key F) Term := ⟨toTerm⟩

@[simp]
theorem toTerm_mk (t : Term) : (⟨t⟩ : Key F).toTerm = .key F.keyType t := rfl

@[rocq_alias cryptis.term_of_aenc_key_inj, rocq_alias cryptis.term_of_sign_key_inj,
  rocq_alias cryptis.term_of_senc_key_inj]
theorem toTerm_injective : Function.Injective (toTerm (F := F)) := by
  rintro ⟨_⟩ ⟨_⟩ ⟨⟩; rfl

@[simp, norm_cast]
theorem toTerm_inj {k₁ k₂ : Key F} : (k₁ : Term) = k₂ ↔ k₁ = k₂ := toTerm_injective.eq_iff

@[simp]
theorem functionality_toTerm (k : Key F) : (k : Term).functionality = some F := by
  cases F <;> rfl

end Key

namespace Term

/-! ### Terms as normal pre-terms -/

/-- The pre-term that a term stands for. -/
@[rocq_alias cryptis.unfold_term]
def unfold : Term → PreTerm
  | int n => .op0 (.int n)
  | pair t₁ t₂ => .op2 .pair t₁.unfold t₂.unfold
  | nonce a => .op0 (.nonce a)
  | key kt t => .op1 (.key kt) t.unfold
  | sealed k t => .op2 .sealed k.unfold t.unfold
  | hash t => .op1 .hash t.unfold
  | nonFree pt _ _ => pt

/-- The term of a normal pre-term; pre-terms that are not normal give junk. -/
@[rocq_alias cryptis.fold_term_predef]
def foldAux : PreTerm → Term
  | .op0 (.int n) => int n
  | .op0 (.nonce a) => nonce a
  | .op1 (.key kt) pt => key kt (foldAux pt)
  | .op1 .hash pt => hash (foldAux pt)
  | .op2 .pair pt₁ pt₂ => pair (foldAux pt₁) (foldAux pt₂)
  | .op2 .sealed pt₁ pt₂ => sealed (foldAux pt₁) (foldAux pt₂)
  | pt => if h : pt.wf ∧ pt.isNonFree then nonFree pt h.1 h.2 else int 0

/-- The term of a pre-term, through its normal form. -/
@[rocq_alias cryptis.fold_term]
def fold (pt : PreTerm) : Term := foldAux pt.normalize

variable {t t₁ t₂ x : Term} {pt : PreTerm} {s : SMS Term}

@[simp, rocq_alias cryptis.wf_unfold_term]
theorem wf_unfold (t : Term) : t.unfold.wf := by
  induction t using Term.rec <;> simp_all [unfold, PreTerm.wf]

#rocq_ignore cryptis.wf_unfold_terms "Term.wf_unfold"

@[rocq_alias cryptis.fold_predef_NonFree]
theorem foldAux_nonFree (wf : pt.wf) (nf : pt.isNonFree) : foldAux pt = nonFree pt wf nf := by
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | ⟨_ | _⟩
  case op2.exp | opN.mul | opN.gmul => simp [foldAux, wf, nf]
  all_goals simp [PreTerm.isNonFree, PreTerm.isExp, PreTerm.isProd] at nf

theorem foldAux_unfold (t : Term) : foldAux t.unfold = t := by
  induction t using Term.rec with
  | nonFree pt wf nf => exact foldAux_nonFree wf nf
  | _ => simp_all [unfold, foldAux]

theorem unfold_foldAux (h : pt.wf) : (foldAux pt).unfold = pt := by
  induction pt with
  | op0 o => cases o <;> rfl
  | op1 o t ih => cases o <;> simp_all [foldAux, unfold, PreTerm.wf]
  | op2 o t₁ t₂ ih₁ ih₂ =>
    cases o
    case exp => rw [foldAux_nonFree h rfl]; rfl
    all_goals simp_all [foldAux, unfold, PreTerm.wf]
  | opN o ps ns => rw [foldAux_nonFree h (by cases o <;> rfl)]; rfl

@[simp, rocq_alias cryptis.unfold_termK]
theorem fold_unfold (t : Term) : fold t.unfold = t := by
  rw [fold, PreTerm.normalize_of_wf (wf_unfold t), foldAux_unfold]

@[simp, rocq_alias cryptis.unfold_fold]
theorem unfold_fold (pt : PreTerm) : (fold pt).unfold = pt.normalize :=
  unfold_foldAux (PreTerm.wf_normalize pt)

@[rocq_alias cryptis.fold_termK]
theorem unfold_fold_of_wf (h : pt.wf) : (fold pt).unfold = pt := by
  rw [unfold_fold, PreTerm.normalize_of_wf h]

#rocq_ignore cryptis.fmap_fold_termK "Term.unfold_fold_of_wf, with List.map_map"
#rocq_ignore cryptis.fmap_unfold_termK "Term.fold_unfold, with List.map_map"

@[simp, rocq_alias cryptis.fold_normalize]
theorem fold_normalize (pt : PreTerm) : fold pt.normalize = fold pt := by
  rw [← unfold_fold, fold_unfold]

@[rocq_alias cryptis.unfold_term_inj]
theorem unfold_injective : Function.Injective unfold :=
  Function.LeftInverse.injective fold_unfold

@[simp]
theorem unfold_inj : t₁.unfold = t₂.unfold ↔ t₁ = t₂ := unfold_injective.eq_iff

/-- Terms are countable through their pre-terms, which makes them usable in namespaces. -/
@[rocq_alias cryptis.term_countable]
instance : Pos.Countable Term where
  encode t := Pos.Countable.encode t.unfold
  decode p := (Pos.Countable.decode p).map fold
  decode_encode t := by simp [Pos.Countable.decode_encode]

@[simp, rocq_alias cryptis.normalize_unfold]
theorem normalize_unfold (t : Term) : t.unfold.normalize = t.unfold :=
  PreTerm.normalize_of_wf (wf_unfold t)

#rocq_ignore cryptis.fmap_normalize_unfold "Term.normalize_unfold, with List.map_map"

/-! ### The linear order on terms

Terms are ordered by their pre-terms. Finite maps keyed by terms use this order. -/

instance : Ord Term := ⟨fun t₁ t₂ => compare t₁.unfold t₂.unfold⟩

instance : Std.TransOrd Term where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := (compare : PreTerm → PreTerm → Ordering))
  isLE_trans := Std.TransCmp.isLE_trans (cmp := (compare : PreTerm → PreTerm → Ordering))

instance : Std.LawfulEqOrd Term where
  eq_of_compare h := unfold_injective <|
    Std.LawfulEqCmp.eq_of_compare (cmp := (compare : PreTerm → PreTerm → Ordering)) h

/-- The order of `Ord Term` as a Mathlib linear order. -/
@[rocq_alias cryptis.term_lexico, rocq_alias cryptis.term_lexico_strict,
  rocq_alias cryptis.term_lexico_trichotomyT, rocq_alias cryptis.term_order]
instance : LinearOrder Term := .ofStd Term

theorem compare_def : compare t₁ t₂ = compare t₁.unfold t₂.unfold := rfl

@[rocq_alias cryptis.term_orderE]
theorem le_iff_unfold_le : t₁ ≤ t₂ ↔ t₁.unfold ≤ t₂.unfold := .rfl
#rocq_ignore cryptis.smap_unfold_fold "Multisets need no list representation"
#rocq_ignore cryptis.wf_term_pair "Multisets need no list representation"

theorem forall_mem_map_unfold {p : PreTerm → Prop} :
    (∀ pt ∈ s.map unfold, p pt) ↔ ∀ t ∈ s, p t.unfold := by
  refine ⟨fun h t ht => h _ ((SMS.mem_map_of_injective unfold_injective).mpr ht), ?_⟩
  intro h pt hpt
  obtain ⟨t, ht, rfl⟩ := SMS.exists_of_mem_map hpt
  exact h t ht

/-! ### Exponentials and products

The scalar product of exponents and the group product of Diffie–Hellman values share their
theory, so it is stated once for the product of kind `o : TermOpN`. -/

/-- The product of kind `o` of the elements of `s`, flattening the products of that kind among
them: the scalar product for `o = .mul` and the group product for `o = .gmul`. -/
@[rocq_alias cryptis.TMul, rocq_alias cryptis.TGMul]
def prod (o : TermOpN) (s : SMS Term) : Term := fold (PreTerm.prod o (s.map unfold))

/-- Exponentiation. -/
@[rocq_alias cryptis.TExp]
def exp (b e : Term) : Term := fold (PreTerm.exp b.unfold e.unfold)

variable {o : TermOpN}

@[rocq_alias cryptis.unfold_TMul, rocq_alias cryptis.unfold_TGMul]
theorem unfold_prod (o : TermOpN) (s : SMS Term) :
    (prod o s).unfold = PreTerm.prod o (s.map unfold) := by
  rw [prod, unfold_fold_of_wf (PreTerm.wf_prod (forall_mem_map_unfold.mpr fun t _ => wf_unfold t))]

@[rocq_alias cryptis.unfold_TExp]
theorem unfold_exp (b e : Term) : (exp b e).unfold = PreTerm.exp b.unfold e.unfold :=
  unfold_fold_of_wf (PreTerm.wf_exp (wf_unfold b) (wf_unfold e))

@[rocq_alias cryptis.unfold_TMul_make, rocq_alias cryptis.unfold_TGMul_make]
theorem unfold_prod_make (o : TermOpN) (X Y : Multiset Term) :
    (prod o (.make X Y)).unfold = PreTerm.prod o (.make (X.map unfold) (Y.map unfold)) := by
  rw [unfold_prod, SMS.map_make]

theorem unfold_prod_pair (o : TermOpN) (t₁ t₂ : Term) :
    (prod o ({t₁} + {t₂})).unfold = PreTerm.prod o ({t₁.unfold} + {t₂.unfold}) := by
  rw [unfold_prod, SMS.map_add, SMS.map_singleton, SMS.map_singleton]

theorem unfold_prod_neg_singleton (o : TermOpN) (t : Term) :
    (prod o (-{t})).unfold = PreTerm.prod o (-{t.unfold}) := by
  rw [unfold_prod, SMS.map_neg, SMS.map_singleton]

@[simp]
theorem unfold_prod_zero (o : TermOpN) : (prod o 0).unfold = .opN o [] [] := by
  rw [unfold_prod, SMS.map_zero, PreTerm.prod_zero]

/-! `fold` commutes with the operators. -/

@[simp]
theorem fold_int (n : Int) : fold (.op0 (.int n)) = int n := by
  simp only [fold, PreTerm.normalize, foldAux]

@[simp]
theorem fold_nonce (a : Nonce) : fold (.op0 (.nonce a)) = nonce a := by
  simp only [fold, PreTerm.normalize, foldAux]

@[simp]
theorem fold_key (kt : KeyType) (pt : PreTerm) : fold (.op1 (.key kt) pt) = key kt (fold pt) := by
  simp only [fold, PreTerm.normalize, foldAux]

@[simp]
theorem fold_hash (pt : PreTerm) : fold (.op1 .hash pt) = hash (fold pt) := by
  simp only [fold, PreTerm.normalize, foldAux]

@[simp]
theorem fold_pair (pt₁ pt₂ : PreTerm) :
    fold (.op2 .pair pt₁ pt₂) = pair (fold pt₁) (fold pt₂) := by
  simp only [fold, PreTerm.normalize, foldAux]

@[simp]
theorem fold_sealed (pt₁ pt₂ : PreTerm) :
    fold (.op2 .sealed pt₁ pt₂) = sealed (fold pt₁) (fold pt₂) := by
  simp only [fold, PreTerm.normalize, foldAux]

@[simp]
theorem fold_ptExp (b e : PreTerm) : fold (.ptExp b e) = exp (fold b) (fold e) := by
  apply unfold_injective
  rw [unfold_exp, unfold_fold, unfold_fold, unfold_fold, PreTerm.normalize]

@[simp]
theorem map_unfold_map_fold (ps : List PreTerm) :
    (ps.map fold).map unfold = ps.map PreTerm.normalize := by
  simp [Function.comp_def]

@[simp]
theorem fold_opN (o : TermOpN) (ps ns : List PreTerm) :
    fold (.opN o ps ns) = prod o (.make (ps.map fold : Multiset Term) (ns.map fold)) := by
  apply unfold_injective
  cases o <;> simp [unfold_prod_make, PreTerm.normalize, PreTerm.prod, Function.comp_def]

#rocq_ignore cryptis.fold_termE "Split into the simp lemmas Term.fold_int, …, Term.fold_opN"

/-! ### Recognisers -/

@[rocq_alias cryptis.is_nonce]
def isNonce : Term → Bool
  | nonce _ => true
  | _ => false

@[rocq_alias cryptis.is_exp]
def isExp : Term → Bool
  | nonFree pt _ _ => pt.isExp
  | _ => false

/-- Whether a term is a product of kind `o`. -/
@[rocq_alias cryptis.is_mul, rocq_alias cryptis.is_gmul]
def isProd (o : TermOpN) : Term → Bool
  | nonFree pt _ _ => pt.isProd o
  | _ => false

@[simp, rocq_alias cryptis.is_nonce_unfold]
theorem isNonce_unfold (t : Term) : t.unfold.isNonce = t.isNonce := by
  cases t
  case nonFree pt _ nf =>
    rcases pt with ⟨_ | _⟩ | _ | _ | _ <;> first
      | rfl | simp [PreTerm.isNonFree, PreTerm.isExp, PreTerm.isProd] at nf
  all_goals rfl

@[simp, rocq_alias cryptis.is_exp_unfold]
theorem isExp_unfold (t : Term) : t.unfold.isExp = t.isExp := by cases t <;> rfl

@[simp, rocq_alias cryptis.is_mul_unfold, rocq_alias cryptis.is_gmul_unfold]
theorem isProd_unfold (o : TermOpN) (t : Term) : t.unfold.isProd o = t.isProd o := by
  cases t <;> cases o <;> rfl

theorem isExp_fold (h : pt.wf) : (fold pt).isExp = pt.isExp := by
  rw [← isExp_unfold, unfold_fold_of_wf h]

theorem isProd_fold (o : TermOpN) (h : pt.wf) : (fold pt).isProd o = pt.isProd o := by
  rw [← isProd_unfold, unfold_fold_of_wf h]

/-! ### Bases and exponents -/

/-- The base of an exponential, and any other term itself. -/
@[rocq_alias cryptis.base]
def base (t : Term) : Term := fold t.unfold.base

/-- The exponent of an exponential, and the scalar unit otherwise. -/
@[rocq_alias cryptis.expo]
def expo (t : Term) : Term := fold t.unfold.expo

@[rocq_alias cryptis.unfold_base]
theorem unfold_base (t : Term) : t.base.unfold = t.unfold.base :=
  unfold_fold_of_wf (PreTerm.wf_base (wf_unfold t))

@[rocq_alias cryptis.unfold_expo]
theorem unfold_expo (t : Term) : t.expo.unfold = t.unfold.expo :=
  unfold_fold_of_wf (PreTerm.wf_expo (wf_unfold t))

/-! ### Factors -/

/-- The factors of a product of kind `o`, and any other term as a single factor. -/
@[rocq_alias cryptis.factors, rocq_alias cryptis.gfactors]
def factors (o : TermOpN) (t : Term) : SMS Term := (t.unfold.factors o).map fold

#rocq_ignore cryptis.car_factors "Multisets need no list representation"
#rocq_ignore cryptis.car_gfactors "Multisets need no list representation"

@[simp, rocq_alias cryptis.unfold_factors, rocq_alias cryptis.unfold_gfactors]
theorem map_unfold_factors (o : TermOpN) (t : Term) :
    (t.factors o).map unfold = t.unfold.factors o := by
  rw [factors, SMS.map_map]
  exact SMS.map_eq_self fun pt h =>
    unfold_fold_of_wf ((PreTerm.wfFactors_factors (wf_unfold t)).wf h)

@[rocq_alias cryptis.elements_factors, rocq_alias cryptis.elements_gfactors]
theorem map_unfold_elements_factors (o : TermOpN) (t : Term) :
    (t.factors o).elements.map unfold = (t.unfold.factors o).elements := by
  rw [← SMS.elements_map_of_injective unfold_injective, map_unfold_factors]

@[rocq_alias cryptis.elem_of_factors_unfold, rocq_alias cryptis.elem_of_gfactors_unfold]
theorem mem_factors_iff_unfold : x ∈ t.factors o ↔ x.unfold ∈ t.unfold.factors o := by
  rw [← map_unfold_factors, SMS.mem_map_of_injective unfold_injective]

@[rocq_alias cryptis.Nmul_factors, rocq_alias cryptis.Ngmul_gfactors]
theorem isProd_of_mem_factors (h : x ∈ t.factors o) : x.isProd o = false := by
  rw [← isProd_unfold]
  exact (PreTerm.wfFactors_factors (wf_unfold t)).isProd_eq_false
    (mem_factors_iff_unfold.mp h)

@[rocq_alias cryptis.factors_Nmul, rocq_alias cryptis.gfactors_Ngmul]
theorem factors_eq_singleton (h : t.isProd o = false) : t.factors o = {t} := by
  rw [factors, PreTerm.factors_eq_singleton (by rwa [isProd_unfold]), SMS.map_singleton,
    fold_unfold]

@[simp, rocq_alias cryptis.factorsK, rocq_alias cryptis.gfactorsK]
theorem prod_factors (o : TermOpN) (t : Term) : prod o (t.factors o) = t := by
  apply unfold_injective
  rw [unfold_prod, map_unfold_factors, PreTerm.prod_factors (wf_unfold t)]

@[rocq_alias cryptis.factors_inj, rocq_alias cryptis.gfactors_inj]
theorem factors_injective (o : TermOpN) : Function.Injective (factors o) :=
  Function.LeftInverse.injective (prod_factors o)

@[simp]
theorem factors_inj : t₁.factors o = t₂.factors o ↔ t₁ = t₂ := (factors_injective o).eq_iff

/-- `factors o` is a homomorphism into the free abelian group on terms. -/
@[simp, rocq_alias cryptis.factors_TMul, rocq_alias cryptis.gfactors_TGMul]
theorem factors_prod (o : TermOpN) (s : SMS Term) : (prod o s).factors o = s.bind (factors o) := by
  rw [factors, unfold_prod,
    PreTerm.factors_prod (forall_mem_map_unfold.mpr fun t _ => wf_unfold t), SMS.bind_map,
    SMS.map_bind]
  rfl

@[rocq_alias cryptis.factors_TMul_atoms, rocq_alias cryptis.gfactors_TGMul_atoms]
theorem factors_prod_of_forall (h : ∀ x ∈ s, x.isProd o = false) : (prod o s).factors o = s := by
  rw [factors_prod, SMS.bind_congr fun x hx => factors_eq_singleton (h x hx),
    SMS.bind_singleton_right]

/-! ### Signed multiplicities -/

/-- The multiplicity of `x` among the factors of kind `o` of `t`. -/
@[rocq_alias cryptis.count, rocq_alias cryptis.gcount]
def count (o : TermOpN) (x t : Term) : ℤ := (t.factors o).count x

@[rocq_alias cryptis.is_mul_count, rocq_alias cryptis.is_gmul_gcount]
theorem count_of_isProd (h : x.isProd o) (t : Term) : count o x t = 0 :=
  SMS.count_eq_zero_of_not_mem fun hx => by simp [isProd_of_mem_factors hx] at h

/-- Terms are determined by the multiplicities of their factors. -/
@[rocq_alias cryptis.count_inj, rocq_alias cryptis.gcount_inj]
theorem ext_count (h : ∀ x, x.isProd o = false → count o x t₁ = count o x t₂) : t₁ = t₂ := by
  refine factors_injective o (SMS.ext fun x => ?_)
  cases hx : x.isProd o
  · exact h x hx
  · exact (count_of_isProd hx t₁).trans (count_of_isProd hx t₂).symm

/-! ### Induction -/

/-- The factor lists of a normal product are not a single positive factor. -/
theorem make_map_fold_ne_singleton {ps ns : List PreTerm} (hw : ∀ p ∈ ps ++ ns, p.wf)
    (hc : PreTerm.IsCanonical (ps, ns)) (hs : PreTerm.single (ps, ns) = false) (t : Term) :
    SMS.make (ps.map fold : Multiset Term) (ns.map fold) ≠ {t} := by
  intro h
  have h := congrArg (SMS.map unfold) h
  rw [SMS.map_make, Multiset.map_coe, Multiset.map_coe, map_unfold_map_fold, map_unfold_map_fold,
    PreTerm.map_normalize_of_wf fun p hp => hw p (List.mem_append_left _ hp),
    PreTerm.map_normalize_of_wf fun p hp => hw p (List.mem_append_right _ hp),
    SMS.map_singleton] at h
  have h := congrArg PreTerm.toLists h
  rw [PreTerm.toLists_make hc, PreTerm.toLists_singleton] at h
  simp [h, PreTerm.single] at hs

theorem exists_of_mem_make_map_fold {ps ns : List PreTerm}
    (h : t ∈ SMS.make (ps.map fold : Multiset Term) (ns.map fold)) :
    ∃ p ∈ ps ++ ns, fold p = t := by
  simpa [or_and_right, exists_or] using SMS.mem_of_mem_make h

/-- Induction on terms, recursing under exponentials and products. The base of an exponential is
neither an exponential nor a group product, and its exponent is not the scalar unit. The factors
of a product are not products of the same kind, and are not a single positive factor. -/
@[elab_as_elim, induction_eliminator, rocq_alias cryptis.term_rect, rocq_alias cryptis.term_ind]
theorem ind {motive : Term → Prop}
    (int : ∀ n, motive (.int n))
    (pair : ∀ t₁ t₂, motive t₁ → motive t₂ → motive (.pair t₁ t₂))
    (nonce : ∀ a, motive (.nonce a))
    (key : ∀ kt t, motive t → motive (.key kt t))
    (sealed : ∀ k t, motive k → motive t → motive (.sealed k t))
    (hash : ∀ t, motive t → motive (.hash t))
    (exp : ∀ b e, b.isExp = false → b.isProd .gmul = false → e ≠ .prod .mul 0 → motive b →
      motive e → motive (.exp b e))
    (prod : ∀ o s, (∀ t ∈ s, t.isProd o = false) → (∀ t, s ≠ {t}) → (∀ t ∈ s, motive t) →
      motive (.prod o s))
    (t : Term) : motive t := by
  suffices ∀ pt : PreTerm, pt.wf → motive (fold pt) from fold_unfold t ▸ this _ (wf_unfold t)
  intro pt hpt
  induction pt with
  | op0 o => cases o <;> simp only [fold_int, fold_nonce] <;> solve_by_elim
  | op1 o pt ih =>
    replace ih := ih (by simpa [PreTerm.wf] using hpt)
    cases o <;> simp only [fold_key, fold_hash] <;> solve_by_elim
  | op2 o t₁ t₂ ih₁ ih₂ =>
    cases o
    case exp =>
      obtain ⟨hb, hg, he, he1⟩ := PreTerm.wf_ptExp.mp hpt
      rw [fold_ptExp]
      refine exp _ _ ?_ ?_ (fun h => he1 ?_) (ih₁ hb) (ih₂ he)
      · rw [isExp_fold hb, (PreTerm.isGNonFree_eq_false.mp hg).1]
      · rw [isProd_fold _ hb, (PreTerm.isGNonFree_eq_false.mp hg).2]
      · rw [← unfold_fold_of_wf he, h, unfold_prod_zero]
    all_goals
      have ⟨h₁, h₂⟩ : t₁.wf ∧ t₂.wf := by simpa [PreTerm.wf] using hpt
      simp only [fold_pair, fold_sealed]
      solve_by_elim
  | opN o ps ns ihp ihn =>
    obtain ⟨hw, hc, hs⟩ := PreTerm.wf_opN.mp hpt
    rw [fold_opN]
    refine prod o _ (fun t ht => ?_) (make_map_fold_ne_singleton (fun p hp => (hw p hp).1) hc hs)
      fun t ht => ?_ <;> obtain ⟨p, hp, rfl⟩ := exists_of_mem_make_map_fold ht
    · exact (isProd_fold o (hw p hp).1).trans (hw p hp).2
    · rcases List.mem_append.mp hp with hp' | hp'
      exacts [ihp p hp' (hw p hp).1, ihn p hp' (hw p hp).1]

end Term
end Cryptis
