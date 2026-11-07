module

public import Cryptis.Core.PreTerm
public import Cryptis.Primitives.SMS

/-! HeapLang programs on pre-terms, with specs saying that each program computes the
corresponding Lean function of `Cryptis.Core.PreTerm`.

- Structural equality and the order of pre-terms.
- Recognisers and destructors: the head of a pre-term, the base and exponent of an exponential,
  and the factor lists of a product.
- Smart constructors: products and exponentials, built in normal form from normal arguments.
  `HL.prod o` computes `PreTerm.prod o`, for either kind of product, and `HL.exp` computes
  `PreTerm.exp`. Products sort and cancel their factors with `HL.smsTo` from
  `Cryptis.Primitives.SMS`, at the order of pre-terms. -/

@[expose] public section

namespace Cryptis

open Iris Iris.HeapLang BI ProgramLogic PreTerm

namespace HL

/-! ## Structural equality -/

/-- Equality of nullary operators. -/
@[rocq_alias cryptis.eq_term_op0]
def eqTermOp0 : Val := hl_val% λ x y, (fst(x) = fst(y)) && (snd(x) = snd(y))

/-- Equality of key types. -/
@[rocq_alias cryptis.eq_key_type]
def eqKeyType : Val := hl_val% λ x y, x = y

/-- Equality of unary operators. -/
@[rocq_alias cryptis.eq_term_op1]
def eqTermOp1 : Val := hl_val%
  λ x y,
    if fst(x) = fst(y) then
      let tag := fst(x);
      if tag = #Tag.key then &eqKeyType (snd(x)) (snd(y)) else #true
    else #false

/-- Equality of binary operators. -/
@[rocq_alias cryptis.eq_term_op2]
def eqTermOp2 : Val := hl_val% λ x y, x = y

/-- Equality of variadic operators. -/
@[rocq_alias cryptis.eq_term_opN]
def eqTermOpN : Val := hl_val% λ x y, x = y

/-- Structural equality of pre-terms. -/
@[rocq_alias cryptis.eq_term]
def eqTerm : Val := hl_val%
  rec eq x y :=
    if fst(x) = fst(y) then
      let tag := fst(x);
      if tag = #Tag.op0 then &eqTermOp0 (snd(x)) (snd(y))
      else if tag = #Tag.op1 then
        &eqTermOp1 (fst(snd(x))) (fst(snd(y))) && eq (snd(snd(x))) (snd(snd(y)))
      else if tag = #Tag.op2 then
        &eqTermOp2 (fst(fst(snd(x)))) (fst(fst(snd(y)))) &&
        eq (snd(fst(snd(x)))) (snd(fst(snd(y)))) &&
        eq (snd(snd(x))) (snd(snd(y)))
      else if tag = #Tag.opN then
        &eqTermOpN (fst(fst(snd(x)))) (fst(fst(snd(y)))) &&
        &eqList eq (snd(fst(snd(x)))) (snd(fst(snd(y)))) &&
        &eqList eq (snd(snd(x))) (snd(snd(y)))
      else #false
    else #false

/-! ## The order -/

/-- The order of nullary operators. -/
@[rocq_alias cryptis.leq_term_op0]
def leqTermOp0 : Val := hl_val%
  λ x y, if fst(x) < fst(y) then #true else if fst(x) = fst(y) then snd(x) ≤ snd(y) else #false

/-- The order of key types. -/
@[rocq_alias cryptis.leq_key_type]
def leqKeyType : Val := hl_val% λ x y, x ≤ y

/-- The order of unary operators. -/
@[rocq_alias cryptis.leq_term_op1]
def leqTermOp1 : Val := hl_val%
  λ x y,
    if fst(x) < fst(y) then #true
    else if fst(x) = fst(y) then
      if fst(x) = #Tag.key then &leqKeyType (snd(x)) (snd(y)) else #true
    else #false

/-- The order of binary operators. -/
@[rocq_alias cryptis.leq_term_op2]
def leqTermOp2 : Val := hl_val% λ x y, x ≤ y

/-- The order of variadic operators. -/
@[rocq_alias cryptis.leq_term_opN]
def leqTermOpN : Val := hl_val% λ x y, x ≤ y

/-- The order of pre-terms. -/
@[rocq_alias cryptis.leq_term]
def leqTerm : Val := hl_val%
  rec loop t1 t2 :=
    if fst(t1) < fst(t2) then #true
    else if fst(t1) = fst(t2) then
      let tag := fst(t1);
      let a1 := snd(t1);
      let a2 := snd(t2);
      if tag = #Tag.op0 then &leqTermOp0 a1 a2
      else if tag = #Tag.op1 then
        let o1 := fst(a1);
        let o2 := fst(a2);
        if &eqTermOp1 o1 o2 then loop (snd(a1)) (snd(a2)) else &leqTermOp1 o1 o2
      else if tag = #Tag.op2 then
        let o1 := fst(fst(a1));
        let o2 := fst(fst(a2));
        if &eqTermOp2 o1 o2 then
          (if &eqTerm (snd(fst(a1))) (snd(fst(a2))) then loop (snd(a1)) (snd(a2))
           else loop (snd(fst(a1))) (snd(fst(a2))))
        else &leqTermOp2 o1 o2
      else if tag = #Tag.opN then
        let o1 := fst(fst(a1));
        let o2 := fst(fst(a2));
        if &eqTermOpN o1 o2 then
          (if &eqList &eqTerm (snd(fst(a1))) (snd(fst(a2)))
           then &leqList &eqTerm loop (snd(a1)) (snd(a2))
           else &leqList &eqTerm loop (snd(fst(a1))) (snd(fst(a2))))
        else &leqTermOpN o1 o2
      else #false
    else #false

/-! ## Recognisers -/

/-- `PreTerm.isExp`. -/
@[rocq_alias cryptis.hl_is_exp]
def isExp : Val := hl_val%
  λ pt, if fst(pt) = #Tag.op2 then fst(fst(snd(pt))) = #Tag.exp else #false

/-- `PreTerm.isProd o`. -/
@[rocq_alias cryptis.hl_is_mul, rocq_alias cryptis.hl_is_gmul]
def isProd (o : TermOpN) : Val := hl_val%
  λ pt, if fst(pt) = #Tag.opN then fst(fst(snd(pt))) = &(encode o) else #false

/-- `PreTerm.isNonce`. -/
@[rocq_alias cryptis.hl_is_nonce]
def isNonce : Val := hl_val%
  λ pt, if fst(pt) = #Tag.op0 then fst(snd(pt)) = #Tag.nonce else #false

/-! ## Destructors -/

/-- The unit of the products of kind `o`, `opN o [] []`. -/
@[rocq_alias cryptis.hl_one, rocq_alias cryptis.hl_gone]
def unit (o : TermOpN) : Val := hl_val((#Tag.opN, ((&(encode o), none()), none())))

/-- `PreTerm.base`. -/
@[rocq_alias cryptis.hl_base]
def base : Val := hl_val% λ pt, if &isExp pt then snd(fst(snd(pt))) else pt

/-- `PreTerm.expo`. -/
@[rocq_alias cryptis.hl_expo]
def expo : Val := hl_val% λ pt, if &isExp pt then snd(snd(pt)) else &(unit .mul)

/-- `PreTerm.rawFactors o`. -/
@[rocq_alias cryptis.hl_factors, rocq_alias cryptis.hl_gfactors]
def factors (o : TermOpN) : Val := hl_val%
  λ pt, if &(isProd o) pt then (snd(fst(snd(pt))), snd(snd(pt))) else (pt :: [], [])

/-! ## Smart constructors -/

/-- `PreTerm.prodAux o`, on the encoding of a signed multiset. -/
@[rocq_alias cryptis.hl_mul_aux, rocq_alias cryptis.hl_gmul_aux]
def prodAux (o : TermOpN) : Val := hl_val%
  λ A,
    match fst(A) with
    | none() => (#Tag.opN, ((&(encode o), fst(A)), snd(A)))
    | some(x) =>
      (match snd(x) with
       | none() =>
         (match snd(A) with
          | none() => fst(x)
          | some(_) => (#Tag.opN, ((&(encode o), fst(A)), snd(A))))
       | some(_) => (#Tag.opN, ((&(encode o), fst(A)), snd(A))))

/-- The concatenation of the first components of `f` on the elements of a list. -/
@[rocq_alias cryptis.hl_bind_fst]
def bindFst : Val := hl_val% λ f l, &foldrList (λ t acc, &appendLists (fst(f t)) acc) [] l

/-- The concatenation of the second components of `f` on the elements of a list. -/
@[rocq_alias cryptis.hl_bind_snd]
def bindSnd : Val := hl_val% λ f l, &foldrList (λ t acc, &appendLists (snd(f t)) acc) [] l

/-- Replace each element of a pair of lists by the pair of lists `f` returns for it, swapping
the pairs of negative elements. -/
@[rocq_alias cryptis.hl_flat]
def flat : Val := hl_val%
  λ f A,
    (&appendLists (&bindFst f (fst(A))) (&bindSnd f (snd(A))),
     &appendLists (&bindSnd f (fst(A))) (&bindFst f (snd(A))))

/-- `bind (factors o)`, on the signed multiset of a pair of lists of normal pre-terms. -/
@[rocq_alias cryptis.hl_normalize_factors, rocq_alias cryptis.hl_normalize_gfactors]
def normalizeFactors (o : TermOpN) : Val := hl_val%
  λ A, &smsTo &leqTerm &eqTerm (&flat &(factors o) A)

/-- `PreTerm.prod o`, on the signed multiset of a pair of lists. -/
@[rocq_alias cryptis.hl_mul_pair, rocq_alias cryptis.hl_gmul_pair]
def prod (o : TermOpN) : Val := hl_val% λ A, &(prodAux o) (&(normalizeFactors o) A)

/-- The product of kind `o` of two pre-terms. -/
@[rocq_alias cryptis.hl_mul, rocq_alias cryptis.hl_gmul]
def mul (o : TermOpN) : Val := hl_val% λ t1 t2, &(prod o) (t1 :: t2 :: [], [])

/-- The inverse of a pre-term for the product of kind `o`. -/
@[rocq_alias cryptis.hl_inv, rocq_alias cryptis.hl_ginv]
def inv (o : TermOpN) : Val := hl_val% λ t, &(prod o) ([], t :: [])

/-- `PreTerm.mkExp`. -/
@[rocq_alias cryptis.hl_mk_exp]
def mkExp : Val := hl_val%
  λ b e, if &eqTerm e &(unit .mul) then b else (#Tag.op2, ((#Tag.exp, b), e))

/-- `PreTerm.expAux`. -/
@[rocq_alias cryptis.hl_exp_aux]
def expAux : Val := hl_val%
  λ b e, &mkExp (&base b) (&(prod .mul) (&expo b :: e :: [], []))

/-- Exponentiation, which distributes over the group factors of the base. -/
@[rocq_alias cryptis.hl_exp]
def exp : Val := hl_val%
  λ b e,
    let A := &(factors .gmul) b;
    let f := (λ t, &expAux t e);
    &(prod .gmul) (&mapList f (fst(A)), &mapList f (snd(A)))

/-- Exponentiation, as exposed to protocol code. -/
@[rocq_alias cryptis.texp]
def texp : Val := hl_val% λ b e, &exp b e

end HL

/-! ## Factors as stored -/

namespace PreTerm

variable {o : TermOpN} {pt : PreTerm}

/-- A signed multiset of pre-terms is encoded as its factor lists. -/
theorem encode_sms (S : SMS PreTerm) : encode S = encode (toLists S) := rfl

/-- On normal pre-terms, multiplying the factors of the elements of two lists computes
`bind (factors o)`. -/
@[rocq_alias cryptis.car_bind_factors, rocq_alias cryptis.car_bind_gfactors]
theorem make_flatMap_rawFactors {A : List PreTerm × List PreTerm} (h : ∀ t ∈ A.1 ++ A.2, wf t) :
    SMS.make (A.1.flatMap (fun t => (t.rawFactors o).1) ++
        A.2.flatMap (fun t => (t.rawFactors o).2) : List PreTerm)
      (A.1.flatMap (fun t => (t.rawFactors o).2) ++
        A.2.flatMap (fun t => (t.rawFactors o).1) : List PreTerm) =
      (SMS.make A.1 A.2).bind (factors o) :=
  SMS.make_flatMap fun t ht => by
    rw [← toLists_factors (h t ht)]
    exact ⟨Multiset.sort_eq _ _, Multiset.sort_eq _ _⟩

theorem map_factors_eq_make (f : PreTerm → PreTerm) (h : wf pt) :
    (pt.factors o).map f =
      SMS.make ((pt.rawFactors o).1.map f) ((pt.rawFactors o).2.map f) := by
  rw [SMS.map_eq_make, ← Multiset.map_coe, ← Multiset.map_coe, ← toLists_factors h, toLists,
    Multiset.sort_eq, Multiset.sort_eq]

theorem make_pair_nil (t₁ t₂ : PreTerm) :
    SMS.make (([t₁, t₂] : List PreTerm) : Multiset PreTerm) ([] : List PreTerm) =
      {t₁} + {t₂} := by
  simp [← Multiset.cons_coe, SMS.make_cons_left]

theorem make_nil_singleton (t : PreTerm) :
    SMS.make (([] : List PreTerm) : Multiset PreTerm) ([t] : List PreTerm) = -{t} := by
  simp [← SMS.make_singleton_zero]

end PreTerm

/-! ## Specifications -/

namespace WpEncode

/-! After `open scoped Cryptis.WpEncode`, the WP tactics unfold the tags and the encodings of
operators and pre-terms. -/

attribute [scoped wp_expr_simp] Tag.int Tag.nonce Tag.key Tag.hash Tag.pair Tag.sealed Tag.exp
  Tag.mul Tag.gmul Tag.op0 Tag.op1 Tag.op2 Tag.opN
  TermOp0.encode_int TermOp0.encode_nonce TermOp1.encode_key TermOp1.encode_hash
  TermOp2.encode_pair TermOp2.encode_sealed TermOp2.encode_exp TermOpN.encode_mul
  TermOpN.encode_gmul PreTerm.encode_op0 PreTerm.encode_op1 PreTerm.encode_op2
  PreTerm.encode_opN encode_prod

end WpEncode

section Specs

/-! In this section, the HeapLang tactics evaluate literals (`Cryptis.WpLit`) and unfold the
encodings of operators and pre-terms (`Cryptis.WpEncode`). -/

open scoped WpLit WpEncode

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset}
local bi (IProp GF)

namespace HL

@[rocq_alias cryptis.twp_eq_term_op0]
theorem twp_eqTermOp0 (o₁ o₂ : TermOp0) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (o₁ = o₂))) ⊢ WP hl(&eqTermOp0 &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  cases o₁ <;> cases o₂ <;> twp_rec <;> twp_pures <;> simp [Nonce.ext_iff] <;> iexact H

@[rocq_alias cryptis.twp_eq_key_type]
theorem twp_eqKeyType (kt₁ kt₂ : KeyType) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (kt₁ = kt₂))) ⊢
      WP hl(&eqKeyType &(encode kt₁) &(encode kt₂)) @ s; E [{ Ψ }] := by
  iintro H
  simp only [KeyType.encode_eq]
  twp_rec
  twp_pures
  simp
  iexact H

@[rocq_alias cryptis.twp_eq_term_op1]
theorem twp_eqTermOp1 (o₁ o₂ : TermOp1) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (o₁ = o₂))) ⊢ WP hl(&eqTermOp1 &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  cases o₁ <;> cases o₂ <;> twp_rec <;> twp_pures <;> simp <;>
    first | iexact H | twp_apply twp_eqKeyType; iexact H

@[rocq_alias cryptis.twp_eq_term_op2]
theorem twp_eqTermOp2 (o₁ o₂ : TermOp2) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (o₁ = o₂))) ⊢ WP hl(&eqTermOp2 &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  cases o₁ <;> cases o₂ <;> twp_rec <;> twp_pures <;> simp <;> iexact H

@[rocq_alias cryptis.twp_eq_term_opN]
theorem twp_eqTermOpN (o₁ o₂ : TermOpN) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (o₁ = o₂))) ⊢ WP hl(&eqTermOpN &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  cases o₁ <;> cases o₂ <;> twp_rec <;> twp_pures <;> simp <;> iexact H

/-- Structural equality decides equality of pre-terms. -/
@[rocq_alias cryptis.twp_eq_pre_term, rocq_alias cryptis.twp_eq_pre_term_aux]
theorem twp_eqTerm_preTerm (t₁ t₂ : PreTerm) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (t₁ = t₂))) ⊢ WP hl(&eqTerm &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  induction t₁ generalizing t₂ Ψ with
  | op0 o =>
    rcases t₂ with o' | _ | _ | _ <;> iintro H <;> twp_rec <;> twp_pures <;> simp <;>
      try iexact H
    twp_apply twp_eqTermOp0; iexact H
  | op1 o t ih =>
    rcases t₂ with _ | ⟨o', t'⟩ | _ | _ <;> iintro H <;> twp_rec <;> twp_pures <;> simp <;>
      try iexact H
    twp_apply twp_eqTermOp1
    by_cases ho : o = o' <;> simp [ho] <;> twp_pures
    · twp_apply ih; iexact H
    · iexact H
  | op2 o t u iht ihu =>
    rcases t₂ with _ | _ | ⟨o', t', u'⟩ | _ <;> iintro H <;> twp_rec <;> twp_pures <;> simp <;>
      try iexact H
    twp_apply twp_eqTermOp2
    by_cases ho : o = o' <;> simp [ho] <;> twp_pures
    · twp_apply iht
      by_cases ht : t = t' <;> simp [ht] <;> twp_pures
      · twp_apply ihu; iexact H
      · iexact H
    · iexact H
  | opN o ps ns ihp ihn =>
    rcases t₂ with _ | _ | _ | ⟨o', ps', ns'⟩ <;> iintro H <;> twp_rec <;> twp_pures <;> simp <;>
      try iexact H
    twp_apply twp_eqTermOpN
    by_cases ho : o = o' <;> simp [ho] <;> twp_pures
    · twp_apply twp_eqList _ _ _ _ ihp
      by_cases hp : ps = ps' <;> simp [hp] <;> twp_pures
      · twp_apply twp_eqList _ _ _ _ ihn; iexact H
      · iexact H
    · iexact H

@[rocq_alias cryptis.twp_leq_key_type]
theorem twp_leqKeyType (kt₁ kt₂ : KeyType) (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare kt₁ kt₂).isLE)) ⊢
      WP hl(&leqKeyType &(encode kt₁) &(encode kt₂)) @ s; E [{ Ψ }] := by
  iintro H
  simp only [KeyType.encode_eq]
  twp_rec
  twp_pures
  simp [KeyType.compare_eq, isLE_compare_eq_decide]
  iexact H

@[rocq_alias cryptis.twp_leq_term_op0]
theorem twp_leqTermOp0 (o₁ o₂ : TermOp0) (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare o₁ o₂).isLE)) ⊢
      WP hl(&leqTermOp0 &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  cases o₁ <;> cases o₂ <;> twp_rec <;> twp_pures <;>
    simp [Nonce.compare_eq, Loc.le_iff, isLE_compare_eq_decide] <;> iexact H

@[rocq_alias cryptis.twp_leq_term_op1]
theorem twp_leqTermOp1 (o₁ o₂ : TermOp1) (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare o₁ o₂).isLE)) ⊢
      WP hl(&leqTermOp1 &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  cases o₁ <;> cases o₂ <;> twp_rec <;> twp_pures <;> simp <;>
    first | iexact H | twp_apply twp_leqKeyType; iexact H

@[rocq_alias cryptis.twp_leq_term_op2]
theorem twp_leqTermOp2 (o₁ o₂ : TermOp2) (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare o₁ o₂).isLE)) ⊢
      WP hl(&leqTermOp2 &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  simp only [TermOp2.encode_eq, TermOp2.compare_eq]
  twp_rec
  twp_pures
  simp [isLE_compare_eq_decide]
  iexact H

@[rocq_alias cryptis.twp_leq_term_opN]
theorem twp_leqTermOpN (o₁ o₂ : TermOpN) (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare o₁ o₂).isLE)) ⊢
      WP hl(&leqTermOpN &(encode o₁) &(encode o₂)) @ s; E [{ Ψ }] := by
  iintro H
  simp only [TermOpN.encode_eq, TermOpN.compare_eq]
  twp_rec
  twp_pures
  simp [isLE_compare_eq_decide]
  iexact H

/-- `leqTerm` compares pre-terms with different constructors by their constructors. -/
theorem twp_leqTerm_of_ctorIdx_ne {t₁ t₂ : PreTerm} (h : t₁.ctorIdx ≠ t₂.ctorIdx)
    (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare t₁ t₂).isLE)) ⊢
      WP hl(&leqTerm &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  rw [compare_of_ctorIdx_ne h]
  cases t₁ <;> cases t₂ <;> first | exact absurd rfl h |
    (iintro H; twp_rec; twp_pures; simp [PreTerm.ctorIdx, isLE_compare_eq_decide]; iexact H)

#rocq_ignore cryptis.eq_term_spec "Local induction motive of HL.twp_eqTerm_preTerm"
#rocq_ignore cryptis.leq_term_spec "Local induction motive of HL.twp_leqTerm"
#rocq_ignore cryptis.bool_decide_lexico_pair "isLE_compare_then, with PreTerm.compare_opN"

/-- `leqTerm` decides the order of pre-terms. -/
@[rocq_alias cryptis.twp_leq_pre_term]
theorem twp_leqTerm (t₁ t₂ : PreTerm) (Ψ : Val → IProp GF) :
    Ψ hl_val(#((compare t₁ t₂).isLE)) ⊢
      WP hl(&leqTerm &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  have heq t₁ t₂ := triple_of_twp (GF := GF) (s := s) (E := E) (twp_eqTerm_preTerm t₁ t₂)
  induction t₁ generalizing t₂ Ψ with
  | op0 o =>
    cases t₂
    case op0 o' =>
      iintro H; twp_rec; twp_pures
      twp_apply twp_leqTermOp0
      simp only [compare_op0]
      iexact H
    all_goals exact twp_leqTerm_of_ctorIdx_ne (by simp [PreTerm.ctorIdx]) Ψ
  | op1 o t ih =>
    cases t₂
    case op1 o' t' =>
      rw [compare_op1, isLE_compare_then]
      iintro H; twp_rec; twp_pures
      twp_apply twp_eqTermOp1
      by_cases ho : o = o' <;> simp [ho] <;> twp_pures
      · twp_apply ih; iexact H
      · twp_apply twp_leqTermOp1; iexact H
    all_goals exact twp_leqTerm_of_ctorIdx_ne (by simp [PreTerm.ctorIdx]) Ψ
  | op2 o t u iht ihu =>
    cases t₂
    case op2 o' t' u' =>
      rw [compare_op2, isLE_compare_then, isLE_compare_then]
      iintro H; twp_rec; twp_pures
      twp_apply twp_eqTermOp2
      by_cases ho : o = o' <;> simp [ho] <;> twp_pures
      · twp_apply twp_eqTerm_preTerm
        by_cases ht : t = t' <;> simp [ht] <;> twp_pures
        · twp_apply ihu; iexact H
        · twp_apply iht; iexact H
      · twp_apply twp_leqTermOp2; iexact H
    all_goals exact twp_leqTerm_of_ctorIdx_ne (by simp [PreTerm.ctorIdx]) Ψ
  | opN o ps ns ihp ihn =>
    cases t₂
    case opN o' ps' ns' =>
      rw [compare_opN, isLE_compare_then, isLE_compare_then]
      iintro H; twp_rec; twp_pures
      twp_apply twp_eqTermOpN
      by_cases ho : o = o' <;> simp [ho] <;> twp_pures
      · twp_apply twp_eqList _ _ _ _ fun x _ y Ψ => twp_eqTerm_preTerm x y Ψ
        by_cases hp : ps = ps' <;> simp [hp] <;> twp_pures
        · twp_apply twp_leqList _ _ _ _ heq (fun x hx y => triple_of_twp (ihn x hx y)) $$ [//]
            with -
          iexact H
        · twp_apply twp_leqList _ _ _ _ heq (fun x hx y => triple_of_twp (ihp x hx y)) $$ [//]
            with -
          iexact H
      · twp_apply twp_leqTermOpN; iexact H
    all_goals exact twp_leqTerm_of_ctorIdx_ne (by simp [PreTerm.ctorIdx]) Ψ

/-! ### Recognisers -/

@[rocq_alias cryptis.twp_hl_is_exp]
theorem twp_isExp (pt : PreTerm) (Ψ : Val → IProp GF) :
    Ψ hl_val(#pt.isExp) ⊢ WP hl(&isExp &(encode pt)) @ s; E [{ Ψ }] := by
  iintro H
  rcases pt with _ | _ | ⟨_ | _ | _⟩ | _ <;> twp_rec <;> twp_pures <;> simp only [PreTerm.isExp] <;>
    iexact H

@[rocq_alias cryptis.twp_hl_is_mul, rocq_alias cryptis.twp_hl_is_gmul]
theorem twp_isProd (o : TermOpN) (pt : PreTerm) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(pt.isProd o)) ⊢ WP hl(&(isProd o) &(encode pt)) @ s; E [{ Ψ }] := by
  iintro H
  cases o <;> rcases pt with _ | _ | _ | ⟨_ | _⟩ <;> twp_rec <;> twp_pures <;>
    simp only [PreTerm.isProd, reduceCtorEq, decide_true, decide_false] <;> iexact H

@[rocq_alias cryptis.twp_hl_is_nonce]
theorem twp_isNonce (pt : PreTerm) (Ψ : Val → IProp GF) :
    Ψ hl_val(#pt.isNonce) ⊢ WP hl(&isNonce &(encode pt)) @ s; E [{ Ψ }] := by
  iintro H
  rcases pt with ⟨_ | _⟩ | _ | _ | _ <;> twp_rec <;> twp_pures <;> simp only [PreTerm.isNonce] <;>
    iexact H

/-! ### Destructors -/

@[rocq_alias cryptis.hl_oneE, rocq_alias cryptis.hl_goneE]
theorem unit_eq (o : TermOpN) : unit o = encode (opN o [] []) := rfl

@[rocq_alias cryptis.twp_hl_base]
theorem twp_base (pt : PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode pt.base) ⊢ WP hl(&base &(encode pt)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_isExp
  cases h : pt.isExp
  · twp_pures; rw [base_eq_self h]; iexact H
  · obtain ⟨b, e, rfl⟩ := isExp_iff.mp h
    twp_pures; simp only [PreTerm.base]; iexact H

@[rocq_alias cryptis.twp_hl_expo]
theorem twp_expo (pt : PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode pt.expo) ⊢ WP hl(&expo &(encode pt)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_isExp
  cases h : pt.isExp
  · twp_pures; rw [expo_eq_unit h, ← unit_eq]; iexact H
  · obtain ⟨b, e, rfl⟩ := isExp_iff.mp h
    twp_pures; simp only [PreTerm.expo]; iexact H

@[rocq_alias cryptis.twp_hl_factors, rocq_alias cryptis.twp_hl_gfactors]
theorem twp_factors (o : TermOpN) (pt : PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode (pt.rawFactors o)) ⊢ WP hl(&(factors o) &(encode pt)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_isProd
  cases h : pt.isProd o
  · twp_pures
    twp_rec
    twp_pures
    simp only [rawFactors_eq_singleton h, encode_prod, encode_cons, encode_nil]
    iexact H
  · obtain ⟨ps, ns, rfl⟩ := isProd_iff.mp h
    twp_pures; simp only [rawFactors_opN, encode_prod]; iexact H

/-! ### Smart constructors -/

@[rocq_alias cryptis.twp_hl_mul_aux, rocq_alias cryptis.twp_hl_gmul_aux]
theorem twp_prodAux (o : TermOpN) (S : SMS PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.prodAux o S)) ⊢ WP hl(&(prodAux o) &(encode S)) @ s; E [{ Ψ }] := by
  rw [encode_sms, PreTerm.prodAux]
  generalize toLists S = A
  obtain ⟨ps, ns⟩ := A
  iintro H
  rcases ps with _ | ⟨t, _ | ⟨u, ps⟩⟩ <;> rcases ns with _ | ⟨n, ns⟩ <;>
    simp only [encode_prod, encode_cons, encode_nil, encode_opN, Tag.opN] <;> twp_rec <;>
    twp_pures <;> iexact H

section Flat

variable (f : PreTerm → List PreTerm × List PreTerm) (fv : Val)
  (hfv : ∀ (pt : PreTerm) (Ψ : Val → IProp GF),
    Ψ (encode (f pt)) ⊢ WP hl(&fv &(encode pt)) @ s; E [{ Ψ }])
include hfv

@[rocq_alias cryptis.twp_hl_bind_fst]
theorem twp_bindFst (ts : List PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode (ts.flatMap fun t => (f t).1)) ⊢
      WP hl(&bindFst &fv &(encode ts)) @ s; E [{ Ψ }] := by
  have hg (t : PreTerm) (acc : List PreTerm) :
      [{ True }] hl(v(λ t acc, &appendLists (fst(&fv t)) acc) &(encode t) &(encode acc)) @ s; E
        [{ RET encode ((f t).1 ++ acc); True }] := by
    iintro %Φ - HΦ
    twp_pures
    twp_apply hfv
    rw [encode_prod (f t)]
    twp_pures
    twp_apply twp_appendLists
    iapply HΦ $$ [//]
  have hfold : ts.foldr (fun t acc => (f t).1 ++ acc) [] = ts.flatMap fun t => (f t).1 := by
    induction ts <;> simp [*]
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val(none()) = encode ([] : List PreTerm) from rfl]
  twp_apply twp_foldrList (fun t acc => (f t).1 ++ acc) _ ts [] hg $$ [//] with -
  rw [hfold]
  iexact H

@[rocq_alias cryptis.twp_hl_bind_snd]
theorem twp_bindSnd (ts : List PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode (ts.flatMap fun t => (f t).2)) ⊢
      WP hl(&bindSnd &fv &(encode ts)) @ s; E [{ Ψ }] := by
  have hg (t : PreTerm) (acc : List PreTerm) :
      [{ True }] hl(v(λ t acc, &appendLists (snd(&fv t)) acc) &(encode t) &(encode acc)) @ s; E
        [{ RET encode ((f t).2 ++ acc); True }] := by
    iintro %Φ - HΦ
    twp_pures
    twp_apply hfv
    rw [encode_prod (f t)]
    twp_pures
    twp_apply twp_appendLists
    iapply HΦ $$ [//]
  have hfold : ts.foldr (fun t acc => (f t).2 ++ acc) [] = ts.flatMap fun t => (f t).2 := by
    induction ts <;> simp [*]
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val(none()) = encode ([] : List PreTerm) from rfl]
  twp_apply twp_foldrList (fun t acc => (f t).2 ++ acc) _ ts [] hg $$ [//] with -
  rw [hfold]
  iexact H

@[rocq_alias cryptis.twp_hl_flat]
theorem twp_flat (A : List PreTerm × List PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode (A.1.flatMap (fun t => (f t).1) ++ A.2.flatMap (fun t => (f t).2),
      A.1.flatMap (fun t => (f t).2) ++ A.2.flatMap (fun t => (f t).1))) ⊢
      WP hl(&flat &fv &(encode A)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_smart_apply twp_bindFst f fv hfv A.2
  twp_smart_apply twp_bindSnd f fv hfv A.1
  twp_smart_apply twp_appendLists
  twp_smart_apply twp_bindSnd f fv hfv A.2
  twp_smart_apply twp_bindFst f fv hfv A.1
  twp_smart_apply twp_appendLists
  twp_pures
  iexact H

end Flat

@[rocq_alias cryptis.twp_leq_pre_term_le]
theorem twp_leqTerm_le (t₁ t₂ : PreTerm) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (t₁ ≤ t₂))) ⊢ WP hl(&leqTerm &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  rw [show decide (t₁ ≤ t₂) = (compare t₁ t₂).isLE from Bool.eq_iff_iff.mpr (by simp; rfl)]
  exact twp_leqTerm t₁ t₂ Ψ

@[rocq_alias cryptis.twp_hl_normalize_factors, rocq_alias cryptis.twp_hl_normalize_gfactors]
theorem twp_normalizeFactors (o : TermOpN) (A : List PreTerm × List PreTerm)
    (h : ∀ t ∈ A.1 ++ A.2, wf t) (Ψ : Val → IProp GF) :
    Ψ (encode ((SMS.make A.1 A.2).bind (PreTerm.factors o))) ⊢
      WP hl(&(normalizeFactors o) &(encode A)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_apply twp_flat (PreTerm.rawFactors o) (factors o) (twp_factors o) A
  twp_apply twp_smsTo eqTerm leqTerm twp_eqTerm_preTerm twp_leqTerm_le
  rw [make_flatMap_rawFactors h]
  iexact H

@[rocq_alias cryptis.twp_hl_mul_pair, rocq_alias cryptis.twp_hl_gmul_pair]
theorem twp_prod (o : TermOpN) (A : List PreTerm × List PreTerm) (h : ∀ t ∈ A.1 ++ A.2, wf t)
    (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.prod o (SMS.make A.1 A.2))) ⊢
      WP hl(&(prod o) &(encode A)) @ s; E [{ Ψ }] := by
  rw [PreTerm.prod]
  iintro H
  twp_rec
  twp_apply twp_normalizeFactors o A h
  twp_apply twp_prodAux
  iexact H

@[rocq_alias cryptis.twp_hl_mul, rocq_alias cryptis.twp_hl_gmul]
theorem twp_mul (o : TermOpN) {t₁ t₂ : PreTerm} (h₁ : wf t₁) (h₂ : wf t₂) (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.prod o ({t₁} + {t₂}))) ⊢
      WP hl(&(mul o) &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val(none()) = encode ([] : List PreTerm) from rfl]
  twp_apply twp_cons t₂ []
  twp_apply twp_cons t₁ [t₂]
  twp_pures
  rw [show hl_val((&(encode [t₁, t₂]), &(encode ([] : List PreTerm)))) =
    encode (([t₁, t₂] : List PreTerm), ([] : List PreTerm)) from rfl]
  twp_apply twp_prod o ([t₁, t₂], []) (by simp [h₁, h₂])
  rw [make_pair_nil]
  iexact H

@[rocq_alias cryptis.twp_hl_inv, rocq_alias cryptis.twp_hl_ginv]
theorem twp_inv (o : TermOpN) {t : PreTerm} (h : wf t) (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.prod o (-{t}))) ⊢ WP hl(&(inv o) &(encode t)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val(none()) = encode ([] : List PreTerm) from rfl]
  twp_apply twp_cons t []
  twp_pures
  rw [show hl_val((none(), &(encode [t]))) =
    encode (([] : List PreTerm), ([t] : List PreTerm)) from rfl]
  twp_apply twp_prod o ([], [t]) (by simp [h])
  rw [make_nil_singleton]
  iexact H

@[rocq_alias cryptis.twp_hl_mk_exp]
theorem twp_mkExp (b e : PreTerm) (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.mkExp b e)) ⊢ WP hl(&mkExp &(encode b) &(encode e)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [unit_eq]
  twp_apply twp_eqTerm_preTerm
  unfold PreTerm.mkExp
  by_cases h : e = ptMul [] [] <;> simp [h] <;> twp_pures <;> iexact H

@[rocq_alias cryptis.twp_hl_exp_aux]
theorem twp_expAux {b e : PreTerm} (hb : wf b) (he : wf e) (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.expAux b e)) ⊢ WP hl(&expAux &(encode b) &(encode e)) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val(none()) = encode ([] : List PreTerm) from rfl]
  twp_apply twp_cons e []
  twp_smart_apply twp_expo b
  twp_apply twp_cons b.expo [e]
  twp_pures
  rw [show hl_val((&(encode [b.expo, e]), &(encode ([] : List PreTerm)))) =
    encode (([b.expo, e] : List PreTerm), ([] : List PreTerm)) from rfl]
  twp_apply twp_prod .mul ([b.expo, e], []) (by simp [wf_expo hb, he])
  twp_smart_apply twp_base b
  twp_apply twp_mkExp
  rw [PreTerm.expAux, ← make_pair_nil]
  iexact H

/-- `exp` computes `exp`, distributing over the group factors of the base. -/
@[rocq_alias cryptis.twp_hl_exp]
theorem twp_exp {b e : PreTerm} (hb : wf b) (he : wf e) (Ψ : Val → IProp GF) :
    Ψ (encode (PreTerm.exp b e)) ⊢ WP hl(&exp &(encode b) &(encode e)) @ s; E [{ Ψ }] := by
  have hg := wfFactors_factors (o := .gmul) hb
  have hmem {t} (ht : t ∈ (b.rawFactors .gmul).1 ++ (b.rawFactors .gmul).2) :
      t ∈ b.factors .gmul :=
    mem_of_mem_toLists (by rwa [toLists_factors hb])
  have hf t (ht : t ∈ (b.rawFactors .gmul).1 ++ (b.rawFactors .gmul).2) :
      [{ True }] hl(v(λ t, &expAux t &(encode e)) &(encode t)) @ s; E
        [{ RET encode (PreTerm.expAux t e); True }] := by
    iintro %Φ - HΦ
    twp_pures
    twp_apply twp_expAux (hg.wf (hmem ht)) he
    iapply HΦ $$ [//]
  iintro H
  twp_rec
  twp_pures
  twp_apply twp_factors .gmul b
  twp_pures
  twp_smart_apply twp_mapList (PreTerm.expAux · e) _ (b.rawFactors .gmul).2
    (fun t ht => hf t (List.mem_append_right _ ht)) $$ [//] with -
  twp_smart_apply twp_mapList (PreTerm.expAux · e) _ (b.rawFactors .gmul).1
    (fun t ht => hf t (List.mem_append_left _ ht)) $$ [//] with -
  twp_pures
  have hwf : ∀ t ∈ (b.rawFactors .gmul).1.map (PreTerm.expAux · e) ++
      (b.rawFactors .gmul).2.map (PreTerm.expAux · e), wf t := by
    simp only [← List.map_append, List.mem_map]
    rintro _ ⟨u, hu, rfl⟩
    exact wf_expAux (hg.wf (hmem hu)) (hg.isProd_eq_false (hmem hu)) he
  rw [show hl_val((&(encode ((b.rawFactors .gmul).1.map (PreTerm.expAux · e))),
      &(encode ((b.rawFactors .gmul).2.map (PreTerm.expAux · e))))) =
    encode ((b.rawFactors .gmul).1.map (PreTerm.expAux · e),
      (b.rawFactors .gmul).2.map (PreTerm.expAux · e)) from rfl]
  twp_apply twp_prod .gmul (_, _) hwf
  rw [PreTerm.exp, map_factors_eq_make _ hb]
  iexact H

end HL

end Specs

end Cryptis
