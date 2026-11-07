module

public import Cryptis.Core.Term
public import Cryptis.Primitives.PreTerm

/-! HeapLang programs that compute exponentials and products of terms, with specs saying that
they compute the action `a • g` of the exponents `Term.E` on the Diffie-Hellman group `Term.G`,
and the products, inverses and units of both groups. They are wrappers
around the pre-term programs of `Cryptis.Primitives.PreTerm`, since a term is encoded as its
pre-term. -/

@[expose] public section

namespace Cryptis

open Iris Iris.HeapLang BI ProgramLogic Term Term.ProdGroup

namespace HL

/-! ## Programs -/

/-- The scalar product of two terms. -/
@[rocq_alias cryptis.tmul]
def tmul : Val := hl_val% λ t1 t2, &(mul .mul) t1 t2

/-- The scalar inverse of a term. -/
@[rocq_alias cryptis.tinv]
def tinv : Val := hl_val% λ t, &(inv .mul) t

/-- The unit of scalar products. -/
@[rocq_alias cryptis.tone]
def tone : Val := hl_val% λ _, &(prodAux .mul) ([], [])

/-- The group product of two terms. -/
@[rocq_alias cryptis.tgmul]
def tgmul : Val := hl_val% λ t1 t2, &(mul .gmul) t1 t2

/-- The group inverse of a term. -/
@[rocq_alias cryptis.tginv]
def tginv : Val := hl_val% λ t, &(inv .gmul) t

/-- The unit of group products. -/
@[rocq_alias cryptis.tgone]
def tgone : Val := hl_val% λ _, &(prodAux .gmul) ([], [])

/-! ## Specifications -/

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset}
local bi (IProp GF)

/-- Structural equality decides equality of terms. -/
@[rocq_alias cryptis.twp_eq_term]
theorem twp_eqTerm (t₁ t₂ : Term) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (t₁ = t₂))) ⊢ WP hl(&eqTerm &(encode t₁) &(encode t₂)) @ s; E [{ Ψ }] := by
  simpa only [Term.encode_unfold, Term.unfold_inj] using
    twp_eqTerm_preTerm (s := s) (E := E) t₁.unfold t₂.unfold Ψ

@[rocq_alias cryptis.wp_eq_term]
theorem wp_eqTerm (t₁ t₂ : Term) (Ψ : Val → IProp GF) :
    Ψ hl_val(#(decide (t₁ = t₂))) ⊢ WP hl(&eqTerm &(encode t₁) &(encode t₂)) @ s; E {{ Ψ }} :=
  (twp_eqTerm t₁ t₂ Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_texp]
theorem twp_texp (a : Term.E) (g : Term.G) (Ψ : Val → IProp GF) :
    Ψ (encode (↑(a • g) : Term)) ⊢
      WP hl(&texp &(encode (g : Term)) &(encode (a : Term))) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [← Term.encode_unfold ↑g, ← Term.encode_unfold ↑a]
  twp_apply twp_exp (Term.wf_unfold _) (Term.wf_unfold _)
  rw [← Term.unfold_exp, Term.encode_unfold, ← coe_smul]
  iexact H

@[rocq_alias cryptis.wp_texp]
theorem wp_texp (a : Term.E) (g : Term.G) (Ψ : Val → IProp GF) :
    Ψ (encode (↑(a • g) : Term)) ⊢
      WP hl(&texp &(encode (g : Term)) &(encode (a : Term))) @ s; E {{ Ψ }} :=
  (twp_texp a g Ψ).trans (wand_entails twp.to_wp)

/-- `wp_texp` for terms rather than group elements. -/
theorem wp_texp_exp (g a : Term) (Ψ : Val → IProp GF) :
    Ψ (encode (g.exp a)) ⊢ WP hl(&texp &(encode g) &(encode a)) @ s; E {{ Ψ }} :=
  wp_texp (Term.E.ofTerm a) (G.ofTerm g) Ψ

@[rocq_alias cryptis.twp_tmul]
theorem twp_tmul (a b : Term.E) (Ψ : Val → IProp GF) :
    Ψ (encode (↑(a * b) : Term)) ⊢
      WP hl(&tmul &(encode (a : Term)) &(encode (b : Term))) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [← Term.encode_unfold ↑a, ← Term.encode_unfold ↑b]
  twp_apply twp_mul .mul (Term.wf_unfold _) (Term.wf_unfold _)
  rw [← Term.unfold_prod_pair, Term.encode_unfold, ← coe_mul]
  iexact H

@[rocq_alias cryptis.wp_tmul]
theorem wp_tmul (a b : Term.E) (Ψ : Val → IProp GF) :
    Ψ (encode (↑(a * b) : Term)) ⊢
      WP hl(&tmul &(encode (a : Term)) &(encode (b : Term))) @ s; E {{ Ψ }} :=
  (twp_tmul a b Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tinv]
theorem twp_tinv (a : Term.E) (Ψ : Val → IProp GF) :
    Ψ (encode (↑a⁻¹ : Term)) ⊢ WP hl(&tinv &(encode (a : Term))) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  rw [← Term.encode_unfold ↑a]
  twp_apply twp_inv .mul (Term.wf_unfold _)
  rw [← Term.unfold_prod_neg_singleton, Term.encode_unfold, ← coe_inv]
  iexact H

@[rocq_alias cryptis.wp_tinv]
theorem wp_tinv (a : Term.E) (Ψ : Val → IProp GF) :
    Ψ (encode (↑a⁻¹ : Term)) ⊢ WP hl(&tinv &(encode (a : Term))) @ s; E {{ Ψ }} :=
  (twp_tinv a Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tone]
theorem twp_tone (Ψ : Val → IProp GF) :
    Ψ (encode (↑(1 : Term.E) : Term)) ⊢ WP hl(&tone #()) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val((none(), none())) = encode (0 : SMS PreTerm) by simp [SMS.encode_eq]]
  twp_apply twp_prodAux
  rw [show PreTerm.prodAux .mul 0 = (↑(1 : Term.E) : Term).unfold by
    rw [coe_one, Term.unfold_prod, SMS.map_zero, PreTerm.prod, SMS.bind_zero],
    Term.encode_unfold]
  iexact H

@[rocq_alias cryptis.wp_tone]
theorem wp_tone (Ψ : Val → IProp GF) :
    Ψ (encode (↑(1 : Term.E) : Term)) ⊢ WP hl(&tone #()) @ s; E {{ Ψ }} :=
  (twp_tone Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tgmul]
theorem twp_tgmul (x y : Term.G) (Ψ : Val → IProp GF) :
    Ψ (encode (↑(x * y) : Term)) ⊢
      WP hl(&tgmul &(encode (x : Term)) &(encode (y : Term))) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [← Term.encode_unfold ↑x, ← Term.encode_unfold ↑y]
  twp_apply twp_mul .gmul (Term.wf_unfold _) (Term.wf_unfold _)
  rw [← Term.unfold_prod_pair, Term.encode_unfold, ← coe_mul]
  iexact H

@[rocq_alias cryptis.wp_tgmul]
theorem wp_tgmul (x y : Term.G) (Ψ : Val → IProp GF) :
    Ψ (encode (↑(x * y) : Term)) ⊢
      WP hl(&tgmul &(encode (x : Term)) &(encode (y : Term))) @ s; E {{ Ψ }} :=
  (twp_tgmul x y Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tginv]
theorem twp_tginv (x : Term.G) (Ψ : Val → IProp GF) :
    Ψ (encode (↑x⁻¹ : Term)) ⊢ WP hl(&tginv &(encode (x : Term))) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  rw [← Term.encode_unfold ↑x]
  twp_apply twp_inv .gmul (Term.wf_unfold _)
  rw [← Term.unfold_prod_neg_singleton, Term.encode_unfold, ← coe_inv]
  iexact H

@[rocq_alias cryptis.wp_tginv]
theorem wp_tginv (x : Term.G) (Ψ : Val → IProp GF) :
    Ψ (encode (↑x⁻¹ : Term)) ⊢ WP hl(&tginv &(encode (x : Term))) @ s; E {{ Ψ }} :=
  (twp_tginv x Ψ).trans (wand_entails twp.to_wp)

@[rocq_alias cryptis.twp_tgone]
theorem twp_tgone (Ψ : Val → IProp GF) :
    Ψ (encode (↑(1 : Term.G) : Term)) ⊢ WP hl(&tgone #()) @ s; E [{ Ψ }] := by
  iintro H
  twp_rec
  twp_pures
  rw [show hl_val((none(), none())) = encode (0 : SMS PreTerm) by simp [SMS.encode_eq]]
  twp_apply twp_prodAux
  rw [show PreTerm.prodAux .gmul 0 = (↑(1 : Term.G) : Term).unfold by
    rw [coe_one, Term.unfold_prod, SMS.map_zero, PreTerm.prod, SMS.bind_zero],
    Term.encode_unfold]
  iexact H

@[rocq_alias cryptis.wp_tgone]
theorem wp_tgone (Ψ : Val → IProp GF) :
    Ψ (encode (↑(1 : Term.G) : Term)) ⊢ WP hl(&tgone #()) @ s; E {{ Ψ }} :=
  (twp_tgone Ψ).trans (wand_entails twp.to_wp)

end HL

end Cryptis
