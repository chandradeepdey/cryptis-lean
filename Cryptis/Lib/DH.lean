module

public import Cryptis.Tactics

/-! Diffie-Hellman key shares.

A Diffie-Hellman share `g.exp a` has a single exponent, which is what `dhKeyShare` says, and a
shared secret `g.exp (a * b)` has two. If the owner of a seed `a` consents to publishing only
exponentials with a single exponent (`expPred a t ↔ ▷ □ dhKeyShare t`), then the share of `a` is
public, and the secret is public only if `a` or `b` is.

- `dhSeed P a` says that `a` is such a seed, that it stays secret forever, and that its published
  shares satisfy the invariant `P`. The first part of the file proves the facts above for it.
- Seeds with conditional secrecy: the same facts for a seed whose owner decides when it is public.
- `HL.mkDH` generates a seed. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode Term Term.ProdGroup BigSepFinset

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] [CryptisGS GF]
variable {g a b t : Term}
local bi (IProp GF)

/-- `t` has a single exponent, as a Diffie-Hellman share does. -/
@[rocq_alias cryptis.dh_key_share]
def dhKeyShare (t : Term) : IProp GF := iprop(⌜Multiset.card t.exps.elements = 1⌝)

instance dhKeyShare_persistent (t : Term) : Persistent (dhKeyShare (GF := GF) t) := by
  unfold dhKeyShare; infer_instance

/-- `t` is a share that satisfies `P`. -/
@[rocq_alias cryptis.dh_publ]
def dhPubl (P : Term → IProp GF) (t : Term) : IProp GF := iprop(dhKeyShare t ∧ P t)

/-- `a` is a secret Diffie-Hellman seed whose published exponentials are shares that satisfy
`P`. -/
@[rocq_alias cryptis.dh_seed]
def dhSeed (P : Term → IProp GF) (a : Term) : IProp GF :=
  iprop(minted a ∧ ⌜a.isProd .mul = false⌝ ∧ □ (isPublic a ↔ ▷ False) ∧
    □ (∀ t, expPred a t ↔ ▷ □ dhPubl P t) ∧ □ (∀ t, expPred ↑(E.ofTerm a)⁻¹ t ↔ ▷ False))

instance dhSeed_persistent (P : Term → IProp GF) (a : Term) : Persistent (dhSeed P a) := by
  unfold dhSeed; infer_instance

/-- A term with a single exponent `a` is `a` applied to its base. -/
theorem eq_exp_of_card_exps (h : Multiset.card t.exps.elements = 1) (ha : a ∈ t.exps.posPart) :
    t = t.base.exp a := by
  conv_lhs => rw [← exp_base_prod_exps t, SMS.eq_singleton_of_card_elements_eq_one h ha, prod_singleton]

theorem two_le_card_exps (h : {a, b} ≤ t.exps.posPart) : 2 ≤ Multiset.card t.exps.elements :=
  (Multiset.card_le_card h).trans (by simp [SMS.elements])

theorem exps_dh_share (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (ha : a.isProd .mul = false) : (g.exp a).exps = {a} := by
  rw [exps_exp hx hg, factors_eq_singleton ha]

theorem posPart_exps_dh_secret (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (ha : a.isProd .mul = false) (hb : b.isProd .mul = false) :
    (g.exp (prod .mul ({a} + {b}))).exps.posPart = {a, b} := by
  rw [exps_exp_prod hx hg fun u hu => by
      rcases SMS.mem_or_mem_of_mem_add hu with hu | hu <;> rwa [SMS.mem_singleton.mp hu],
    ← SMS.make_singleton_zero, ← SMS.make_singleton_zero, SMS.make_add_make, add_zero,
    SMS.posPart_make_zero, Multiset.singleton_add, Multiset.insert_eq_cons]

/-- The positive exponents of `g` raised to a product of atoms are these atoms. -/
theorem posPart_exps_exp_prod (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    {X : Multiset Term} (h : ∀ u ∈ X, u.isProd .mul = false) :
    (g.exp ↑(X.map E.ofTerm).prod).exps.posPart = X := by
  rw [show (X.map E.ofTerm).prod = (SMS.make X 0).prod ProdGroup.ofTerm by simp [SMS.prod_make],
    coe_prod, exps_exp_prod hx hg fun u hu => h u (by simpa using SMS.mem_of_mem_make hu),
    SMS.posPart_make_zero]

/-- A share is not the unit of the group. -/
theorem ofTerm_exp_ne_one (hg : g.isProd .gmul = false) (e : Term) : G.ofTerm (g.exp e) ≠ 1 :=
  fun h => ne_prod_zero (isProd_exp_eq_false hg e) (congrArg toTerm h)

/-- If the secret of two seeds is public, then one of the seeds is, up to a later. -/
private theorem isPublic_dh_secret_inv_aux (h : {a, b} ≤ t.exps.posPart) :
    □ (∀ u, expPred a u -∗ ▷ dhKeyShare u) -∗ □ (∀ u, expPred b u -∗ ▷ dhKeyShare u) -∗
    isPublic t -∗ ◇ (isPublic a ∨ isPublic b) := by
  iintro #Ha #Hb #Hp
  icases isPublic_exp_inv_of_le (Multiset.mem_cons_self a {b}) t h $$ Hp with
    ⟨%c, %hc, (#Hc | ⟨%t₃, -, %h₃, #He⟩)⟩
  · simp only [Multiset.mem_cons, Multiset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · imodintro; ileft; iexact Hc
    · imodintro; iright; iexact Hc
  · ihave H : ▷ dhKeyShare t₃ $$ [He]
    · simp only [Multiset.mem_cons, Multiset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · iapply Ha $$ He
      · iapply Hb $$ He
    unfold dhKeyShare
    icases H with >%hcard
    have := two_le_card_exps h₃
    iexfalso; ipureintro; omega

variable {P : Term → IProp GF}

theorem dhSeed_isProd : dhSeed P a ⊢ ⌜a.isProd .mul = false⌝ := by
  unfold dhSeed
  iintro ⟨-, %h, -⟩
  ipureintro; exact h

@[rocq_alias cryptis.dh_seed_elim0]
theorem dhSeed_not_isPublic : dhSeed P a -∗ isPublic a -∗ ▷ False := by
  unfold dhSeed
  iintro ⟨-, -, ⟨#Ha, -⟩, -⟩ #Hp
  iapply Ha $$ Hp

@[rocq_alias cryptis.dh_seed_exp_pred_elim]
theorem dhSeed_expPred_elim (h : a ∈ t.exps.posPart) :
    dhSeed P a -∗ expPred a t -∗ □ ▷ (⌜t = t.base.exp a⌝ ∗ P t) := by
  unfold dhSeed dhPubl dhKeyShare
  iintro ⟨-, -, -, #Ha, -⟩ #He
  icases Ha $$ %t with ⟨#Ha, -⟩
  ihave #H := Ha $$ He
  imodintro
  inext
  icases H with ⟨%hc, #HP⟩
  isplitr
  · ipureintro; exact eq_exp_of_card_exps hc h
  · iexact HP

@[rocq_alias cryptis.dh_seed_elim1]
theorem dhSeed_isPublic_dh_share (hx : g.isExp = false) (hg : g.isProd .gmul = false) :
    dhSeed P a -∗ isPublic (g.exp a) -∗ ▷ P (g.exp a) := by
  iintro #Ha #Hp
  ihave %hm := dhSeed_isProd $$ Ha
  icases isPublic_exp_inv_same (t₁ := a) _ (by simp [exps_dh_share hx hg hm]) $$ Hp with
    (#Hc | ⟨%t, %hb, %ht, #He⟩)
  · ihave H := dhSeed_not_isPublic $$ Ha Hc
    inext
    iexfalso
    iexact H
  · ihave #H := dhSeed_expPred_elim ht $$ Ha He
    inext
    icases H with ⟨%he, #HP⟩
    rw [hb, base_exp hg, base_eq_self hx] at he
    rw [← he]
    iexact HP

@[rocq_alias cryptis.dh_seed_elim2]
theorem dhSeed_isPublic_dh_secret (hx : g.isExp = false) (hg : g.isProd .gmul = false) :
    dhSeed P a -∗ dhSeed P b -∗ isPublic (g.exp (prod .mul ({a} + {b}))) -∗ ▷ False := by
  iintro #Ha #Hb #Hp
  ihave %ha := dhSeed_isProd $$ Ha
  ihave %hb := dhSeed_isProd $$ Hb
  have hkey (c : Term) : dhSeed P c ⊢ □ (∀ u, expPred c u -∗ ▷ dhKeyShare u) := by
    unfold dhSeed dhPubl
    iintro ⟨-, -, -, #H, -⟩ !> %u #He
    icases H $$ %u with ⟨#H, -⟩
    ihave #H := H $$ He
    inext
    icases H with ⟨#H, -⟩
    iexact H
  ihave #Ka := hkey a $$ Ha
  ihave #Kb := hkey b $$ Hb
  icases isPublic_dh_secret_inv_aux (posPart_exps_dh_secret hx hg ha hb).ge $$ Ka Kb Hp with
    >(#Hc | #Hc)
  · iapply dhSeed_not_isPublic $$ Ha Hc
  · iapply dhSeed_not_isPublic $$ Hb Hc

@[rocq_alias cryptis.dh_public_TExp]
theorem isPublic_dh_share_of_dhSeed (hx : g.isExp = false) (hg : g.isProd .gmul = false) :
    minted g -∗ dhSeed P a -∗ ▷ □ P (g.exp a) -∗ isPublic (g.exp a) := by
  iintro #Hg #Ha #HP
  ihave %hm := dhSeed_isProd $$ Ha
  unfold dhSeed dhPubl dhKeyShare
  icases Ha with ⟨#Hm, -, ⟨#Hs, -⟩, #He, -⟩
  iapply (isPublic_exp_iff_of_atom hx hg hm).mpr
  isplit
  · iexact Hg
  isplit
  · iexact Hm
  isplit
  · iright
    icases He $$ %(g.exp a) with ⟨-, #He⟩
    iapply He
    inext
    imodintro
    isplit
    · ipureintro; simp [exps_dh_share hx hg hm]
    · iexact HP
  · imodintro
    iintro #Hp
    iapply isPublic_of_later_false $$ Hg
    iapply Hs $$ Hp

/-! ### Seeds with conditional secrecy

A seed whose owner decides when it is public has a public share, and a secret that is public only
if one of the seeds is. -/

@[rocq_alias cryptis.public_dh_share]
theorem isPublic_dh_share (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (ha : a.isProd .mul = false) :
    isPublic g -∗ minted a -∗ □ (∀ t, expPred a t ↔ ▷ □ dhKeyShare t) -∗
      isPublic (g.exp a) := by
  iintro #Hg #Hm #He
  iapply (isPublic_exp_iff_of_atom hx hg ha).mpr
  isplit
  · iapply isPublic_minted $$ Hg
  isplit
  · iexact Hm
  isplit
  · iright
    icases He $$ %(g.exp a) with ⟨-, #He⟩
    iapply He
    unfold dhKeyShare
    inext; imodintro; ipureintro
    simp [exps_dh_share hx hg ha]
  · iintro !> -
    iexact Hg

@[rocq_alias cryptis.public_dh_secret1]
theorem isPublic_dh_secret (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (ha : a.isProd .mul = false) (hb : b.isProd .mul = false) :
    isPublic g -∗ minted a -∗ minted b -∗ □ (∀ t, expPred a t ↔ ▷ □ dhKeyShare t) -∗
      □ (∀ t, expPred b t ↔ ▷ □ dhKeyShare t) -∗ isPublic a ∨ isPublic b -∗
      isPublic (g.exp (prod .mul ({a} + {b}))) := by
  iintro #Hg #Hma #Hmb #Hea #Heb (#H | #H)
  · rw [show g.exp (prod .mul ({a} + {b})) = (g.exp b).exp a by rw [exp_exp, add_comm]]
    iapply isPublic_exp $$ [] H
    iapply isPublic_dh_share hx hg hb $$ Hg Hmb Heb
  · rw [← exp_exp]
    iapply isPublic_exp $$ [] H
    iapply isPublic_dh_share hx hg ha $$ Hg Hma Hea

@[rocq_alias cryptis.public_dh_secret_gen2]
theorem isPublic_dh_secret_inv_of_le (h : {a, b} ≤ t.exps.posPart) :
    □ (∀ u, expPred a u ↔ ▷ □ dhKeyShare u) -∗ □ (∀ u, expPred b u ↔ ▷ □ dhKeyShare u) -∗
      isPublic t -∗ isPublic a ∨ isPublic b := by
  have hm (c : Term) (hc : c ∈ a ::ₘ {b}) : ⊢ minted (GF := GF) t -∗ minted c :=
    (Subterm.of_mem_exps (SMS.mem_of_mem_posPart (Multiset.mem_of_le h hc))).minted
  have hkey (c : Term) :
      □ (∀ u, expPred c u ↔ ▷ □ dhKeyShare u) ⊢
        □ (∀ u, expPred (GF := GF) c u -∗ ▷ dhKeyShare u) := by
    iintro #H !> %u #He
    icases H $$ %u with ⟨#H, -⟩
    ihave #H := H $$ He
    inext
    iexact H
  iintro #Ha #Hb #Hp
  ihave #Hm := isPublic_minted $$ Hp
  ihave #Ka := hkey a $$ Ha
  ihave #Kb := hkey b $$ Hb
  icases isPublic_dh_secret_inv_aux h $$ Ka Kb Hp with (#H | #H)
  · ileft
    iapply isPublic_of_except0 $$ [] H
    iapply hm a (by simp) $$ Hm
  · iright
    iapply isPublic_of_except0 $$ [] H
    iapply hm b (by simp) $$ Hm

@[rocq_alias cryptis.public_dh_secret_gen]
theorem isPublic_dh_secret_elim_of_le (h : {a, b} ≤ t.exps.posPart) (Q : IProp GF) :
    □ (isPublic a ↔ Q) -∗ □ (∀ u, expPred a u ↔ ▷ □ dhKeyShare u) -∗ □ (isPublic b ↔ Q) -∗
      □ (∀ u, expPred b u ↔ ▷ □ dhKeyShare u) -∗ (isPublic t → Q) := by
  iintro #Hsa #Ha #Hsb #Hb #Hp
  icases isPublic_dh_secret_inv_of_le h $$ Ha Hb Hp with (#H | #H)
  · icases Hsa with ⟨#Hsa, -⟩
    iapply Hsa $$ H
  · icases Hsb with ⟨#Hsb, -⟩
    iapply Hsb $$ H

@[rocq_alias cryptis.public_dh_secret2]
theorem isPublic_dh_secret_inv (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (ha : a.isProd .mul = false) (hb : b.isProd .mul = false) :
    □ (∀ t, expPred a t ↔ ▷ □ dhKeyShare t) -∗ □ (∀ t, expPred b t ↔ ▷ □ dhKeyShare t) -∗
      isPublic (g.exp (prod .mul ({a} + {b}))) -∗ isPublic a ∨ isPublic b :=
  isPublic_dh_secret_inv_of_le (posPart_exps_dh_secret hx hg ha hb).ge

@[rocq_alias cryptis.public_dh_secret']
theorem isPublic_dh_secret_elim (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (ha : a.isProd .mul = false) (hb : b.isProd .mul = false) (Q : IProp GF) :
    □ (isPublic a ↔ Q) -∗ □ (∀ t, expPred a t ↔ ▷ □ dhKeyShare t) -∗ □ (isPublic b ↔ Q) -∗
      □ (∀ t, expPred b t ↔ ▷ □ dhKeyShare t) -∗
      (isPublic (g.exp (prod .mul ({a} + {b}))) → Q) :=
  isPublic_dh_secret_elim_of_le (posPart_exps_dh_secret hx hg ha hb).ge Q

namespace HL

/-- Generate a Diffie-Hellman seed. -/
@[rocq_alias cryptis.mk_dh]
def mkDH : Val := mkNonce

@[rocq_alias cryptis.wp_mk_dh]
theorem wp_mkDH (T : Finset Term) (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (Ψ : Val → IProp GF) :
    cryptisCtx -∗ minted g -∗ □ (∀ t, ⌜t ∈ T⌝ -∗ minted t) -∗
    (∀ a : Nonce, minted (a : Term) -∗ dhSeed P a -∗ termToken (a : Term) ⊤ -∗
      termToken (g.exp a) ⊤ -∗
      ⌜∀ t ∈ T, ∀ t' : Term, t'.Subterm t → (a : Term) ≠ Term.prod .mul (-{t'})⌝ -∗
      Ψ (encode (a : Term))) -∗
    WP hl(&mkDH #()) {{ Ψ }} := by
  iintro #Hctx #Hg #HT Hpost
  unfold mkDH
  iapply wp_mkNonce_freshN T (fun _ => iprop(False)) (dhPubl P) (fun a => {(a : Term), g.exp a})
    $$ Hctx [] [] [Hpost]
  · iintro %t %ht
    iapply HT $$ %t %ht
  · iintro %a
    iapply bigSepFinset_forall.mpr
    iintro %t %ht !>
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · isplit <;> iintro #H <;> iexact H
    · rw [(minted_exp hx hg _).to_eq]
      isplit
      · iintro #H; isplit; iexact Hg; iexact H
      · iintro ⟨-, #H⟩; iexact H
  · simp only [intuitionistically_false.to_eq]
    iintro %a %hfresh #Hm #Hp #He #Hinv Htok
    have hne : (a : Term) ∉ ({g.exp a} : Finset Term) := fun h => by
      have := isExp_of_mem_exps (t := g.exp a) (t' := a)
        (by simp [exps_dh_share (a := (a : Term)) hx hg rfl])
      rw [← Finset.mem_singleton.mp h] at this
      cases this
    icases (bigSepFinset_insert hne).mp $$ Htok with ⟨Ta, Tg⟩
    iapply Hpost $$ %a Hm [] Ta [Tg]
    · unfold dhSeed
      iframe Hm Hp He Hinv
      ipureintro; rfl
    · iapply (bigSepFinset_singleton _).mp $$ Tg
    ipureintro
    rintro t ht t' hsub h
    have : t' = ↑(E.ofTerm a)⁻¹ := congrArg ProdGroup.toTerm (show E.ofTerm t' = _ by
      rw [show E.ofTerm a = (E.ofTerm t')⁻¹ from ProdGroup.ext h, inv_inv])
    refine hfresh t ht (Subterm.trans (Subterm.of_mem_factors (o := .mul) ?_ .refl) hsub)
    rw [this, mem_factors_coe_inv, mem_factors_iff_eq rfl]

end HL

end Cryptis
