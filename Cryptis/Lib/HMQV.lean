module

public import Cryptis.Lib.DH
public import Cryptis.Lib.EExp
public import Cryptis.Upstream.Iris.Namespaces
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-! The HMQV key exchange.

HMQV is an authenticated Diffie-Hellman key exchange. Each party `a` has a long-term private key
`pa` with public key `Pa = g^pa`, and generates an ephemeral private key `xa` with public key
`Xa = g^xa` for each session. The parties exchange their public keys, and each computes the
session key

  `K = (Xb * Pb^mb)^(xa + ma * pa) = (Xa * Pa^ma)^(xb + mb * pb)`,

where the multiplier `ma = H(ta, Xa, Pb)` hashes the party's ephemeral key and the peer's
long-term key with a tag `ta`, and the tags of the two roles differ. The key can only be computed
from the long-term and ephemeral private keys of one of the parties, so a session that uses it is
implicitly authenticated.

Terms have no addition of exponents, so the scalar `xa + ma * pa` is the extended exponent
`hmqvS`, and `hmqvK` raises the base `hmqvY` to it: the key is `(Y^xa) * (Y^(ma * pa))`. Its
logarithms are products, `log b K = (xa + ma * pa) * log b Y`, so equations between keys become
equations in the domain `EExp`. The main results:

- `hmqvK_comm`: both parties compute the same key.
- `hmqvK_inj` and `hmqvK_inj'`: the key determines the public keys used to compute it, for two
  keys of the same role and for the keys of an initiator and a responder, provided that neither
  the key nor the claimed long-term keys are the unit of the group (`hmqvK_ne_one`).
- `hmqvK_inj_fresh`: a responder whose ephemeral key is fresh binds the long-term key that its
  peer claimed, whatever that key is.
- `isPublic_hmqvK_honest` (forward secrecy) and `isPublic_hmqvK_forged` (resistance to key
  compromise impersonation): a key is public only if the private keys of the parties are.

The injectivity proofs compare the parts of the logarithms by their degree in the largest
multiplier, which the public inputs are too small to contain. -/

@[expose] public section
namespace Cryptis

open Iris Iris.BI Iris.HeapLang Iris.ProofMode Term Term.ProdGroup MonoidAlgebra EExp BigSepMultiset

/-! ### The key formula -/

/-- The multiplier of a party with ephemeral public key `X` whose peer has long-term public key
`P`. -/
@[rocq_alias cryptis.hmqv_m]
def hmqvM (N : Namespace) (t : String) (X P : Term) : Term :=
  .hash (Spec.tag (ofNamespace (N.@t)) (Spec.ofList [X, P]))

/-- The base that a party with long-term public key `Pa` raises to its scalar: the peer's
ephemeral public key times its long-term public key raised to the peer's multiplier. -/
@[rocq_alias cryptis.hmqv_Y]
def hmqvY (N : Namespace) (tb : String) (Pa Pb Xb : Term) : G :=
  G.ofTerm Xb * (E.ofTerm (hmqvM N tb Xb Pa) • G.ofTerm Pb)

/-- The scalar `x + m * p` of a party with multiplier `m`, long-term private key `p` and
ephemeral private key `x`. -/
@[rocq_alias cryptis.hmqv_s]
noncomputable def hmqvS (m p x : Term) : EExp :=
  of ℤ E (E.ofTerm x) + of ℤ E (E.ofTerm m * E.ofTerm p)

/-- The session key of a party with private keys `pa`, `xa` and public keys `Pa`, `Xa`, whose peer
has public keys `Pb`, `Xb`. -/
@[rocq_alias cryptis.hmqv_K]
noncomputable def hmqvK (N : Namespace) (ta tb : String) (pa xa Pa Xa Pb Xb : Term) : G :=
  (hmqvS (hmqvM N ta Xa Pb) pa xa • Additive.ofMul (hmqvY N tb Pa Pb Xb)).toMul

variable {N : Namespace} {g : Term} {t t' ta tb : String}
variable {X P X' P' Pa Xa Pb Xb Pa' Xa' Pb' Xb' pa xa : Term}

@[simp, rocq_alias cryptis.hmqv_m_inj]
theorem hmqvM_inj : hmqvM N t X P = hmqvM N t' X' P' ↔ t = t' ∧ X = X' ∧ P = P' := by
  simp [hmqvM, ndot_inj]

theorem hmqvM_ne (h : t ≠ t') : hmqvM N t X P ≠ hmqvM N t' X' P' :=
  fun e => h (hmqvM_inj.mp e).1

@[rocq_alias cryptis.tsize_hmqv_m_lt]
theorem tsize_lt_hmqvM_left (N : Namespace) (t : String) (X P : Term) :
    X.tsize < (hmqvM N t X P).tsize := by
  simp [hmqvM, Spec.tag]; omega

@[rocq_alias cryptis.tsize_hmqv_m_lt2]
theorem tsize_lt_hmqvM_right (N : Namespace) (t : String) (X P : Term) :
    P.tsize < (hmqvM N t X P).tsize := by
  simp [hmqvM, Spec.tag]; omega

@[simp, rocq_alias cryptis.hmqv_m_Nmul]
theorem isProd_hmqvM (o : TermOpN) : (hmqvM N t X P).isProd o = false := rfl

@[simp, rocq_alias cryptis.count_hmqv_m_diag]
theorem count_hmqvM_self : count .mul (hmqvM N t X P) (hmqvM N t X P) = 1 :=
  count_self_of_isProd_eq_false rfl

@[simp, rocq_alias cryptis.count_hmqv_m_nonce]
theorem count_hmqvM_nonce (n : Nonce) : count .mul (hmqvM N t X P) n = 0 :=
  count_of_ne rfl nofun

@[rocq_alias cryptis.count_hmqv_m_neq]
theorem count_hmqvM_of_ne (h : hmqvM N t X P ≠ hmqvM N t' X' P') :
    count .mul (hmqvM N t X P) (hmqvM N t' X' P') = 0 :=
  count_of_ne rfl h

@[simp]
theorem count_nonce_hmqvM (n : Nonce) : count .mul n (hmqvM N t X P) = 0 :=
  count_of_ne rfl nofun

@[simp]
theorem count_hmqvM_of_tag_ne (h : t ≠ t') : count .mul (hmqvM N t X P) (hmqvM N t' X' P') = 0 :=
  count_hmqvM_of_ne (hmqvM_ne h)

#rocq_ignore cryptis.count_hmqv_m_e "simp, with count_hmqvM_nonce"

@[rocq_alias cryptis.hmqv_s_neq0]
theorem hmqvS_ne_zero (m p x : Term) : hmqvS m p x ≠ 0 := fun h => by
  have := congrArg (·.coeff (E.ofTerm x)) h
  by_cases hx : E.ofTerm m * E.ofTerm p = E.ofTerm x <;> simp [hmqvS, of_apply, hx] at this

theorem hmqvK_eq_mul (N : Namespace) (ta tb : String) (pa xa Pa Xa Pb Xb : Term) :
    hmqvK N ta tb pa xa Pa Xa Pb Xb = (E.ofTerm xa • hmqvY N tb Pa Pb Xb) *
      ((E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa) • hmqvY N tb Pa Pb Xb) := by
  simp only [hmqvK, hmqvS, add_smul, EExp.of_smul, toMul_add, toMul_ofMul]

@[rocq_alias cryptis.log_hmqv_Y]
theorem log_hmqvY (b : Term) :
    log b (.ofMul (hmqvY N tb Pa Pb Xb)) = log b (.ofMul (G.ofTerm Xb)) +
      of ℤ E (E.ofTerm (hmqvM N tb Xb Pa)) * log b (.ofMul (G.ofTerm Pb)) := by
  rw [hmqvY, ofMul_mul, map_add, ← toMul_ofMul (G.ofTerm Pb), ← EExp.of_smul, map_smul,
    smul_eq_mul, toMul_ofMul]

@[rocq_alias cryptis.log_hmqv_K]
theorem log_hmqvK (b : Term) :
    log b (.ofMul (hmqvK N ta tb pa xa Pa Xa Pb Xb)) =
      hmqvS (hmqvM N ta Xa Pb) pa xa * log b (.ofMul (hmqvY N tb Pa Pb Xb)) := by
  rw [hmqvK, ofMul_toMul, map_smul, smul_eq_mul]

/-- With honest public keys, the base is `g` raised to the peer's scalar. -/
@[rocq_alias cryptis.hmqv_Y_honest]
theorem hmqvY_exp (N : Namespace) (tb : String) (Pa pb xb g : Term) :
    Additive.ofMul (hmqvY N tb Pa (g.exp pb) (g.exp xb)) =
      hmqvS (hmqvM N tb (g.exp xb) Pa) pb xb • Additive.ofMul (G.ofTerm g) := by
  simp only [hmqvY, hmqvS, add_smul, EExp.of_smul, toMul_ofMul, ofMul_mul, mul_smul]
  rfl

@[rocq_alias cryptis.hmqv_K_sym]
theorem hmqvK_comm (N : Namespace) (ta tb : String) (pa xa pb xb g : Term) :
    hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) (g.exp pb) (g.exp xb) =
      hmqvK N tb ta pb xb (g.exp pb) (g.exp xb) (g.exp pa) (g.exp xa) := by
  simp only [hmqvK, hmqvY_exp, smul_smul, mul_comm]

/-! ### Independence of the multipliers -/

#rocq_ignore cryptis.indep_log_hmqv_m "EExp.isHomogeneous_log_of_tsize_le"

variable {h b : Term} {s r : EExp}

@[rocq_alias cryptis.indep_hmqv_s_ne]
theorem isHomogeneous_hmqvS {m p x : Term} (hm : count .mul h m = 0) (hp : count .mul h p = 0)
    (hx : count .mul h x = 0) : IsHomogeneous h 0 (hmqvS m p x) :=
  (isHomogeneous_of.mpr hx).add (isHomogeneous_of.mpr (by simp [hm, hp]))

@[rocq_alias cryptis.indep_log_hmqv_Y]
theorem isHomogeneous_log_hmqvY (hX : IsHomogeneous h 0 (log b (.ofMul (G.ofTerm Xb))))
    (hP : IsHomogeneous h 0 (log b (.ofMul (G.ofTerm Pb))))
    (hm : count .mul h (hmqvM N tb Xb Pa) = 0) :
    IsHomogeneous h 0 (log b (.ofMul (hmqvY N tb Pa Pb Xb))) := by
  rw [log_hmqvY]
  exact hX.add ((isHomogeneous_of.mpr hm).mul hP)

@[rocq_alias cryptis.indep_log_hmqv_K]
theorem isHomogeneous_log_hmqvK {pa xa : Term}
    (hS : IsHomogeneous h 0 (hmqvS (hmqvM N ta Xa Pb) pa xa))
    (hY : IsHomogeneous h 0 (log b (.ofMul (hmqvY N tb Pa Pb Xb)))) :
    IsHomogeneous h 0 (log b (.ofMul (hmqvK N ta tb pa xa Pa Xa Pb Xb))) := by
  rw [log_hmqvK]
  exact hS.mul hY

#rocq_ignore cryptis.hmqv_s_eq0 "Mathlib's mul_eq_zero on the domain EExp, with hmqvS_ne_zero"

/-- Of two products by scalars with the same multiplier `m`, the parts of degree one in `m` are
equal. -/
@[rocq_alias cryptis.hmqv_s_part]
theorem mul_of_eq_of_mul_hmqvS_eq {pa xa pa' xa' : Nonce}
    (hs : IsHomogeneous (hmqvM N t X P) 0 s) (hr : IsHomogeneous (hmqvM N t X P) 0 r)
    (hsr : s * hmqvS (hmqvM N t X P) pa xa = r * hmqvS (hmqvM N t X P) pa' xa') :
    s * of ℤ E (E.ofTerm (hmqvM N t X P) * E.ofTerm pa) =
      r * of ℤ E (E.ofTerm (hmqvM N t X P) * E.ofTerm pa') :=
  (hs.mul (isHomogeneous_of.mpr (count_hmqvM_nonce xa))).eq_of_add_eq_add
    (hr.mul (isHomogeneous_of.mpr (count_hmqvM_nonce xa')))
    (hs.mul (isHomogeneous_of (k := 1).mpr (by simp)))
    (hr.mul (isHomogeneous_of (k := 1).mpr (by simp)))
    (by decide) (by simpa only [hmqvS, mul_add] using hsr)

/-! ### Degenerate keys -/

@[rocq_alias cryptis.hmqv_K_unit]
theorem hmqvK_eq_one : hmqvK N ta tb pa xa Pa Xa Pb Xb = 1 ↔ hmqvY N tb Pa Pb Xb = 1 := by
  rw [← ofMul_eq_zero, hmqvK, ofMul_toMul, smul_eq_zero, ofMul_eq_zero]
  simp [hmqvS_ne_zero]

/-- The key determines the base that the party exponentiated. -/
@[rocq_alias cryptis.hmqv_K_inj_base]
theorem hmqvY_eq_of_hmqvK_eq
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = hmqvK N ta tb pa xa Pa Xa Pb Xb') :
    hmqvY N tb Pa Pb Xb = hmqvY N tb Pa Pb Xb' :=
  Additive.ofMul.injective <|
    smul_right_injective _ (hmqvS_ne_zero _ _ _) (congrArg Additive.ofMul h)

/-- A key that is not the unit does not bind an unvetted peer: a peer that claims the long-term
key `1` and another that reflects the party's ephemeral public key `g^xa` can make the party
compute the same key. -/
@[rocq_alias cryptis.hmqv_K_inj_counterexample]
theorem hmqvK_inj_counterexample (hg : g.isProd .gmul = false) (pa xa : Nonce) (Pa Xa : Term) :
    ∃ Xb Pb' Xb', G.ofTerm Pb' ≠ 1 ∧
      hmqvK N ta tb pa xa Pa Xa ↑(1 : G) Xb = hmqvK N ta tb pa xa Pa Xa Pb' Xb' ∧
      hmqvK N ta tb pa xa Pa Xa ↑(1 : G) Xb ≠ 1 := by
  have hg1 : G.ofTerm g ≠ 1 := fun h => ne_prod_zero hg (congrArg toTerm h)
  obtain ⟨c, hc⟩ : ∃ c : E, E.ofTerm (hmqvM N tb (g.exp xa) Pa) * c =
      E.ofTerm (hmqvM N ta Xa ↑(1 : G)) * E.ofTerm pa := ⟨_, mul_inv_cancel_left _ _⟩
  have hY : Additive.ofMul (hmqvY N tb Pa ↑(c • G.ofTerm g) (g.exp xa)) =
      hmqvS (hmqvM N ta Xa ↑(1 : G)) pa xa • Additive.ofMul (G.ofTerm g) := by
    simp only [hmqvY, ofTerm_coe, smul_smul, hc, hmqvS, add_smul, EExp.of_smul, toMul_ofMul,
      ofMul_mul]
    rfl
  have hK : Additive.ofMul (hmqvK N ta tb pa xa Pa Xa ↑(1 : G)
      ↑(hmqvS (hmqvM N ta Xa ↑(c • G.ofTerm g)) pa xa • Additive.ofMul (G.ofTerm g)).toMul) =
      hmqvS (hmqvM N ta Xa ↑(1 : G)) pa xa •
        hmqvS (hmqvM N ta Xa ↑(c • G.ofTerm g)) pa xa • Additive.ofMul (G.ofTerm g) := by
    simp only [hmqvK, ofMul_toMul, hmqvY, ofTerm_coe, smul_one, mul_one]
  refine ⟨↑(hmqvS (hmqvM N ta Xa ↑(c • G.ofTerm g)) pa xa • Additive.ofMul (G.ofTerm g)).toMul,
    ↑(c • G.ofTerm g), g.exp xa, fun h => hg1 ?_, Additive.ofMul.injective ?_, fun h => ?_⟩
  · rw [← smul_left_cancel_iff c, smul_one]
    simpa only [ofTerm_coe] using h
  · rw [hK, hmqvK, ofMul_toMul, hY, smul_comm]
  · rw [← ofMul_eq_zero, hK, smul_eq_zero, smul_eq_zero, ofMul_eq_zero] at h
    exact h.elim (hmqvS_ne_zero _ _ _) (·.elim (hmqvS_ne_zero _ _ _) hg1)

@[rocq_alias cryptis.hmqv_K_neq_unit]
theorem hmqvK_ne_one (hx : g.isExp = false) (hg : g.isProd .gmul = false) {pa xa pb : Nonce} :
    hmqvK N ta tb pa xa Pa Xa (g.exp pb) Xb ≠ 1 := fun h => by
  have := congrArg (fun y => (log g (.ofMul y)).coeff
    (E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm pb)) (hmqvK_eq_one.mp h)
  simp only [log_hmqvY, log_exp hx hg, ← map_mul, coeff_add, Finsupp.add_apply, ofMul_one,
    map_zero, coeff_zero, Finsupp.zero_apply] at this
  rw [(isHomogeneous_log_of_tsize_le (tsize_lt_hmqvM_left N tb Xb Pa).le g).coeff_eq_zero
    (by simp)] at this
  simp [of_apply] at this

/-! ### Binding the public keys

Two equal keys have equal logarithms: for every base `b`,

  `(xa + ma * pa) * (α + mb * β) = (xa' + ma' * pa') * (α' + mb' * β')`,

where `α = log b Xb`, `β = log b Pb`, and so on. Every public input is smaller than the multiplier
that hashes it, so all four coefficients are independent of the largest of the four multipliers.

- If the largest is `ma`, its linear coefficient forces `ma = ma'` unless the key is the unit,
  hence `Pb = Pb'`. The parts of degree one in `ma` then differ by a multiple of
  `mb * pa - mb' * pa'`; substituting for the larger of `mb` and `mb'` shows that this multiple
  is zero unless `Pb` is the unit, so `mb = mb'` (`hmqvM_eq_of_log_hmqvY`).
- If the largest is `mb`, its linear coefficient forces `mb = mb'` unless `Pb` is the unit. The
  parts of degree one in `mb` then agree, and the larger of `ma` and `ma'` occurs on one side
  only, unless one of the claimed long-term keys is the unit.

Both multipliers agree, and so do the public inputs that they hash. -/

/-- If the key is independent of the party's own multiplier, then it is the unit. -/
@[rocq_alias cryptis.hmqv_K_own]
theorem hmqvK_eq_one_of_isHomogeneous {pa xa : Nonce} {K : G}
    (hY : ∀ b, IsHomogeneous (hmqvM N ta Xa Pb) 0 (log b (.ofMul (hmqvY N tb Pa Pb Xb))))
    (hK : ∀ b, IsHomogeneous (hmqvM N ta Xa Pb) 0 (log b (.ofMul K)))
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = K) : hmqvK N ta tb pa xa Pa Xa Pb Xb = 1 :=
  hmqvK_eq_one.mpr <| ofMul_eq_zero.mp <| eq_zero_of_forall_log_eq_zero fun b =>
    (hY b).eq_zero_of_mul_add_eq (hK b) (e₁ := E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa)
      (count_hmqvM_nonce xa) (by simp) <| by
      rw [← h, log_hmqvK, hmqvS, mul_comm]

/-- If the key is independent of the peer's multiplier, then the peer's long-term key is the
unit. -/
@[rocq_alias cryptis.hmqv_K_peer]
theorem ofTerm_eq_one_of_hmqvK_eq (hab : ta ≠ tb) {pa xa : Nonce} {K : G}
    (hP : ∀ b, IsHomogeneous (hmqvM N tb Xb Pa) 0 (log b (.ofMul (G.ofTerm Pb))))
    (hK : ∀ b, IsHomogeneous (hmqvM N tb Xb Pa) 0 (log b (.ofMul K)))
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = K) : G.ofTerm Pb = 1 := by
  refine ofMul_eq_zero.mp (eq_zero_of_forall_log_eq_zero fun b => ?_)
  have hS : IsHomogeneous (hmqvM N tb Xb Pa) 0 (hmqvS (hmqvM N ta Xa Pb) pa xa) :=
    isHomogeneous_hmqvS (count_hmqvM_of_ne (hmqvM_ne hab.symm)) (by simp) (by simp)
  have hm := (isHomogeneous_of (e := E.ofTerm (hmqvM N tb Xb Pa))).mpr count_hmqvM_self
  have := (hS.mul (isHomogeneous_log_of_tsize_le (tsize_lt_hmqvM_left N tb Xb Pa).le b))
    |>.eq_of_add_eq_add (hK b) (hS.mul (hm.mul (hP b))) (isHomogeneous_zero _ _) (by decide)
      (by rw [add_zero, ← h, log_hmqvK, log_hmqvY, mul_add])
  simpa [hmqvS_ne_zero, of_apply] using this

/-- The parts of degree one in the party's multiplier `ma` determine the peer's multiplier,
unless the peer's long-term key is the unit. -/
@[rocq_alias cryptis.hmqv_Y_inj]
theorem hmqvM_eq_of_log_hmqvY (hab : ta ≠ tb) (hP : G.ofTerm Pb ≠ 1) {pa pa' : Nonce}
    (hle : (hmqvM N tb Xb' Pa').tsize ≤ (hmqvM N tb Xb Pa).tsize)
    (h : ∀ b, log b (.ofMul (hmqvY N tb Pa Pb Xb)) *
        of ℤ E (E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa) =
      log b (.ofMul (hmqvY N tb Pa' Pb Xb')) *
        of ℤ E (E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa')) :
    hmqvM N tb Xb Pa = hmqvM N tb Xb' Pa' := by
  by_contra hne
  refine hP (ofMul_eq_zero.mp (eq_zero_of_forall_log_eq_zero fun b => ?_))
  have hA : count .mul (hmqvM N tb Xb Pa) (hmqvM N ta Xa Pb) = 0 :=
    count_hmqvM_of_tag_ne hab.symm
  refine eq_zero_of_add_mul_eq_add_mul (h := hmqvM N tb Xb Pa)
    (u := E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa)
    (v := E.ofTerm (hmqvM N tb Xb' Pa') * (E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa')) rfl
    (by simp [hA]) (by simp [hA, count_hmqvM_of_ne hne])
    ((isHomogeneous_log_of_tsize_le (tsize_lt_hmqvM_left N tb Xb Pa).le b).mul
      (isHomogeneous_of (k := 0) (e := E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa).mpr
        (by simp [hA])))
    ((isHomogeneous_log_of_tsize_le ((tsize_lt_hmqvM_left N tb Xb' Pa').le.trans hle) b).mul
      (isHomogeneous_of (k := 0) (e := E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa').mpr
        (by simp [hA]))) ?_
  have := h b
  simp only [log_hmqvY, map_mul] at this ⊢
  linear_combination this

theorem log_eq_of_hmqvK_eq {pa xa pa' xa' : Term}
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = hmqvK N ta tb pa' xa' Pa' Xa' Pb' Xb') (b : Term) :
    hmqvS (hmqvM N ta Xa Pb) pa xa * (log b (.ofMul (G.ofTerm Xb)) +
        of ℤ E (E.ofTerm (hmqvM N tb Xb Pa)) * log b (.ofMul (G.ofTerm Pb))) =
      hmqvS (hmqvM N ta Xa' Pb') pa' xa' * (log b (.ofMul (G.ofTerm Xb')) +
        of ℤ E (E.ofTerm (hmqvM N tb Xb' Pa')) * log b (.ofMul (G.ofTerm Pb'))) := by
  simpa only [log_hmqvK, log_hmqvY] using congrArg (fun K => log b (.ofMul K)) h

/-- One of four numbers is the largest. -/
private theorem le_four (a b c d : ℕ) : (b ≤ a ∧ c ≤ a ∧ d ≤ a) ∨ (a ≤ b ∧ c ≤ b ∧ d ≤ b) ∨
    (a ≤ c ∧ b ≤ c ∧ d ≤ c) ∨ (a ≤ d ∧ b ≤ d ∧ c ≤ d) := by
  omega

/-- The case of `hmqvK_inj_of_ne_one` where the party's own multiplier is the largest. -/
@[rocq_alias cryptis.hmqv_K_inj_maxA]
theorem hmqvK_inj_of_le_own (hab : ta ≠ tb) (hP : G.ofTerm Pb ≠ 1) {pa xa pa' xa' : Nonce}
    (h₁ : (hmqvM N ta Xa' Pb').tsize ≤ (hmqvM N ta Xa Pb).tsize)
    (h₂ : (hmqvM N tb Xb Pa).tsize ≤ (hmqvM N ta Xa Pb).tsize)
    (h₃ : (hmqvM N tb Xb' Pa').tsize ≤ (hmqvM N ta Xa Pb).tsize)
    (hK : hmqvK N ta tb pa xa Pa Xa Pb Xb ≠ 1)
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = hmqvK N ta tb pa' xa' Pa' Xa' Pb' Xb') :
    Pa = Pa' ∧ Xa = Xa' ∧ Pb = Pb' ∧ Xb = Xb' := by
  have hY {Q Z P : Term} (hZ : (hmqvM N tb Z Q).tsize ≤ (hmqvM N ta Xa Pb).tsize)
      (hP : P.tsize < (hmqvM N ta Xa Pb).tsize) (b : Term) :
      IsHomogeneous (hmqvM N ta Xa Pb) 0 (log b (.ofMul (hmqvY N tb Q P Z))) :=
    isHomogeneous_log_hmqvY
      (isHomogeneous_log_of_tsize_le ((tsize_lt_hmqvM_left N tb Z Q).le.trans hZ) b)
      (isHomogeneous_log_of_tsize_le hP.le b) (count_hmqvM_of_ne (hmqvM_ne hab))
  have hPb := tsize_lt_hmqvM_right N ta Xa Pb
  obtain ⟨-, rfl, rfl⟩ : ta = ta ∧ Xa = Xa' ∧ Pb = Pb' := by
    refine (hmqvM_inj (N := N)).mp (by_contra fun hA =>
      hK (hmqvK_eq_one_of_isHomogeneous (hY h₂ hPb) (fun b => ?_) h))
    exact isHomogeneous_log_hmqvK (isHomogeneous_hmqvS (count_hmqvM_of_ne hA) (by simp) (by simp))
      (hY h₃ ((tsize_lt_hmqvM_right N ta Xa' Pb').trans_le h₁) b)
  have part (b : Term) := mul_of_eq_of_mul_hmqvS_eq (hY h₂ hPb b) (hY h₃ hPb b) (by
    simpa only [log_hmqvK, mul_comm] using congrArg (fun K => log b (.ofMul K)) h)
  rcases le_total (hmqvM N tb Xb' Pa').tsize (hmqvM N tb Xb Pa).tsize with hle | hle
  · obtain ⟨-, rfl, rfl⟩ := hmqvM_inj.mp (hmqvM_eq_of_log_hmqvY hab hP hle part)
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨-, rfl, rfl⟩ :=
      hmqvM_inj.mp (hmqvM_eq_of_log_hmqvY hab hP hle fun b => (part b).symm)
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The case of `hmqvK_inj_of_ne_one` where the peer's multiplier is the largest. -/
@[rocq_alias cryptis.hmqv_K_inj_maxB]
theorem hmqvK_inj_of_le_peer (hab : ta ≠ tb) (hP : G.ofTerm Pb ≠ 1) (hP' : G.ofTerm Pb' ≠ 1)
    {pa xa pa' xa' : Nonce}
    (h₁ : (hmqvM N ta Xa Pb).tsize ≤ (hmqvM N tb Xb Pa).tsize)
    (h₂ : (hmqvM N ta Xa' Pb').tsize ≤ (hmqvM N tb Xb Pa).tsize)
    (h₃ : (hmqvM N tb Xb' Pa').tsize ≤ (hmqvM N tb Xb Pa).tsize)
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = hmqvK N ta tb pa' xa' Pa' Xa' Pb' Xb') :
    Pa = Pa' ∧ Xa = Xa' ∧ Pb = Pb' ∧ Xb = Xb' := by
  have hPb b := isHomogeneous_log_of_tsize_le
    ((tsize_lt_hmqvM_right N ta Xa Pb).trans_le h₁).le b
  have hPb' b := isHomogeneous_log_of_tsize_le
    ((tsize_lt_hmqvM_right N ta Xa' Pb').trans_le h₂).le b
  have hS {X P : Term} {p x : Nonce} :
      IsHomogeneous (hmqvM N tb Xb Pa) 0 (hmqvS (hmqvM N ta X P) p x) :=
    isHomogeneous_hmqvS (count_hmqvM_of_ne (hmqvM_ne hab.symm)) (by simp) (by simp)
  obtain ⟨-, rfl, rfl⟩ : tb = tb ∧ Xb = Xb' ∧ Pa = Pa' := by
    refine (hmqvM_inj (N := N)).mp (by_contra fun hB => hP (ofTerm_eq_one_of_hmqvK_eq hab hPb
      (fun b => ?_) h))
    exact isHomogeneous_log_hmqvK hS (isHomogeneous_log_hmqvY (isHomogeneous_log_of_tsize_le
      ((tsize_lt_hmqvM_left N tb Xb' Pa').le.trans h₃) b) (hPb' b) (count_hmqvM_of_ne hB))
  -- The parts of degree one in the peer's multiplier `mb`.
  have part (b : Term) :
      of ℤ E (E.ofTerm (hmqvM N tb Xb Pa)) * log b (.ofMul (G.ofTerm Pb)) *
          hmqvS (hmqvM N ta Xa Pb) pa xa =
        of ℤ E (E.ofTerm (hmqvM N tb Xb Pa)) * log b (.ofMul (G.ofTerm Pb')) *
          hmqvS (hmqvM N ta Xa' Pb') pa' xa' := by
    have hX := isHomogeneous_log_of_tsize_le (tsize_lt_hmqvM_left N tb Xb Pa).le b
    have hm := (isHomogeneous_of (k := 1) (e := E.ofTerm (hmqvM N tb Xb Pa))).mpr
      count_hmqvM_self
    have hS' := hS (X := Xa') (P := Pb') (p := pa') (x := xa')
    exact (hX.mul hS).eq_of_add_eq_add (hX.mul hS') ((hm.mul (hPb b)).mul hS)
      ((hm.mul (hPb' b)).mul hS') (by decide) (by linear_combination log_eq_of_hmqvK_eq h b)
  -- The larger of `ma` and `ma'` has a linear coefficient on one side only.
  have key {X P X' P' Q Q' : Term} {p x p' x' : Nonce}
      (hne : hmqvM N ta X P ≠ hmqvM N ta X' P')
      (hQ : Q.tsize < (hmqvM N ta X P).tsize) (hQ' : Q'.tsize < (hmqvM N ta X P).tsize)
      (he : ∀ b, of ℤ E (E.ofTerm (hmqvM N tb Xb Pa)) * log b (.ofMul (G.ofTerm Q)) *
          hmqvS (hmqvM N ta X P) p x =
        of ℤ E (E.ofTerm (hmqvM N tb Xb Pa)) * log b (.ofMul (G.ofTerm Q')) *
          hmqvS (hmqvM N ta X' P') p' x') : G.ofTerm Q = 1 := by
    refine ofMul_eq_zero.mp (eq_zero_of_forall_log_eq_zero fun b => ?_)
    have hm : IsHomogeneous (hmqvM N ta X P) 0 (of ℤ E (E.ofTerm (hmqvM N tb Xb Pa))) :=
      isHomogeneous_of.mpr (count_hmqvM_of_ne (hmqvM_ne hab))
    have := (hm.mul (isHomogeneous_log_of_tsize_le hQ.le b)).eq_zero_of_mul_add_eq
      ((hm.mul (isHomogeneous_log_of_tsize_le hQ'.le b)).mul
        (isHomogeneous_hmqvS (count_hmqvM_of_ne hne) (by simp) (by simp)))
      (e₁ := E.ofTerm (hmqvM N ta X P) * E.ofTerm p) (count_hmqvM_nonce x) (by simp) (he b)
    simpa [of_apply] using this
  obtain ⟨-, rfl, rfl⟩ : ta = ta ∧ Xa = Xa' ∧ Pb = Pb' := by
    refine (hmqvM_inj (N := N)).mp (by_contra fun hA => ?_)
    rcases le_total (hmqvM N ta Xa' Pb').tsize (hmqvM N ta Xa Pb).tsize with hle | hle
    · exact hP (key hA (tsize_lt_hmqvM_right ..) ((tsize_lt_hmqvM_right ..).trans_le hle) part)
    · exact hP' (key (Ne.symm hA) (tsize_lt_hmqvM_right ..)
        ((tsize_lt_hmqvM_right ..).trans_le hle) fun b => (part b).symm)
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A key that is not the unit determines the public keys used to compute it, provided that the
claimed long-term keys of the peers are not the unit. -/
@[rocq_alias cryptis.hmqv_K_inj_gen]
theorem hmqvK_inj_of_ne_one (hab : ta ≠ tb) (hP : G.ofTerm Pb ≠ 1) (hP' : G.ofTerm Pb' ≠ 1)
    {pa xa pa' xa' : Nonce} (hK : hmqvK N ta tb pa xa Pa Xa Pb Xb ≠ 1)
    (h : hmqvK N ta tb pa xa Pa Xa Pb Xb = hmqvK N ta tb pa' xa' Pa' Xa' Pb' Xb') :
    Pa = Pa' ∧ Xa = Xa' ∧ Pb = Pb' ∧ Xb = Xb' := by
  have symm (h : Pa' = Pa ∧ Xa' = Xa ∧ Pb' = Pb ∧ Xb' = Xb) :
      Pa = Pa' ∧ Xa = Xa' ∧ Pb = Pb' ∧ Xb = Xb' :=
    ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
  rcases le_four (hmqvM N ta Xa Pb).tsize (hmqvM N ta Xa' Pb').tsize (hmqvM N tb Xb Pa).tsize
    (hmqvM N tb Xb' Pa').tsize with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact hmqvK_inj_of_le_own hab hP h₁ h₂ h₃ hK h
  · exact symm (hmqvK_inj_of_le_own hab hP' h₁ h₃ h₂ (h ▸ hK) h.symm)
  · exact hmqvK_inj_of_le_peer hab hP hP' h₁ h₂ h₃ h
  · exact symm (hmqvK_inj_of_le_peer hab hP' hP h₂ h₁ h₃ h.symm)

/-- The key of a party with honest public keys determines its private keys and the public keys
of its peer, provided that the key and the claimed long-term keys are not the unit. -/
@[rocq_alias cryptis.hmqv_K_inj]
theorem hmqvK_inj (hx : g.isExp = false) (hg : g.isProd .gmul = false) (hab : ta ≠ tb)
    (hP : G.ofTerm Pb ≠ 1) (hP' : G.ofTerm Pb' ≠ 1) {pa xa pa' xa' : Nonce}
    (hK : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) Pb Xb ≠ 1)
    (h : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) Pb Xb =
      hmqvK N ta tb pa' xa' (g.exp pa') (g.exp xa') Pb' Xb') :
    pa = pa' ∧ xa = xa' ∧ Pb = Pb' ∧ Xb = Xb' := by
  obtain ⟨h₁, h₂, rfl, rfl⟩ := hmqvK_inj_of_ne_one hab hP hP' hK h
  exact ⟨nonce_eq_of_exp_eq hx hg h₁, nonce_eq_of_exp_eq hx hg h₂, rfl, rfl⟩

/-! ### Binding identities across roles

An initiator and a responder each know that their own public keys are honest, `g^p` and `g^x`,
but not their peer's. The multipliers `ma` and `mb` of the initiator's key have counterparts
`ma'` and `mb'` in the responder's key, computed with the same tags. A multiplier that equals its
counterpart makes the public keys it hashes honest, so their logarithms are independent of every
multiplier. The largest unmatched multiplier has a linear coefficient on one side only, which
forces the key to be the unit if it is `ma`, and the claimed long-term key `Pb` if it is `mb`
(`hmqvK_cross_max`). -/

@[rocq_alias cryptis.hmqv_K_cross_max]
theorem hmqvK_cross_max (hx : g.isExp = false) (hg : g.isProd .gmul = false) (hab : ta ≠ tb)
    (hP : G.ofTerm Pb ≠ 1) {pa xa pb xb : Nonce} {Qa Ya h : Term}
    (hK : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) Pb Xb ≠ 1)
    (heq : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) Pb Xb =
      hmqvK N tb ta pb xb (g.exp pb) (g.exp xb) Qa Ya)
    (hA : hmqvM N ta (g.exp xa) Pb = hmqvM N ta Ya (g.exp pb) ∨
      (hmqvM N ta (g.exp xa) Pb).tsize ≤ h.tsize ∧ (hmqvM N ta Ya (g.exp pb)).tsize ≤ h.tsize)
    (hB : hmqvM N tb Xb (g.exp pa) = hmqvM N tb (g.exp xb) Qa ∨
      (hmqvM N tb Xb (g.exp pa)).tsize ≤ h.tsize ∧ (hmqvM N tb (g.exp xb) Qa).tsize ≤ h.tsize)
    (hh : h = hmqvM N ta (g.exp xa) Pb ∧ hmqvM N ta (g.exp xa) Pb ≠ hmqvM N ta Ya (g.exp pb) ∨
      h = hmqvM N tb Xb (g.exp pa) ∧ hmqvM N tb Xb (g.exp pa) ≠ hmqvM N tb (g.exp xb) Qa) :
    False := by
  have hn (n : Nonce) : count .mul h n = 0 := by
    rcases hh with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact count_hmqvM_nonce n
  have hsmall {T : Term} (hT : T.tsize < h.tsize) b := isHomogeneous_log_of_tsize_le hT.le b
  have fX b : IsHomogeneous h 0 (log b (.ofMul (G.ofTerm Xb))) := by
    rcases hB with hB | ⟨hB, -⟩
    · obtain ⟨-, rfl, -⟩ := hmqvM_inj.mp hB; exact isHomogeneous_log_exp hx hg (hn xb) b
    · exact hsmall ((tsize_lt_hmqvM_left ..).trans_le hB) b
  have fP b : IsHomogeneous h 0 (log b (.ofMul (G.ofTerm Pb))) := by
    rcases hA with hA | ⟨hA, -⟩
    · obtain ⟨-, -, rfl⟩ := hmqvM_inj.mp hA; exact isHomogeneous_log_exp hx hg (hn pb) b
    · exact hsmall ((tsize_lt_hmqvM_right ..).trans_le hA) b
  have fY b : IsHomogeneous h 0 (log b (.ofMul (G.ofTerm Ya))) := by
    rcases hA with hA | ⟨-, hA⟩
    · obtain ⟨-, rfl, -⟩ := hmqvM_inj.mp hA; exact isHomogeneous_log_exp hx hg (hn xa) b
    · exact hsmall ((tsize_lt_hmqvM_left ..).trans_le hA) b
  have fQ b : IsHomogeneous h 0 (log b (.ofMul (G.ofTerm Qa))) := by
    rcases hB with hB | ⟨-, hB⟩
    · obtain ⟨-, -, rfl⟩ := hmqvM_inj.mp hB; exact isHomogeneous_log_exp hx hg (hn pa) b
    · exact hsmall ((tsize_lt_hmqvM_right ..).trans_le hB) b
  rcases hh with ⟨rfl, hA'⟩ | ⟨rfl, hB'⟩
  · refine hK (hmqvK_eq_one_of_isHomogeneous
      (fun b => isHomogeneous_log_hmqvY (fX b) (fP b) (count_hmqvM_of_ne (hmqvM_ne hab)))
      (fun b => isHomogeneous_log_hmqvK ?_ (isHomogeneous_log_hmqvY (fY b) (fQ b)
        (count_hmqvM_of_ne hA'))) heq)
    exact isHomogeneous_hmqvS (count_hmqvM_of_ne (hmqvM_ne hab)) (hn pb) (hn xb)
  · exact hP (ofTerm_eq_one_of_hmqvK_eq hab fP (fun b => isHomogeneous_log_hmqvK
      (isHomogeneous_hmqvS (count_hmqvM_of_ne hB') (hn pb) (hn xb))
      (isHomogeneous_log_hmqvY (fY b) (fQ b) (count_hmqvM_of_ne (hmqvM_ne hab.symm)))) heq)

/-- The keys of an initiator and a responder with honest public keys agree only if each used
the other's public keys, provided that the key and the claimed long-term keys are not the
unit. -/
@[rocq_alias cryptis.hmqv_K_inj']
theorem hmqvK_inj' (hx : g.isExp = false) (hg : g.isProd .gmul = false) (hab : ta ≠ tb)
    {Qa Ya : Term} (hP : G.ofTerm Pb ≠ 1) (hQ : G.ofTerm Qa ≠ 1) {pa xa pb xb : Nonce}
    (hK : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) Pb Xb ≠ 1)
    (heq : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) Pb Xb =
      hmqvK N tb ta pb xb (g.exp pb) (g.exp xb) Qa Ya) :
    Pb = g.exp pb ∧ Xb = g.exp xb ∧ Qa = g.exp pa ∧ Ya = g.exp xa := by
  have L {h} := hmqvK_cross_max (h := h) hx hg hab hP hK heq
  have R {h} := hmqvK_cross_max (h := h) hx hg hab.symm hQ (heq ▸ hK) heq.symm
  suffices hmqvM N ta (g.exp xa) Pb = hmqvM N ta Ya (g.exp pb) ∧
      hmqvM N tb Xb (g.exp pa) = hmqvM N tb (g.exp xb) Qa by
    obtain ⟨⟨-, hY, hP⟩, ⟨-, hX, hQ⟩⟩ := And.imp hmqvM_inj.mp hmqvM_inj.mp this
    exact ⟨hP, hX, hQ.symm, hY.symm⟩
  by_cases eA : hmqvM N ta (g.exp xa) Pb = hmqvM N ta Ya (g.exp pb) <;>
    by_cases eB : hmqvM N tb Xb (g.exp pa) = hmqvM N tb (g.exp xb) Qa
  · exact ⟨eA, eB⟩
  · rcases le_total (hmqvM N tb (g.exp xb) Qa).tsize (hmqvM N tb Xb (g.exp pa)).tsize with hle | hle
    · exact (L (.inl eA) (.inr ⟨le_rfl, hle⟩) (.inr ⟨rfl, eB⟩)).elim
    · exact (R (.inr ⟨le_rfl, hle⟩) (.inl eA.symm) (.inl ⟨rfl, Ne.symm eB⟩)).elim
  · rcases le_total (hmqvM N ta Ya (g.exp pb)).tsize (hmqvM N ta (g.exp xa) Pb).tsize with hle | hle
    · exact (L (.inr ⟨le_rfl, hle⟩) (.inl eB) (.inl ⟨rfl, eA⟩)).elim
    · exact (R (.inl eB.symm) (.inr ⟨le_rfl, hle⟩) (.inr ⟨rfl, Ne.symm eA⟩)).elim
  · exfalso
    rcases le_four (hmqvM N ta (g.exp xa) Pb).tsize (hmqvM N tb Xb (g.exp pa)).tsize
      (hmqvM N ta Ya (g.exp pb)).tsize (hmqvM N tb (g.exp xb) Qa).tsize with
      ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact L (.inr ⟨le_rfl, h₂⟩) (.inr ⟨h₁, h₃⟩) (.inl ⟨rfl, eA⟩)
    · exact L (.inr ⟨h₁, h₂⟩) (.inr ⟨le_rfl, h₃⟩) (.inr ⟨rfl, eB⟩)
    · exact R (.inr ⟨h₃, h₂⟩) (.inr ⟨le_rfl, h₁⟩) (.inr ⟨rfl, Ne.symm eA⟩)
    · exact R (.inr ⟨le_rfl, h₂⟩) (.inr ⟨h₃, h₁⟩) (.inl ⟨rfl, Ne.symm eB⟩)

/-! ### Group factors of the key

With an honest long-term key for the peer, the logarithm of the key has a part of degree one in
the peer's multiplier `mb` that the peer's share is too small to cancel: the mixed factor
`g^(pb * mb * xa)` and the static factor `g^(pb * mb * ma * pa)`. -/

@[rocq_alias cryptis.count_log_hmqv_K]
theorem coeff_log_hmqvK (hx : g.isExp = false) (hg : g.isProd .gmul = false) (hab : ta ≠ tb)
    {pa xa pb : Nonce} {e : E} (he : count .mul (hmqvM N tb Xb Pa) ↑e = 1) :
    (log g (.ofMul (hmqvK N ta tb pa xa Pa Xa (g.exp pb) Xb))).coeff e =
      (of ℤ E (E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm xa) +
        of ℤ E (E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) *
          E.ofTerm (hmqvM N ta Xa (g.exp pb)) * E.ofTerm pa)).coeff e := by
  have hS : IsHomogeneous (hmqvM N tb Xb Pa) 0 (hmqvS (hmqvM N ta Xa (g.exp pb)) pa xa) :=
    isHomogeneous_hmqvS (count_hmqvM_of_tag_ne hab.symm) (by simp) (by simp)
  rw [log_hmqvK, log_hmqvY, log_exp hx hg, mul_add, coeff_add, Finsupp.add_apply,
    (hS.mul (isHomogeneous_log_of_tsize_le (tsize_lt_hmqvM_left N tb Xb Pa).le g)).coeff_eq_zero
      (by rw [he]; decide), zero_add]
  refine congrArg (fun s : EExp => s.coeff e) ?_
  simp only [hmqvS, map_mul]
  ring

@[rocq_alias cryptis.hmqv_K_gfactor]
theorem exp_mem_factors_hmqvK (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (hab : ta ≠ tb) {pa xa pb : Nonce} {e : E}
    (he : e = E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm xa ∨
      e = E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm (hmqvM N ta Xa (g.exp pb)) *
        E.ofTerm pa) :
    g.exp ↑e ∈ ((hmqvK N ta tb pa xa Pa Xa (g.exp pb) Xb : Term).factors .gmul).posPart := by
  have hne : E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm xa ≠
      E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm (hmqvM N ta Xa (g.exp pb)) *
        E.ofTerm pa := fun h => by
    simpa [hab.symm] using congrArg (fun e : E => count .mul (hmqvM N ta Xa (g.exp pb)) ↑e) h
  refine exp_mem_factors_of_coeff_log_pos hx hg ?_
  rw [coeff_log_hmqvK hx hg hab (by rcases he with rfl | rfl <;> simp [hab.symm])]
  rcases he with rfl | rfl <;> simp [of_apply, hne, hne.symm]

#rocq_ignore cryptis.hmqv_ss "Inlined in Cryptis.isPublic_hmqvK_static"
#rocq_ignore cryptis.exps_hmqv_ss "Cryptis.posPart_exps_exp_prod"
#rocq_ignore cryptis.exps_hmqv_mixed "Cryptis.posPart_exps_exp_prod"
#rocq_ignore cryptis.TMul3 "Mathlib's mul_assoc on Term.E"
#rocq_ignore cryptis.TMul4 "Mathlib's mul_assoc and mul_comm on Term.E"
#rocq_ignore cryptis.hmqv_key_gfactors
  "Cryptis.exp_mem_factors_hmqvK, with Cryptis.posPart_exps_exp_prod"

/-- With honest shares on both sides, the ephemeral factor `g^(xb * xa)` is in the key: its
logarithm is a sum of four monomials with positive coefficients, none of which cancels. -/
@[rocq_alias cryptis.hmqv_K_gfactor_eph]
theorem exp_mem_factors_hmqvK_eph (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    {pa xa pb xb : Nonce} :
    g.exp ↑(E.ofTerm xb * E.ofTerm xa) ∈
      ((hmqvK N ta tb pa xa Pa Xa (g.exp pb) (g.exp xb) : Term).factors .gmul).posPart := by
  refine exp_mem_factors_of_coeff_log_pos hx hg ?_
  simp only [log_hmqvK, log_hmqvY, log_exp hx hg, hmqvS, add_mul, mul_add, ← map_mul, coeff_add,
    Finsupp.add_apply]
  simp only [of_apply, coeff_single, Finsupp.single_apply, mul_comm (E.ofTerm xa) (E.ofTerm xb)]
  split_ifs <;> omega

/-! ### Binding a claimed key by freshness

`hmqvK_inj'` binds a responder's key to the long-term key `P` that its peer claimed only if `P` is
not the unit. Freshness makes that check unnecessary: if the responder's ephemeral private key
`xb'` differs from its long-term private key and occurs neither in `P` nor in the share `Xa'` it
received, then an initiator that computes the same key learns that `P` is its own long-term key.

Freshness plays the role of size: the logarithms of `P` and `Xa'` are independent of every atom
with the subterm `xb'` (`EExp.isHomogeneous_log_of_subterm`). The logarithm of the responder's
key is `xb' * y + mb' * pb' * y`, where `y` is the logarithm of its base. Each summand has a
single degree in such an atom, other than the degree of the initiator's static monomial
`μ = pb * mb * ma * pa`: the second in `mb'`, and the first in `xb'` or, if `xb'` is one of the
initiator's long-term keys `pa` or `pb`, in the multiplier `mb` or `ma` that hashes the
corresponding public key. So `μ` occurs in the initiator's key but not in the responder's. -/

theorem Term.Subterm.hmqvM_left {n : Term} (h : n.Subterm X) : n.Subterm (hmqvM N t X P) :=
  .hash (.pairRight (.pairLeft h))

theorem Term.Subterm.hmqvM_right {n : Term} (h : n.Subterm P) : n.Subterm (hmqvM N t X P) :=
  .hash (.pairRight (.pairRight (.pairLeft h)))

#rocq_ignore cryptis.subterm_hmqv_m "Term.Subterm.hmqvM_left and Term.Subterm.hmqvM_right"

@[rocq_alias cryptis.hmqv_K_inj_fresh]
theorem hmqvK_inj_fresh (hx : g.isExp = false) (hg : g.isProd .gmul = false) (hab : ta ≠ tb)
    {pa xa pb pb' xb' : Nonce} {P Xa' : Term} (hP : ¬(xb' : Term).Subterm P)
    (hXa : ¬(xb' : Term).Subterm Xa') (hne : xb' ≠ pb')
    (h : hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) (g.exp pb) Xb =
      hmqvK N tb ta pb' xb' (g.exp pb') (g.exp xb') P Xa') :
    P = g.exp pa ∧ pb = pb' ∧ Xb = g.exp xb' ∧ Xa' = g.exp xa := by
  suffices hPa : P = g.exp pa by
    subst hPa
    obtain ⟨h₁, h₂, -, h₄⟩ := hmqvK_inj' hx hg hab (ofTerm_exp_ne_one hg _)
      (ofTerm_exp_ne_one hg _) (hmqvK_ne_one hx hg) h
    exact ⟨rfl, nonce_eq_of_exp_eq hx hg h₁, h₂, h₄⟩
  by_contra hPa
  have hb : hmqvM N tb Xb (g.exp pa) ≠ hmqvM N tb (g.exp xb') P :=
    fun e => hPa (hmqvM_inj.mp e).2.2.symm
  -- The static monomial of the initiator's key.
  let μ : E := E.ofTerm pb * E.ofTerm (hmqvM N tb Xb (g.exp pa)) *
    E.ofTerm (hmqvM N ta (g.exp xa) (g.exp pb)) * E.ofTerm pa
  have hμ :
      (log g (.ofMul (hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) (g.exp pb) Xb))).coeff μ = 1 := by
    have hne : E.ofTerm pb * E.ofTerm (hmqvM N tb Xb (g.exp pa)) * E.ofTerm xa ≠ μ := fun h => by
      simpa [μ, hab.symm] using
        congrArg (fun e : E => count .mul (hmqvM N ta (g.exp xa) (g.exp pb)) ↑e) h
    rw [coeff_log_hmqvK hx hg hab (by simp [μ, hab.symm])]
    change (of ℤ E _ + of ℤ E μ).coeff μ = 1
    simp [of_apply, hne]
  -- The logarithm of the responder's base is independent of the atoms with the subterm `xb'`,
  -- but the multiplier `ma'` that it contains.
  have hY {h : Term} (hs : (xb' : Term).Subterm h) (hm : h ≠ hmqvM N ta Xa' (g.exp pb')) :
      IsHomogeneous h 0 (log g (.ofMul (hmqvY N ta (g.exp pb') P Xa'))) :=
    isHomogeneous_log_hmqvY (isHomogeneous_log_of_subterm hs hXa g)
      (isHomogeneous_log_of_subterm hs hP g) (count_of_ne rfl hm)
  obtain ⟨h₁, hs₁, hm₁, hc₁⟩ : ∃ h₁, (xb' : Term).Subterm h₁ ∧ h₁ ≠ hmqvM N ta Xa' (g.exp pb') ∧
      count .mul h₁ ↑μ ≠ count .mul h₁ xb' := by
    by_cases ha : xb' = pa
    · subst ha
      exact ⟨hmqvM N tb Xb (g.exp xb'), .hmqvM_right (.nonce_exp _ hx hg), hmqvM_ne hab.symm,
        by simp [μ, hab.symm]⟩
    by_cases hb' : xb' = pb
    · subst hb'
      refine ⟨hmqvM N ta (g.exp xa) (g.exp xb'), .hmqvM_right (.nonce_exp _ hx hg), fun e => hne ?_,
        by simp [μ, hab]⟩
      exact nonce_eq_of_exp_eq hx hg (hmqvM_inj.mp e).2.2
    have hc {n : Nonce} (h : n ≠ xb') : count .mul xb' n = 0 :=
      count_of_ne rfl fun e => h (Term.nonce.inj e).symm
    exact ⟨xb', .refl, nofun, by
      simp [μ, hc (Ne.symm ha), hc (Ne.symm hb'), count_self_of_isProd_eq_false (t := xb') rfl]⟩
  have z₁ := ((isHomogeneous_of.mpr rfl).mul (hY hs₁ hm₁)).coeff_eq_zero (m := μ)
    (by rwa [add_zero])
  have z₂ := ((isHomogeneous_of (e := E.ofTerm (hmqvM N tb (g.exp xb') P) * E.ofTerm pb')
    (k := 1) |>.mpr (by simp)).mul
    (hY (h := hmqvM N tb (g.exp xb') P) (.hmqvM_left (.nonce_exp _ hx hg))
      (hmqvM_ne hab.symm))).coeff_eq_zero (m := μ)
    (by simp [μ, hab.symm, count_hmqvM_of_ne hb.symm])
  rw [h, log_hmqvK, hmqvS, add_mul, coeff_add, Finsupp.add_apply, z₁, z₂] at hμ
  exact absurd hμ (by decide)

/-! ### Secrecy of the key -/

private theorem isProd_nonce (o : TermOpN) (a : Nonce) : (a : Term).isProd o = false := rfl

section Secrecy

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
local bi (IProp GF)

@[rocq_alias cryptis.minted_hmqv_m]
theorem minted_hmqvM : minted (GF := GF) X -∗ minted P -∗ minted (hmqvM N t X P) := by
  iintro #HX #HP
  rw [hmqvM, (minted_hash _).to_eq, (minted_tag _ _).to_eq, (minted_ofList _).to_eq]
  iapply BigSepL.bigSepL_cons.mpr
  isplitl [HX]
  · iexact HX
  · iapply BigSepL.bigSepL_singleton.mpr; iexact HP

@[rocq_alias cryptis.minted_hmqv_K]
theorem minted_hmqvK {pa xa : Term} :
    minted (GF := GF) pa -∗ minted xa -∗ minted Pa -∗ minted Xa -∗ minted Pb -∗ minted Xb -∗
      minted ↑(hmqvK N ta tb pa xa Pa Xa Pb Xb) := by
  iintro #Hpa #Hxa #HPa #HXa #HPb #HXb
  ihave #Hma := minted_hmqvM (N := N) (t := ta) $$ HXa HPb
  ihave #Hmb := minted_hmqvM (N := N) (t := tb) $$ HXb HPa
  ihave #HY : minted ↑(hmqvY N tb Pa Pb Xb) $$ []
  · rw [hmqvY]
    iapply minted_coe_mul_intro
    isplit
    · iexact HXb
    · iapply minted_coe_smul_intro; isplit; iexact HPb; iexact Hmb
  rw [hmqvK_eq_mul]
  iapply minted_coe_mul_intro
  isplit
  · iapply minted_coe_smul_intro; isplit; iexact HY; iexact Hxa
  · iapply minted_coe_smul_intro
    isplit
    · iexact HY
    · iapply minted_coe_mul_intro; isplit; iexact Hma; iexact Hpa

variable [CryptisGS GF]

@[rocq_alias cryptis.public_hmqv_m]
theorem isPublic_hmqvM : isPublic (GF := GF) X -∗ isPublic P -∗ isPublic (hmqvM N t X P) := by
  iintro #HX #HP
  rw [hmqvM, (isPublic_hash _).to_eq, (isPublic_tag _ _).to_eq, (isPublic_ofList _).to_eq]
  ileft
  iapply BigSepL.bigSepL_cons.mpr
  isplitl [HX]
  · iexact HX
  · iapply BigSepL.bigSepL_singleton.mpr; iexact HP

/-- Whoever knows all the inputs of the key formula can compute the key. -/
@[rocq_alias cryptis.public_hmqv_K]
theorem isPublic_hmqvK {pa xa : Term} :
    isPublic (GF := GF) pa -∗ isPublic xa -∗ isPublic Pa -∗ isPublic Xa -∗ isPublic Pb -∗
      isPublic Xb -∗ isPublic ↑(hmqvK N ta tb pa xa Pa Xa Pb Xb) := by
  iintro #Hpa #Hxa #HPa #HXa #HPb #HXb
  ihave #Hma := isPublic_hmqvM (N := N) (t := ta) $$ HXa HPb
  ihave #Hmb := isPublic_hmqvM (N := N) (t := tb) $$ HXb HPa
  ihave #HY : isPublic ↑(hmqvY N tb Pa Pb Xb) $$ []
  · rw [hmqvY]
    iapply isPublic_coe_mul $$ HXb
    iapply isPublic_coe_smul $$ HPb Hmb
  rw [hmqvK_eq_mul]
  iapply isPublic_coe_mul
  · iapply isPublic_coe_smul $$ HY Hxa
  · iapply isPublic_coe_smul $$ HY
    iapply isPublic_coe_mul $$ Hma Hpa

/-- The persistent part of a Diffie-Hellman private key, long-term or ephemeral: it may be used as
an exponent of shares. Whether it stays secret is up to its owner. -/
@[rocq_alias cryptis.hmqv_key]
abbrev hmqvKey (x : Nonce) : IProp GF :=
  iprop(minted (x : Term) ∗ □ (∀ t, expPred (x : Term) t ↔ ▷ □ dhKeyShare t))

@[rocq_alias cryptis.hmqv_key_persistent]
instance hmqvKey_persistent (x : Nonce) : Persistent (hmqvKey (GF := GF) x) := by
  unfold hmqvKey; infer_instance

/-- An ephemeral private key, which is never public. -/
@[rocq_alias cryptis.ephemeral]
abbrev hmqvEphemeral (x : Nonce) : IProp GF := iprop(hmqvKey x ∗ □ (isPublic (x : Term) ↔ ▷ False))

@[rocq_alias cryptis.ephemeral_persistent]
instance hmqvEphemeral_persistent (x : Nonce) : Persistent (hmqvEphemeral (GF := GF) x) := by
  unfold hmqvEphemeral; infer_instance

/-- With honest shares, the ephemeral factor binds the key to the two ephemeral private keys. -/
@[rocq_alias cryptis.public_hmqv_K_eph]
theorem isPublic_hmqvK_eph (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    {pa xa pb xb : Nonce} :
    hmqvKey (GF := GF) xa -∗ hmqvKey xb -∗
      isPublic ↑(hmqvK N ta tb pa xa Pa Xa (g.exp pb) (g.exp xb)) -∗ isPublic xa ∨ isPublic xb := by
  have hm := SMS.mem_of_mem_posPart (exp_mem_factors_hmqvK_eph hx hg (N := N) (ta := ta)
    (tb := tb) (pa := pa) (xa := xa) (pb := pb) (xb := xb) (Pa := Pa) (Xa := Xa))
  simp only [coe_mul] at hm
  unfold hmqvKey
  iintro ⟨-, #Ha⟩ ⟨-, #Hb⟩ #Hp
  icases (isPublic_factors .gmul _).mp $$ Hp with ⟨-, #Hfs⟩
  ihave #He := bigSepMultiset_mem hm $$ Hfs
  icases isPublic_dh_secret_inv hx hg rfl rfl $$ Hb Ha He with (#H | #H)
  · iright; iexact H
  · ileft; iexact H

/-- With an honest long-term key for the peer, the static factor binds the key to the long-term
private keys of both parties. -/
@[rocq_alias cryptis.public_hmqv_K_static]
theorem isPublic_hmqvK_static (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (hab : ta ≠ tb) {pa xa pb : Nonce} :
    hmqvKey (GF := GF) pa -∗ hmqvKey pb -∗
      isPublic ↑(hmqvK N ta tb pa xa Pa Xa (g.exp pb) Xb) -∗ isPublic pa ∨ isPublic pb := by
  have hm := SMS.mem_of_mem_posPart (exp_mem_factors_hmqvK hx hg hab (.inr rfl) (N := N)
    (pa := pa) (xa := xa) (pb := pb) (Pa := Pa) (Xa := Xa) (Xb := Xb))
  have hle : {(pa : Term), (pb : Term)} ≤ (g.exp ↑(E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) *
      E.ofTerm (hmqvM N ta Xa (g.exp pb)) * E.ofTerm pa)).exps.posPart := by
    rw [show E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm (hmqvM N ta Xa (g.exp pb)) *
        E.ofTerm pa = (({(pb : Term), hmqvM N tb Xb Pa, hmqvM N ta Xa (g.exp pb), (pa : Term)} :
          Multiset Term).map E.ofTerm).prod by simp [mul_assoc],
      posPart_exps_exp_prod hx hg (by simp [isProd_nonce]), Multiset.pair_comm]
    exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr (by simp))
  unfold hmqvKey
  iintro ⟨-, #Ha⟩ ⟨-, #Hb⟩ #Hp
  icases (isPublic_factors .gmul _).mp $$ Hp with ⟨-, #Hfs⟩
  iapply isPublic_dh_secret_inv_of_le hle $$ Ha Hb
  iapply bigSepMultiset_mem hm $$ Hfs

/-- With an honest long-term key for the peer, whatever the peer's share, the mixed factor binds
the key to the party's ephemeral key and to the peer's long-term key. -/
@[rocq_alias cryptis.public_hmqv_K_mixed]
theorem isPublic_hmqvK_mixed (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (hab : ta ≠ tb) {pa xa pb : Nonce} :
    hmqvKey (GF := GF) xa -∗ hmqvKey pb -∗
      isPublic ↑(hmqvK N ta tb pa xa Pa Xa (g.exp pb) Xb) -∗ isPublic xa ∨ isPublic pb := by
  have hm := SMS.mem_of_mem_posPart (exp_mem_factors_hmqvK hx hg hab (.inl rfl) (N := N)
    (pa := pa) (xa := xa) (pb := pb) (Pa := Pa) (Xa := Xa) (Xb := Xb))
  have hle : {(xa : Term), (pb : Term)} ≤
      (g.exp ↑(E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm xa)).exps.posPart := by
    rw [show E.ofTerm pb * E.ofTerm (hmqvM N tb Xb Pa) * E.ofTerm xa =
        (({(pb : Term), hmqvM N tb Xb Pa, (xa : Term)} : Multiset Term).map E.ofTerm).prod by
          simp [mul_assoc],
      posPart_exps_exp_prod hx hg (by simp [isProd_nonce]), Multiset.pair_comm]
    exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr (by simp))
  unfold hmqvKey
  iintro ⟨-, #Ha⟩ ⟨-, #Hb⟩ #Hp
  icases (isPublic_factors .gmul _).mp $$ Hp with ⟨-, #Hfs⟩
  iapply isPublic_dh_secret_inv_of_le hle $$ Ha Hb
  iapply bigSepMultiset_mem hm $$ Hfs

/-- Resistance to key compromise impersonation: if an honest party talks to an attacker
impersonating an honest peer, the key is public only if the peer's long-term key is, or both of
the party's private keys are. -/
@[rocq_alias cryptis.public_hmqv_K_forged]
theorem isPublic_hmqvK_forged (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (hab : ta ≠ tb) {pa xa pb : Nonce} :
    hmqvKey (GF := GF) pa -∗ hmqvKey xa -∗ hmqvKey pb -∗
      isPublic ↑(hmqvK N ta tb pa xa Pa Xa (g.exp pb) Xb) -∗
      isPublic pb ∨ isPublic pa ∗ isPublic xa := by
  iintro #Hpa #Hxa #Hpb #Hp
  icases isPublic_hmqvK_static hx hg hab $$ Hpa Hpb Hp with (#H₁ | #H)
  · icases isPublic_hmqvK_mixed hx hg hab $$ Hxa Hpb Hp with (#H₂ | #H)
    · iright; iframe H₁ H₂
    · ileft; iexact H
  · ileft; iexact H

/-- Forward secrecy: a key exchanged by two honest parties is public only if both private keys of
one of the parties are. -/
@[rocq_alias cryptis.public_hmqv_K_honest]
theorem isPublic_hmqvK_honest (hx : g.isExp = false) (hg : g.isProd .gmul = false)
    (hab : ta ≠ tb) {pa xa pb xb : Nonce} :
    hmqvKey (GF := GF) pa -∗ hmqvKey xa -∗ hmqvKey pb -∗ hmqvKey xb -∗
      isPublic ↑(hmqvK N ta tb pa xa (g.exp pa) (g.exp xa) (g.exp pb) (g.exp xb)) -∗
      isPublic pa ∗ isPublic xa ∨ isPublic pb ∗ isPublic xb := by
  iintro #Hpa #Hxa #Hpb #Hxb #Hp
  ihave #S := isPublic_hmqvK_static hx hg hab $$ Hpa Hpb Hp
  ihave #E := isPublic_hmqvK_eph hx hg $$ Hxa Hxb Hp
  ihave #M₁ := isPublic_hmqvK_mixed hx hg hab $$ Hxa Hpb Hp
  rw [hmqvK_comm]
  ihave #M₂ := isPublic_hmqvK_mixed hx hg hab.symm $$ Hxb Hpa Hp
  icases S with (#S | #S)
  · icases M₁ with (#M | #M)
    · ileft; iframe S M
    · icases E with (#E | #E)
      · ileft; iframe S E
      · iright; iframe M E
  · icases M₂ with (#M | #M)
    · iright; iframe S M
    · icases E with (#E | #E)
      · ileft; iframe M E
      · iright; iframe S E

end Secrecy

/-! ### The key formula in HeapLang -/

namespace HL

/-- The key of a party with private keys `pa`, `xa` and public keys `Pa`, `Xa`, whose peer has
public keys `Pb`, `Xb`. -/
@[rocq_alias cryptis.hmqv_ke]
def hmqvKE (N : Namespace) (ta tb : String) : Val := hl_val%
  λ pa xa Pa Xa Pb Xb,
    let ma := &hash (&tag &(encode (ofNamespace (N.@ta))) (&termOfList [Xa, Pb]));
    let mb := &hash (&tag &(encode (ofNamespace (N.@tb))) (&termOfList [Xb, Pa]));
    let Y := &tgmul Xb (&texp Pb mb);
    &tgmul (&texp Y xa) (&texp Y (&tmul ma pa))

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF] {s : Stuckness} {𝓔 : CoPset}
local bi (IProp GF)

@[rocq_alias cryptis.wp_hmqv_ke]
theorem wp_hmqvKE (N : Namespace) (ta tb : String) (pa xa Pa Xa Pb Xb : Term)
    (Ψ : Val → IProp GF) :
    Ψ (encode (hmqvK N ta tb pa xa Pa Xa Pb Xb : Term)) ⊢
      WP hl(&(hmqvKE N ta tb) &(encode pa) &(encode xa) &(encode Pa) &(encode Xa) &(encode Pb)
        &(encode Xb)) @ s; 𝓔 {{ Ψ }} := by
  iintro H
  wp_rec
  wp_pures
  wp_list
  wp_term_of_list
  wp_tag
  wp_hash
  wp_list
  wp_term_of_list
  wp_tag
  wp_hash
  wp_pures
  rw [show (Spec.tag (ofNamespace (N.@ta)) (Spec.ofList [Xa, Pb])).hash = hmqvM N ta Xa Pb from rfl,
    show (Spec.tag (ofNamespace (N.@tb)) (Spec.ofList [Xb, Pa])).hash = hmqvM N tb Xb Pa from rfl]
  wp_apply wp_texp (E.ofTerm (hmqvM N tb Xb Pa)) (G.ofTerm Pb)
  wp_apply wp_tgmul (G.ofTerm Xb)
  rw [show G.ofTerm Xb * (E.ofTerm (hmqvM N tb Xb Pa) • G.ofTerm Pb) = hmqvY N tb Pa Pb Xb from rfl]
  wp_pures
  wp_apply wp_tmul (E.ofTerm (hmqvM N ta Xa Pb)) (E.ofTerm pa)
  wp_apply wp_texp (E.ofTerm (hmqvM N ta Xa Pb) * E.ofTerm pa) (hmqvY N tb Pa Pb Xb)
  wp_apply wp_texp (E.ofTerm xa) (hmqvY N tb Pa Pb Xb)
  wp_apply wp_tgmul
  rw [hmqvK_eq_mul]
  iexact H

end HL

end Cryptis
