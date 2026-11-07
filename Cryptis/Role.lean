module

public import Cryptis.Lib.Encode

/-! The roles of the two participants of a protocol session: the initiator and the responder. -/

@[expose] public section

namespace Cryptis

open Iris Iris.HeapLang

@[rocq_alias cryptis.role]
inductive Role where
  | init
  | resp
deriving DecidableEq, Inhabited, Repr

attribute [rocq_alias cryptis.role_eq_dec] instDecidableEqRole
attribute [rocq_alias cryptis.role_inhabited] instInhabitedRole

#rocq_ignore cryptis.roleO "Leibniz OFEs are built on demand with OFE.ofDiscrete"
#rocq_ignore cryptis.role_equivI
  "Roles form a discrete OFE, so internal equality of roles is ⌜rl₁ = rl₂⌝"

namespace Role

/-- The initiator is `true`. -/
@[rocq_alias cryptis.bool_of_role]
def toBool : Role → Bool
  | init => true
  | resp => false

@[rocq_alias cryptis.role_of_bool]
def ofBool : Bool → Role
  | true => init
  | false => resp

@[simp, rocq_alias cryptis.bool_of_roleK]
theorem ofBool_toBool (rl : Role) : ofBool rl.toBool = rl := by
  cases rl <;> rfl

@[simp]
theorem toBool_ofBool (b : Bool) : (ofBool b).toBool = b := by
  cases b <;> rfl

@[rocq_alias cryptis.role_countable]
instance : Pos.Countable Role where
  encode rl := Pos.Countable.encode rl.toBool
  decode p := (Pos.Countable.decode p).map ofBool
  decode_encode _ := by simp [Pos.Countable.decode_encode]

/-- The other role. -/
@[rocq_alias cryptis.swap_role]
def swap : Role → Role
  | init => resp
  | resp => init

@[simp, rocq_alias cryptis.swap_roleK]
theorem swap_swap (rl : Role) : rl.swap.swap = rl := by
  cases rl <;> rfl

@[rocq_alias cryptis.repr_role]
instance : Encode Role where
  encode
    | init => hl_val(#(1 : Int))
    | resp => hl_val(#(0 : Int))

end Role

end Cryptis
