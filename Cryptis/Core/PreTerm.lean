module

public import Cryptis.Core.PreTerm.Base
public import Cryptis.Core.PreTerm.WithStdpp
public import Cryptis.Core.PreTerm.Normalize

/-! Pre-terms: the datatype and its order (`Base`), its HeapLang encoding, nonces and linear order
(`WithStdpp`), and normalization (`Normalize`). -/

@[expose] public section
namespace Cryptis
namespace PreTerm

/-- The number of constructors in a pre-term. -/
@[rocq_alias cryptis.PreTerm.tsize]
def tsize : PreTerm → Nat
  | op0 _ => 1
  | op1 _ t => t.tsize + 1
  | op2 _ t₁ t₂ => t₁.tsize + t₂.tsize + 1
  | opN _ ps ns => (ps.map tsize).sum + (ns.map tsize).sum + 1

end PreTerm
end Cryptis
