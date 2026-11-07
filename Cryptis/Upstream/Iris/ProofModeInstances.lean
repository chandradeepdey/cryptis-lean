module

public import Iris.ProofMode.Instances

/-! Upstream candidate (Iris-Lean): proof-mode instances for `Iris/ProofMode/Instances.lean`.

- `iapply` and `ispecialize` use a hypothesis `P ↔ Q` in either direction, as they do for
  `P ∗-∗ Q`.
- `iframe` closes a big separating conjunction over a list literal once its last element is
  framed.
- `icases` splits an intuitionistic big separating conjunction over a list literal. -/

@[expose] public section

namespace Iris.ProofMode

open BI

instance intoWand_iff (p q : Bool) [BI PROP] (R1 R2 P' Q' : PROP)
    [h : IntoWand p q iprop((R1 → R2) ∧ (R2 → R1)) m P' Q'] :
    IntoWand p q iprop(R1 ↔ R2) m P' Q' := h

/-- Framing the element of a singleton list leaves no `[∗list] _ ∈ []` behind. -/
instance (priority := high) frame_bigSepL_singleton [BI PROP] {A} p (Φ : Nat → A → PROP)
    (R Q : PROP) (x : A) [h : Frame p R (Φ 0 x) Q] :
    Frame p R ([∗list] k ↦ y ∈ [x], Φ k y) Q where
  frame := h.frame.trans BigSepL.bigSepL_singleton.mpr

@[ipm_backtrack]
instance intoAnd_bigSepL_cons [BI PROP] {A} (p : Bool) (Φ : Nat → A → PROP) (l : List A) (x : A)
    (l' : List A) (P Q : PROP) [hl : IsCons l x l']
    [h : IntoAnd p iprop(Φ 0 x ∗ [∗list] k ↦ y ∈ l', Φ (k + 1) y) P Q] :
    IntoAnd p ([∗list] k ↦ y ∈ l, Φ k y) P Q where
  into_and := hl.is_cons ▸ h.into_and

end Iris.ProofMode
