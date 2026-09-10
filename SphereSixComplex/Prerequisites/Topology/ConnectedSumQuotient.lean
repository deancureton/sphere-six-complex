module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Data.Quot

/-!
# Group structures on quotients by connected-sum relations

The geometric construction of connected sum is independent of the quotient bookkeeping proved in
this file.  `ConnectedSumQuotientData` records exactly the representative-level operation,
well-definedness, and laws needed to put an additive commutative group on equivalence classes.

For smooth homotopy spheres, supplying these fields requires the missing smooth connected-sum
construction and its geometric theorems.  This module proves that no further algebraic obstruction
remains once those theorems are available.
-/

@[expose] public section

namespace SphereSixComplex

/-- Representative-level connected sum, standard object, orientation reversal, and their laws
modulo an equivalence relation. -/
public structure ConnectedSumQuotientData {A : Type*} (relation : Setoid A) where
  /-- Connected sum of representatives. -/
  connectedSum : A → A → A
  /-- The standard sphere representative. -/
  standard : A
  /-- Orientation reversal. -/
  reverseOrientation : A → A
  /-- Connected sum respects the equivalence relation in both arguments. -/
  connectedSum_congr :
    ∀ {a a' b b'}, relation.r a a' → relation.r b b' →
      relation.r (connectedSum a b) (connectedSum a' b')
  /-- Orientation reversal respects the equivalence relation. -/
  reverseOrientation_congr :
    ∀ {a a'}, relation.r a a' →
      relation.r (reverseOrientation a) (reverseOrientation a')
  /-- Associativity up to the relation. -/
  connectedSum_assoc :
    ∀ a b c, relation.r (connectedSum (connectedSum a b) c)
      (connectedSum a (connectedSum b c))
  /-- The standard sphere is a left unit up to the relation. -/
  standard_connectedSum : ∀ a, relation.r (connectedSum standard a) a
  /-- Orientation reversal is a left inverse up to the relation. -/
  reverseOrientation_connectedSum :
    ∀ a, relation.r (connectedSum (reverseOrientation a) a) standard
  /-- Connected sum is commutative up to the relation. -/
  connectedSum_comm : ∀ a b, relation.r (connectedSum a b) (connectedSum b a)

namespace ConnectedSumQuotientData

variable {A : Type*} {relation : Setoid A} (D : ConnectedSumQuotientData relation)

/-- Connected sum on equivalence classes. -/
public def addClass : Quotient relation → Quotient relation → Quotient relation :=
  Quotient.map₂ D.connectedSum fun _ _ ha _ _ hb ↦ D.connectedSum_congr ha hb

/-- The standard-sphere class. -/
public def zeroClass : Quotient relation := Quotient.mk relation D.standard

/-- Orientation reversal on equivalence classes. -/
public def negClass : Quotient relation → Quotient relation :=
  Quotient.map D.reverseOrientation fun _ _ h ↦ D.reverseOrientation_congr h

@[simp]
public theorem addClass_mk (a b : A) :
    D.addClass (Quotient.mk relation a) (Quotient.mk relation b) =
      Quotient.mk relation (D.connectedSum a b) :=
  rfl

@[simp]
public theorem negClass_mk (a : A) :
    D.negClass (Quotient.mk relation a) = Quotient.mk relation (D.reverseOrientation a) :=
  rfl

/-- The connected-sum data induces an additive commutative group on equivalence classes. -/
@[instance_reducible]
public def addCommGroup : AddCommGroup (Quotient relation) := by
  letI : Add (Quotient relation) := ⟨D.addClass⟩
  letI : Zero (Quotient relation) := ⟨D.zeroClass⟩
  letI : Neg (Quotient relation) := ⟨D.negClass⟩
  let hAddGroup : AddGroup (Quotient relation) := AddGroup.ofLeftAxioms
    (by
      intro a b c
      refine Quotient.inductionOn₃ a b c ?_
      intro x y z
      exact Quotient.sound (D.connectedSum_assoc x y z))
    (by
      intro a
      refine Quotient.inductionOn a ?_
      intro x
      exact Quotient.sound (D.standard_connectedSum x))
    (by
      intro a
      refine Quotient.inductionOn a ?_
      intro x
      exact Quotient.sound (D.reverseOrientation_connectedSum x))
  exact
    { hAddGroup with
      add_comm := by
        intro a b
        refine Quotient.inductionOn₂ a b ?_
        intro x y
        exact Quotient.sound (D.connectedSum_comm x y) }

end ConnectedSumQuotientData

end SphereSixComplex
