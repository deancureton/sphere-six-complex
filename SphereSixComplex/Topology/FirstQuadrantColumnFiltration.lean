module

public import SphereSixComplex.Topology.FirstQuadrantSingleColumnTotal
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Finite column filtrations of first-quadrant bicomplexes

This file constructs the brutal finite-prefix filtration in the outer direction of a
first-quadrant bicomplex.  It is the elementary filtration used to promote componentwise
quasi-isomorphisms to quasi-isomorphisms after direct-sum totalization.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace SphereSixComplex

/-- The finite interval of outer degrees retained by the `n`th brutal prefix. -/
public abbrev FirstQuadrantColumnPrefixIndex (n : ℕ) := {p : ℕ // p ≤ n}

/-- The chain-complex shape obtained by restricting the usual downward shape on `ℕ` to
`0, ..., n`.  Defining the shape by restriction avoids all dependent casts at the cutoff. -/
public def firstQuadrantColumnPrefixShape (n : ℕ) :
    ComplexShape (FirstQuadrantColumnPrefixIndex n) where
  Rel p q := (ComplexShape.down ℕ).Rel p.1 q.1
  next_eq hp hq := Subtype.ext ((ComplexShape.down ℕ).next_eq hp hq)
  prev_eq hp hq := Subtype.ext ((ComplexShape.down ℕ).prev_eq hp hq)

/-- Inclusion of the finite prefix shape in the first-quadrant outer shape. -/
public def firstQuadrantColumnPrefixEmbedding (n : ℕ) :
    (firstQuadrantColumnPrefixShape n).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk'
    (firstQuadrantColumnPrefixShape n) (ComplexShape.down ℕ)
    Subtype.val Subtype.val_injective (fun _ _ => Iff.rfl)

noncomputable instance (n : ℕ) :
    (firstQuadrantColumnPrefixEmbedding n).IsRelIff where
  rel' _ _ h := h

/-- The brutal prefix consisting of outer columns `0, ..., n`.

This is Mathlib's restriction followed by extension by zero.  Consequently the shape and
`d² = 0` proofs, including the differential crossing the cutoff, come from the generic
zero-extension construction rather than from hand-written dependent `if` expressions. -/
public noncomputable def firstQuadrantColumnPrefix
    (K : FirstQuadrantBicomplex) (n : ℕ) : FirstQuadrantBicomplex :=
  K.stupidTrunc (firstQuadrantColumnPrefixEmbedding n)

/-- A bicomplex map restricts to every brutal finite column prefix. -/
public noncomputable def firstQuadrantColumnPrefixMap
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (n : ℕ) :
    firstQuadrantColumnPrefix K n ⟶ firstQuadrantColumnPrefix L n :=
  HomologicalComplex.stupidTruncMap f (firstQuadrantColumnPrefixEmbedding n)

/-- Inside the retained range, the brutal prefix has the original column. -/
public noncomputable def firstQuadrantColumnPrefixXIso
    (K : FirstQuadrantBicomplex) (n p : ℕ) (hp : p ≤ n) :
    (firstQuadrantColumnPrefix K n).X p ≅ K.X p :=
  K.stupidTruncXIso (firstQuadrantColumnPrefixEmbedding n)
    (i := ⟨p, hp⟩) rfl

/-- Outside the retained range, the brutal prefix column is zero. -/
public theorem firstQuadrantColumnPrefix_isZero_X
    (K : FirstQuadrantBicomplex) (n p : ℕ) (hp : n < p) :
    IsZero ((firstQuadrantColumnPrefix K n).X p) := by
  unfold firstQuadrantColumnPrefix
  apply HomologicalComplex.isZero_stupidTrunc_X
  intro i hi
  change i.1 = p at hi
  omega

end SphereSixComplex
