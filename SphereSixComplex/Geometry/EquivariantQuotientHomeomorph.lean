module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Equivariant homeomorphisms of orbit quotients

An equivariant homeomorphism between open subactions identifies their orbit relations and
therefore descends to a homeomorphism of orbit quotients.
-/

namespace SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

open Set

universe u v w

variable {G : Type u} {X : Type v} {Y : Type w} [Group G]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- Evaluate an explicitly supplied action without installing it as a global instance. -/
@[expose] public def smulOf (A : MulAction G X) (g : G) (x : X) : X :=
  letI := A
  g • x

/-- A subaction whose underlying carrier is open.  The action is supplied explicitly so that
several actions on the same ambient type can be used in one declaration. -/
public structure OpenSubMulAction (A : MulAction G X) where
  toSubMulAction : letI := A; SubMulAction G X
  isOpen_carrier : IsOpen (toSubMulAction : Set X)

omit [TopologicalSpace Y] in
public instance {A : MulAction G X} : CoeSort (OpenSubMulAction A) (Type v) where
  coe S := letI := A; S.toSubMulAction

omit [TopologicalSpace Y] in
@[instance_reducible] public def OpenSubMulAction.mulAction
    {A : MulAction G X} (S : OpenSubMulAction A) : MulAction G S := by
  letI := A
  exact S.toSubMulAction.mulAction

omit [TopologicalSpace Y] in
/-- The orbit relation on an open subaction. -/
public abbrev OpenSubMulAction.orbitRel
    {A : MulAction G X} (S : OpenSubMulAction A) : Setoid S :=
  MulAction.orbitRel G S

omit [TopologicalSpace Y] in
/-- The orbit quotient of an open subaction. -/
public abbrev OpenSubMulAction.OrbitQuotient
    {A : MulAction G X} (S : OpenSubMulAction A) :=
  MulAction.orbitRel.Quotient G S

/-- A homeomorphism between two open subactions which intertwines their group actions. -/
public structure EquivariantOpenHomeomorph
    (AX : MulAction G X) (AY : MulAction G Y)
    (S : OpenSubMulAction AX) (T : OpenSubMulAction AY) where
  toHomeomorph : Homeomorph S T
  equivariant : ∀ (g : G) (x : S),
    toHomeomorph (g • x) = g • toHomeomorph x

/-- Equivariance for a cyclic action follows from equivariance for a chosen generator. -/
public theorem equivariant_of_cyclic_generator
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : OpenSubMulAction AX} {T : OpenSubMulAction AY}
    (e : Homeomorph S T) (generator : G)
    (hgenerate : ∀ g : G, ∃ k : ℕ, g = generator ^ k)
    (hgenerator : ∀ x : S, e (generator • x) = generator • e x) :
    ∀ (g : G) (x : S), e (g • x) = g • e x := by
  intro g x
  obtain ⟨k, rfl⟩ := hgenerate g
  induction k generalizing x with
  | zero => simp
  | succ k ih => simp only [pow_succ, mul_smul, ih, hgenerator]

/-- An equivariant homeomorphism of open subactions descends to their orbit quotients. -/
@[expose] public noncomputable def orbitQuotientHomeomorph
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : OpenSubMulAction AX} {T : OpenSubMulAction AY}
    (e : EquivariantOpenHomeomorph AX AY S T) :
    Homeomorph S.OrbitQuotient T.OrbitQuotient :=
  Homeomorph.Quotient.congr e.toHomeomorph fun x y => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (e.equivariant g y).symm.trans (congrArg e.toHomeomorph hg)⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.toHomeomorph.injective ((e.equivariant g y).trans hg)⟩

@[simp]
public theorem orbitQuotientHomeomorph_mk
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : OpenSubMulAction AX} {T : OpenSubMulAction AY}
    (e : EquivariantOpenHomeomorph AX AY S T) (x : S) :
    orbitQuotientHomeomorph e (Quotient.mk _ x) =
      Quotient.mk _ (e.toHomeomorph x) :=
  rfl

end SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
