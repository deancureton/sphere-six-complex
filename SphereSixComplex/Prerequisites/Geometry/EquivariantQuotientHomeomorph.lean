module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Equivariant homeomorphisms of orbit quotients

An equivariant homeomorphism between invariant open carriers identifies their orbit relations
and therefore descends to a homeomorphism of orbit quotients.
-/

namespace SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

open Set

variable {G X Y : Type*} [Group G]
  [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction G X] [MulAction G Y]

/-- A homeomorphism between invariant open carriers which intertwines their restricted group
actions. -/
public structure EquivariantOpenHomeomorph
    (S : SubMulAction G X) (T : SubMulAction G Y) where
  toHomeomorph : S ≃ₜ T
  isOpen_source : IsOpen (S : Set X)
  isOpen_target : IsOpen (T : Set Y)
  equivariant : ∀ (g : G) (x : S),
    toHomeomorph (g • x) = g • toHomeomorph x

/-- An equivariant homeomorphism of invariant open carriers descends to their orbit quotients. -/
@[expose] public noncomputable def orbitQuotientHomeomorph
    {S : SubMulAction G X} {T : SubMulAction G Y}
    (e : EquivariantOpenHomeomorph S T) :
    MulAction.orbitRel.Quotient G S ≃ₜ
      MulAction.orbitRel.Quotient G T :=
  Homeomorph.Quotient.congr e.toHomeomorph fun x y => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      rw [← e.equivariant]
      exact congrArg e.toHomeomorph hg
    · rintro ⟨g, hg⟩
      refine ⟨g, e.toHomeomorph.injective ?_⟩
      rw [e.equivariant]
      exact hg

@[simp]
public theorem orbitQuotientHomeomorph_mk
    {S : SubMulAction G X} {T : SubMulAction G Y}
    (e : EquivariantOpenHomeomorph S T) (x : S) :
    orbitQuotientHomeomorph e (Quotient.mk _ x) =
      Quotient.mk _ (e.toHomeomorph x) :=
  rfl

/-- Evaluate an explicitly supplied action without installing it as a global instance. -/
@[expose] public def actionMap (A : MulAction G X) (g : G) (x : X) : X :=
  letI := A
  g • x

/-- The orbit relation of an explicitly supplied action. -/
@[expose] public def orbitRelOf (A : MulAction G X) : Setoid X :=
  letI := A
  MulAction.orbitRel G X

/-- An open carrier invariant under an explicitly supplied action. -/
public structure InvariantOpenCarrier (A : MulAction G X) where
  carrier : Set X
  isOpen_carrier : IsOpen carrier
  invariant : ∀ (g : G), MapsTo (actionMap A g) carrier carrier

/-- The action restricted to an invariant open carrier. -/
@[expose] public def restrictedActionMap
    {A : MulAction G X} (S : InvariantOpenCarrier A)
    (g : G) (x : S.carrier) : S.carrier :=
  ⟨actionMap A g x, S.invariant g x.property⟩

omit [MulAction G X] in
public theorem restrictedActionMap_one
    {A : MulAction G X} (S : InvariantOpenCarrier A) (x : S.carrier) :
    restrictedActionMap S 1 x = x := by
  apply Subtype.ext
  simp [restrictedActionMap, actionMap]

omit [MulAction G X] in
public theorem restrictedActionMap_mul
    {A : MulAction G X} (S : InvariantOpenCarrier A)
    (g h : G) (x : S.carrier) :
    restrictedActionMap S (g * h) x =
      restrictedActionMap S g (restrictedActionMap S h x) := by
  apply Subtype.ext
  simp [restrictedActionMap, actionMap, mul_smul]

@[expose, instance_reducible]
public def restrictedMulAction (A : MulAction G X) (S : InvariantOpenCarrier A) :
    MulAction G S.carrier where
  smul := restrictedActionMap S
  one_smul := restrictedActionMap_one S
  mul_smul := restrictedActionMap_mul S

/-- The orbit relation of the action restricted to an invariant carrier. -/
@[expose] public def restrictedOrbitRel
    (A : MulAction G X) (S : InvariantOpenCarrier A) : Setoid S.carrier :=
  letI := restrictedMulAction A S
  MulAction.orbitRel G S.carrier

/-- An equivariant homeomorphism for two explicitly supplied actions.  This version permits the
source and target actions to live on the same ambient type. -/
public structure EquivariantOpenHomeomorphOfActions
    (AX : MulAction G X) (AY : MulAction G Y)
    (S : InvariantOpenCarrier AX) (T : InvariantOpenCarrier AY) where
  toHomeomorph : S.carrier ≃ₜ T.carrier
  equivariant : ∀ (g : G) (x : S.carrier),
    toHomeomorph (restrictedActionMap S g x) =
      restrictedActionMap T g (toHomeomorph x)

omit [MulAction G X] [MulAction G Y] in
/-- Equivariance for a cyclic action follows from equivariance for a chosen generator. -/
public theorem equivariant_of_cyclic_generator
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : InvariantOpenCarrier AX} {T : InvariantOpenCarrier AY}
    (e : S.carrier ≃ₜ T.carrier) (generator : G)
    (hgenerate : ∀ g : G, ∃ k : ℕ, g = generator ^ k)
    (hgenerator : ∀ x : S.carrier,
      e (restrictedActionMap S generator x) =
        restrictedActionMap T generator (e x)) :
    ∀ (g : G) (x : S.carrier),
      e (restrictedActionMap S g x) = restrictedActionMap T g (e x) := by
  intro g x
  obtain ⟨k, rfl⟩ := hgenerate g
  induction k generalizing x with
  | zero => simp only [pow_zero, restrictedActionMap_one]
  | succ k ih =>
      rw [pow_succ, restrictedActionMap_mul, restrictedActionMap_mul,
        ih, hgenerator]

/-- Explicit-action form of equivariant descent, applicable when the two actions have the same
ambient point type. -/
@[expose] public noncomputable def restrictedOrbitQuotientHomeomorph
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : InvariantOpenCarrier AX} {T : InvariantOpenCarrier AY}
    (e : EquivariantOpenHomeomorphOfActions AX AY S T) :
    Quotient (restrictedOrbitRel AX S) ≃ₜ
      Quotient (restrictedOrbitRel AY T) :=
  Homeomorph.Quotient.congr e.toHomeomorph fun x y => by
    change (∃ g : G, restrictedActionMap S g y = x) ↔
      ∃ g : G, restrictedActionMap T g (e.toHomeomorph y) = e.toHomeomorph x
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      exact (e.equivariant g y).symm.trans (congrArg e.toHomeomorph hg)
    · rintro ⟨g, hg⟩
      exact ⟨g, e.toHomeomorph.injective ((e.equivariant g y).trans hg)⟩

omit [MulAction G X] [MulAction G Y] in
@[simp]
public theorem restrictedOrbitQuotientHomeomorph_mk
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : InvariantOpenCarrier AX} {T : InvariantOpenCarrier AY}
    (e : EquivariantOpenHomeomorphOfActions AX AY S T) (x : S.carrier) :
    restrictedOrbitQuotientHomeomorph e (Quotient.mk _ x) =
      Quotient.mk _ (e.toHomeomorph x) :=
  rfl

omit [MulAction G X] [MulAction G Y] in
@[simp]
public theorem restrictedOrbitQuotientHomeomorph_symm_mk
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : InvariantOpenCarrier AX} {T : InvariantOpenCarrier AY}
    (e : EquivariantOpenHomeomorphOfActions AX AY S T) (y : T.carrier) :
    (restrictedOrbitQuotientHomeomorph e).symm (Quotient.mk _ y) =
      Quotient.mk _ (e.toHomeomorph.symm y) := by
  apply (restrictedOrbitQuotientHomeomorph e).injective
  rw [Homeomorph.apply_symm_apply, restrictedOrbitQuotientHomeomorph_mk,
    e.toHomeomorph.apply_symm_apply]

end SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
