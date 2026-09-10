module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SphereSixComplex.Prerequisites.Geometry.ComplexUnitDisc

namespace SphereSixComplex.Geometry.EllipticWholeFiberTrivialization

open Filter Set

noncomputable section

universe u v w

/-- Raw compatibility data for gluing local partial diffeomorphisms.  The global forward and
inverse maps carry only topological inverse data.  Their analyticity is forced by local agreement
with the supplied partial diffeomorphisms. -/
public structure CompatiblePartialDiffeomorphs
    (Index : Type u) {E H : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M N : Type w) [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] (n : WithTop ℕ∞) where
  source : Set M
  target : Set N
  open_source : IsOpen source
  open_target : IsOpen target
  toFun : M → N
  invFun : N → M
  map_source : MapsTo toFun source target
  map_target : MapsTo invFun target source
  left_inv : Set.LeftInvOn invFun toFun source
  right_inv : Set.RightInvOn invFun toFun target
  chart : Index → PartialDiffeomorph I I M N n
  locally_toFun : ∀ x ∈ source, ∃ i,
    x ∈ (chart i).source ∧
    toFun =ᶠ[nhdsWithin x source] chart i ∧ toFun x = chart i x
  locally_invFun : ∀ y ∈ target, ∃ i,
    y ∈ (chart i).target ∧
    invFun =ᶠ[nhdsWithin y target] (chart i).symm ∧ invFun y = (chart i).symm y

namespace CompatiblePartialDiffeomorphs

variable {Index : Type u} {E H : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] {n : WithTop ℕ∞}
    (D : CompatiblePartialDiffeomorphs Index I M N n)

public theorem contMDiffOn_toFun : ContMDiffOn I I n D.toFun D.source := by
  intro x hx
  obtain ⟨i, hxi, hevent, hpoint⟩ := D.locally_toFun x hx
  have hchart : ContMDiffAt I I n (D.chart i) x :=
    (D.chart i).contMDiffOn_toFun.contMDiffAt ((D.chart i).open_source.mem_nhds hxi)
  exact hchart.contMDiffWithinAt.congr_of_eventuallyEq hevent hpoint

public theorem contMDiffOn_invFun : ContMDiffOn I I n D.invFun D.target := by
  intro y hy
  obtain ⟨i, hyi, hevent, hpoint⟩ := D.locally_invFun y hy
  have hchart : ContMDiffAt I I n (D.chart i).symm y :=
    (D.chart i).contMDiffOn_invFun.contMDiffAt ((D.chart i).open_target.mem_nhds hyi)
  exact hchart.contMDiffWithinAt.congr_of_eventuallyEq hevent hpoint

/-- Compatible local analytic charts glue to one analytic partial diffeomorphism. -/
@[expose] public noncomputable def toPartialDiffeomorph : PartialDiffeomorph I I M N n where
  toPartialEquiv :=
    { toFun := D.toFun
      invFun := D.invFun
      source := D.source
      target := D.target
      map_source' := D.map_source
      map_target' := D.map_target
      left_inv' := D.left_inv
      right_inv' := D.right_inv }
  open_source := D.open_source
  open_target := D.open_target
  contMDiffOn_toFun := D.contMDiffOn_toFun
  contMDiffOn_invFun := D.contMDiffOn_invFun

@[simp]
public theorem toPartialDiffeomorph_apply (x : M) : D.toPartialDiffeomorph x = D.toFun x :=
  rfl

@[simp]
public theorem toPartialDiffeomorph_symm_apply (y : N) :
    D.toPartialDiffeomorph.symm y = D.invFun y :=
  rfl

end CompatiblePartialDiffeomorphs

/-- The punctured product is the collar side of an elliptic filling. -/
@[expose] public def puncturedDiscProduct (T : Type*) : Set (ComplexUnitDisc × T) :=
  {p | p.1 ≠ ComplexUnitDisc.center}

public theorem puncturedDiscProduct_isOpen (T : Type*) [TopologicalSpace T] :
    IsOpen (puncturedDiscProduct T) := by
  change IsOpen (Prod.fst ⁻¹' ({ComplexUnitDisc.center} : Set ComplexUnitDisc)ᶜ)
  exact (isClosed_singleton.preimage continuous_fst).isOpen_compl

section Collar

variable {Index : Type u} {E H : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    {M T : Type w} [TopologicalSpace M] [TopologicalSpace T]
    [ChartedSpace H M] [ChartedSpace H (ComplexUnitDisc × T)] {n : WithTop ℕ∞}

/-- The collar identification obtained by restricting a whole-fibre trivialization away from the
central disc point. -/
@[expose] public noncomputable def collarOpenPartialHomeomorph
    (D : CompatiblePartialDiffeomorphs Index I M (ComplexUnitDisc × T) n) :
    OpenPartialHomeomorph M (ComplexUnitDisc × T) :=
  (((D.toPartialDiffeomorph.symm.toOpenPartialHomeomorph).restrOpen
    (puncturedDiscProduct T) (puncturedDiscProduct_isOpen T)).symm)

public theorem collar_target_subset_puncturedDiscProduct
    (D : CompatiblePartialDiffeomorphs Index I M (ComplexUnitDisc × T) n) :
    (collarOpenPartialHomeomorph D).target ⊆ puncturedDiscProduct T := by
  intro p hp
  exact hp.2

end Collar

/-- Equivariance data for the glued neighbourhood.  Invariance ensures that both actions restrict
to the two open sets, while the last field is the exact overlap identity required for descent to
the finite filling quotient. -/
public structure EquivariantWholeFiberCompatibility
    (G Index : Type u) [Group G]
    {E H : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M N : Type w) [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] (n : WithTop ℕ∞) where
  gluing : CompatiblePartialDiffeomorphs Index I M N n
  sourceRepresentation : G →* Equiv.Perm M
  targetRepresentation : G →* Equiv.Perm N
  source_invariant : ∀ g, MapsTo (sourceRepresentation g) gluing.source gluing.source
  target_invariant : ∀ g, MapsTo (targetRepresentation g) gluing.target gluing.target
  equivariant : ∀ g, Set.EqOn
    (gluing.toFun ∘ sourceRepresentation g)
    (targetRepresentation g ∘ gluing.toFun) gluing.source

namespace EquivariantWholeFiberCompatibility

variable {G Index : Type u} [Group G]
    {E H : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace H M] [ChartedSpace H N] {n : WithTop ℕ∞}
    (D : EquivariantWholeFiberCompatibility G Index I M N n)

/-- The glued analytic partial diffeomorphism retains the stipulated group equivariance. -/
public theorem toPartialDiffeomorph_equivariant (g : G) : Set.EqOn
    (D.gluing.toPartialDiffeomorph ∘ D.sourceRepresentation g)
    (D.targetRepresentation g ∘ D.gluing.toPartialDiffeomorph) D.gluing.source :=
  D.equivariant g

end EquivariantWholeFiberCompatibility

end

end SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
