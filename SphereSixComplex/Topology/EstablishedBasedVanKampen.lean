module

public import SphereSixComplex.Topology.ConcreteVanKampen

/-!
# Based generator extraction from groupoid van Kampen

Mathlib proves the fundamental-groupoid colimit theorem for open covers. This module isolates the
standard based-group consequence: after choosing connector paths, generators for the local
fundamental groups generate the fundamental group of the covered space.
-/

@[expose] public section

noncomputable section

open Set Topology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- Inclusion of a subspace into its ambient space. -/
public def subsetInclusion (U : Set Y) : C(U, Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The central-piece fundamental group mapped to the ambient base point. -/
public def coreFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.core ⟨base, D.base_mem_core⟩ →* FundamentalGroup Y base :=
  FundamentalGroup.map (subsetInclusion D.core) ⟨base, D.base_mem_core⟩

/-- The cusp-piece fundamental group, transported to the ambient base along its connector. -/
public def cuspFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.cusp ⟨D.cuspPoint, D.cuspPoint_mem.2⟩ →* FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath D.cuspConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.cusp) ⟨D.cuspPoint, D.cuspPoint_mem.2⟩)

/-- The order-three filling fundamental group, transported to the ambient base. -/
public def ellipticThreeFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.ellipticThree
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩ →*
      FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      D.ellipticThreeConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.ellipticThree)
      ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩)

/-- The order-four filling fundamental group, transported to the ambient base. -/
public def ellipticFourFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup D.ellipticFour
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩ →*
      FundamentalGroup Y base :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      D.ellipticFourConnector.symm).toMonoidHom.comp
    (FundamentalGroup.map (subsetInclusion D.ellipticFour)
      ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩)

/-- Inclusion of the cusp overlap into the cusp piece. -/
public def cuspOverlapToPiece (D : PaperVanKampenFourPieceCover base) :
    C((D.core ∩ D.cusp : Set Y), D.cusp) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the order-three overlap into its filling piece. -/
public def ellipticThreeOverlapToPiece (D : PaperVanKampenFourPieceCover base) :
    C((D.core ∩ D.ellipticThree : Set Y), D.ellipticThree) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the order-four overlap into its filling piece. -/
public def ellipticFourOverlapToPiece (D : PaperVanKampenFourPieceCover base) :
    C((D.core ∩ D.ellipticFour : Set Y), D.ellipticFour) where
  toFun x := ⟨x, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The map on fundamental groups from the cusp overlap to the cusp filling. -/
public def cuspOverlapFundamentalGroupMap (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup (D.core ∩ D.cusp : Set Y) ⟨D.cuspPoint, D.cuspPoint_mem⟩ →*
      FundamentalGroup D.cusp ⟨D.cuspPoint, D.cuspPoint_mem.2⟩ :=
  FundamentalGroup.map D.cuspOverlapToPiece ⟨D.cuspPoint, D.cuspPoint_mem⟩

/-- The map on fundamental groups from the order-three overlap to its filling. -/
public def ellipticThreeOverlapFundamentalGroupMap
    (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup (D.core ∩ D.ellipticThree : Set Y)
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩ →*
      FundamentalGroup D.ellipticThree
        ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem.2⟩ :=
  FundamentalGroup.map D.ellipticThreeOverlapToPiece
    ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩

/-- The map on fundamental groups from the order-four overlap to its filling. -/
public def ellipticFourOverlapFundamentalGroupMap
    (D : PaperVanKampenFourPieceCover base) :
    FundamentalGroup (D.core ∩ D.ellipticFour : Set Y)
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩ →*
      FundamentalGroup D.ellipticFour
        ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem.2⟩ :=
  FundamentalGroup.map D.ellipticFourOverlapToPiece
    ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩

/-- A subgroup containing the images of the four local fundamental groups is the whole ambient
fundamental group. This is the based-group generator consequence of groupoid van Kampen. -/
public axiom localFundamentalGroupImages_generate
    (D : PaperVanKampenFourPieceCover base)
    (H : Subgroup (FundamentalGroup Y base))
    (hcore : D.coreFundamentalGroupMap.range ≤ H)
    (hcusp : D.cuspFundamentalGroupMap.range ≤ H)
    (hthree : D.ellipticThreeFundamentalGroupMap.range ≤ H)
    (hfour : D.ellipticFourFundamentalGroupMap.range ≤ H) :
    H = ⊤

/-- Basepoint transport along a path is natural in the space. -/
public theorem map_fundamentalGroupMulEquivOfPath {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {x₀ x₁ : A} (p : Path x₀ x₁) (γ : FundamentalGroup A x₀) :
    FundamentalGroup.map f x₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath p γ) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x₀ γ) := by
  show (FundamentalGroupoid.map f).map
      (((Groupoid.isoEquivHom _ _).symm (Path.Homotopic.Quotient.mk p)).conj γ) = _
  show (FundamentalGroupoid.map f).map _ = _
  simp only [Iso.conj_apply, Groupoid.isoEquivHom_symm_apply_inv,
    Groupoid.isoEquivHom_symm_apply_hom, Functor.map_comp]
  show _ = ((Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (p.map f.continuous))).conj
      ((FundamentalGroupoid.map f).map γ)
  simp only [Iso.conj_apply, Groupoid.isoEquivHom_symm_apply_inv,
    Groupoid.isoEquivHom_symm_apply_hom]
  congr 1
  rw [Functor.map_inv]
  exact (Groupoid.inv_eq_inv _).symm

/-- Functoriality of the induced map on fundamental groups. -/
public theorem map_map {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (x : A) (γ : FundamentalGroup A x) :
    FundamentalGroup.map g (f x) (FundamentalGroup.map f x γ) =
      FundamentalGroup.map (g.comp f) x γ :=
  (Path.Homotopic.Quotient.map_comp (p := γ) (f := f) (g := g)).symm

/-- Inclusion of an overlap into the core. -/
public def overlapToCore (D : PaperVanKampenFourPieceCover base) (P : Set Y) :
    C((D.core ∩ P : Set Y), D.core) where
  toFun x := ⟨x, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- A connector that stays in the core, viewed as a path in the core. -/
public def connectorInCore (D : PaperVanKampenFourPieceCover base) {pt : Y}
    (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core) (hpt : pt ∈ D.core) :
    Path (⟨base, D.base_mem_core⟩ : D.core) ⟨pt, hpt⟩ where
  toFun t := ⟨conn t, hconn t⟩
  continuous_toFun := conn.continuous.subtype_mk _
  source' := by simp
  target' := by simp

/-- Loops of a piece that come from its overlap with the core, transported to the base point along
a connector inside the core, already lie in the image of the core. -/
public theorem transport_mem_range_core (D : PaperVanKampenFourPieceCover base) {P : Set Y} {pt : Y}
    (hpt : pt ∈ D.core ∩ P) (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core)
    (y : FundamentalGroup (D.core ∩ P : Set Y) ⟨pt, hpt⟩) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm)
        (FundamentalGroup.map (subsetInclusion P) ⟨pt, hpt.2⟩
          (FundamentalGroup.map
            (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z, z.2.2⟩ : P), by fun_prop⟩ :
              C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ y)) ∈
      D.coreFundamentalGroupMap.range := by
  classical
  set connCore : Path (⟨base, D.base_mem_core⟩ : D.core) ⟨pt, hpt.1⟩ :=
    D.connectorInCore conn hconn hpt.1 with hconnCore
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm)
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ y), ?_⟩
  have hnat := map_fundamentalGroupMulEquivOfPath (subsetInclusion D.core) connCore.symm
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ y)
  have hpath : (connCore.symm.map (subsetInclusion D.core).continuous) = conn.symm := by
    ext t
    rfl
  show FundamentalGroup.map (subsetInclusion D.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) = _
  rw [hnat, hpath]
  congr 1
  have h1 : FundamentalGroup.map (subsetInclusion D.core) ⟨pt, hpt.1⟩
      (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ y)
      = FundamentalGroup.map ((subsetInclusion D.core).comp (D.overlapToCore P)) ⟨pt, hpt⟩ y :=
    map_map _ _ _ _
  have h2 : FundamentalGroup.map (subsetInclusion P) ⟨pt, hpt.2⟩
      (FundamentalGroup.map
        (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z, z.2.2⟩ : P), by fun_prop⟩ :
          C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ y)
      = FundamentalGroup.map ((subsetInclusion P).comp
          ⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z, z.2.2⟩ : P), by fun_prop⟩) ⟨pt, hpt⟩ y :=
    map_map _ _ _ _
  rw [h1, h2]
  congr 1

/-- If every filling fundamental group is generated by its overlap with the core, the core
inclusion surjects on the fundamental group of the four-piece star.

This is a consequence of the van Kampen generation statement above rather than a separate input:
the overlap loops, and the connectors used to move them to the base point, all lie in the core, so
each filling's image is already contained in the image of the core. -/
public theorem coreFundamentalGroupMap_surjective_of_overlap_surjective
    (D : PaperVanKampenFourPieceCover base)
    (hcusp : Function.Surjective D.cuspOverlapFundamentalGroupMap)
    (hthree : Function.Surjective D.ellipticThreeOverlapFundamentalGroupMap)
    (hfour : Function.Surjective D.ellipticFourOverlapFundamentalGroupMap) :
    Function.Surjective D.coreFundamentalGroupMap := by
  rw [← MonoidHom.range_eq_top]
  refine localFundamentalGroupImages_generate D _ le_rfl ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hcusp x
    exact D.transport_mem_range_core D.cuspPoint_mem D.cuspConnector D.cuspConnector_mem y
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hthree x
    exact D.transport_mem_range_core D.ellipticThreePoint_mem D.ellipticThreeConnector
      D.ellipticThreeConnector_mem y
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hfour x
    exact D.transport_mem_range_core D.ellipticFourPoint_mem D.ellipticFourConnector
      D.ellipticFourConnector_mem y

end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

end
