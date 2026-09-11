module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineMarkedBandTrivialization

@[expose] public section
noncomputable section
open Set Topology
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData
variable (A : PaperAnalyticData)

public def regularFixedFiberCover
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (v : ComplexTwoSpace) : A.CentralFamily :=
  A.centralQuotientProjection (projection (regularParameterMap A.periods)
    (b, A.regularFixedToMoving b v))

public theorem regularFixedFiberCover_respects
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (v v' : ComplexTwoSpace)
    (h : MulAction.orbitRel (PeriodGroup A.duplicatedSectionSevenBandParameter)
      ComplexTwoSpace v v') :
    A.regularFixedFiberCover b v = A.regularFixedFiberCover b v' := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  change (g.toAdd : ComplexTwoSpace) + v' = v at hg
  obtain ⟨n, hn⟩ := g.toAdd.2
  change periodVector A.duplicatedSectionSevenBandParameter n =
    (g.toAdd : ComplexTwoSpace) at hn
  have hv : v = periodVector A.duplicatedSectionSevenBandParameter n + v' := by
    rw [hn]
    exact hg.symm
  rw [regularFixedFiberCover, regularFixedFiberCover, hv, A.regularFixedToMoving_period_add]
  congr 1
  apply Quotient.sound
  exact ⟨Multiplicative.ofAdd n, rfl⟩

public def regularFixedFiberPoint
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) : A.CentralFamily :=
  Quotient.liftOn t (A.regularFixedFiberCover b) (A.regularFixedFiberCover_respects b)

public theorem regularFixedFiberPoint_continuous :
    Continuous fun p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter ↦ A.regularFixedFiberPoint p.1 p.2 := by
  have hq : IsOpenQuotientMap
      (Prod.map (id : RegularBase
        (U := A.modular.modularParameter.toTriangleUniformization) → _)
        (Quotient.mk (MulAction.orbitRel
          (PeriodGroup A.duplicatedSectionSevenBandParameter) ComplexTwoSpace))) :=
    IsOpenQuotientMap.id.prodMap
    (MulAction.isOpenQuotientMap_quotientMk
      (Γ := PeriodGroup A.duplicatedSectionSevenBandParameter) (T := ComplexTwoSpace))
  apply hq.isQuotientMap.continuous_iff.mpr
  have hfib : Continuous fun p :
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization) × ComplexTwoSpace ↦
      A.regularFixedToMoving p.1 p.2 :=
    continuous_snd.comp ((fixedToMovingCover_continuous A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
  exact A.centralQuotientProjection_isLocalHomeomorph.continuous.comp
    (continuous_quot_mk.comp (continuous_fst.prodMk hfib))

public def regularFixedFiberMap
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    C(AdditiveTorus A.duplicatedSectionSevenBandParameter, A.CentralFamily) :=
  ⟨A.regularFixedFiberPoint b,
    A.regularFixedFiberPoint_continuous.comp (continuous_const.prodMk continuous_id)⟩

public theorem regularFixedFiberMap_homotopic
    (b c : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    (A.regularFixedFiberMap b).Homotopic (A.regularFixedFiberMap c) := by
  let _ := regularBase_pathConnected A.modular.modularParameter.toTriangleUniformization
  let p := PathConnectedSpace.somePath b c
  exact ⟨{
    toFun := fun q ↦ A.regularFixedFiberPoint (p q.1) q.2
    continuous_toFun := A.regularFixedFiberPoint_continuous.comp
      ((p.continuous.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := fun t ↦ by change A.regularFixedFiberPoint (p 0) t = _; rw [p.source]; rfl
    map_one_left := fun t ↦ by change A.regularFixedFiberPoint (p 1) t = _; rw [p.target]; rfl }⟩

public theorem regularFixedFiberPoint_strip (L : A.AffineStripLift)
    (z : affineVerticalStrip) (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.regularFixedFiberPoint (L.lift z) t = A.stripLiftPoint L z t := rfl

end SphereSixComplex.Geometry.PaperAnalyticData
