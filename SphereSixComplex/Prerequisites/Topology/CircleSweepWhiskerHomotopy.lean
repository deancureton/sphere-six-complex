module
public import SphereSixComplex.Prerequisites.Topology.MappingTorusTwoSliceBoundary
public import Mathlib.Topology.Subpath

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex

public def whiskerLoopFreeHomotopy {X : Type} [TopologicalSpace X]
    {a b : X} (p : Path a b) (q : Path b b) :
    (p.trans (q.trans p.symm)).toContinuousMap.Homotopy
      ((Path.refl b).trans (q.trans (Path.refl b))).toContinuousMap where
  toFun z := ((p.subpath z.1 1).trans
    ((q.cast p.target p.target).trans (p.subpath z.1 1).symm)) z.2
  continuous_toFun := by
    have hp : Continuous (fun z : unitInterval × unitInterval ↦ p.subpath z.1 1 z.2) :=
      p.subpath_continuous_family.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    have hps : Continuous (fun z : unitInterval × unitInterval ↦
        (p.subpath z.1 1).symm z.2) :=
      hp.comp (continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd))
    have hin : Continuous (fun z : unitInterval × unitInterval ↦
        ((q.cast p.target p.target).trans (p.subpath z.1 1).symm) z.2) :=
      Path.trans_continuous_family (fun _ ↦ q.cast p.target p.target)
        (q.continuous.comp continuous_snd) (fun s ↦ (p.subpath s 1).symm) hps
    exact Path.trans_continuous_family (fun s ↦ p.subpath s 1) hp
      (fun s ↦ (q.cast p.target p.target).trans (p.subpath s 1).symm) hin
  map_zero_left t := by
    change ((p.subpath 0 1).trans
      ((q.cast p.target p.target).trans (p.subpath 0 1).symm)) t = _
    rw [Path.subpath_zero_one]
    rfl
  map_one_left t := by
    change ((p.subpath 1 1).trans
      ((q.cast p.target p.target).trans (p.subpath 1 1).symm)) t = _
    rw [Path.subpath_self]
    simp only [Path.trans_apply, Path.symm_apply, Path.refl_apply,
      Path.cast_coe, p.target, Path.coe_toContinuousMap, Function.comp_apply]

public theorem whiskerLoopFreeHomotopy_closed {X : Type} [TopologicalSpace X]
    {a b : X} (p : Path a b) (q : Path b b) (t : unitInterval) :
    whiskerLoopFreeHomotopy p q (t, 0) = whiskerLoopFreeHomotopy p q (t, 1) := by
  change ((p.subpath t 1).trans
      ((q.cast p.target p.target).trans (p.subpath t 1).symm)) 0 =
    ((p.subpath t 1).trans
      ((q.cast p.target p.target).trans (p.subpath t 1).symm)) 1
  rw [Path.source, Path.target]

public def identityMappingTorusMapOfLoop_whiskerHomotopy
    {F X : Type} [TopologicalSpace F] [LocallyCompactSpace F] [TopologicalSpace X]
    {a b : C(F, X)} (p : Path a b) (q : Path b b) :
    (identityMappingTorusMapOfLoop (p.trans (q.trans p.symm))).Homotopy
      (identityMappingTorusMapOfLoop q) := by
  refine (identityMappingTorusMapOfLoop_freeHomotopy (whiskerLoopFreeHomotopy p q)
    (whiskerLoopFreeHomotopy_closed p q)).trans ?_
  apply identityMappingTorusMapOfLoop_homotopy
  apply Nonempty.some
  apply Path.Homotopic.Quotient.exact
  simp

end SphereSixComplex
end
end
