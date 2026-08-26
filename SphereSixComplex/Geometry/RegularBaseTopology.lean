module

public import SphereSixComplex.Geometry.GlobalDeckQuotient
public import Mathlib.Topology.LocallyFinite
import all SphereSixComplex.Geometry.GlobalDeckQuotient
import all SphereSixComplex.Geometry.GlobalTorusFamily

/-!
# Topology of the regular Fuchsian base

Proper discontinuity makes each source orbit locally finite and closed.  Hence deleting the two
elliptic orbits gives an open complex submanifold, the correct base for the paper's unfilled global
torus family.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.GlobalTorusFamily

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus

noncomputable section

variable {U : TriangleUniformization}

/-- The orbit of a point under the source action. -/
@[expose] public def sourceOrbitSet (p : UpperHalfPlane) : Set UpperHalfPlane :=
  ⋃ g : Delta, {U.sourceAction g • p}

/-- Proper discontinuity makes the family of singleton translates locally finite. -/
public theorem sourceOrbitSingletons_locallyFinite
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (p : UpperHalfPlane) :
    LocallyFinite (fun g : Delta ↦ ({U.sourceAction g • p} : Set UpperHalfPlane)) := by
  unfold SourceActionProperlyDiscontinuous at hproper
  intro z
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds z
  refine ⟨K, hKnhds, ?_⟩
  simpa only [Set.image_singleton] using hproper isCompact_singleton hKcompact

/-- Every source orbit is closed. -/
public theorem sourceOrbitSet_isClosed
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (p : UpperHalfPlane) :
    IsClosed (sourceOrbitSet (U := U) p) :=
  (sourceOrbitSingletons_locallyFinite hproper p).isClosed_iUnion
    (fun _ ↦ isClosed_singleton)

private theorem smul_eq_iff_eq_inv_smul (g : Delta) (z p : UpperHalfPlane) :
    U.sourceAction g • z = p ↔ z = U.sourceAction g⁻¹ • p := by
  constructor
  · intro h
    calc
      z = U.sourceAction g⁻¹ • (U.sourceAction g • z) := by
        rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ = U.sourceAction g⁻¹ • p := congrArg _ h
  · intro h
    calc
      U.sourceAction g • z =
          U.sourceAction g • (U.sourceAction g⁻¹ • p) := congrArg _ h
      _ = p := by rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

public theorem isRegularBasePoint_iff_not_mem_orbits (z : UpperHalfPlane) :
    IsRegularBasePoint (U := U) z ↔
      z ∉ sourceOrbitSet (U := U) U.zOne ∪ sourceOrbitSet (U := U) U.zTwo := by
  constructor
  · intro hz hmem
    unfold IsRegularBasePoint at hz
    rcases hmem with hmem | hmem
    · simp only [sourceOrbitSet, mem_iUnion, mem_singleton_iff] at hmem
      obtain ⟨g, hg⟩ := hmem
      exact (hz g⁻¹).1 ((smul_eq_iff_eq_inv_smul g⁻¹ z U.zOne).2 (by
        simpa only [inv_inv] using hg))
    · simp only [sourceOrbitSet, mem_iUnion, mem_singleton_iff] at hmem
      obtain ⟨g, hg⟩ := hmem
      exact (hz g⁻¹).2 ((smul_eq_iff_eq_inv_smul g⁻¹ z U.zTwo).2 (by
        simpa only [inv_inv] using hg))
  · intro hz
    unfold IsRegularBasePoint
    intro g
    constructor
    · intro hg
      apply hz
      left
      simp only [sourceOrbitSet, mem_iUnion, mem_singleton_iff]
      exact ⟨g⁻¹, (smul_eq_iff_eq_inv_smul g z U.zOne).1 hg⟩
    · intro hg
      apply hz
      right
      simp only [sourceOrbitSet, mem_iUnion, mem_singleton_iff]
      exact ⟨g⁻¹, (smul_eq_iff_eq_inv_smul g z U.zTwo).1 hg⟩

/-- The regular source locus is open. -/
public theorem isOpen_isRegularBasePoint
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    IsOpen {z : UpperHalfPlane | IsRegularBasePoint (U := U) z} := by
  have hc : IsClosed
      (sourceOrbitSet (U := U) U.zOne ∪ sourceOrbitSet (U := U) U.zTwo) :=
    (sourceOrbitSet_isClosed hproper U.zOne).union
      (sourceOrbitSet_isClosed hproper U.zTwo)
  rw [show {z : UpperHalfPlane | IsRegularBasePoint (U := U) z} =
      (sourceOrbitSet (U := U) U.zOne ∪ sourceOrbitSet (U := U) U.zTwo)ᶜ by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact isRegularBasePoint_iff_not_mem_orbits z]
  exact hc.isOpen_compl

/-- The regular source locus as an open subset of the upper half-plane. -/
@[expose] public noncomputable def regularBaseOpen
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    TopologicalSpace.Opens UpperHalfPlane :=
  ⟨{z | IsRegularBasePoint (U := U) z}, isOpen_isRegularBasePoint hproper⟩

/-- The complex atlas inherited by the regular source locus. -/
@[expose, instance_reducible] public noncomputable def regularBaseChartedSpace
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    ChartedSpace ℂ (RegularBase (U := U)) := by
  change ChartedSpace ℂ (regularBaseOpen hproper)
  infer_instance

/-- The regular source locus is a complex one-manifold. -/
public theorem regularBase_isManifold
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularBaseChartedSpace hproper
    IsManifold (modelWithCornersSelf ℂ ℂ) ∞ (RegularBase (U := U)) := by
  let _ := regularBaseChartedSpace hproper
  change IsManifold (modelWithCornersSelf ℂ ℂ) ∞ (regularBaseOpen hproper)
  infer_instance

/-- Every lifted deck transformation restricts to a complex-smooth map on the regular vector
bundle cover. -/
public theorem regularDeckMap_contMDiff
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U))
    (g : Delta) :
    letI := regularBaseChartedSpace hproper
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞ (regularDeckMap F g) := by
  let _ := regularBaseChartedSpace hproper
  have hval : ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel ∞
      (fun z : RegularBase (U := U) ↦ z.1) := by
    change ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel ∞
      (Subtype.val : regularBaseOpen hproper → UpperHalfPlane)
    exact contMDiff_subtype_val
  have hinclude : ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (fun p : RegularBase (U := U) × ComplexTwoSpace ↦ (p.1.1, p.2)) :=
    (hval.comp contMDiff_fst).prodMk contMDiff_snd
  have hfull : ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (deckMap F g ∘ fun p : RegularBase (U := U) × ComplexTwoSpace ↦ (p.1.1, p.2)) :=
    (deckMap_contMDiff F g ∞).comp hinclude
  have hbaseVal : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel ∞
      (fun p : RegularBase (U := U) × ComplexTwoSpace ↦
        (regularSourceEquiv g p.1).1) := by
    exact (U.sourceAction_contMDiff g ∞).comp
      (hval.comp contMDiff_fst)
  have hbase : ContMDiff GlobalDeckTotalModel GlobalDeckBaseModel ∞
      (fun p : RegularBase (U := U) × ComplexTwoSpace ↦ regularSourceEquiv g p.1) := by
    apply (ContMDiff.subtypeVal_comp_iff (regularBaseOpen hproper) _).mp
    convert hbaseVal using 1
    rfl
  have hfiber : ContMDiff GlobalDeckTotalModel GlobalDeckFiberModel ∞
      (fun p : RegularBase (U := U) × ComplexTwoSpace ↦
        periodTransport g (regularParameterMap F p.1) p.2) := by
    have hsnd := contMDiff_snd.comp hfull
    convert hsnd using 1
    rfl
  exact hbase.prodMk hfiber

/-- Every regular deck transformation is continuous on the vector-bundle cover.  This
topological form is convenient when transporting explicit paths by a named deck element. -/
public theorem regularDeckMap_continuous
    (F : PeriodFunctions U) (hproper : SourceActionProperlyDiscontinuous (U := U))
    (g : Delta) :
    Continuous (regularDeckMap F g) := by
  let _ := regularBaseChartedSpace hproper
  exact (regularDeckMap_contMDiff F hproper g).continuous

end

end SphereSixComplex.Geometry.GlobalTorusFamily
