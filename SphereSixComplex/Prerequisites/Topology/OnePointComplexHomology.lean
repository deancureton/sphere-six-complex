module

public import SphereSixComplex.Prerequisites.Topology.IntegralMayerVietorisTheorem
public import SphereSixComplex.Prerequisites.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section
noncomputable section

open Set Metric Topology
namespace SphereSixComplex.IntegralMayerVietoris
variable {X : Type} [TopologicalSpace X] (A B : Set X)
theorem subsingleton_homologyOne_union_of_subsingleton
    (h : ExactSequence A B)
    [Subsingleton (IntegralSingularHomology 1 A)]
    [Subsingleton (IntegralSingularHomology 1 B)]
    [PathConnectedSpace (A ∩ B : Set X)] :
    Subsingleton (IntegralSingularHomology 1 (A ∪ B : Set X)) := by
  obtain ⟨boundary, he⟩ := h
  have hz (x : IntegralSingularHomology 1 (A ∪ B : Set X)) : x = 0 := by
    have hb : boundary 0 x = 0 := by
      apply differenceMap_zero_injective A B
      rw [map_zero]
      exact ((he 0).2.1 (boundary 0 x)).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := ((he 0).1 x).mp hb
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

theorem subsingleton_homologyOne_union
    (hA : IsOpen A) (hB : IsOpen B)
    [ContractibleSpace A] [ContractibleSpace B]
    [PathConnectedSpace (A ∩ B : Set X)] :
    Subsingleton (IntegralSingularHomology 1 (A ∪ B : Set X)) := by
  let _ := subsingleton_integralSingularHomology_of_contractible (X := A) 1 one_ne_zero
  let _ := subsingleton_integralSingularHomology_of_contractible (X := B) 1 one_ne_zero
  exact subsingleton_homologyOne_union_of_subsingleton A B
    (exact_sequence_of_isOpen A B hA hB)

end SphereSixComplex.IntegralMayerVietoris
namespace SphereSixComplex
private abbrev SphereTwo := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private def sphereTwoChart (v : SphereTwo) :
    ({v}ᶜ : Set SphereTwo) ≃ₜ EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact ((Homeomorph.setCongr (by simp : ({v}ᶜ : Set SphereTwo) =
    (stereographic' 2 v).source)).trans
    (stereographic' 2 v).toHomeomorphSourceTarget).trans
    ((Homeomorph.setCongr (by simp)).trans (Homeomorph.Set.univ _))

private theorem sphereTwo_inter_pathConnected (v w : SphereTwo) (hvw : w ≠ v) :
    PathConnectedSpace (({v}ᶜ ∩ {w}ᶜ : Set SphereTwo)) := by
  let e := sphereTwoChart v
  let w' : ({v}ᶜ : Set SphereTwo) := ⟨w, hvw⟩
  have hc : IsPathConnected ({e w'}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by rw [← Module.finrank_eq_rank]; norm_num) _
  have himage : (fun x ↦ (e.symm x).val) '' ({e w'}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) =
      ({v}ᶜ ∩ {w}ᶜ : Set SphereTwo) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).property, ?_⟩
      intro heq
      apply hy
      have heq' : e.symm y = w' := Subtype.ext heq
      exact e.symm.injective (by simpa using heq')
    · intro hx
      refine ⟨e ⟨x, hx.1⟩, ?_, by simp⟩
      intro heq
      exact hx.2 (congrArg Subtype.val (e.injective heq))
  rw [← isPathConnected_iff_pathConnectedSpace, ← himage]
  exact hc.image (continuous_subtype_val.comp e.symm.continuous)
private theorem sphereTwo_homologyOne_subsingleton (v w : SphereTwo) (hvw : w ≠ v) :
    Subsingleton (IntegralSingularHomology 1 SphereTwo) := by
  let A : Set SphereTwo := {v}ᶜ
  let B : Set SphereTwo := {w}ᶜ
  let : ContractibleSpace A := (sphereTwoChart v).contractibleSpace
  let : ContractibleSpace B := (sphereTwoChart w).contractibleSpace
  let : PathConnectedSpace (A ∩ B : Set SphereTwo) :=
    sphereTwo_inter_pathConnected v w hvw
  let := IntegralMayerVietoris.subsingleton_homologyOne_union A B
    (isClosed_singleton.isOpen_compl) (isClosed_singleton.isOpen_compl)
  have hcover : A ∪ B = Set.univ := by
    ext x
    simp only [A, B, mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
    by_cases hx : x = v
    · exact Or.inr (by intro hw; exact hvw (hw.symm.trans hx))
    · exact Or.inl hx
  let e : (A ∪ B : Set SphereTwo) ≃ₜ SphereTwo :=
    (Homeomorph.setCongr hcover).trans (Homeomorph.Set.univ _)
  exact (integralSingularHomologyEquiv 1 e).symm.injective.subsingleton

theorem onePointComplex_homologyOne_subsingleton :
    Subsingleton (IntegralSingularHomology 1 (OnePoint ℂ)) := by
  let e : OnePoint ℂ ≃ₜ SphereTwo :=
    onePointEquivSphereOfFinrankEq (by simp)
  let v : SphereTwo := e (0 : ℂ)
  let w : SphereTwo := e OnePoint.infty
  have hwv : w ≠ v := by
    intro h
    have := e.injective h
    exact OnePoint.infty_ne_coe _ this
  let := sphereTwo_homologyOne_subsingleton v w hwv
  exact (integralSingularHomologyEquiv 1 e).injective.subsingleton

end SphereSixComplex
