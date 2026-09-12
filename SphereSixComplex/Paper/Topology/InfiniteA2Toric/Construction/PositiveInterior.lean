module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.PositiveOffCentral

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction
open SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions

public theorem continuous_torusCoordinates_of_height_ne_zero
    {X : Type*} [TopologicalSpace X] (M : Model) (f : X → M.Carrier)
    (hf : Continuous f) (ht : ∀ x, M.t (f x) ≠ 0) :
    Continuous (fun x ↦ torusCoordinates M (f x)) := by
  apply M.torus_openEmbedding.isEmbedding.continuous_iff.mpr
  convert hf using 1 <;> first | rfl | exact funext (fun x ↦ torusEmbedding_torusCoordinates M (ht x))
namespace Construction


public def positiveInteriorRegion (r : ℝ) : Set (Fin 3 → ℝ) :=
  {x | 0 < x 2 ∧ x 2 < r}

public def positiveInteriorCoordinate {r : ℝ}
    (q : positiveOffCentral r) : positiveInteriorRegion r :=
  ⟨offCentralMomentCoordinate q.1,
    norm_pos_iff.mpr q.2, mem_ball_zero_iff.mp q.1.1.2⟩

public def positiveInteriorInverse {r : ℝ}
    (x : positiveInteriorRegion r) : positiveOffCentral r :=
  ⟨offCentralMomentInverse ⟨x.1, x.2.1.le, x.2.2⟩ x.2.1, by
    change constructedModel.t _ ≠ 0
    rw [offCentralMomentInverse_t]
    exact_mod_cast x.2.1.ne'⟩

public theorem continuous_positiveInteriorCoordinate {r : ℝ} (hr : r < 1) :
    Continuous (positiveInteriorCoordinate (r := r)) := by
  have hf : Continuous (fun q : positiveOffCentral r ↦
      (q.1.1.1 : Carrier)) := by fun_prop
  have hg := continuous_torusCoordinates_of_height_ne_zero constructedModel _ hf
    (fun q : positiveOffCentral r ↦ q.2)
  have ht := constructedModel.t_holomorphic.continuous.comp hf
  have hd : Continuous (fun q : positiveOffCentral r ↦
      Real.log ‖constructedModel.t q.1.1.1‖) :=
    ht.norm.log (fun q ↦ (norm_pos_iff.mpr q.2).ne')
  have hdne (q : positiveOffCentral r) :
      Real.log ‖constructedModel.t q.1.1.1‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.mpr q.2)
      (ne_of_lt ((mem_ball_zero_iff.mp q.1.1.2).trans hr))
  have hgi (i : Fin 3) : Continuous (fun q : positiveOffCentral r ↦
      ((torusCoordinates constructedModel q.1.1.1 i : ℂˣ) : ℂ)) := by
    exact Units.continuous_val.comp ((continuous_apply i).comp hg)
  have hlog (i : Fin 3) : Continuous (fun q : positiveOffCentral r ↦
      Real.log ‖((torusCoordinates constructedModel q.1.1.1 i : ℂˣ) : ℂ)‖) :=
    (hgi i).norm.log (fun q ↦ (Units.norm_pos (torusCoordinates constructedModel q.1.1.1 i)).ne')
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · exact (hlog 0).div hd hdne
  · exact (hlog 1).div hd hdne
  · exact ht.norm

public theorem continuous_positiveInteriorInverse (r : ℝ) :
    Continuous (positiveInteriorInverse (r := r)) := by
  have hc (i : Fin 3) : Continuous (fun x : positiveInteriorRegion r ↦ x.1 i) := by
    exact (continuous_apply i).comp continuous_subtype_val
  have hu {X : Type} [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f)
      (hp : ∀ x, 0 < f x) :
      Continuous (fun x ↦ constructedA2PositiveRealUnit (f x) (hp x)) := by
    rw [Units.continuous_iff]
    refine ⟨Complex.continuous_ofReal.comp hf, ?_⟩
    change Continuous (fun x ↦ ((f x : ℂ))⁻¹)
    exact (Complex.continuous_ofReal.comp hf).inv₀ (fun x ↦ by
      change (f x : ℂ) ≠ 0
      exact_mod_cast (hp x).ne')
  have hg : Continuous (fun x : positiveInteriorRegion r ↦
      momentTorusPoint x.1 x.2.1) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hu _ ((hc 2).rpow (hc 0) (fun x ↦ Or.inl x.2.1.ne'))
        (fun x ↦ Real.rpow_pos_of_pos x.2.1 _)
    · exact hu _ ((hc 2).rpow (hc 1) (fun x ↦ Or.inl x.2.1.ne'))
        (fun x ↦ Real.rpow_pos_of_pos x.2.1 _)
    · exact hu _ (hc 2) (fun x ↦ x.2.1)
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact constructedModel.torus_openEmbedding.continuous.comp hg

public def positiveInteriorHomeomorph {r : ℝ} (hr : r < 1) :
    positiveOffCentral r ≃ₜ positiveInteriorRegion r where
  toFun := positiveInteriorCoordinate
  invFun := positiveInteriorInverse
  left_inv q := by
    apply Subtype.ext
    exact offCentralMomentInverse_coordinate hr q.1 q.2
  right_inv x := by
    apply Subtype.ext
    exact offCentralMomentCoordinate_inverse hr
      ⟨x.1, x.2.1.le, x.2.2⟩ x.2.1
  continuous_toFun := continuous_positiveInteriorCoordinate hr
  continuous_invFun := continuous_positiveInteriorInverse r

public theorem positiveInteriorRegion_convex (r : ℝ) :
    Convex ℝ (positiveInteriorRegion r) := by
  have hl : IsLinearMap ℝ (fun x : Fin 3 → ℝ ↦ x 2) :=
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  exact (convex_halfSpace_gt hl 0).inter (convex_halfSpace_lt hl r)

public theorem positiveOffCentral_contractible {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) : ContractibleSpace (positiveOffCentral r) := by
  have hn : (positiveInteriorRegion r).Nonempty :=
    ⟨fun _ ↦ r / 2, by constructor <;> linarith⟩
  let _ := (positiveInteriorRegion_convex r).contractibleSpace hn
  exact (positiveInteriorHomeomorph hr1).contractibleSpace

end Construction

end SphereSixComplex.Geometry.InfiniteA2Toric
