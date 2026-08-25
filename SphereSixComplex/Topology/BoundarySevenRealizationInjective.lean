module

public import SphereSixComplex.Topology.BoundarySevenRealization

/-!
# Injectivity of the realized boundary inclusion

This file proves the remaining point-set assertion face by face.  Two points of the realized
boundary are represented by codimension-one faces.  If their ordinary barycentric coordinates
agree, either the faces coincide or both representatives factor through their common
codimension-two face.
-/

@[expose] public section

noncomputable section

open CategoryTheory Set Simplicial

namespace SphereSixComplex

public theorem stdSimplex_map_apply_of_injective
    {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f)
    (w : stdSimplex ℝ (Fin m)) (i : Fin m) :
    stdSimplex.map f w (f i) = w i := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, hf.eq_iff]
  rw [Finset.sum_eq_single i]
  · simp
  · simp

public theorem stdSimplex_map_injective
    {m n : ℕ} (f : Fin m → Fin n) (hf : Function.Injective f) :
    Function.Injective (stdSimplex.map (S := ℝ) f) := by
  intro x y h
  apply stdSimplex.ext
  funext i
  have hi := congrArg (fun w : stdSimplex ℝ (Fin n) ↦ w (f i)) h
  simpa only [stdSimplex_map_apply_of_injective f hf] using hi

public theorem stdSimplex_map_succAbove_apply_self
    {n : ℕ} (i : Fin (n + 2)) (w : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex.map i.succAbove w i = 0 := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2).elim

/-- Removing a zero coordinate gives the unique point of the corresponding affine face. -/
public noncomputable def stdSimplexDeleteZeroCoordinate
    {n : ℕ} (i : Fin (n + 2)) (w : stdSimplex ℝ (Fin (n + 2)))
    (hi : w i = 0) : stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun j ↦ w (i.succAbove j),
    ⟨fun j ↦ w.2.1 _, by
      have hsum := w.2.2
      change (∑ k : Fin (n + 2), w k) = 1 at hsum
      change (∑ j : Fin (n + 1), w (i.succAbove j)) = 1
      rw [Fin.sum_univ_succAbove (fun k ↦ w k) i, hi, zero_add] at hsum
      exact hsum⟩⟩

public theorem stdSimplex_map_deleteZeroCoordinate
    {n : ℕ} (i : Fin (n + 2)) (w : stdSimplex ℝ (Fin (n + 2)))
    (hi : w i = 0) :
    stdSimplex.map i.succAbove (stdSimplexDeleteZeroCoordinate i w hi) = w := by
  apply stdSimplex.ext
  funext k
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i k
  · simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_eq_zero]
    · exact hi.symm
    · intro j hj
      exact (Fin.succAbove_ne k j (Finset.mem_filter.mp hj).2).elim
  · exact stdSimplex_map_apply_of_injective i.succAbove
      Fin.succAbove_right_injective _ j

/-- Each individual realized face embeds in the realized boundary. -/
public theorem boundarySevenRealizedFace_injective (i : Fin 8) :
    Function.Injective (SSet.toTop.map (SSet.boundary.ι.{0} i)) := by
  intro x y h
  apply (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).injective
  apply stdSimplex_map_injective i.succAbove Fin.succAbove_right_injective
  simpa only [boundarySevenRealizationToStdSimplex_face] using
    congrArg (fun z : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ↦
      boundarySevenRealizationToStdSimplex z) h

/-- The two standard parametrizations of a codimension-two face use the same ordered embedding
of its six vertices. -/
public theorem finPairFaceEmbedding_eq
    (i j : Fin 8) (hij : i < j) :
    (fun k : Fin 6 ↦
        i.succAbove ((j.pred (Fin.ne_zero_of_lt hij)).succAbove k)) =
      (fun k : Fin 6 ↦
        j.succAbove ((i.castPred (Fin.ne_last_of_lt hij)).succAbove k)) := by
  funext k
  let ki := j.pred (Fin.ne_zero_of_lt hij)
  let kj := i.castPred (Fin.ne_last_of_lt hij)
  have hkj : Fin.castSucc kj < j := by
    simpa [kj] using hij
  have hcat : SimplexCategory.δ kj ≫ SimplexCategory.δ j =
      SimplexCategory.δ ki ≫ SimplexCategory.δ i := by
    simpa [ki, kj] using SimplexCategory.δ_comp_δ' hkj
  exact congrArg (fun f : SimplexCategory.mk 5 ⟶ SimplexCategory.mk 7 ↦
    f.toOrderHom k) hcat.symm

/-- Representatives lying in two different facets with the same barycentric point are identified
through their common codimension-two simplicial face. -/
public theorem boundarySevenRealizedFaces_eq_of_lt
    (i j : Fin 8) (hij : i < j)
    (x y : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type))
    (hxy : stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) =
      stdSimplex.map j.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y)) :
    SSet.toTop.map (SSet.boundary.ι.{0} i) x =
      SSet.toTop.map (SSet.boundary.ι.{0} j) y := by
  let xi := SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x
  let yj := SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y
  let ki : Fin 7 := j.pred (Fin.ne_zero_of_lt hij)
  let kj : Fin 7 := i.castPred (Fin.ne_last_of_lt hij)
  have hiki : i.succAbove ki = j := by
    exact Fin.succAbove_pred_of_lt i j hij
  have hjkj : j.succAbove kj = i := by
    exact Fin.succAbove_castPred_of_lt j i hij
  have hxi : xi ki = 0 := by
    calc
      xi ki = stdSimplex.map i.succAbove xi (i.succAbove ki) :=
        (stdSimplex_map_apply_of_injective i.succAbove
          Fin.succAbove_right_injective xi ki).symm
      _ = stdSimplex.map j.succAbove yj (i.succAbove ki) :=
        congrArg (fun w : stdSimplex ℝ (Fin 8) ↦ w (i.succAbove ki)) hxy
      _ = stdSimplex.map j.succAbove yj j := by rw [hiki]
      _ = 0 := stdSimplex_map_succAbove_apply_self j yj
  have hyj : yj kj = 0 := by
    calc
      yj kj = stdSimplex.map j.succAbove yj (j.succAbove kj) :=
        (stdSimplex_map_apply_of_injective j.succAbove
          Fin.succAbove_right_injective yj kj).symm
      _ = stdSimplex.map i.succAbove xi (j.succAbove kj) :=
        congrArg (fun w : stdSimplex ℝ (Fin 8) ↦ w (j.succAbove kj)) hxy.symm
      _ = stdSimplex.map i.succAbove xi i := by rw [hjkj]
      _ = 0 := stdSimplex_map_succAbove_apply_self i xi
  let zx := stdSimplexDeleteZeroCoordinate ki xi hxi
  let zy := stdSimplexDeleteZeroCoordinate kj yj hyj
  have hz : zx = zy := by
    apply stdSimplex_map_injective
      (fun k : Fin 6 ↦ i.succAbove (ki.succAbove k))
      (Fin.succAbove_right_injective.comp Fin.succAbove_right_injective)
    calc
      stdSimplex.map (fun k : Fin 6 ↦ i.succAbove (ki.succAbove k)) zx =
          stdSimplex.map i.succAbove (stdSimplex.map ki.succAbove zx) := by
            exact (stdSimplex.map_comp_apply ki.succAbove i.succAbove zx).symm
      _ = stdSimplex.map i.succAbove xi := by
        rw [stdSimplex_map_deleteZeroCoordinate]
      _ = stdSimplex.map j.succAbove yj := hxy
      _ = stdSimplex.map j.succAbove (stdSimplex.map kj.succAbove zy) := by
        rw [stdSimplex_map_deleteZeroCoordinate]
      _ = stdSimplex.map (fun k : Fin 6 ↦ j.succAbove (kj.succAbove k)) zy := by
        exact stdSimplex.map_comp_apply kj.succAbove j.succAbove zy
      _ = stdSimplex.map (fun k : Fin 6 ↦ i.succAbove (ki.succAbove k)) zy := by
        rw [finPairFaceEmbedding_eq i j hij]
  let z : (SSet.toTop.obj (Δ[5] : SSet.{0}) : Type) :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 5)).symm zx
  have hx : SSet.toTop.map (SSet.stdSimplex.δ ki) z = x := by
    apply (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).injective
    calc
      SimplexCategory.toTopHomeo (SimplexCategory.mk 6)
          (SSet.toTop.map (SSet.stdSimplex.δ ki) z) =
          stdSimplex.map ki.succAbove
            (SimplexCategory.toTopHomeo (SimplexCategory.mk 5) z) :=
        SimplexCategory.toTopHomeo_naturality_apply
          (SimplexCategory.δ ki) z
      _ = stdSimplex.map ki.succAbove zx := by
        rw [show SimplexCategory.toTopHomeo (SimplexCategory.mk 5) z = zx by
          simp [z]]
      _ = xi := stdSimplex_map_deleteZeroCoordinate ki xi hxi
      _ = SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x := rfl
  have hy : SSet.toTop.map (SSet.stdSimplex.δ kj) z = y := by
    apply (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).injective
    calc
      SimplexCategory.toTopHomeo (SimplexCategory.mk 6)
          (SSet.toTop.map (SSet.stdSimplex.δ kj) z) =
          stdSimplex.map kj.succAbove
            (SimplexCategory.toTopHomeo (SimplexCategory.mk 5) z) :=
        SimplexCategory.toTopHomeo_naturality_apply
          (SimplexCategory.δ kj) z
      _ = stdSimplex.map kj.succAbove zx := by
        rw [show SimplexCategory.toTopHomeo (SimplexCategory.mk 5) z = zx by
          simp [z]]
      _ = stdSimplex.map kj.succAbove zy := by rw [hz]
      _ = yj := stdSimplex_map_deleteZeroCoordinate kj yj hyj
      _ = SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y := rfl
  have hfaces : SSet.stdSimplex.δ ki ≫ SSet.boundary.ι.{0} i =
      SSet.stdSimplex.δ kj ≫ SSet.boundary.ι.{0} j := by
    rw [← cancel_mono (SSet.boundary 7).ι]
    simp only [Category.assoc, SSet.boundary.ι_ι]
    let hpair := SSet.stdSimplex.facePairComplIso_hom_ι
      (n := 5) i j hij
    let hpair' := SSet.stdSimplex.facePairComplIso_hom_ι'
      (n := 5) i j hij
    simpa [ki, kj] using hpair'.symm.trans hpair
  rw [← hx, ← hy]
  change (SSet.toTop.map (SSet.stdSimplex.δ ki) ≫
      SSet.toTop.map (SSet.boundary.ι.{0} i)) z =
    (SSet.toTop.map (SSet.stdSimplex.δ kj) ≫
      SSet.toTop.map (SSet.boundary.ι.{0} j)) z
  rw [← Functor.map_comp, ← Functor.map_comp, hfaces]

/-- The canonical map from realization of the simplicial boundary to the ordinary barycentric
boundary is injective.  Equal barycentric points either lie in the same standard facet or factor
through the common codimension-two face of two distinct facets. -/
public theorem boundarySevenRealizationToBoundary_injective :
    Function.Injective boundarySevenRealizationToBoundary := by
  intro x y hxy
  obtain ⟨i, xi, hxi⟩ := boundarySevenRealization_standardFaceCovered x
  obtain ⟨j, yj, hyj⟩ := boundarySevenRealization_standardFaceCovered y
  rw [← hxi, ← hyj]
  have hcoord : stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) xi) =
      stdSimplex.map j.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) yj) := by
    have hv := congrArg Subtype.val hxy
    rw [← hxi, ← hyj] at hv
    simpa only [boundarySevenRealizationToBoundary_val,
      boundarySevenRealizationToStdSimplex_face] using hv
  rcases lt_trichotomy i j with hij | hij | hij
  · exact boundarySevenRealizedFaces_eq_of_lt i j hij xi yj hcoord
  · subst j
    have hface : xi = yj := by
      apply (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).injective
      apply stdSimplex_map_injective i.succAbove Fin.succAbove_right_injective
      exact hcoord
    subst yj
    rfl
  · exact (boundarySevenRealizedFaces_eq_of_lt j i hij yj xi hcoord.symm).symm

/-- The geometric realization of the boundary of the seven-simplex is homeomorphic to the
project's standard six-sphere. -/
public theorem boundarySevenRealizationHomeomorphSixSphere :
    BoundarySevenRealizationHomeomorphSixSphere :=
  boundarySevenRealizationHomeomorphSixSphere_of_injective
    boundarySevenRealizationToBoundary_injective

/-- Consequently the boundary comparison package now requires only the chain-level
simplicial-to-singular quasi-isomorphism. -/
public theorem boundarySevenComparisonInputs_of_quasiIsomorphism
    (R : AddCommGrpCat)
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) R) :
    BoundarySevenComparisonInputs R :=
  ⟨hcomparison, boundarySevenRealizationHomeomorphSixSphere⟩

end SphereSixComplex
