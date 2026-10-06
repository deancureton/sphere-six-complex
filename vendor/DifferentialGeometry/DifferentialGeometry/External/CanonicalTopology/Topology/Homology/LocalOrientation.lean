module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Manifold.TangentOrientation
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalDerivativeComparison
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCompactHomology
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section

noncomputable section

open Set Bundle
open scoped Manifold Topology

universe u v w

namespace DifferentialGeometry.Topology

private theorem det_pos_of_orientations_agree
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (A B : F ≃ₗ[ℝ] E) (o : Orientation ℝ F (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (hA : Orientation.map _ A o = ω)
    (hB : Orientation.map _ B o = ω) :
    0 < LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E) := by
  have hinv : Orientation.map _ A.symm ω = o := by
    rw [← hA]
    exact (Orientation.map _ A).symm_apply_apply o
  apply (Orientation.map_eq_iff_det_pos ω (A.symm.trans B) (by simp)).mp
  rw [DifferentialGeometry.orientation_map_trans, hinv, hB]

private theorem tangent_trivialization_transition_eq_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (x y p : M) (hx : p ∈ (chartAt E x).source) (hy : p ∈ (chartAt E y).source) :
    (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm.trans
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)) : E →L[ℝ] E) =
      fderiv ℝ ((chartAt E y) ∘ (chartAt E x).symm) (chartAt E x p) := by
  have hcomp :
      (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm.trans
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)) : E →L[ℝ] E) =
        tangentCoordChange 𝓘(ℝ, E) x y p := by
    change ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hy) :
        TangentSpace 𝓘(ℝ, E) p →L[ℝ] E).comp
        (((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).symm :
          E →L[ℝ] TangentSpace 𝓘(ℝ, E) p) = _
    rw [Trivialization.coe_continuousLinearEquivAt_eq', Trivialization.symm_continuousLinearEquivAt_eq',
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy,
      TangentBundle.symmL_trivializationAt_eq_core hx]
    apply ContinuousLinearMap.ext
    intro z
    exact tangentCoordChange_comp (I := 𝓘(ℝ, E)) (w := x) (x := p) (y := y) (z := p)
      ⟨⟨by simpa only [extChartAt_source] using hx, mem_extChartAt_source p⟩,
        by simpa only [extChartAt_source] using hy⟩
  simpa only [tangentCoordChange_def, mfld_simps, fderivWithin_univ] using hcomp

theorem integralLocalHomology_chart_maps_eq_det_sign
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (x y p : M) (hx : p ∈ (chartAt E x).source) (hy : p ∈ (chartAt E y).source) :
    (SignType.sign (LinearMap.det
      (fderiv ℝ ((chartAt E y) ∘ (chartAt E x).symm) (chartAt E x p)).toLinearMap) : ℤ) •
      (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E x p)))
        (show MapsTo (Homeomorph.subRight (chartAt E x p))
          ({chartAt E x p}ᶜ : Set E) ({0}ᶜ : Set E) from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E x) p hx).hom.hom =
      (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E y p)))
        (show MapsTo (Homeomorph.subRight (chartAt E y p))
          ({chartAt E y p}ᶜ : Set E) ({0}ᶜ : Set E) from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E y) p hy).hom.hom := by
  let n := Module.finrank ℝ E
  let e := chartAt E x
  let f := chartAt E y
  let g := e.symm.trans f
  let c : ℤ := SignType.sign (LinearMap.det (fderiv ℝ g (e p)).toLinearMap)
  have hga : e p ∈ g.source := by
    change e p ∈ e.target ∧ e.symm (e p) ∈ f.source
    exact ⟨e.map_source hx, by rwa [e.left_inv hx]⟩
  have hgp : g (e p) = f p := by
    change f (e.symm (e p)) = f p
    rw [e.left_inv hx]
  have hd : HasFDerivAt g (tangentCoordChange 𝓘(ℝ, E) x y p) (e p) := by
    change HasFDerivAt ((chartAt E y) ∘ (chartAt E x).symm)
      (tangentCoordChange 𝓘(ℝ, E) x y p) (chartAt E x p)
    simpa only [mfld_simps, hasFDerivWithinAt_univ] using
      (hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, E)) (x := x) (y := y) (z := p)
        ⟨by simpa only [extChartAt_source] using hx,
          by simpa only [extChartAt_source] using hy⟩)
  have hd' : HasFDerivAt g.symm (tangentCoordChange 𝓘(ℝ, E) y x p) (g (e p)) := by
    rw [hgp]
    change HasFDerivAt ((chartAt E x) ∘ (chartAt E y).symm)
      (tangentCoordChange 𝓘(ℝ, E) y x p) (chartAt E y p)
    simpa only [mfld_simps, hasFDerivWithinAt_univ] using
      (hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, E)) (x := y) (y := x) (z := p)
        ⟨by simpa only [extChartAt_source] using hy,
          by simpa only [extChartAt_source] using hx⟩)
  have hsign := integralLocalHomologyOpenPartialHomeomorphIso_translation_eq_det_sign
    g (e p) hga hd.differentiableAt hd'.differentiableAt
  let U := e.source ∩ f.source
  have hU : IsOpen U := e.open_source.inter f.open_source
  have hpU : p ∈ U := ⟨hx, hy⟩
  have hUe : U ⊆ e.source := fun _ hz => hz.1
  have hUf : U ⊆ f.source := fun _ hz => hz.2
  let J := integralLocalHomologyNeighborhoodIso n p U hU hpU
  let Jg := integralLocalHomologyNeighborhoodIso n (e p) g.source g.open_source hga
  let Ie := integralLocalHomologyOpenPartialHomeomorphIso n e p hx
  let If := integralLocalHomologyOpenPartialHomeomorphIso n f p hy
  let Ig := integralLocalHomologyOpenPartialHomeomorphIso n g (e p) hga
  have hUeg : MapsTo e U g.source := by
    intro z hz
    change e z ∈ e.target ∧ e.symm (e z) ∈ f.source
    refine ⟨e.map_source hz.1, ?_⟩
    rw [e.left_inv hz.1]
    exact hz.2
  let q : C(U, g.source) :=
    ⟨fun z => ⟨e z, hUeg z.property⟩,
      ((e.continuousOn.mono hUe).domRestrict).subtype_mk _⟩
  have hq : MapsTo q ({(⟨p, hpU⟩ : U)}ᶜ : Set U)
      ({(⟨e p, hga⟩ : g.source)}ᶜ : Set g.source) := by
    intro z hz heq
    apply hz
    apply Subtype.ext
    apply e.injOn z.property.1 hx
    exact congrArg (fun w : g.source => (w : E)) heq
  let F : C(U, E) := ⟨fun z => f z, (f.continuousOn.mono hUf).domRestrict⟩
  have hF : MapsTo F ({(⟨p, hpU⟩ : U)}ᶜ : Set U) ({f p}ᶜ : Set E) :=
    fun z hz heq => hz (Subtype.ext (f.injOn z.property.2 hy heq))
  let G : C(g.source, E) := ⟨fun z => g z, g.continuousOn.domRestrict⟩
  have hG : MapsTo G ({(⟨e p, hga⟩ : g.source)}ᶜ : Set g.source)
      ({g (e p)}ᶜ : Set E) :=
    fun z hz heq => hz (Subtype.ext (g.injOn z.property hga heq))
  let Te := toContinuousMap (Homeomorph.subRight (e p))
  let Tf := toContinuousMap (Homeomorph.subRight (f p))
  let Tg := toContinuousMap (Homeomorph.subRight (g (e p)))
  have hTe : MapsTo Te ({e p}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hz => sub_ne_zero.mpr hz
  have hTf : MapsTo Tf ({f p}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hz => sub_ne_zero.mpr hz
  have hTg : MapsTo Tg ({g (e p)}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hz => sub_ne_zero.mpr hz
  change (integralRelativeHomologyMap n Tg hTg).comp Ig.hom.hom =
    c • integralRelativeHomologyMap n Te hTe at hsign
  have heJ : Ie.hom.hom.comp J.hom.hom =
      Jg.hom.hom.comp (integralRelativeHomologyMap n q hq) := by
    rw [integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood n e p U hU hpU hUe]
    change integralRelativeHomologyMap n _ _ =
      (integralRelativeHomologyMap n _ _).comp (integralRelativeHomologyMap n _ _)
    rw [← integralRelativeHomologyMap_comp]
    rfl
  have hfJ : If.hom.hom.comp J.hom.hom = integralRelativeHomologyMap n F hF :=
    integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood n f p U hU hpU hUf
  have hgJ : Ig.hom.hom.comp Jg.hom.hom = integralRelativeHomologyMap n G hG :=
    integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
      n g (e p) g.source g.open_source hga Subset.rfl
  have hmiddle : Ig.hom.hom.comp (Jg.hom.hom.comp (integralRelativeHomologyMap n q hq)) =
      (integralRelativeHomologyMap n G hG).comp (integralRelativeHomologyMap n q hq) := by
    rw [← LinearMap.comp_assoc, hgJ]
  have hmaps : Tg.comp (G.comp q) = Tf.comp F := by
    ext z
    change f (e.symm (e z)) - f (e.symm (e p)) = f z - f p
    rw [e.left_inv z.property.1, e.left_inv hx]
  let L := c • (integralRelativeHomologyMap n Te hTe).comp Ie.hom.hom
  let R := (integralRelativeHomologyMap n Tf hTf).comp If.hom.hom
  have hcomp : L.comp J.hom.hom = R.comp J.hom.hom := by
    calc
      L.comp J.hom.hom = (c • integralRelativeHomologyMap n Te hTe).comp
          (Ie.hom.hom.comp J.hom.hom) := by
        simp only [L, LinearMap.smul_comp, LinearMap.comp_assoc]
      _ = ((integralRelativeHomologyMap n Tg hTg).comp Ig.hom.hom).comp
          (Ie.hom.hom.comp J.hom.hom) := by rw [hsign]
      _ = (integralRelativeHomologyMap n Tg hTg).comp
          (Ig.hom.hom.comp (Jg.hom.hom.comp (integralRelativeHomologyMap n q hq))) := by
        rw [heJ, LinearMap.comp_assoc]
      _ = (integralRelativeHomologyMap n Tg hTg).comp
          ((integralRelativeHomologyMap n G hG).comp (integralRelativeHomologyMap n q hq)) := by
        rw [hmiddle]
      _ = (integralRelativeHomologyMap n Tf hTf).comp (integralRelativeHomologyMap n F hF) := by
        rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp,
          ← integralRelativeHomologyMap_comp]
        simp only [hmaps]
      _ = (integralRelativeHomologyMap n Tf hTf).comp (If.hom.hom.comp J.hom.hom) := by rw [hfJ]
      _ = R.comp J.hom.hom := (LinearMap.comp_assoc _ _ _).symm
  change L = R
  apply LinearMap.ext
  intro z
  have hz : J.hom.hom (J.inv.hom z) = z := congrArg (fun k => k.hom z) J.inv_hom_id
  have h := LinearMap.congr_fun hcomp (J.inv.hom z)
  change L (J.hom.hom (J.inv.hom z)) = R (J.hom.hom (J.inv.hom z)) at h
  rw [hz] at h
  exact h

theorem oriented_local_homology_chart_maps_eq
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (x y p : M) (hx : p ∈ (chartAt E x).source) (hy : p ∈ (chartAt E y).source)
    (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) p) (Fin (Module.finrank ℝ E)))
    (hori : Orientation.map _
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o =
      Orientation.map _
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv o) :
    (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E x p)))
        (show MapsTo (Homeomorph.subRight (chartAt E x p))
          ({chartAt E x p}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E x) p hx).hom.hom =
      (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (chartAt E y p)))
        (show MapsTo (Homeomorph.subRight (chartAt E y p))
          ({chartAt E y p}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hz => sub_ne_zero.mpr hz)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
          (chartAt E y) p hy).hom.hom := by
  have hdet : 0 < LinearMap.det
      (fderiv ℝ ((chartAt E y) ∘ (chartAt E x).symm) (chartAt E x p)).toLinearMap := by
    have h := det_pos_of_orientations_agree
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ p
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ p
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv
      o _ rfl hori.symm
    have hd := tangent_trivialization_transition_eq_fderiv x y p hx hy
    rw [← hd]
    exact h
  have h := integralLocalHomology_chart_maps_eq_det_sign x y p hx hy
  rw [sign_pos hdet, SignType.coe_one, one_smul] at h
  exact h

open ContinuousMap in
theorem exists_compact_neighborhood_class_with_oriented_chart_maps
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (p : M) (μ : integralLocalHomology (Module.finrank ℝ E) (0 : E)) :
    ∃ (K : Set M) (hK : K ⊆ (chartAt E p).source), IsCompact K ∧ p ∈ interior K ∧
      ∃! a : integralRelativeHomology (Module.finrank ℝ E) Kᶜ,
        ∀ (x : M) (hx : x ∈ K) (y : M) (hy : x ∈ (chartAt E y).source)
          (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))),
          Orientation.map _
            ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
              (by simpa only [TangentBundle.trivializationAt_baseSet] using hK hx)).toLinearEquiv o =
            Orientation.map _
              ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) y).continuousLinearEquivAt ℝ x
                (by simpa only [TangentBundle.trivializationAt_baseSet] using hy)).toLinearEquiv o →
          integralRelativeHomologyMap (Module.finrank ℝ E)
            (toContinuousMap (Homeomorph.subRight (chartAt E y x)))
            (show MapsTo (Homeomorph.subRight (chartAt E y x))
              ({chartAt E y x}ᶜ : Set E) ({0}ᶜ : Set E)
              from fun _ hz => sub_ne_zero.mpr hz)
            ((integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
              (chartAt E y) x hy).hom.hom
              (integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M)
                (show Kᶜ ⊆ ({x}ᶜ : Set M) from
                  fun _ hz heq => hz (heq.symm ▸ hx)) a)) = μ := by
  obtain ⟨K, hK, hcompact, hpK, a, ha, huniq⟩ := exists_compact_chart_neighborhood_class
    (Module.finrank ℝ E) (chartAt E p) p (mem_chart_source E p) μ
  refine ⟨K, hK, hcompact, hpK, a, ?_, ?_⟩
  · intro x hx y hy o hori
    have hmaps := oriented_local_homology_chart_maps_eq p y x (hK hx) hy o hori
    have h := LinearMap.congr_fun hmaps
      (integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M)
        (show Kᶜ ⊆ ({x}ᶜ : Set M) from fun _ hz heq => hz (heq.symm ▸ hx)) a)
    exact h.symm.trans (ha x hx)
  · intro b hb
    apply huniq b
    intro x hx
    let A := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hK hx)).toLinearEquiv
    exact hb x hx p (hK hx)
      (Orientation.map _ A.symm (Module.finBasis ℝ E).orientation) rfl

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set Bundle Module
open scoped Manifold Topology

universe u v w

namespace DifferentialGeometry.Topology

open scoped Classical in
private theorem orientation_coordinate_class_transition
    {E : Type u} {F : Type v} {H : Type w}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup H]
    (A B : F ≃ₗ[ℝ] E) (o : Orientation ℝ F (Fin (finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (finrank ℝ E))) (c : H) :
    (SignType.sign (LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E)) : ℤ) •
        (if Orientation.map _ A o = ω then c else -c) =
      if Orientation.map _ B o = ω then c else -c := by
  let a := Orientation.map (Fin (finrank ℝ E)) A o
  let b := Orientation.map (Fin (finrank ℝ E)) B o
  have hmap : Orientation.map _ (A.symm.trans B) a = b := by
    rw [DifferentialGeometry.orientation_map_trans]
    change Orientation.map _ B ((Orientation.map _ A).symm (Orientation.map _ A o)) = b
    rw [Equiv.symm_apply_apply]
  have hpos (h : b = a) : 0 < LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E) :=
    (Orientation.map_eq_iff_det_pos a (A.symm.trans B) (by simp)).mp (hmap.trans h)
  have hneg (h : b = -a) : LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E) < 0 :=
    (Orientation.map_eq_neg_iff_det_neg a (A.symm.trans B) (by simp)).mp (hmap.trans h)
  change (SignType.sign (LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E)) : ℤ) •
    (if a = ω then c else -c) = if b = ω then c else -c
  by_cases ha : a = ω
  · by_cases hb : b = ω
    · rw [ite_eq_left ha, ite_eq_left hb, sign_pos (hpos (hb.trans ha.symm))]
      simp
    · have hb' : b = -ω := (Orientation.ne_iff_eq_neg b ω (by simp)).mp hb
      have hba : b = -a := hb'.trans (congrArg Neg.neg ha).symm
      rw [ite_eq_left ha, ite_eq_right hb, sign_neg (hneg hba)]
      simp
  · have ha' : a = -ω := (Orientation.ne_iff_eq_neg a ω (by simp)).mp ha
    by_cases hb : b = ω
    · have hba : b = -a := (Orientation.ne_iff_eq_neg b a (by simp)).mp
        (fun h => ha (h.symm.trans hb))
      rw [ite_eq_right ha, ite_eq_left hb, sign_neg (hneg hba)]
      simp
    · have hb' : b = -ω := (Orientation.ne_iff_eq_neg b ω (by simp)).mp hb
      rw [ite_eq_right ha, ite_eq_right hb, sign_pos (hpos (hb'.trans ha'.symm))]
      simp

private def normalizedChartLocalIso
    {E M : Type u} [NormedAddCommGroup E] [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (n : ℕ) (p x : M) (hx : x ∈ (chartAt E p).source) :
    integralLocalHomology n x ≅ integralLocalHomology n (0 : E) :=
  integralLocalHomologyOpenPartialHomeomorphIso n (chartAt E p) x hx ≪≫
    integralRelativeHomologyHomeomorphIso n (Homeomorph.subRight (chartAt E p x))
      ({chartAt E p x}ᶜ : Set E) {0}ᶜ
      (fun _ hz => sub_ne_zero.mpr hz)
      (fun z hz heq => by
        apply hz
        change z + chartAt E p x = chartAt E p x at heq
        exact add_right_cancel (heq.trans (zero_add _).symm))

private def tangentChartOrientation
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (p x : M) (hx : x ∈ (chartAt E p).source)
    (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E))) :
    Orientation ℝ E (Fin (Module.finrank ℝ E)) :=
  Orientation.map _
    ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv o

open scoped Classical in
private theorem normalized_chart_local_class_coordinate_change
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T1Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (p q x : M) (hp : x ∈ (chartAt E p).source) (hq : x ∈ (chartAt E q).source)
    (o : Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (c : integralLocalHomology (Module.finrank ℝ E) (0 : E)) :
    (normalizedChartLocalIso (Module.finrank ℝ E) q x hq).hom.hom
        ((normalizedChartLocalIso (Module.finrank ℝ E) p x hp).inv.hom
          (if tangentChartOrientation p x hp o = ω then c else -c)) =
      if tangentChartOrientation q x hq o = ω then c else -c := by
  let A := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hp)).toLinearEquiv
  let B := ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) q).continuousLinearEquivAt ℝ x
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hq)).toLinearEquiv
  let I := normalizedChartLocalIso (Module.finrank ℝ E) p x hp
  let J := normalizedChartLocalIso (Module.finrank ℝ E) q x hq
  let b := if tangentChartOrientation p x hp o = ω then c else -c
  have hI : I.hom.hom (I.inv.hom b) = b :=
    congrArg (fun f => f.hom b) I.inv_hom_id
  have h := LinearMap.congr_fun (integralLocalHomology_chart_maps_eq_det_sign p q x hp hq)
    (I.inv.hom b)
  change (SignType.sign (LinearMap.det
      (fderiv ℝ ((chartAt E q) ∘ (chartAt E p).symm) (chartAt E p x)).toLinearMap) : ℤ) •
    I.hom.hom (I.inv.hom b) = J.hom.hom (I.inv.hom b) at h
  rw [hI] at h
  have hderiv := tangent_trivialization_transition_eq_fderiv p q x hp hq
  have hdet : LinearMap.det
      (fderiv ℝ ((chartAt E q) ∘ (chartAt E p).symm) (chartAt E p x)).toLinearMap =
      LinearMap.det (A.symm.trans B : E →ₗ[ℝ] E) :=
    congrArg (fun f : E →L[ℝ] E => LinearMap.det f.toLinearMap) hderiv.symm
  rw [hdet] at h
  exact h.symm.trans (orientation_coordinate_class_transition A B o ω c)

open Classical in
theorem exists_locally_realized_family_of_tangent_orientation_locality
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (c : integralLocalHomology (Module.finrank ℝ E) (0 : E))
    (hlocal : ∀ p : M, ∃ (U : Set M) (hUs : U ⊆ (chartAt E p).source),
      IsOpen U ∧ p ∈ U ∧ ∀ (x : M) (hx : x ∈ U),
        (Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              (hUs hx))).toLinearEquiv
          (o x)) =
          (Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ p
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              (mem_chart_source E p))).toLinearEquiv
          (o p))) :
    ∃! μ : ∀ x : M, integralLocalHomology (Module.finrank ℝ E) x,
      (∀ (p x : M) (hx : x ∈ (chartAt E p).source),
        ((integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
          (show MapsTo (Homeomorph.subRight (chartAt E p x))
            ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from
              fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            (chartAt E p) x hx).hom.hom) (μ x) =
          if (Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hx)).toLinearEquiv
          (o x)) = ω then c else -c) ∧
      ∀ p : M, ∃ L : Set M, IsCompact L ∧ p ∈ interior L ∧
        ∃ a : integralRelativeHomology (Module.finrank ℝ E) Lᶜ,
          ∀ (x : M) (hx : x ∈ L),
            integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M)
              (show Lᶜ ⊆ ({x}ᶜ : Set M) from
                compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = μ x := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let μ (x : M) : integralLocalHomology (Module.finrank ℝ E) x :=
    (normalizedChartLocalIso (Module.finrank ℝ E) x x (mem_chart_source E x)).inv.hom
      (if tangentChartOrientation x x (mem_chart_source E x) (o x) = ω then c else -c)
  have hmaps (p x : M) (hx : x ∈ (chartAt E p).source) :
      (normalizedChartLocalIso (Module.finrank ℝ E) p x hx).hom.hom (μ x) =
        if tangentChartOrientation p x hx (o x) = ω then c else -c :=
    normalized_chart_local_class_coordinate_change x p x (mem_chart_source E x) hx (o x) ω c
  refine ⟨μ, ⟨hmaps, ?_⟩, ?_⟩
  · intro p
    obtain ⟨U, hUs, hU, hpU, hori⟩ := hlocal p
    let d := if tangentChartOrientation p p (mem_chart_source E p) (o p) = ω then c else -c
    obtain ⟨K, hKs, _, hpK, a, ha, _⟩ := exists_compact_chart_neighborhood_class
      (Module.finrank ℝ E) (chartAt E p) p (mem_chart_source E p) d
    obtain ⟨L, hL, hpL, hLU⟩ := exists_compact_between isCompact_singleton
      (isOpen_interior.inter hU) (singleton_subset_iff.mpr ⟨hpK, hpU⟩)
    have hLK : L ⊆ K := hLU.trans (inter_subset_left.trans interior_subset)
    let hKL : MapsTo (ContinuousMap.id M) Kᶜ Lᶜ := compl_subset_compl.mpr hLK
    let b := integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M) hKL a
    refine ⟨L, hL, hpL (mem_singleton p), b, ?_⟩
    intro x hx
    let I := normalizedChartLocalIso (Module.finrank ℝ E) p x (hKs (hLK hx))
    apply I.toLinearEquiv.injective
    change I.hom.hom _ = I.hom.hom (μ x)
    have hpoint := hmaps p x (hKs (hLK hx))
    have hconst : tangentChartOrientation p x (hKs (hLK hx)) (o x) =
        tangentChartOrientation p p (mem_chart_source E p) (o p) :=
      hori x (hLU hx).2
    rw [hconst] at hpoint
    change I.hom.hom (μ x) = d at hpoint
    rw [hpoint]
    let hLx : MapsTo (ContinuousMap.id M) Lᶜ ({x}ᶜ : Set M) :=
      compl_subset_compl.mpr (singleton_subset_iff.mpr hx)
    have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp (Module.finrank ℝ E)
      (ContinuousMap.id M) (ContinuousMap.id M) hKL hLx) a
    exact (congrArg I.hom.hom hcomp.symm).trans (ha x (hLK hx))
  · intro ν hν
    funext x
    apply (normalizedChartLocalIso (Module.finrank ℝ E) x x
      (mem_chart_source E x)).toLinearEquiv.injective
    exact (hν.1 x x (mem_chart_source E x)).trans
      (hmaps x x (mem_chart_source E x)).symm

end DifferentialGeometry.Topology

end

section
open Bundle Set
open scoped Manifold Topology

universe u

namespace DifferentialGeometry.Topology

open Classical in
theorem exists_locally_realized_family_of_tangent_local_frames
    {E M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)))
    (ω : Orientation ℝ E (Fin (Module.finrank ℝ E)))
    (c : integralLocalHomology (Module.finrank ℝ E) (0 : E))
    (hframes : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ s : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ∃ hs : IsLocalFrameOn 𝓘(ℝ, E) E 0 s U,
          ∀ (x : M) (hx : x ∈ U), (hs.toBasisAt hx).orientation = o x) :
    ∃! μ : ∀ x : M, integralLocalHomology (Module.finrank ℝ E) x,
      (∀ (p x : M) (hx : x ∈ (chartAt E p).source),
        ((integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight (chartAt E p x)))
          (show MapsTo (Homeomorph.subRight (chartAt E p x))
            ({chartAt E p x}ᶜ : Set E) ({0}ᶜ : Set E) from
              fun _ hz => sub_ne_zero.mpr hz)).comp
          (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E)
            (chartAt E p) x hx).hom.hom) (μ x) =
          if (Orientation.map _
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearEquivAt ℝ x
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              hx)).toLinearEquiv
          (o x)) = ω then c else -c) ∧
      ∀ p : M, ∃ L : Set M, IsCompact L ∧ p ∈ interior L ∧
        ∃ a : integralRelativeHomology (Module.finrank ℝ E) Lᶜ,
          ∀ (x : M) (hx : x ∈ L),
            integralRelativeHomologyMap (Module.finrank ℝ E) (ContinuousMap.id M)
              (show Lᶜ ⊆ ({x}ᶜ : Set M) from
                compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) a = μ x := by
  exact exists_locally_realized_family_of_tangent_orientation_locality o ω c
    (tangent_orientation_locality_of_local_frames o hframes)

end DifferentialGeometry.Topology

end
