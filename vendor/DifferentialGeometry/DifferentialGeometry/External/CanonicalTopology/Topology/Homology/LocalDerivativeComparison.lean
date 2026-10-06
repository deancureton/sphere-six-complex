module

public import DifferentialGeometry.External.CanonicalTopology.Analysis.LocalDerivativeHomotopy
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeZero
public import Mathlib.Analysis.Convex.Contractible
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalLinearMaps
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCharts
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

theorem exists_ball_relative_homologyMap_eq_derivative
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (A : E ≃L[ℝ] F) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) 0)
    {s : Set E} (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) :
    ∃ (r : ℝ) (hr : 0 < r), Metric.ball (0 : E) r ⊆ s ∧
      ∃ g h : C(Metric.ball (0 : E) r, F),
        (∀ x, g x = A (x : E)) ∧ (∀ x, h x = f (x : E)) ∧
        ∃ hg : MapsTo g
            ({(⟨0, Metric.mem_ball_self hr⟩ : Metric.ball (0 : E) r)}ᶜ : Set _)
            ({0}ᶜ : Set F),
          ∃ hh : MapsTo h
              ({(⟨0, Metric.mem_ball_self hr⟩ : Metric.ball (0 : E) r)}ᶜ : Set _)
              ({0}ᶜ : Set F),
            ∀ n : ℕ, integralRelativeHomologyMap (n + 1) h hh =
              integralRelativeHomologyMap (n + 1) g hg := by
  obtain ⟨r, hr, hrs, g₀, h₀, hg₀, hh₀, H, _⟩ :=
    DifferentialGeometry.Analysis.exists_punctured_ball_derivative_homotopy A hzero hf hs hc
  let B : Set E := Metric.ball (0 : E) r
  let z : B := ⟨0, Metric.mem_ball_self hr⟩
  let V : Set B := {z}ᶜ
  let U : Set E := Metric.ball (0 : E) r \ {0}
  have hne (x : V) : ((x : B) : E) ≠ 0 := by
    intro hx
    exact x.property (Subtype.ext hx)
  let k : C(V, U) :=
    ⟨fun x => ⟨((x : B) : E), ⟨(x : B).property, hne x⟩⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let g : C(B, F) :=
    ⟨fun x => A (x : E), A.continuous.comp continuous_subtype_val⟩
  let h : C(B, F) :=
    ⟨fun x => f (x : E),
      hc.comp_continuous continuous_subtype_val (fun x => hrs x.property)⟩
  have hg : MapsTo g V ({0}ᶜ : Set F) := by
    intro x hx hz
    have hxzero : (x : E) = 0 := A.injective (hz.trans (map_zero A).symm)
    exact hx (Subtype.ext hxzero)
  have hh : MapsTo h V ({0}ᶜ : Set F) := by
    intro x hx
    have hval := hh₀ (k ⟨x, hx⟩)
    have hnonzero : (h₀ (k ⟨x, hx⟩) : F) ≠ 0 := (h₀ (k ⟨x, hx⟩)).property
    change f (x : E) ≠ 0
    rw [hval] at hnonzero
    exact hnonzero
  have hgcomp : g₀.comp k = singularPairRestriction g hg := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact hg₀ (k x)
  have hhcomp : h₀.comp k = singularPairRestriction h hh := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact hh₀ (k x)
  have hrestr : (singularPairRestriction g hg).Homotopic
      (singularPairRestriction h hh) := by
    rw [← hgcomp, ← hhcomp]
    exact ⟨H.compContinuousMap k⟩
  refine ⟨r, hr, hrs, g, h, (fun _ => rfl), (fun _ => rfl), hg, hh, ?_⟩
  intro n
  let := integralSingularHomology_subsingleton_of_contractible (n + 1)
    (Nat.succ_ne_zero n) F
  exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n g h V
    ({0}ᶜ : Set F) hg hh hrestr).symm

theorem integralRelativeHomologyMap_eq_derivative
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(E, F)) (A : E ≃L[ℝ] F) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) 0)
    (hpair : MapsTo f ({0}ᶜ : Set E) ({0}ᶜ : Set F)) (n : ℕ) :
    integralRelativeHomologyMap n f hpair =
      integralRelativeHomologyMap n ⟨A, A.continuous⟩
        (show MapsTo A ({0}ᶜ : Set E) ({0}ᶜ : Set F) from
          fun _ hx h => hx (A.injective (h.trans (map_zero A).symm))) := by
  let L : C(E, F) := ⟨A, A.continuous⟩
  have hL : MapsTo L ({0}ᶜ : Set E) ({0}ᶜ : Set F) :=
    fun _ hx h => hx (A.injective (h.trans (map_zero A).symm))
  change integralRelativeHomologyMap n f hpair =
    integralRelativeHomologyMap n L hL
  cases n with
  | zero =>
    exact integralRelativeHomologyMap_zero_eq_of_joined f L
      ({0}ᶜ : Set E) ({0}ᶜ : Set F) hpair hL
      (fun _ => ⟨PathConnectedSpace.somePath _ _⟩)
  | succ n =>
    obtain ⟨r, hr, _, g, h, hg, hh, hgp, hhp, hcompare⟩ :=
      exists_ball_relative_homologyMap_eq_derivative A hzero hf
        (s := Set.univ) Filter.univ_mem f.continuous.continuousOn
    let U : Set E := Metric.ball (0 : E) r
    let J := integralLocalHomologyNeighborhoodIso (n + 1) (0 : E) U
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hJmap : J.hom.hom =
        integralRelativeHomologyMap (n + 1) (singularSubspaceInclusion U)
          (neighborhoodPointComplement_mapsTo (0 : E) U (Metric.mem_ball_self hr)) :=
      integralLocalHomologyNeighborhoodIso_hom (n + 1) (0 : E) U
        Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hsurj : Function.Surjective J.hom.hom := by
      intro a
      refine ⟨J.inv.hom a, ?_⟩
      exact congrArg (fun k => k.hom a) J.inv_hom_id
    have hcomp : (integralRelativeHomologyMap (n + 1) f hpair).comp J.hom.hom =
        (integralRelativeHomologyMap (n + 1) L hL).comp J.hom.hom := by
      simp only [hJmap]
      rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
      have hincf : f.comp (singularSubspaceInclusion U) = h := by
        apply ContinuousMap.ext
        intro x
        exact (hh x).symm
      have hincL : L.comp (singularSubspaceInclusion U) = g := by
        apply ContinuousMap.ext
        intro x
        exact (hg x).symm
      simpa only [hincf, hincL] using
        ((hcompare n : integralRelativeHomologyMap (n + 1) h hhp =
          integralRelativeHomologyMap (n + 1) g hgp))
    apply LinearMap.ext
    intro a
    obtain ⟨b, rfl⟩ := hsurj a
    exact LinearMap.congr_fun hcomp b

private theorem exists_ball_local_homologyMap_eq_det_sign
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} (A : E ≃L[ℝ] E) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] E) 0)
    {s : Set E} (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) :
    ∃ (r : ℝ) (hr : 0 < r), Metric.ball (0 : E) r ⊆ s ∧
      ∃ h : C(Metric.ball (0 : E) r, E), (∀ x, h x = f (x : E)) ∧
        ∃ hp : MapsTo h
            ({(⟨0, Metric.mem_ball_self hr⟩ : Metric.ball (0 : E) r)}ᶜ : Set _)
            ({0}ᶜ : Set E),
          (integralRelativeHomologyMap (Module.finrank ℝ E) h hp).comp
              (integralLocalHomologyNeighborhoodIso (Module.finrank ℝ E) (0 : E)
                (Metric.ball (0 : E) r) Metric.isOpen_ball (Metric.mem_ball_self hr)).inv.hom =
            (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) • LinearMap.id := by
  obtain ⟨r, hr, hrs, g, h, hg, hh, hgp, hhp, hcompare⟩ :=
    exists_ball_relative_homologyMap_eq_derivative A hzero hf hs hc
  let U : Set E := Metric.ball (0 : E) r
  let J := integralLocalHomologyNeighborhoodIso (Module.finrank ℝ E) (0 : E) U
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  let L := toContinuousMap A
  have hL : MapsTo L ({0}ᶜ : Set E) ({0}ᶜ : Set E) :=
    fun _ hx h => hx (A.injective (h.trans (map_zero A).symm))
  have hinc : L.comp (singularSubspaceInclusion U) = g := by
    apply ContinuousMap.ext
    intro x
    exact (hg x).symm
  have hJmap : J.hom.hom =
      integralRelativeHomologyMap (Module.finrank ℝ E) (singularSubspaceInclusion U)
        (neighborhoodPointComplement_mapsTo (0 : E) U (Metric.mem_ball_self hr)) :=
    integralLocalHomologyNeighborhoodIso_hom (Module.finrank ℝ E) (0 : E) U
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hgmap : integralRelativeHomologyMap (Module.finrank ℝ E) g hgp =
      (integralRelativeHomologyMap (Module.finrank ℝ E) L hL).comp J.hom.hom := by
    rw [hJmap, ← integralRelativeHomologyMap_comp]
    simp only [hinc]
  have hall (n : ℕ) : integralRelativeHomologyMap n h hhp =
      integralRelativeHomologyMap n g hgp := by
    cases n with
    | zero =>
        exact integralRelativeHomologyMap_zero_eq_of_joined h g _ _ hhp hgp
          (fun _ => ⟨PathConnectedSpace.somePath _ _⟩)
    | succ n => exact hcompare n
  have hcancel : J.hom.hom.comp J.inv.hom = LinearMap.id :=
    congrArg (fun k => k.hom) J.inv_hom_id
  refine ⟨r, hr, hrs, h, hh, hhp, ?_⟩
  change (integralRelativeHomologyMap (Module.finrank ℝ E) h hhp).comp J.inv.hom = _
  rw [hall, hgmap, LinearMap.comp_assoc, hcancel, LinearMap.comp_id]
  exact integralRelativeHomologyMap_linearEquiv_eq_det_sign A

private theorem exists_ball_local_homologyMap_translation_eq_det_sign
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} (a : E) (A : E ≃L[ℝ] E) (hf : HasFDerivAt f (A : E →L[ℝ] E) a)
    {s : Set E} (hs : s ∈ 𝓝 a) (hc : ContinuousOn f s) :
    ∃ (r : ℝ) (hr : 0 < r), Metric.ball a r ⊆ s ∧
      ∃ h : C(Metric.ball a r, E), (∀ x, h x = f (x : E)) ∧
        ∃ hp : MapsTo h
            ({(⟨a, Metric.mem_ball_self hr⟩ : Metric.ball a r)}ᶜ : Set _)
            ({f a}ᶜ : Set E),
          (integralRelativeHomologyMap (Module.finrank ℝ E)
              (toContinuousMap (Homeomorph.subRight (f a)))
              (show MapsTo (Homeomorph.subRight (f a)) ({f a}ᶜ : Set E) ({0}ᶜ : Set E)
                from fun _ hx => sub_ne_zero.mpr hx)).comp
              ((integralRelativeHomologyMap (Module.finrank ℝ E) h hp).comp
                (integralLocalHomologyNeighborhoodIso (Module.finrank ℝ E) a
                  (Metric.ball a r) Metric.isOpen_ball (Metric.mem_ball_self hr)).inv.hom) =
            (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) •
              integralRelativeHomologyMap (Module.finrank ℝ E)
                (toContinuousMap (Homeomorph.subRight a))
                (show MapsTo (Homeomorph.subRight a) ({a}ᶜ : Set E) ({0}ᶜ : Set E)
                  from fun _ hx => sub_ne_zero.mpr hx) := by
  let F : E → E := fun x => f (a + x) - f a
  let t := (fun x : E => a + x) ⁻¹' s
  have hFzero : F 0 = 0 := by simp [F]
  have hFderiv : HasFDerivAt F (A : E →L[ℝ] E) 0 := by
    exact ((hasFDerivAt_comp_add_left a).mpr (by simpa only [add_zero] using hf)).sub_const (f a)
  have ht : t ∈ 𝓝 (0 : E) :=
    ((by fun_prop : ContinuousAt (fun x : E => a + x) 0)).preimage_mem_nhds
      (by simpa only [add_zero] using hs)
  have hFc : ContinuousOn F t :=
    (hc.comp' ((by fun_prop : ContinuousOn (fun x : E => a + x) t))
      (show MapsTo (fun x : E => a + x) t s from fun _ hx => hx)).sub
      ((continuousOn_const : ContinuousOn (fun _ : E => f a) t))
  obtain ⟨r, hr, hrt, g, hg, hgp, hsign⟩ :=
    exists_ball_local_homologyMap_eq_det_sign A hFzero hFderiv ht hFc
  let U := Metric.ball (0 : E) r
  let V := Metric.ball a r
  have hsub (x : V) : (x : E) - a ∈ U := by
    simpa only [U, V, Metric.mem_ball, dist_eq_norm, sub_zero] using x.property
  have hadd (x : E) : a + (x - a) = x := by
    simp [sub_eq_add_neg]
  have hVs : V ⊆ s := by
    intro x hx
    have hx' := hrt (hsub ⟨x, hx⟩)
    change a + (x - a) ∈ s at hx'
    simpa only [hadd] using hx'
  let h : C(V, E) := ⟨fun x => f x, (hc.mono hVs).domRestrict⟩
  let k : C(V, U) := ⟨fun x => ⟨(x : E) - a, hsub x⟩, by fun_prop⟩
  have hkp : MapsTo k ({(⟨a, Metric.mem_ball_self hr⟩ : V)}ᶜ : Set V)
      ({(⟨0, Metric.mem_ball_self hr⟩ : U)}ᶜ : Set U) := by
    intro x hx hx0
    apply hx
    apply Subtype.ext
    exact sub_eq_zero.mp (congrArg Subtype.val hx0)
  have hp : MapsTo h ({(⟨a, Metric.mem_ball_self hr⟩ : V)}ᶜ : Set V)
      ({f a}ᶜ : Set E) := by
    intro x hx hxa
    apply hgp (hkp hx)
    rw [hg (k x)]
    change f (a + ((x : E) - a)) - f a = 0
    rw [hadd]
    exact sub_eq_zero.mpr hxa
  let S := toContinuousMap (Homeomorph.subRight a)
  let T := toContinuousMap (Homeomorph.subRight (f a))
  have hS : MapsTo S ({a}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hx => sub_ne_zero.mpr hx
  have hT : MapsTo T ({f a}ᶜ : Set E) ({0}ᶜ : Set E) := fun _ hx => sub_ne_zero.mpr hx
  let n := Module.finrank ℝ E
  let J0 := integralLocalHomologyNeighborhoodIso n (0 : E) U Metric.isOpen_ball
    (Metric.mem_ball_self hr)
  let Ja := integralLocalHomologyNeighborhoodIso n a V Metric.isOpen_ball
    (Metric.mem_ball_self hr)
  have hJ0 : J0.hom.hom = integralRelativeHomologyMap n (singularSubspaceInclusion U)
      (neighborhoodPointComplement_mapsTo (0 : E) U (Metric.mem_ball_self hr)) := rfl
  have hJa : Ja.hom.hom = integralRelativeHomologyMap n (singularSubspaceInclusion V)
      (neighborhoodPointComplement_mapsTo a V (Metric.mem_ball_self hr)) := rfl
  have hcomm : (integralRelativeHomologyMap n S hS).comp Ja.hom.hom =
      J0.hom.hom.comp (integralRelativeHomologyMap n k hkp) := by
    rw [hJ0, hJa, ← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    rfl
  have hcancel0 : J0.inv.hom.comp J0.hom.hom = LinearMap.id :=
    congrArg (fun q => q.hom) J0.hom_inv_id
  have hcancelA : Ja.hom.hom.comp Ja.inv.hom = LinearMap.id :=
    congrArg (fun q => q.hom) Ja.inv_hom_id
  have hkmap : (integralRelativeHomologyMap n k hkp).comp Ja.inv.hom =
      J0.inv.hom.comp (integralRelativeHomologyMap n S hS) := by
    calc
      (integralRelativeHomologyMap n k hkp).comp Ja.inv.hom =
          (J0.inv.hom.comp J0.hom.hom).comp
            ((integralRelativeHomologyMap n k hkp).comp Ja.inv.hom) := by
        rw [hcancel0, LinearMap.id_comp]
      _ = J0.inv.hom.comp
          ((J0.hom.hom.comp (integralRelativeHomologyMap n k hkp)).comp Ja.inv.hom) := by
        simp only [LinearMap.comp_assoc]
      _ = J0.inv.hom.comp
          (((integralRelativeHomologyMap n S hS).comp Ja.hom.hom).comp Ja.inv.hom) := by
        rw [← hcomm]
      _ = J0.inv.hom.comp (integralRelativeHomologyMap n S hS) := by
        rw [LinearMap.comp_assoc, hcancelA, LinearMap.comp_id]
  have hsquare : T.comp h = g.comp k := by
    apply ContinuousMap.ext
    intro x
    change f (x : E) - f a = g (k x)
    rw [hg (k x)]
    change f (x : E) - f a = f (a + ((x : E) - a)) - f a
    rw [hadd]
  have hsquareMap : (integralRelativeHomologyMap n T hT).comp
      (integralRelativeHomologyMap n h hp) =
      (integralRelativeHomologyMap n g hgp).comp (integralRelativeHomologyMap n k hkp) := by
    rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
    simp only [hsquare]
  refine ⟨r, hr, hVs, h, fun _ => rfl, hp, ?_⟩
  change (integralRelativeHomologyMap n T hT).comp
      ((integralRelativeHomologyMap n h hp).comp Ja.inv.hom) =
    (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) • integralRelativeHomologyMap n S hS
  rw [← LinearMap.comp_assoc, hsquareMap, LinearMap.comp_assoc, hkmap,
    ← LinearMap.comp_assoc, hsign]
  apply LinearMap.ext
  intro x
  rfl

private theorem integralLocalHomologyOpenPartialHomeomorphIso_translation_eq_det_sign_of_hasFDerivAt
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E) (a : E) (ha : a ∈ e.source)
    (A : E ≃L[ℝ] E) (hf : HasFDerivAt e (A : E →L[ℝ] E) a) :
    (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (e a)))
        (show MapsTo (Homeomorph.subRight (e a)) ({e a}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hx => sub_ne_zero.mpr hx)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E) e a ha).hom.hom =
      (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) •
        integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight a))
          (show MapsTo (Homeomorph.subRight a) ({a}ᶜ : Set E) ({0}ᶜ : Set E)
            from fun _ hx => sub_ne_zero.mpr hx) := by
  obtain ⟨r, hr, hrs, h, hh, hp, hsign⟩ :=
    exists_ball_local_homologyMap_translation_eq_det_sign a A hf
      (e.open_source.mem_nhds ha) e.continuousOn
  let n := Module.finrank ℝ E
  let U := Metric.ball a r
  let I := integralLocalHomologyOpenPartialHomeomorphIso n e a ha
  let J := integralLocalHomologyNeighborhoodIso n a U Metric.isOpen_ball (Metric.mem_ball_self hr)
  let g : C(U, E) := ⟨fun x => e x, (e.continuousOn.mono hrs).domRestrict⟩
  have hgh : g = h := by
    apply ContinuousMap.ext
    intro x
    exact (hh x).symm
  have hsmall : I.hom.hom.comp J.hom.hom = integralRelativeHomologyMap n h hp := by
    have H := integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
      n e a U Metric.isOpen_ball (Metric.mem_ball_self hr) hrs
    change I.hom.hom.comp J.hom.hom = integralRelativeHomologyMap n g _ at H
    simpa only [hgh] using H
  have hcancel : J.hom.hom.comp J.inv.hom = LinearMap.id :=
    congrArg (fun f => f.hom) J.inv_hom_id
  have hI : I.hom.hom = (integralRelativeHomologyMap n h hp).comp J.inv.hom := by
    have H := congrArg (fun f => f.comp J.inv.hom) hsmall
    simpa only [LinearMap.comp_assoc, hcancel, LinearMap.comp_id] using H
  change (integralRelativeHomologyMap n _ _).comp I.hom.hom = _
  rw [hI]
  exact hsign

theorem integralLocalHomologyOpenPartialHomeomorphIso_translation_eq_det_sign
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph E E) (a : E) (ha : a ∈ e.source)
    (he : DifferentiableAt ℝ e a) (he' : DifferentiableAt ℝ e.symm (e a)) :
    (integralRelativeHomologyMap (Module.finrank ℝ E)
        (toContinuousMap (Homeomorph.subRight (e a)))
        (show MapsTo (Homeomorph.subRight (e a)) ({e a}ᶜ : Set E) ({0}ᶜ : Set E)
          from fun _ hx => sub_ne_zero.mpr hx)).comp
        (integralLocalHomologyOpenPartialHomeomorphIso (Module.finrank ℝ E) e a ha).hom.hom =
      (SignType.sign (LinearMap.det (fderiv ℝ e a).toLinearMap) : ℤ) •
        integralRelativeHomologyMap (Module.finrank ℝ E)
          (toContinuousMap (Homeomorph.subRight a))
          (show MapsTo (Homeomorph.subRight a) ({a}ᶜ : Set E) ({0}ᶜ : Set E)
            from fun _ hx => sub_ne_zero.mpr hx) := by
  let D := fderiv ℝ e a
  let D' := fderiv ℝ e.symm (e a)
  have hleft : D'.comp D = ContinuousLinearMap.id ℝ E := by
    calc
      D'.comp D = fderiv ℝ (e.symm ∘ e) a := (fderiv_comp a he' he).symm
      _ = fderiv ℝ (id : E → E) a := Filter.EventuallyEq.fderiv_eq
        ((e.eventually_left_inverse ha : (e.symm ∘ e : E → E) =ᶠ[𝓝 a] id))
      _ = ContinuousLinearMap.id ℝ E := fderiv_id
  have hright : D.comp D' = ContinuousLinearMap.id ℝ E := by
    have he0 : DifferentiableAt ℝ e (e.symm (e a)) := by rwa [e.left_inv ha]
    calc
      D.comp D' = (fderiv ℝ e (e.symm (e a))).comp D' := by rw [e.left_inv ha]
      _ = fderiv ℝ (e ∘ e.symm) (e a) := (fderiv_comp (e a) he0 he').symm
      _ = fderiv ℝ (id : E → E) (e a) :=
        Filter.EventuallyEq.fderiv_eq
          ((e.eventually_right_inverse (e.map_source ha) : (e ∘ e.symm : E → E) =ᶠ[𝓝 (e a)] id))
      _ = ContinuousLinearMap.id ℝ E := fderiv_id
  let A := ContinuousLinearEquiv.equivOfInverse' D D' hright hleft
  exact integralLocalHomologyOpenPartialHomeomorphIso_translation_eq_det_sign_of_hasFDerivAt
    e a ha A he.hasFDerivAt

end DifferentialGeometry.Topology
