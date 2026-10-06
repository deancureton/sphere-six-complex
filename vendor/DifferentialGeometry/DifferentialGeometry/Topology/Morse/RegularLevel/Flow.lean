module

public import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
public import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
public import DifferentialGeometry.Topology.Morse.Defs
public import DifferentialGeometry.Topology.Morse.NormalForm.Local
public import Mathlib.Geometry.Manifold.Diffeomorph

@[expose] public section

open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable {f : M → ℝ} {a b : ℝ}

structure UnitSpeedFlow (f : M → ℝ) (a b : ℝ) where
  flow : ℝ → M → M
  flow_zero : ∀ x : M, flow 0 x = x
  flow_add : ∀ s t : ℝ, flow (s + t) = flow s ∘ flow t
  strip_eq_sub : ∀ x : M, ∀ t : ℝ, 0 ≤ t → a ≤ f x - t → f (flow t x) = f x - t
  strip_eq_add_back : ∀ x : M, ∀ t : ℝ, 0 ≤ t → a ≤ f x → f x + t ≤ b →
    f (flow (-t) x) = f x + t
  rate_bound : ∀ x : M, ∀ t : ℝ, 0 ≤ t → f x - t ≤ f (flow t x) ∧ f (flow t x) ≤ f x

structure GradientLikeFlow (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ)
    extends UnitSpeedFlow f a b where
  contMDiffAt : ∀ t : ℝ, ∀ x : M, ContMDiffAt I I (⊤ : WithTop ℕ∞) (fun x : M => flow t x) x
  contMDiffAt_t : ∀ x : M, ContMDiffAt 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) (fun t : ℝ => flow t x) (0 : ℝ)

noncomputable def unitSpeedFlowOfVectorField [T2Space M] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] (a b : ℝ) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hdf : ∀ x, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    UnitSpeedFlow f a b where
  flow := fun t x => curveAt v hcomplete x t
  flow_zero := by
    intro x
    exact curveAt_zero v hcomplete x
  flow_add := by
    intro s t
    funext x
    have hγt : IsMIntegralCurve (curveAt v hcomplete x ∘ (· + t)) v :=
      IsMIntegralCurve.comp_add (curveAt_integralCurve v hcomplete x) t
    have hEq := integralCurve_eq_of_agree (t₀ := 0) v hv hγt
      (curveAt_integralCurve v hcomplete (curveAt v hcomplete x t)) (by
        simp [curveAt_zero v hcomplete (curveAt v hcomplete x t)])
    have hmain : curveAt v hcomplete (curveAt v hcomplete x t) s = curveAt v hcomplete x (s + t) := by
      have hh := congrFun hEq s
      simpa [Function.comp_def] using hh.symm
    change curveAt v hcomplete x (s + t) = curveAt v hcomplete (curveAt v hcomplete x t) s
    exact hmain.symm
  strip_eq_sub := by
    intro x t ht hst
    have hEq := f_eq_sub_of_integralCurve f hf v hdf (curveAt_integralCurve v hcomplete x) t
    rw [curveAt_zero v hcomplete x] at hEq
    exact hEq
  strip_eq_add_back := by
    intro x t ht h1 h2
    have hEq := f_eq_sub_of_integralCurve f hf v hdf (curveAt_integralCurve v hcomplete x) (-t)
    have hx0 : curveAt v hcomplete x 0 = x := curveAt_zero v hcomplete x
    simpa [hx0, sub_neg_eq_add] using hEq
  rate_bound := by
    intro x t ht
    have hEq := f_eq_sub_of_integralCurve f hf v hdf (curveAt_integralCurve v hcomplete x) t
    have hx0 : curveAt v hcomplete x 0 = x := curveAt_zero v hcomplete x
    constructor
    · rw [curveAt_zero v hcomplete x] at hEq
      exact le_of_eq hEq.symm
    · have h1 : f (curveAt v hcomplete x t) ≤ f x := by
        rw [hEq, hx0]
        linarith
      simpa using h1

def GradientLikeFlow.toDiffeomorph (Φ : GradientLikeFlow I f a b) (t : ℝ) :
    Diffeomorph I I M M (⊤ : WithTop ℕ∞) where
  toEquiv :=
    { toFun := Φ.flow t
      invFun := Φ.flow (-t)
      left_inv := by
        intro x
        have h := congrFun (Φ.flow_add (-t) t) x
        change Φ.flow (-t) (Φ.flow t x) = x
        calc
          Φ.flow (-t) (Φ.flow t x) = (Φ.flow (-t) ∘ Φ.flow t) x := rfl
          _ = Φ.flow (-t + t) x := h.symm
          _ = Φ.flow 0 x := by simp
          _ = x := Φ.flow_zero x
      right_inv := by
        intro x
        have h := congrFun (Φ.flow_add t (-t)) x
        change Φ.flow t (Φ.flow (-t) x) = x
        calc
          Φ.flow t (Φ.flow (-t) x) = (Φ.flow t ∘ Φ.flow (-t)) x := rfl
          _ = Φ.flow (t + -t) x := h.symm
          _ = Φ.flow 0 x := by simp
          _ = x := Φ.flow_zero x }
  contMDiff_toFun := Φ.contMDiffAt t
  contMDiff_invFun := Φ.contMDiffAt (-t)

omit [TopologicalSpace M] in
theorem UnitSpeedFlow.flow_sublevel (Φ : UnitSpeedFlow f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) {x : M} (hx : x ∈ sublevel f b) :
    Φ.flow t x ∈ sublevel f (b - t) := by
  change f (Φ.flow t x) ≤ b - t
  by_cases hst : a ≤ f x - t
  · have hEq := Φ.strip_eq_sub x t ht.1 hst
    calc
      f (Φ.flow t x) = f x - t := hEq
      _ ≤ b - t := by
        have hfx : f x ≤ b := by simpa [sublevel] using hx
        linarith
  · by_cases hbelow : f x ≤ a
    · have hb := (Φ.rate_bound x t ht.1).2
      calc
        f (Φ.flow t x) ≤ f x := hb
        _ ≤ a := hbelow
        _ ≤ b - t := by linarith [ht.2]
    · have hax : a < f x := lt_of_not_ge hbelow
      let t₀ : ℝ := f x - a
      have ht₀ : 0 ≤ t₀ := by
        dsimp [t₀]
        linarith
      have ht₀t : t₀ < t := by
        have hnot : f x - t < a := lt_of_not_ge hst
        dsimp [t₀]
        linarith
      have hEq₀ := Φ.strip_eq_sub x t₀ ht₀ (by dsimp [t₀]; linarith)
      have hflow : Φ.flow t x = Φ.flow (t - t₀) (Φ.flow t₀ x) := by
        have h := congrFun (Φ.flow_add (t - t₀) t₀) x
        change Φ.flow ((t - t₀) + t₀) x = Φ.flow (t - t₀) (Φ.flow t₀ x) at h
        rw [sub_add_cancel] at h
        exact h
      have hb := (Φ.rate_bound (Φ.flow t₀ x) (t - t₀) (by linarith)).2
      calc
        f (Φ.flow t x) = f (Φ.flow (t - t₀) (Φ.flow t₀ x)) := by rw [hflow]
        _ ≤ f (Φ.flow t₀ x) := hb
        _ = a := by
          have hE : f (Φ.flow t₀ x) = f x - t₀ := hEq₀
          dsimp [t₀] at hE
          linarith
        _ ≤ b - t := by linarith [ht.2]

omit [TopologicalSpace M] in
theorem UnitSpeedFlow.flow_sublevel_of_mem_lower (Φ : UnitSpeedFlow f a b)
    {t : ℝ} (ht : 0 ≤ t) {x : M} (hx : x ∈ sublevel f a) :
    Φ.flow t x ∈ sublevel f a := by
  change f (Φ.flow t x) ≤ a
  exact le_trans (Φ.rate_bound x t ht).2 hx

omit [TopologicalSpace M] in
theorem UnitSpeedFlow.flow_sublevel_back (Φ : UnitSpeedFlow f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) {y : M} (hy : y ∈ sublevel f (b - t)) :
    Φ.flow (-t) y ∈ sublevel f b := by
  change f (Φ.flow (-t) y) ≤ b
  by_cases hst : a ≤ f y
  · have hEq := Φ.strip_eq_add_back y t ht.1 hst (by
      have hfy : f y ≤ b - t := by simpa [sublevel] using hy
      linarith)
    calc
      f (Φ.flow (-t) y) = f y + t := hEq
      _ ≤ b := by
        have hfy : f y ≤ b - t := by simpa [sublevel] using hy
        linarith
  · have hfy : f y ≤ b - t := by simpa [sublevel] using hy
    let z : M := Φ.flow (-t) y
    have hmain : f z - t ≤ f y := by
      have hle := (Φ.rate_bound z t ht.1).1
      have hzy : Φ.flow t z = y := by
        dsimp [z]
        have h := congrFun (Φ.flow_add t (-t)) y
        change Φ.flow (t + -t) y = Φ.flow t (Φ.flow (-t) y) at h
        rw [add_neg_cancel] at h
        simpa [Φ.flow_zero] using h.symm
      calc
        f z - t ≤ f (Φ.flow t z) := hle
        _ = f y := by rw [hzy]
    calc
      f (Φ.flow (-t) y) = f z := by rfl
      _ ≤ f y + t := by linarith
      _ ≤ b := by linarith

omit [TopologicalSpace M] in
theorem UnitSpeedFlow.flow_sub_back_le_add (Φ : UnitSpeedFlow f a b)
    {t : ℝ} (ht : 0 ≤ t) (y : M) :
    f (Φ.flow (-t) y) ≤ f y + t := by
  let z : M := Φ.flow (-t) y
  have hmain : f z - t ≤ f y := by
    have hle := (Φ.rate_bound z t ht).1
    have hzy : Φ.flow t z = y := by
      dsimp [z]
      have h := congrFun (Φ.flow_add t (-t)) y
      change Φ.flow (t + -t) y = Φ.flow t (Φ.flow (-t) y) at h
      rw [add_neg_cancel] at h
      simpa [Φ.flow_zero] using h.symm
    calc
      f z - t ≤ f (Φ.flow t z) := hle
      _ = f y := by rw [hzy]
  calc
    f (Φ.flow (-t) y) = f z := by rfl
    _ ≤ f y + t := by linarith

omit [TopologicalSpace M] in
noncomputable def UnitSpeedFlow.sublevelEquiv (Φ : UnitSpeedFlow f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) :
    SublevelSpace f b ≃ SublevelSpace f (b - t) where
  toFun := fun x => ⟨Φ.flow t (x : M), Φ.flow_sublevel (t := t) ht (x := (x : M)) x.2⟩
  invFun := fun y => ⟨Φ.flow (-t) (y : M), Φ.flow_sublevel_back (t := t) ht (y := (y : M)) y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have h := congrFun (Φ.flow_add (-t) t) (x : M)
    change Φ.flow (-t) (Φ.flow t (x : M)) = x.1
    calc
      Φ.flow (-t) (Φ.flow t (x : M)) = (Φ.flow (-t) ∘ Φ.flow t) (x : M) := rfl
      _ = Φ.flow (-t + t) (x : M) := h.symm
      _ = Φ.flow 0 (x : M) := by simp
      _ = (x : M) := Φ.flow_zero (x : M)
  right_inv := by
    intro y
    apply Subtype.ext
    have h := congrFun (Φ.flow_add t (-t)) (y : M)
    change Φ.flow t (Φ.flow (-t) (y : M)) = y.1
    calc
      Φ.flow t (Φ.flow (-t) (y : M)) = (Φ.flow t ∘ Φ.flow (-t)) (y : M) := rfl
      _ = Φ.flow (t + -t) (y : M) := h.symm
      _ = Φ.flow 0 (y : M) := by simp
      _ = (y : M) := Φ.flow_zero (y : M)

omit [TopologicalSpace M] in
theorem UnitSpeedFlow.flow_image_sublevel (Φ : UnitSpeedFlow f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) :
    (fun x : M => Φ.flow t x) '' sublevel f b = sublevel f (b - t) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    exact Φ.flow_sublevel (t := t) ht (x := x) hx
  · intro hy
    refine ⟨Φ.flow (-t) y, Φ.flow_sublevel_back (t := t) ht (y := y) hy, ?_⟩
    have h := congrFun (Φ.flow_add t (-t)) y
    change Φ.flow (t + -t) y = Φ.flow t (Φ.flow (-t) y) at h
    rw [add_neg_cancel] at h
    simpa [Φ.flow_zero] using h.symm

theorem GradientLikeFlow.toDiffeomorph_image_sublevel (Φ : GradientLikeFlow I f a b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (b - a)) :
    Φ.toDiffeomorph t '' sublevel f b = sublevel f (b - t) := by
  rw [show (⇑(Φ.toDiffeomorph t) : M → M) = Φ.flow t from rfl]
  exact Φ.flow_image_sublevel ht

omit [TopologicalSpace M] in
theorem UnitSpeedFlow.image_sublevels (Φ : UnitSpeedFlow f a b) (hab : a ≤ b) :
    (fun x : M => Φ.flow (a - b) x) '' sublevel f a = sublevel f b := by
  have ht : b - a ∈ Set.Icc (0 : ℝ) (b - a) := ⟨sub_nonneg.mpr hab, le_rfl⟩
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    have hb : b - (b - a) = a := by ring
    have hx' : x ∈ sublevel f (b - (b - a)) := by
      simpa [hb] using hx
    have hback := Φ.flow_sublevel_back (t := b - a) ht (y := x) hx'
    have hneg : -(b - a) = a - b := by ring
    simpa [hneg] using hback
  · intro hy
    refine ⟨Φ.flow (b - a) y, ?_, ?_⟩
    · have hsub := Φ.flow_sublevel (t := b - a) ht (x := y) hy
      have hb : b - (b - a) = a := by ring
      simpa [hb] using hsub
    · have h := congrFun (Φ.flow_add (a - b) (b - a)) y
      have hz : (a - b) + (b - a) = 0 := by ring
      calc
        Φ.flow (a - b) (Φ.flow (b - a) y) = (Φ.flow (a - b) ∘ Φ.flow (b - a)) y := rfl
        _ = Φ.flow ((a - b) + (b - a)) y := h.symm
        _ = Φ.flow 0 y := by rw [hz]
        _ = y := Φ.flow_zero y

theorem sublevel_transport_of_unitSpeedVectorField [T2Space M] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] (a b : ℝ) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hdf : ∀ x, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (hab : a ≤ b) :
    (fun x : M => (unitSpeedFlowOfVectorField I a b f hf v hv hdf hcomplete).flow (a - b) x) ''
    sublevel f a = sublevel f b :=
  UnitSpeedFlow.image_sublevels (a := a) (b := b)
    (unitSpeedFlowOfVectorField I a b f hf v hv hdf hcomplete) hab

theorem sublevel_transport_on_set_of_stripUnitSpeedVectorField [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M]
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ) f) {a b : ℝ} (hab : a ≤ b)
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (D : Set M)
    (hdfOn : ∀ x ∈ D ∩ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x ∈ D, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (hpreserve : ∀ t : ℝ, Set.MapsTo (fun x => curveAt v hcomplete x t) D D) :
    (fun x : M => curveAt v hcomplete x (a - b)) '' (D ∩ sublevel f a) = D ∩ sublevel f b := by
  let t : ℝ := b - a
  have ht_def : t = b - a := rfl
  have ht : 0 ≤ t := by dsimp [t]; linarith
  let Φ : ℝ → M → M := fun s x => curveAt v hcomplete x s
  have hΦadd : ∀ s r : ℝ, ∀ x : M, Φ (s + r) x = Φ r (Φ s x) := by
    intro s r x
    exact curveAt_add v hv hcomplete x s r
  have hrate_Φ : ∀ x ∈ D, ∀ s : ℝ, 0 ≤ s → f x - s ≤ f (Φ s x) ∧ f (Φ s x) ≤ f x := by
    intro x hx s hs
    have hrb := f_rate_bounds_of_integralCurve_on_set f hf v D hrate
      (curveAt_integralCurve v hcomplete x) hs (fun u _ => hpreserve u hx)
    simpa [Φ, curveAt_zero v hcomplete x] using hrb
  have hstrip_Φ : ∀ x : M, ∀ s : ℝ, 0 ≤ s →
      (∀ u ∈ Set.Icc (0 : ℝ) s, Φ u x ∈ D ∩ f ⁻¹' Set.Icc a b) →
      f (Φ s x) = f x - s := by
    intro x s hs hstay
    have hd (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) s) :
        HasDerivAt (fun u => f (Φ u x) + u) 0 u := by
      have hfd : HasFDerivAt (fun u => f (Φ u x))
          ((mfderiv I 𝓘(ℝ, ℝ) f (Φ u x)).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ u x)))) u :=
        hasMFDerivAt_iff_hasFDerivAt.mp ((hf (Φ u x)).hasMFDerivAt.comp u
          (curveAt_integralCurve v hcomplete x u))
      have heq := hdfOn (Φ u x) (hstay u hu)
      have hneg : HasDerivAt (fun u => f (Φ u x)) (-1) u := by
        apply hasDerivAt_iff_hasFDerivAt.mpr
        apply hfd.congr_fderiv
        apply ContinuousLinearMap.ext
        intro r
        change (mfderiv I 𝓘(ℝ, ℝ) f (Φ u x)) (r • v (Φ u x)) = r • (-1 : ℝ)
        rw [map_smul]
        exact congrArg (fun z : ℝ => r • z) heq
      simpa only [neg_add_cancel] using! hneg.add (hasDerivAt_id u)
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := s) (f := fun u => f (Φ u x) + u) (f' := fun _ => (0 : ℝ))
      (fun u hu => hd u (by simpa only [Set.uIcc_of_le hs] using hu))
      intervalIntegrable_const
    simp only [intervalIntegral.integral_zero, Φ, curveAt_zero, add_zero] at heq
    linarith
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← hxy]
    refine ⟨hpreserve (a - b) hx.1, ?_⟩
    change f (Φ (a - b) x) ≤ b
    have hγ' : IsMIntegralCurve (fun s : ℝ => Φ (s - t) x) v := by
      have hc := IsMIntegralCurve.comp_add (curveAt_integralCurve v hcomplete x) (-t)
      have hfun : (curveAt v hcomplete x ∘ fun s : ℝ ↦ s + -t) =
          fun s : ℝ ↦ Φ (s - t) x := by
        funext s
        rfl
      rw [← hfun]
      exact hc
    have hrb := f_rate_bounds_of_integralCurve_on_set f hf v D hrate (hγ := hγ')
      (t := t) ht (fun u _ => hpreserve (u - t) hx.1)
    have hmain : f (Φ (-t) x) ≤ f x + t := by
      have h1 : f (Φ (-t) x) - t ≤ f x := by
        simpa [Φ, curveAt_zero v hcomplete x] using hrb.1
      linarith
    have hneg : a - b = -t := by dsimp [t]; ring
    rw [hneg]
    have hx' : f x ≤ a := by simpa [sublevel] using hx.2
    linarith [ht_def]
  · intro hy
    have hflow : f (Φ t y) ≤ a := by
      by_cases hst : a ≤ f y - t
      · have hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, Φ s y ∈ D ∩ f ⁻¹' Set.Icc a b := by
          intro s hs
          have hrb := hrate_Φ y hy.1 s hs.1
          have hfy : f y ≤ b := by simpa [sublevel] using hy.2
          refine ⟨hpreserve s hy.1, ?_⟩
          constructor <;> linarith [hst, hrb.1, hrb.2, hs.2, hfy]
        have heq := hstrip_Φ y t ht hstay
        have hfy : f y ≤ b := by simpa [sublevel] using hy.2
        linarith [heq, hfy, ht_def]
      · by_cases hbelow : f y ≤ a
        · exact (hrate_Φ y hy.1 t ht).2.trans hbelow
        · have hafy : a < f y := lt_of_not_ge hbelow
          let s₀ : ℝ := f y - a
          have hs₀pos : 0 < s₀ := by dsimp [s₀]; linarith
          have hs₀t : s₀ < t := by
            dsimp [s₀]
            linarith
          have hstay₀ : ∀ s ∈ Set.Icc (0 : ℝ) s₀, Φ s y ∈ D ∩ f ⁻¹' Set.Icc a b := by
            intro s hs
            have hrb := hrate_Φ y hy.1 s hs.1
            have hfy : f y ≤ b := by simpa [sublevel] using hy.2
            refine ⟨hpreserve s hy.1, ?_⟩
            constructor <;> linarith [hs.2, hrb.1, hrb.2, hfy]
          have heq₀ := hstrip_Φ y s₀ (le_of_lt hs₀pos) hstay₀
          have hval₀ : f (Φ s₀ y) = a := by
            dsimp [s₀] at heq₀ ⊢
            linarith
          have hrb := hrate_Φ (Φ s₀ y) (hpreserve s₀ hy.1) (t - s₀) (by linarith)
          have hflow' : Φ t y = Φ (t - s₀) (Φ s₀ y) := by
            have hh := hΦadd s₀ (t - s₀) y
            change Φ (s₀ + (t - s₀)) y = Φ (t - s₀) (Φ s₀ y) at hh
            rwa [add_sub_cancel] at hh
          rw [hflow']
          linarith
    refine ⟨Φ t y, ?_, ?_⟩
    · exact ⟨hpreserve t hy.1, hflow⟩
    · have hh := hΦadd t (a - b) y
      have hz : t + (a - b) = 0 := by dsimp [t]; ring
      calc
        Φ (a - b) (Φ t y) = Φ (t + (a - b)) y := hh.symm
        _ = Φ 0 y := by rw [hz]
        _ = y := by dsimp [Φ]; exact curveAt_zero v hcomplete y

theorem sublevel_transport_of_stripUnitSpeedVectorField [I.Boundaryless]
    [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (v : (x : M) → TangentSpace I x)
    (hv : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v) :
    (fun x : M => curveAt v hcomplete x (a - b)) '' sublevel f a = sublevel f b := by
  simpa only [Set.univ_inter] using
    sublevel_transport_on_set_of_stripUnitSpeedVectorField f
      (hf.mdifferentiable (by simp)) hab v hv Set.univ
      (by simpa only [Set.univ_inter] using hdfOn) (fun x _ => hrate x)
      hcomplete (fun _ _ _ => Set.mem_univ _)

theorem sublevel_transport_outside_of_unitSpeedVectorField [I.Boundaryless]
    [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (B : Set M)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b \ B,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    (hfix : ∀ x ∈ B, x ∉ tsupport v) :
    (fun x : M => curveAt v hcomplete x (a - b)) '' (sublevel f a \ B) = sublevel f b \ B := by
  let Φ : ℝ → M → M := fun s x => curveAt v hcomplete x s
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hfixΦ : ∀ x ∈ B, ∀ s : ℝ, Φ s x = x := by
    intro x hx s
    exact curveAt_eq_self_of_not_mem_tsupport v hv hcomplete (hfix x hx) s
  have hinj : ∀ s : ℝ, Function.Injective (Φ s) := by
    intro s
    exact curveAt_injective v hv1 hcomplete s
  have houtside : ∀ x : M, x ∉ B → ∀ s : ℝ, Φ s x ∉ B := by
    intro x hx s hmem
    apply hx
    have hfix2 : Φ s (Φ s x) = Φ s x := hfixΦ _ hmem s
    have hEq : Φ s x = x := hinj s hfix2
    rwa [← hEq]
  have h := sublevel_transport_on_set_of_stripUnitSpeedVectorField f
    (hf.mdifferentiable (by simp)) hab v hv1 Bᶜ
    (fun x hx => hdfOn x ⟨hx.2, hx.1⟩) (fun x _ => hrate x) hcomplete
    (fun s x hx => houtside x hx s)
  simpa only [Set.sdiff_eq, Set.inter_comm] using h

theorem GradientLikeFlow.toDiffeomorph_image_sublevels (Φ : GradientLikeFlow I f a b) (hab : a ≤ b) :
    Φ.toDiffeomorph (a - b) '' sublevel f a = sublevel f b := by
  rw [show (⇑(Φ.toDiffeomorph (a - b)) : M → M) = Φ.flow (a - b) from rfl]
  exact UnitSpeedFlow.image_sublevels Φ.toUnitSpeedFlow hab

noncomputable def linearModelFlow (a b : ℝ) :
    GradientLikeFlow 𝓘(ℝ, MorseModel 1) (fun y : MorseModel 1 => y 0) a b where
  flow := fun t y => (fun _ : Fin 1 => y 0 - t)
  flow_zero := by
    intro y
    funext i
    fin_cases i; simp
  flow_add := by
    intro s t
    funext y
    funext i
    fin_cases i
    change y 0 - (s + t) = (y 0 - t) - s
    ring
  contMDiffAt := by
    intro t x
    exact ContDiffAt.contMDiffAt (f := fun y : MorseModel 1 => (fun _ : Fin 1 => y 0 - t))
      ((contDiff_pi' (fun i : Fin 1 => by fun_prop) :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : MorseModel 1 => (fun _ : Fin 1 => y 0 - t))).contDiffAt)
  contMDiffAt_t := by
    intro x
    exact ContDiffAt.contMDiffAt (f := fun t : ℝ => (fun _ : Fin 1 => x 0 - t))
      ((contDiff_pi' (fun i : Fin 1 => by fun_prop) :
        ContDiff ℝ (⊤ : WithTop ℕ∞) (fun t : ℝ => (fun _ : Fin 1 => x 0 - t))).contDiffAt)
  strip_eq_sub := by
    intro x t ht hst
    rfl
  strip_eq_add_back := by
    intro x t ht h1 h2
    simp [sub_eq_add_neg]
  rate_bound := by
    intro x t ht
    constructor
    · rfl
    · simp [sub_eq_add_neg]
      linarith

theorem linearModelFlow_image_sublevels (a b : ℝ) (hab : a ≤ b) :
    (fun y : MorseModel 1 => (linearModelFlow a b).flow (a - b) y) ''
        sublevel (fun y : MorseModel 1 => y 0) a =
      sublevel (fun y : MorseModel 1 => y 0) b :=
  UnitSpeedFlow.image_sublevels (linearModelFlow a b).toUnitSpeedFlow hab

noncomputable def fin1Homeo : MorseModel 1 ≃ₜ ℝ where
  toFun := fun y => y 0
  invFun := fun r => (fun _ : Fin 1 => r)
  left_inv := by
    intro y
    funext i
    fin_cases i; rfl
  right_inv := by
    intro r
    rfl
  continuous_toFun := continuous_apply (0 : Fin 1)
  continuous_invFun := by
    fun_prop

theorem linearModel_strip_compact (a b : ℝ) :
    IsCompact (sublevelStrip (fun y : MorseModel 1 => y 0) a b) := by
  have hIcc : IsCompact (Set.Icc a b) := isCompact_Icc
  have himg : IsCompact (fin1Homeo.symm '' (Set.Icc a b)) :=
    hIcc.image fin1Homeo.symm.continuous
  have hset : sublevelStrip (fun y : MorseModel 1 => y 0) a b = fin1Homeo.symm '' (Set.Icc a b) := by
    ext y
    constructor
    · intro hy
      refine ⟨y 0, by simpa [sublevelStrip] using hy, ?_⟩
      funext i
      fin_cases i; rfl
    · rintro ⟨r, hr, hry⟩
      change a ≤ y 0 ∧ y 0 ≤ b
      have hy0 : y 0 = r := by
        have h := congrFun hry 0
        simpa [fin1Homeo] using h.symm
      rw [hy0]
      exact hr
  rwa [hset]

theorem linearModel_no_critical (y : MorseModel 1) :
    fderiv ℝ (fun y : MorseModel 1 => y 0) y ≠ 0 := by
  have hfd : fderiv ℝ (fun y : MorseModel 1 => y 0) y = ContinuousLinearMap.proj (0 : Fin 1) := by
    have hlin : IsBoundedLinearMap ℝ (fun y : MorseModel 1 => y 0) :=
      (ContinuousLinearMap.proj (0 : Fin 1) : MorseModel 1 →L[ℝ] ℝ).isBoundedLinearMap
    exact hlin.fderiv
  intro hz
  have hproj_ne : (ContinuousLinearMap.proj (0 : Fin 1) : MorseModel 1 →L[ℝ] ℝ) ≠ 0 := by
    intro h
    simpa using (congrArg (fun L : MorseModel 1 →L[ℝ] ℝ => L (fun _ => (1 : ℝ))) h)
  exact hproj_ne (by simpa [hfd] using hz)

end

end DifferentialGeometry.Topology.Morse
