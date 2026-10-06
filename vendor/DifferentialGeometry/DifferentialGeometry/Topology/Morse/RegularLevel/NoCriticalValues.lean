module

public import DifferentialGeometry.Topology.Morse.RegularLevel.VectorField
public import DifferentialGeometry.Topology.Morse.RegularLevel.Flow
public import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
public import Mathlib.Geometry.Manifold.Diffeomorph

@[expose] public section

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.Analysis.ODE

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}

theorem no_critical_value_transport [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ v : (x : M) → TangentSpace I x,
    ∃ Φ : Diffeomorph I I M M ∞,
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) ∧
        IsCompact (tsupport v) ∧
        (∀ x ∈ f ⁻¹' Set.Icc a b,
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1) ∧
        (∀ x,
          -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) ∧
        (∃ hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v,
          (Φ.toEquiv '' sublevel f a) = sublevel f b ∧
          ∀ x : M, Φ.toEquiv x = curveAt v hcomplete x (a - b)) ∧
        (∀ x : M, f x = a → f (Φ x) = b) ∧
        (∀ x : M, f x < a → f (Φ x) < b) ∧
        (∀ x : M, f x = b → f (Φ.symm x) = a) ∧
        (∀ x : M, f x < b → f (Φ.symm x) < a) := by
  rcases exists_unitSpeedVectorField_on_strip I f hf a b hcompact hregular with
    ⟨v, hv, hsupp, hdfOn, hrate⟩
  have hcomplete := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have htransport := sublevel_transport_of_stripUnitSpeedVectorField (I := I) f hf hab v hv1
    hdfOn hrate hcomplete
  let flow : ℝ → M → M := fun t x => curveAt v hcomplete x t
  let t : ℝ := b - a
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htdef : t = b - a := rfl
  have hflowSmooth : ∀ t : ℝ, ContMDiff I I ∞ (fun x : M => flow t x) := by
    intro t x
    exact contMDiffAt_globalFlow_of_compactSupport v hv hsupp t x
  have hflow0 : ∀ x : M, flow 0 x = x := fun x => by
    dsimp [flow]
    exact curveAt_zero v hcomplete x
  have hflowAdd : ∀ s t : ℝ, ∀ x : M, flow (s + t) x = flow t (flow s x) := fun s t x => by
    dsimp [flow]
    exact curveAt_add v hv1 hcomplete x s t
  let Φ : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := fun x => flow (a - b) x
          invFun := fun x => flow (b - a) x
          left_inv := by
            intro x
            have hh := hflowAdd (a - b) (b - a) x
            calc
              flow (b - a) (flow (a - b) x) = flow ((a - b) + (b - a)) x := hh.symm
              _ = flow 0 x := by rw [show (a - b) + (b - a) = 0 by ring]
              _ = x := hflow0 x
          right_inv := by
            intro x
            have hh := hflowAdd (b - a) (a - b) x
            calc
              flow (a - b) (flow (b - a) x) = flow ((b - a) + (a - b)) x := hh.symm
              _ = flow 0 x := by rw [show (b - a) + (a - b) = 0 by ring]
              _ = x := hflow0 x }
      contMDiff_toFun := hflowSmooth (a - b)
      contMDiff_invFun := hflowSmooth (b - a) }
  have htie : ∀ x : M, Φ.toEquiv x = curveAt v hcomplete x (a - b) := by
    intro x
    dsimp [Φ, flow]
  have hbnd : ∀ x : M, f x = a → f (Φ x) = b := by
    intro x hx
    change f (Φ.toEquiv x) = b
    rw [htie x]
    have hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, flow (-s) x ∈ f ⁻¹' Set.Icc a b := by
      intro s hs
      have hrb := f_rate_bounds_of_integralCurve f hf v hrate
        (hγ := IsMIntegralCurve.comp_add (curveAt_integralCurve v hcomplete x) (-s)) (t := s) hs.1
      have h1 : f (flow (-s) x) - s ≤ f x := by
        have hh := hrb.1
        change f (curveAt v hcomplete x (-s)) - s ≤ f x
        simpa [Function.comp_def, curveAt_zero] using hh
      have h2 : f x ≤ f (flow (-s) x) := by
        have hrb' := f_rate_bounds_of_integralCurve f hf v hrate
          (hγ := curveAt_integralCurve v hcomplete (flow (-s) x)) (t := s) hs.1
        have hh : f (flow s (flow (-s) x)) ≤ f (flow (-s) x) := by
          simpa [flow, curveAt_zero] using hrb'.2
        have hzz : flow s (flow (-s) x) = x := by
          have h := hflowAdd (-s) s x
          change flow ((-s) + s) x = flow s (flow (-s) x) at h
          rw [show (-s) + s = 0 by ring] at h
          simpa [hflow0] using h.symm
        rwa [hzz] at hh
      constructor <;> linarith [h1, h2, hx, hs.2, htdef]
    have hval := f_add_of_integralCurve_back f hf v hdfOn
      (hγ := curveAt_integralCurve v hcomplete x) (t := t) ht hstay
    have htneg : a - b = -t := by dsimp [t]; ring
    rw [htneg]
    change f (curveAt v hcomplete x (-t)) = b
    rw [hval, curveAt_zero]
    calc
      f x + t = a + t := by rw [hx]
      _ = a + (b - a) := by rw [htdef]
      _ = b := by ring
  have hstrict : ∀ x : M, f x < a → f (Φ x) < b := by
    intro x hx
    change f (Φ.toEquiv x) < b
    rw [htie x]
    have htneg : a - b = -t := by dsimp [t]; ring
    rw [htneg]
    have hrb := f_rate_bounds_of_integralCurve f hf v hrate
      (hγ := IsMIntegralCurve.comp_add (curveAt_integralCurve v hcomplete x) (-t)) (t := t) ht
    have h1 : f (curveAt v hcomplete x (-t)) - t ≤ f x := by
      have hh := hrb.1
      simpa [Function.comp_def, curveAt_zero] using hh
    have h2 : f (curveAt v hcomplete x (-t)) ≤ f x + t := by linarith
    linarith [hx, htdef]
  have hbnd' : ∀ x : M, f x = b → f (Φ.symm x) = a := by
    intro x hx
    change f (Φ.toEquiv.symm x) = a
    dsimp [Φ]
    change f (curveAt v hcomplete x (b - a)) = a
    rw [← htdef]
    have hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, flow s x ∈ f ⁻¹' Set.Icc a b := by
      intro s hs
      have hrb := f_rate_bounds_of_integralCurve f hf v hrate
        (hγ := curveAt_integralCurve v hcomplete x) (t := s) hs.1
      have h1 : f (flow s x) ≤ f x := by simpa [flow, curveAt_zero] using hrb.2
      have h2 : f x - s ≤ f (flow s x) := by simpa [flow, curveAt_zero] using hrb.1
      constructor <;> linarith [h1, h2, hx, hs.2, htdef]
    have hval := f_eq_sub_of_integralCurve_on_strip f hf v hdfOn
      (hγ := curveAt_integralCurve v hcomplete x) (t := t) ht hstay
    rw [hval, curveAt_zero]
    calc
      f x - t = b - t := by rw [hx]
      _ = b - (b - a) := by rw [htdef]
      _ = a := by ring
  have hstrict' : ∀ x : M, f x < b → f (Φ.symm x) < a := by
    intro x hx
    change f (Φ.toEquiv.symm x) < a
    have hle : f (Φ.toEquiv.symm x) ≤ a := by
      have himg : Φ.toEquiv.symm '' sublevel f b = sublevel f a := by
        have h := congrArg (fun s : Set M => Φ.toEquiv.symm '' s) htransport
        have hL : Φ.toEquiv.symm '' (Φ.toEquiv '' sublevel f a) = sublevel f a := by
          rw [Set.image_image]
          have hleft : (fun y : M => Φ.toEquiv.symm (Φ.toEquiv y)) = id := by
            funext y
            exact Φ.toEquiv.symm_apply_apply y
          rw [hleft, Set.image_id]
        exact (hL.symm.trans h).symm
      have hmem : Φ.toEquiv.symm x ∈ sublevel f a := by
        rw [← himg]
        exact ⟨x, le_of_lt hx, rfl⟩
      exact hmem
    have hnot : ¬ f (Φ.toEquiv.symm x) = a := by
      intro heq
      have h1 : f (Φ (Φ.symm x)) = b := by
        change f (Φ.toEquiv (Φ.toEquiv.symm x)) = b
        exact hbnd (Φ.toEquiv.symm x) heq
      have h2 : Φ (Φ.symm x) = x := by
        dsimp [Φ, flow]
        have h := hflowAdd (b - a) (a - b) x
        change flow ((b - a) + (a - b)) x = flow (a - b) (flow (b - a) x) at h
        rw [show (b - a) + (a - b) = 0 by ring] at h
        simp
      have hx' : f x = b := by rwa [h2] at h1
      exact (ne_of_lt hx) hx'
    exact lt_of_le_of_ne hle hnot
  refine ⟨v, Φ, hv, hsupp, hdfOn, hrate, ⟨hcomplete, ?_, ?_⟩, hbnd, hstrict, hbnd', hstrict'⟩
  · change (fun x : M => flow (a - b) x) '' sublevel f a = sublevel f b
    simpa [flow] using htransport
  · exact htie

theorem no_critical_values [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ Φ : Diffeomorph I I M M ∞, Φ.toEquiv '' sublevel f a = sublevel f b := by
  rcases no_critical_value_transport (I := I) f hf hab hcompact hregular with
    ⟨v, Φ, hv, hsupp, hdfOn, hrate, ⟨hcomplete, hflow, htie⟩, _hbnd, _hstrict, _hbnd', _hstrict'⟩
  exact ⟨Φ, hflow⟩

theorem reverseFlow_value_on_levelSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ}
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0)
    {x : M} (hx : f x = a) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (b - a)) :
    f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x (-t)) = a + t := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hγ : IsMIntegralCurve (fun s : ℝ => curveAt v hcomplete x (-s)) (-v) := by
    have hc := IsMIntegralCurve.comp_mul (curveAt_integralCurve v hcomplete x) (-1)
    have hcurve : (fun s : ℝ => curveAt v hcomplete x (-s)) =
        curveAt v hcomplete x ∘ fun s : ℝ => s * (-1) := by
      funext s
      congr 1
      ring
    rw [hcurve]
    simpa [Pi.smul_apply] using hc
  have hdneg : ∀ y : M,
      (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) =
        (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (v y)) := by
    intro y
    change mvfderiv (I := I) (-f) y ((-v) y) = mvfderiv (I := I) f y (v y)
    rw [_root_.mvfderiv_neg]
    simp
  have hdfneg : ∀ y ∈ (-f) ⁻¹' Set.Icc (-b) (-a),
      (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) = -1 := by
    intro y hy
    rw [hdneg y]
    apply hdfOn
    change a ≤ f y ∧ f y ≤ b
    have h1 : a ≤ f y := (neg_le_neg_iff.mp hy.2)
    have h2 : f y ≤ b := (neg_le_neg_iff.mp hy.1)
    exact ⟨h1, h2⟩
  have hrateneg : ∀ y : M,
      -1 ≤ (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) ∧
        (NormedSpace.fromTangentSpace (-f y)) ((mfderiv I 𝓘(ℝ, ℝ) (-f) y) ((-v) y)) ≤ 0 := by
    intro y
    rw [hdneg y]
    exact hrate y
  have hstay : ∀ s ∈ Set.Icc (0 : ℝ) t, curveAt v hcomplete x (-s) ∈ f ⁻¹' Set.Icc a b := by
    intro s hs
    have hrb := f_rate_bounds_of_integralCurve (-f) hf.neg (-v) hrateneg (hγ := hγ) (t := s) hs.1
    have hxval : f (curveAt v hcomplete x (-0)) = a := by
      simpa [curveAt_zero v hcomplete x] using hx
    constructor
    · have hb : -f (curveAt v hcomplete x (-s)) ≤ -f (curveAt v hcomplete x (-0)) := hrb.2
      have hb' : -f (curveAt v hcomplete x (-s)) ≤ -a := by
        rw [← hxval]
        exact hb
      exact (neg_le_neg_iff.mp hb')
    · have hb : -f (curveAt v hcomplete x (-0)) - s ≤ -f (curveAt v hcomplete x (-s)) := hrb.1
      have hb' : -a - s ≤ -f (curveAt v hcomplete x (-s)) := by
        rw [← hxval]
        exact hb
      have hle : f (curveAt v hcomplete x (-s)) ≤ a + s := by linarith
      exact le_trans hle (by linarith [hs.2, ht.2])
  have hstay' : ∀ s ∈ Set.Icc (0 : ℝ) t, curveAt v hcomplete x (-s) ∈ (-f) ⁻¹' Set.Icc (-b) (-a) := by
    intro s hs
    have hmem := hstay s hs
    change -b ≤ -f (curveAt v hcomplete x (-s)) ∧ -f (curveAt v hcomplete x (-s)) ≤ -a
    exact ⟨neg_le_neg hmem.2, neg_le_neg_iff.mpr hmem.1⟩
  have heq := f_eq_sub_of_integralCurve_on_strip (a := -b) (b := -a) (-f) hf.neg (-v) hdfneg
    (hγ := hγ) (t := t) ht.1 hstay'
  have hmain : -f (curveAt v hcomplete x (-t)) = -f (curveAt v hcomplete x (-0)) - t := heq
  have hxval : f (curveAt v hcomplete x (-0)) = a := by
    simpa [curveAt_zero v hcomplete x] using hx
  have hneg : -f (curveAt v hcomplete x (-t)) = -a - t := by
    rw [hxval] at hmain
    exact hmain
  linarith

noncomputable def noCriticalValueSublevelHomeomorph [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    SublevelSpace f a ≃ₜ SublevelSpace f b := by
  let htrans := no_critical_values (I := I) f hf hab hcompact hregular
  let Φ : Diffeomorph I I M M ∞ := Classical.choose htrans
  have hflow : Φ.toEquiv '' sublevel f a = sublevel f b := Classical.choose_spec htrans
  refine
    { toFun := fun x : SublevelSpace f a => ⟨Φ.toEquiv x.1, by
        have hmem : Φ.toEquiv x.1 ∈ Φ.toEquiv '' sublevel f a := ⟨x.1, x.2, rfl⟩
        rw [hflow] at hmem
        exact hmem⟩
      invFun := fun y : SublevelSpace f b => ⟨Φ.toEquiv.symm y.1, by
        have hmem : y.1 ∈ Φ.toEquiv '' sublevel f a := by
          rw [hflow]
          exact y.2
        rcases hmem with ⟨z, hz, hzΦ⟩
        have hz' : Φ.toEquiv.symm y.1 = z := by
          rw [← hzΦ]
          exact Φ.toEquiv.left_inv z
        change f (Φ.toEquiv.symm y.1) ≤ a
        rw [hz']
        change f z ≤ a at hz
        exact hz⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact Φ.toEquiv.left_inv x.1
      right_inv := by
        intro y
        apply Subtype.ext
        exact Φ.toEquiv.right_inv y.1
      continuous_toFun := by
        have hc : Continuous (fun x : SublevelSpace f a => Φ.toEquiv x.1) :=
          Φ.contMDiff_toFun.continuous.comp continuous_subtype_val
        exact Continuous.subtype_mk hc (by
          intro x
          have hmem : Φ.toEquiv x.1 ∈ Φ.toEquiv '' sublevel f a := ⟨x.1, x.2, rfl⟩
          rw [hflow] at hmem
          exact hmem)
      continuous_invFun := by
        have hc : Continuous (fun y : SublevelSpace f b => Φ.toEquiv.symm y.1) :=
          Φ.contMDiff_invFun.continuous.comp continuous_subtype_val
        exact Continuous.subtype_mk hc (by
          intro y
          have hmem : y.1 ∈ Φ.toEquiv '' sublevel f a := by
            rw [hflow]
            exact y.2
          rcases hmem with ⟨z, hz, hzΦ⟩
          have hz' : Φ.toEquiv.symm y.1 = z := by
            rw [← hzΦ]
            exact Φ.toEquiv.left_inv z
          change f (Φ.toEquiv.symm y.1) ≤ a
          rw [hz']
          change f z ≤ a at hz
          exact hz) }

noncomputable def levelSetTransportHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a ≤ b)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) :
    (f ⁻¹' {a}) ≃ₜ (f ⁻¹' {b}) := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hto : ∀ x : f ⁻¹' {a}, f (curveAt v hcomplete x.1 (a - b)) = b := by
    intro x
    have ht : b - a ∈ Set.Icc (0 : ℝ) (b - a) := by
      constructor
      · exact sub_nonneg.mpr hab
      · rfl
    have hval := reverseFlow_value_on_levelSet (I := I) (f := f) (hf := hf) (v := v) (hv := hv)
      (hsupp := hsupp) (hdfOn := hdfOn) (hrate := hrate) (x := x.1) (by exact x.2) (t := b - a) ht
    have hmain : f (curveAt v hcomplete x.1 (-(b - a))) = a + (b - a) := hval
    have hneg : -(b - a) = a - b := by ring
    rw [hneg] at hmain
    linarith
  have hfrom : ∀ y : f ⁻¹' {b}, f (curveAt v hcomplete y.1 (b - a)) = a := by
    intro y
    have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (b - a), curveAt v hcomplete y.1 s ∈ f ⁻¹' Set.Icc a b := by
      intro s hs
      have hrb := f_rate_bounds_of_integralCurve f hf v hrate
        (hγ := curveAt_integralCurve v hcomplete y.1) (t := s) hs.1
      constructor
      · change a ≤ f (curveAt v hcomplete y.1 s)
        have hle : a ≤ f y.1 - s := by
          have hy : f y.1 = b := y.2
          linarith [hs.2, hy]
        exact le_trans hle (by simpa [curveAt_zero v hcomplete y.1] using hrb.1)
      · change f (curveAt v hcomplete y.1 s) ≤ b
        exact le_trans (b := f y.1) (by simpa [curveAt_zero v hcomplete y.1] using hrb.2)
          (by change f y.1 ≤ b; exact le_of_eq y.2)
    have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
      (hγ := curveAt_integralCurve v hcomplete y.1) (t := b - a) (by linarith) hstay
    have hmain : f (curveAt v hcomplete y.1 (b - a)) = f y.1 - (b - a) := by
      simpa [curveAt_zero v hcomplete y.1] using heq
    have hy : f y.1 = b := y.2
    linarith
  let toFun : f ⁻¹' {a} → f ⁻¹' {b} :=
    fun x => ⟨curveAt v hcomplete x.1 (a - b), hto x⟩
  let invFun : f ⁻¹' {b} → f ⁻¹' {a} :=
    fun y => ⟨curveAt v hcomplete y.1 (b - a), hfrom y⟩
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro x
        apply Subtype.ext
        have hh := curveAt_add v hv1 hcomplete x.1 (a - b) (b - a)
        have hz : (a - b) + (b - a) = 0 := by ring
        rw [hz] at hh
        simpa [curveAt_zero v hcomplete x.1, toFun, invFun] using hh.symm
      right_inv := by
        intro y
        apply Subtype.ext
        have hh := curveAt_add v hv1 hcomplete y.1 (b - a) (a - b)
        have hz : (b - a) + (a - b) = 0 := by ring
        rw [hz] at hh
        simpa [curveAt_zero v hcomplete y.1, toFun, invFun] using hh.symm
      continuous_toFun := by
        have hjointc : Continuous (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) :=
          (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).continuous
        have hpair : Continuous (fun x : f ⁻¹' {a} => (a - b, x.1)) :=
          continuous_const.prodMk continuous_subtype_val
        have hmain : Continuous (fun x : f ⁻¹' {a} => curveAt v hcomplete x.1 (a - b)) :=
          hjointc.comp hpair
        exact Continuous.subtype_mk hmain (by intro x; exact hto x)
      continuous_invFun := by
        have hjointc : Continuous (fun p : ℝ × M => curveAt v hcomplete p.2 p.1) :=
          (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).continuous
        have hpair : Continuous (fun y : f ⁻¹' {b} => (b - a, y.1)) :=
          continuous_const.prodMk continuous_subtype_val
        have hmain : Continuous (fun y : f ⁻¹' {b} => curveAt v hcomplete y.1 (b - a)) :=
          hjointc.comp hpair
        exact Continuous.subtype_mk hmain (by intro y; exact hfrom y) }

theorem frontier_sublevel_eq_levelSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ} (hab : a < b)
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) :
    frontier (sublevel f a) = f ⁻¹' {a} := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hjoint : Continuous (fun p : ℝ × M =>
      curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) :=
    (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).continuous
  apply le_antisymm
  · intro x hx
    by_contra hne
    have hfne : f x ≠ a := by
      change f x = a → False
      exact hne
    have hlt_or_gt : f x < a ∨ a < f x := lt_or_gt_of_ne hfne
    rcases hlt_or_gt with hlt | hgt
    · have hmem : x ∈ interior (sublevel f a) := by
        rw [mem_interior]
        exact ⟨{y : M | f y < a}, by
          intro y hy
          change f y ≤ a
          exact le_of_lt hy, isOpen_lt hf.continuous continuous_const, hlt⟩
      exact hx.2 hmem
    · have hmem : x ∉ closure (sublevel f a) := by
        have hopen : IsOpen {y : M | f y > a} :=
          isOpen_lt continuous_const hf.continuous
        intro hcl
        rcases mem_closure_iff.mp hcl {y : M | f y > a} hopen hgt with ⟨y, hyU, hyS⟩
        exact (not_le_of_gt hyU) (by
          change f y ≤ a
          exact hyS)
      exact hmem hx.1
  · intro x hx
    constructor
    · exact subset_closure (by
        change f x ≤ a
        exact le_of_eq hx)
    · have hiff : x ∈ closure (sublevel f a)ᶜ ↔ x ∈ (interior (sublevel f a))ᶜ := by
        calc
          x ∈ closure (sublevel f a)ᶜ ↔ x ∈ (interior ((sublevel f a)ᶜ)ᶜ)ᶜ := by
            rw [closure_eq_compl_interior_compl (s := (sublevel f a)ᶜ)]
          _ ↔ x ∈ (interior (sublevel f a))ᶜ := by
            rw [compl_compl (x := sublevel f a)]
      have hxcompl : x ∈ closure (sublevel f a)ᶜ := by
        rw [mem_closure_iff]
        intro U hUopen hxU
        have hcont_at : ContinuousAt (fun t : ℝ => curveAt v hcomplete x (-t)) 0 := by
          have hpair : ContinuousAt (fun t : ℝ => (-t, x)) 0 := by
            exact (continuousAt_id.neg).prodMk continuousAt_const
          have hcomp := hjoint.continuousAt.comp hpair
          simpa [Function.comp_def] using hcomp
        have hev : ∀ᶠ t in nhds (0 : ℝ), curveAt v hcomplete x (-t) ∈ U :=
          hcont_at.tendsto.eventually
            (hUopen.mem_nhds (by simpa [curveAt_zero v hcomplete x] using hxU))
        rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hδmem⟩
        let t : ℝ := min (δ / 2) (b - a)
        have htpos : 0 < t := by
          dsimp [t]
          exact lt_min (div_pos hδ (by norm_num)) (sub_pos.mpr hab)
        have htmem : t ∈ Set.Icc (0 : ℝ) (b - a) := by
          dsimp [t]
          constructor
          · exact le_of_lt htpos
          · exact min_le_right (δ / 2) (b - a)
        have hvalue := reverseFlow_value_on_levelSet (I := I) (f := f) (hf := hf) (v := v) (hv := hv)
          (hsupp := hsupp) (hdfOn := hdfOn) (hrate := hrate) (x := x) hx (t := t) htmem
        have hgt : a < f (curveAt v hcomplete x (-t)) := by
          have hval : f (curveAt v hcomplete x (-t)) = a + t := hvalue
          linarith [htpos]
        have htltδ : |t| < δ := by
          dsimp [t]
          rw [abs_of_nonneg (le_of_lt htpos)]
          exact lt_of_le_of_lt (min_le_left (δ / 2) (b - a)) (by linarith [hδ])
        have hball : curveAt v hcomplete x (-t) ∈ U := by
          exact hδmem (by simpa [dist_eq_norm, Real.norm_eq_abs] using htltδ)
        exact ⟨curveAt v hcomplete x (-t), ⟨hball, by
          change ¬ f (curveAt v hcomplete x (-t)) ≤ a
          exact not_le_of_gt hgt⟩⟩
      exact hiff.mp hxcompl

noncomputable def levelSetCollarHomeomorph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [IsManifold I ∞ M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) {a b : ℝ}
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hdfOn : ∀ x ∈ f ⁻¹' Set.Icc a b,
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) = -1)
    (hrate : ∀ x,
      -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ∧
      (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (v x)) ≤ 0) :
    (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) ≃ₜ
      {x : M // x ∈ sublevel f b ∧ a ≤ f x} := by
  let hcomplete : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v :=
    exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  let hfval : ∀ {x : M}, f x = a → ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) (b - a) →
      f (curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x (-t)) = a + t :=
    reverseFlow_value_on_levelSet (I := I) (hf := hf) (v := v) (hv := hv)
      (hsupp := hsupp) (hdfOn := hdfOn) (hrate := hrate)
  let toCollar : (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) → {x : M // x ∈ sublevel f b ∧ a ≤ f x} :=
    fun p => ⟨curveAt v hcomplete p.1.1 (-(p.2 : ℝ)), by
      have hfval' := hfval p.1.2 ⟨p.2.2.1, p.2.2.2⟩
      have hval : f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) = a + (p.2 : ℝ) := hfval'
      have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
      have ht1 : (p.2 : ℝ) ≤ b - a := p.2.2.2
      constructor
      · simpa [sublevel] using (show f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) ≤ b by
          linarith [hval, ht1])
      · linarith [hval, ht0]⟩
  let fromCollar : {x : M // x ∈ sublevel f b ∧ a ≤ f x} →
      (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) :=
    fun z => ⟨⟨curveAt v hcomplete z.1 (f z.1 - a), by
      have hmem : z.1 ∈ f ⁻¹' Set.Icc a b := by
        change a ≤ f z.1 ∧ f z.1 ≤ b
        exact ⟨z.2.2, z.2.1⟩
      have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (f z.1 - a), curveAt v hcomplete z.1 s ∈ f ⁻¹' Set.Icc a b := by
        intro s hs
        have hrb := f_rate_bounds_of_integralCurve f hf v hrate
          (hγ := curveAt_integralCurve v hcomplete z.1) (t := s) hs.1
        constructor
        · change a ≤ f (curveAt v hcomplete z.1 s)
          have hle : a ≤ f z.1 - s := by linarith [hs.2]
          exact le_trans hle (by simpa [curveAt_zero v hcomplete z.1] using hrb.1)
        · change f (curveAt v hcomplete z.1 s) ≤ b
          exact le_trans hrb.2 (by
            rw [curveAt_zero v hcomplete z.1]
            have hzle := z.2.1
            change f z.1 ≤ b at hzle
            exact hzle)
      have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
        (hγ := curveAt_integralCurve v hcomplete z.1) (t := f z.1 - a) (by linarith [z.2.2]) hstay
      have hmain : f (curveAt v hcomplete z.1 (f z.1 - a)) = f z.1 - (f z.1 - a) := by
        simpa [curveAt_zero v hcomplete z.1] using heq
      simp [hmain]⟩, ⟨f z.1 - a, by
        constructor
        · exact sub_nonneg.mpr z.2.2
        · exact sub_le_sub_right z.2.1 a⟩⟩
  refine
    { toFun := toCollar
      invFun := fromCollar
      left_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          change curveAt v hcomplete (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) (f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) - a) =
            p.1.1
          have hfval' := hfval p.1.2 ⟨p.2.2.1, p.2.2.2⟩
          have hval : f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) = a + (p.2 : ℝ) := hfval'
          rw [hval]
          have hh := curveAt_add v hv1 hcomplete p.1.1 (-(p.2 : ℝ)) (p.2 : ℝ)
          have hz : -(p.2 : ℝ) + (p.2 : ℝ) = 0 := by ring
          rw [hz] at hh
          simpa [curveAt_zero v hcomplete p.1.1] using hh.symm
        · apply Subtype.ext
          change f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) - a = (p.2 : ℝ)
          have hfval' := hfval p.1.2 ⟨p.2.2.1, p.2.2.2⟩
          linarith
      right_inv := by
        intro z
        apply Subtype.ext
        change curveAt v hcomplete (curveAt v hcomplete z.1 (f z.1 - a)) (-(f z.1 - a)) = z.1
        have hh := curveAt_add v hv1 hcomplete z.1 (f z.1 - a) (-(f z.1 - a))
        have hz : (f z.1 - a) + (-(f z.1 - a)) = 0 := by ring
        rw [hz] at hh
        simpa [curveAt_zero v hcomplete z.1] using hh.symm
      continuous_toFun := by
        have hjoint := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
        have hjointc : Continuous (fun p : ℝ × M =>
            curveAt v hcomplete p.2 p.1) := hjoint.continuous
        have hpair : Continuous (fun p : (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) =>
            (-(p.2 : ℝ), p.1.1)) := by
          fun_prop
        have hmain : Continuous (fun p : (f ⁻¹' {a}) × Set.Icc (0 : ℝ) (b - a) =>
            curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) :=
          hjointc.comp hpair
        exact Continuous.subtype_mk hmain (by
          intro p
          have hfval' := hfval p.1.2 ⟨p.2.2.1, p.2.2.2⟩
          have hval : f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) = a + (p.2 : ℝ) := hfval'
          have ht0 : 0 ≤ (p.2 : ℝ) := p.2.2.1
          have ht1 : (p.2 : ℝ) ≤ b - a := p.2.2.2
          constructor
          · simpa [sublevel] using (show f (curveAt v hcomplete p.1.1 (-(p.2 : ℝ))) ≤ b by
              linarith [hval, ht1])
          · linarith [hval, ht0])
      continuous_invFun := by
        have hjoint := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
        have hjointc : Continuous (fun p : ℝ × M =>
            curveAt v hcomplete p.2 p.1) := hjoint.continuous
        have hpair : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            (f z.1 - a, z.1)) := by
          exact ((hf.continuous.comp continuous_subtype_val).sub continuous_const).prodMk continuous_subtype_val
        have hmain : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            curveAt v hcomplete z.1 (f z.1 - a)) :=
          hjointc.comp hpair
        have hfst : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} => f z.1 - a) := by
          exact (hf.continuous.comp continuous_subtype_val).sub continuous_const
        have htime : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            (⟨f z.1 - a, by
              constructor
              · exact sub_nonneg.mpr z.2.2
              · exact sub_le_sub_right z.2.1 a⟩ : Set.Icc (0 : ℝ) (b - a))) := by
          exact Continuous.subtype_mk hfst (by
            intro z
            constructor
            · exact sub_nonneg.mpr z.2.2
            · exact sub_le_sub_right z.2.1 a)
        have hsrc : Continuous (fun z : {x : M // x ∈ sublevel f b ∧ a ≤ f x} =>
            (⟨curveAt v hcomplete z.1 (f z.1 - a), by
              have hmem : z.1 ∈ f ⁻¹' Set.Icc a b := by
                change a ≤ f z.1 ∧ f z.1 ≤ b
                exact ⟨z.2.2, z.2.1⟩
              have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (f z.1 - a), curveAt v hcomplete z.1 s ∈ f ⁻¹' Set.Icc a b := by
                intro s hs
                have hrb := f_rate_bounds_of_integralCurve f hf v hrate
                  (hγ := curveAt_integralCurve v hcomplete z.1) (t := s) hs.1
                constructor
                · change a ≤ f (curveAt v hcomplete z.1 s)
                  have hle : a ≤ f z.1 - s := by linarith [hs.2]
                  exact le_trans hle (by simpa [curveAt_zero v hcomplete z.1] using hrb.1)
                · change f (curveAt v hcomplete z.1 s) ≤ b
                  exact le_trans hrb.2 (by
                    rw [curveAt_zero v hcomplete z.1]
                    have hzle := z.2.1
                    change f z.1 ≤ b at hzle
                    exact hzle)
              have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
                (hγ := curveAt_integralCurve v hcomplete z.1) (t := f z.1 - a) (by linarith [z.2.2]) hstay
              have hmain' : f (curveAt v hcomplete z.1 (f z.1 - a)) = f z.1 - (f z.1 - a) := by
                simpa [curveAt_zero v hcomplete z.1] using heq
              simp [hmain']⟩ : f ⁻¹' {a})) := by
          exact Continuous.subtype_mk hmain (by
            intro z
            have hmem : z.1 ∈ f ⁻¹' Set.Icc a b := by
              change a ≤ f z.1 ∧ f z.1 ≤ b
              exact ⟨z.2.2, z.2.1⟩
            have hstay : ∀ s ∈ Set.Icc (0 : ℝ) (f z.1 - a), curveAt v hcomplete z.1 s ∈ f ⁻¹' Set.Icc a b := by
              intro s hs
              have hrb := f_rate_bounds_of_integralCurve f hf v hrate
                (hγ := curveAt_integralCurve v hcomplete z.1) (t := s) hs.1
              constructor
              · change a ≤ f (curveAt v hcomplete z.1 s)
                have hle : a ≤ f z.1 - s := by linarith [hs.2]
                exact le_trans hle (by simpa [curveAt_zero v hcomplete z.1] using hrb.1)
              · change f (curveAt v hcomplete z.1 s) ≤ b
                exact le_trans hrb.2 (by
                  rw [curveAt_zero v hcomplete z.1]
                  have hzle := z.2.1
                  change f z.1 ≤ b at hzle
                  exact hzle)
            have heq := f_eq_sub_of_integralCurve_on_strip (a := a) (b := b) f hf v hdfOn
              (hγ := curveAt_integralCurve v hcomplete z.1) (t := f z.1 - a) (by linarith [z.2.2]) hstay
            have hmain' : f (curveAt v hcomplete z.1 (f z.1 - a)) = f z.1 - (f z.1 - a) := by
              simpa [curveAt_zero v hcomplete z.1] using heq
            simp [hmain'])
        exact hsrc.prodMk htime }

end

end DifferentialGeometry.Topology.Morse
