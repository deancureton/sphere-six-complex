module

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Tactic
public import SphereSixComplex.Periods.EstablishedModularUniformization

public section

open Filter Function Set
open scoped Topology

namespace AnalyticLocalHomeo

/-- A complex-analytic function which is injective on an open neighborhood has nonzero
derivative. -/
theorem AnalyticAt.deriv_ne_zero_of_exists_open_injOn
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hinj : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U.InjOn f) : deriv f z ≠ 0 := by
  intro hderiv
  let g : ℂ → ℂ := fun w ↦ f w - f z
  have hg : AnalyticAt ℂ g z := hf.sub (by fun_prop)
  have hg_zero : g z = 0 := by simp [g]
  obtain ⟨U, hU_open, hzU, hU_inj⟩ := hinj
  have hg_not_eventually_zero : ¬ ∀ᶠ w in nhds z, g w = 0 := by
    intro hzero
    have hU_ne : ∀ᶠ w in nhdsWithin z ({z} : Set ℂ)ᶜ, w ∈ U :=
      mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hzU)
    have hzero_ne : ∀ᶠ w in nhdsWithin z ({z} : Set ℂ)ᶜ, g w = 0 :=
      hzero.filter_mono nhdsWithin_le_nhds
    have hw_ne : ∀ᶠ w in nhdsWithin z ({z} : Set ℂ)ᶜ, w ≠ z := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      simpa using hw
    obtain ⟨w, hwU, hwzero, hwz⟩ := (hU_ne.and (hzero_ne.and hw_ne)).exists
    apply hwz
    apply hU_inj hwU hzU
    exact sub_eq_zero.mp hwzero
  have horder_ne_top : analyticOrderAt g z ≠ ⊤ := by
    intro htop
    exact hg_not_eventually_zero (analyticOrderAt_eq_top.mp htop)
  let n : ℕ := analyticOrderNatAt g z
  have horder : analyticOrderAt g z = (n : ℕ∞) := by
    simpa [n] using (Nat.cast_analyticOrderNatAt horder_ne_top).symm
  have hn_ne_zero : n ≠ 0 := by
    intro hn
    have : analyticOrderAt g z = 0 := by simpa [hn] using horder
    exact (hg.analyticOrderAt_ne_zero.mpr hg_zero) this
  have hg_deriv : deriv g z = 0 := by
    have hgf : HasDerivAt g (deriv f z) z := by
      simpa [g] using hf.differentiableAt.hasDerivAt.sub_const (f z)
    rw [hgf.deriv, hderiv]
  have hn_two : 2 ≤ n := by
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_ne_zero
    by_contra hn_not
    have hn_one : n = 1 := by omega
    have horder_one : analyticOrderAt g z = (1 : ℕ∞) := by
      simpa only [hn_one, Nat.cast_one] using horder
    have hdata := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mp horder_one
    exact hdata.2 (by simpa [iteratedDeriv_one] using hg_deriv)
  obtain ⟨k, hk, hkz, hg_factor⟩ :=
    (hg.analyticOrderAt_eq_natCast (n := n)).mp horder
  let r : ℂ → ℂ := fun w ↦ (k w / k z) ^ ((n : ℂ)⁻¹)
  have hratio : AnalyticAt ℂ (fun w ↦ k w / k z) z :=
    hk.div (by fun_prop) hkz
  have hr : AnalyticAt ℂ r z := by
    apply hratio.cpow (by fun_prop)
    simp [div_self hkz, Complex.one_mem_slitPlane]
  have hr_z : r z = 1 := by simp [r, hkz]
  have hr_pow (w : ℂ) : r w ^ n = k w / k z := by
    simpa [r] using Complex.cpow_nat_inv_pow (k w / k z) hn_ne_zero
  have hk_eq (w : ℂ) : k w = k z * r w ^ n := by
    rw [hr_pow]
    field_simp
  let h : ℂ → ℂ := fun w ↦ (w - z) * r w
  have hh : AnalyticAt ℂ h z :=
    (analyticAt_id.sub (by fun_prop)).mul hr
  have hh_z : h z = 0 := by simp [h]
  have hh_deriv : deriv h z = 1 := by
    have hleft : HasDerivAt (fun w : ℂ ↦ w - z) 1 z :=
      (hasDerivAt_id z).sub_const z
    have hprod := hleft.mul hr.differentiableAt.hasDerivAt
    change deriv ((fun w : ℂ ↦ w - z) * r) z = 1
    simpa only [Pi.mul_apply, hr_z, one_mul, sub_self, zero_mul, add_zero] using hprod.deriv
  have hh_strict : HasStrictDerivAt h 1 z := by
    simpa [hh_deriv] using hh.hasStrictDerivAt
  let inv : ℂ → ℂ := hh_strict.localInverse h 1 z one_ne_zero
  have hinv_tendsto : Tendsto inv (nhds 0) (nhds z) := by
    simpa [inv, hh_z] using
      (hh_strict.hasStrictFDerivAt_equiv one_ne_zero).localInverse_tendsto
  have hright : ∀ᶠ q in nhds 0, h (inv q) = q := by
    simpa [inv, hh_z] using hh_strict.eventually_right_inverse one_ne_zero
  have hnormal : ∀ᶠ w in nhds z, g w = k z * h w ^ n := by
    filter_upwards [hg_factor] with w hw
    rw [hw, hk_eq]
    simp only [h]
    rw [mul_pow]
    ring
  have hgood : ∀ᶠ q in nhds 0,
      inv q ∈ U ∧ g (inv q) = k z * h (inv q) ^ n ∧ h (inv q) = q := by
    filter_upwards [hinv_tendsto.eventually (hU_open.mem_nhds hzU),
      hinv_tendsto.eventually hnormal, hright] with q hqU hqnormal hqright
    exact ⟨hqU, hqnormal, hqright⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ_primitive : IsPrimitiveRoot ζ n := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp n hn_ne_zero
  have hζ_pow : ζ ^ n = 1 := hζ_primitive.pow_eq_one
  have hζ_ne_one : ζ ≠ 1 := hζ_primitive.ne_one (by omega)
  have hζ_tendsto : Tendsto (fun q : ℂ ↦ ζ * q) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun q : ℂ ↦ ζ * q) 0 := by fun_prop
    simpa only [ContinuousAt, mul_zero] using hc
  have hgoodζ : ∀ᶠ q in nhds 0,
      inv (ζ * q) ∈ U ∧
        g (inv (ζ * q)) = k z * h (inv (ζ * q)) ^ n ∧
        h (inv (ζ * q)) = ζ * q :=
    hζ_tendsto.eventually hgood
  have hq_ne : ∀ᶠ q in nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ, q ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    simpa using hq
  obtain ⟨q, ⟨hqgood, hqgoodζ⟩, hq0⟩ :=
    ((hgood.and hgoodζ).filter_mono nhdsWithin_le_nhds |>.and hq_ne).exists
  rcases hqgood with ⟨haU, hga, hha⟩
  rcases hqgoodζ with ⟨hbU, hgb, hhb⟩
  have hab_ne : inv q ≠ inv (ζ * q) := by
    intro hab
    have hqeq : q = ζ * q := by
      calc
        q = h (inv q) := hha.symm
        _ = h (inv (ζ * q)) := congrArg h hab
        _ = ζ * q := hhb
    have : ζ = 1 := by
      apply mul_right_cancel₀ hq0
      simpa using hqeq.symm
    exact hζ_ne_one this
  have hg_eq : g (inv q) = g (inv (ζ * q)) := by
    rw [hga, hgb, hha, hhb, mul_pow, hζ_pow, one_mul]
  have hf_eq : f (inv q) = f (inv (ζ * q)) := by
    simpa [g] using hg_eq
  exact hab_ne (hU_inj haU hbU hf_eq)

/-- A complex-analytic, locally injective function has nonzero derivative. -/
theorem AnalyticAt.deriv_ne_zero_of_isLocallyInjective
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hinj : IsLocallyInjective f) : deriv f z ≠ 0 :=
  AnalyticAt.deriv_ne_zero_of_exists_open_injOn hf (hinj z)

/-- A complex-analytic local homeomorphism has nonzero derivative. -/
theorem AnalyticAt.deriv_ne_zero_of_isLocalHomeomorph
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hhomeo : IsLocalHomeomorph f) : deriv f z ≠ 0 :=
  AnalyticAt.deriv_ne_zero_of_isLocallyInjective hf hhomeo.isLocallyInjective

end AnalyticLocalHomeo

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

/-- The ambient derivative of a complex local uniformizer on the upper half-plane is nonzero. -/
lemma deriv_ne_zero_of_isLocalDiffeomorphAt
    {u : UpperHalfPlane → ℂ} {c : UpperHalfPlane}
    (hu : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ u c) :
    deriv (u ∘ UpperHalfPlane.ofComplex) c ≠ 0 := by
  have huDiff : DifferentiableAt ℂ (u ∘ UpperHalfPlane.ofComplex) c :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hu.mdifferentiableAt (by simp))
  let v : ℂ → UpperHalfPlane := hu.localInverse
  have hvMD : MDiffAt v (u c) := hu.localInverse_mdifferentiableAt (by simp)
  have hvMD' : MDiffAt (fun w ↦ (v w : ℂ)) (u c) :=
    UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt.comp (u c) hvMD
  have hvDiff : DifferentiableAt ℂ (fun w ↦ (v w : ℂ)) (u c) :=
    hvMD'.differentiableAt
  have hleft : v ∘ u =ᶠ[nhds c] id := hu.localInverse_eventuallyEq_left
  have hcomp :
      (fun w : ℂ ↦ (v (u (UpperHalfPlane.ofComplex w)) : ℂ)) =ᶠ[nhds (c : ℂ)] id := by
    have hof : Filter.Tendsto UpperHalfPlane.ofComplex (nhds (c : ℂ)) (nhds c) := by
      have hof' := (UpperHalfPlane.mdifferentiableAt_ofComplex c.im_pos).continuousAt
      change Filter.Tendsto UpperHalfPlane.ofComplex (nhds (c : ℂ))
        (nhds (UpperHalfPlane.ofComplex (c : ℂ))) at hof'
      rw [UpperHalfPlane.ofComplex_apply c] at hof'
      exact hof'
    have hleft' := hleft.comp_tendsto hof
    have hupper : ∀ᶠ w in nhds (c : ℂ), 0 < w.im :=
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds c.im_pos
    filter_upwards [hleft', hupper] with w hw hwi
    change (v (u (UpperHalfPlane.ofComplex w)) : ℂ) = w
    rw [show v (u (UpperHalfPlane.ofComplex w)) = UpperHalfPlane.ofComplex w by exact hw]
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hwi]
  have hchain :
      deriv (fun w : ℂ ↦ (v (u (UpperHalfPlane.ofComplex w)) : ℂ)) c =
        deriv (fun w ↦ (v w : ℂ)) (u c) *
          deriv (u ∘ UpperHalfPlane.ofComplex) c := by
    let vc : ℂ → ℂ := fun w ↦ (v w : ℂ)
    let uc : ℂ → ℂ := u ∘ UpperHalfPlane.ofComplex
    have hvDiff' : DifferentiableAt ℂ vc (uc c) := by simpa [vc, uc] using hvDiff
    have huDiff' : DifferentiableAt ℂ uc c := by simpa [uc] using huDiff
    simpa [vc, uc, Function.comp_def] using
      (HasDerivAt.comp (c : ℂ) hvDiff'.hasDerivAt huDiff'.hasDerivAt).deriv
  rw [hcomp.deriv_eq, deriv_id] at hchain
  intro hzero
  rw [hzero, mul_zero] at hchain
  exact one_ne_zero hchain

/-- The nominal branch unit is genuinely analytic near the branch point.  Away from the center
this follows by division; at the center it is a structure field. -/
lemma HasExactHolomorphicBranchAt.unit_analyticAt
    {f : UpperHalfPlane → ℂ} {c : UpperHalfPlane} {value : ℂ} {n : ℕ}
    (B : HasExactHolomorphicBranchAt f c value n) (hf : MDiff f) :
    AnalyticAt ℂ (B.unit ∘ UpperHalfPlane.ofComplex) c := by
  obtain ⟨S, hSfactor, hSopen, hcS⟩ := eventually_nhds_iff.mp B.factorization
  let T : Set UpperHalfPlane := S ∩ B.uniformizer_isLocalDiffeomorph.localInverse.target
  have hTopen : IsOpen T := hSopen.inter
    B.uniformizer_isLocalDiffeomorph.localInverse.open_target
  have hcT : c ∈ T := ⟨hcS,
    B.uniformizer_isLocalDiffeomorph.localInverse_mem_target⟩
  have hunitMD (z : UpperHalfPlane) (hzT : z ∈ T) : MDiffAt B.unit z := by
    by_cases hzc : z = c
    · simpa [hzc] using B.unit_holomorphic
    · have hu_ne (w : UpperHalfPlane)
          (hwT : w ∈ T) (hwc : w ≠ c) : B.uniformizer w ≠ 0 := by
        intro huw
        have hleftw := B.uniformizer_isLocalDiffeomorph.localInverse_left_inv hwT.2
        have hleftc := B.uniformizer_isLocalDiffeomorph.localInverse_left_inv hcT.2
        apply hwc
        calc
          w = B.uniformizer_isLocalDiffeomorph.localInverse (B.uniformizer w) := hleftw.symm
          _ = B.uniformizer_isLocalDiffeomorph.localInverse (B.uniformizer c) := by
            congr 1
            exact huw.trans B.uniformizer_center.symm
          _ = c := hleftc
      have heq : B.unit =ᶠ[nhds z]
          fun w ↦ (f w - value) / B.uniformizer w ^ n := by
        have hopen : IsOpen (T \ {c}) := hTopen.sdiff isClosed_singleton
        filter_upwards [hopen.mem_nhds ⟨hzT, by simpa using hzc⟩] with w hw
        have huw := hu_ne w hw.1 (by simpa using hw.2)
        apply (eq_div_iff (pow_ne_zero n huw)).2
        simpa [mul_comm] using (hSfactor w hw.1.1).symm
      have hrhs : MDiffAt (fun w ↦ (f w - value) / B.uniformizer w ^ n) z := by
        have huzLocal : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
            (modelWithCornersSelf ℂ ℂ) ⊤ B.uniformizer z := by
          refine ⟨B.uniformizer_isLocalDiffeomorph.choose, ?_,
            B.uniformizer_isLocalDiffeomorph.choose_spec.2⟩
          exact hzT.2
        have huz := huzLocal.mdifferentiableAt (by simp)
        exact ((hf z).sub mdifferentiableAt_const).div (huz.pow n)
          (pow_ne_zero n (hu_ne z hzT hzc))
      exact heq.mdifferentiableAt_iff.mpr hrhs
  let O : Set ℂ := ((↑) : UpperHalfPlane → ℂ) '' T
  have hOopen : IsOpen O := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap T hTopen
  have hcO : (c : ℂ) ∈ O := ⟨c, hcT, rfl⟩
  have hdiff : DifferentiableOn ℂ (B.unit ∘ UpperHalfPlane.ofComplex) O := by
    rintro _ ⟨z, hzT, rfl⟩
    exact (UpperHalfPlane.mdifferentiableAt_iff.mp (hunitMD z hzT)).differentiableWithinAt
  exact hdiff.analyticAt (hOopen.mem_nhds hcO)

/-- Exact branch data computes the analytic order in the ambient complex chart. -/
lemma HasExactHolomorphicBranchAt.analyticOrderAt
    {f : UpperHalfPlane → ℂ} {c : UpperHalfPlane} {value : ℂ} {n : ℕ}
    (B : HasExactHolomorphicBranchAt f c value n) (hf : MDiff f) :
    analyticOrderAt (fun w : ℂ ↦ f (UpperHalfPlane.ofComplex w) - value) c = n := by
  let u : ℂ → ℂ := B.uniformizer ∘ UpperHalfPlane.ofComplex
  let a : ℂ → ℂ := B.unit ∘ UpperHalfPlane.ofComplex
  have huContDiff : ContDiffAt ℂ ⊤ u c := by
    dsimp only [u]
    exact UpperHalfPlane.contMDiffAt_iff.mp
      B.uniformizer_isLocalDiffeomorph.contMDiffAt
  have huAnalytic : AnalyticAt ℂ u c := huContDiff.analyticAt
  have huZero : u c = 0 := by
    simp only [u, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact B.uniformizer_center
  have huDeriv : deriv u c ≠ 0 := by
    simpa only [u] using
      (deriv_ne_zero_of_isLocalDiffeomorphAt B.uniformizer_isLocalDiffeomorph)
  have huOrder : _root_.analyticOrderAt u c = 1 :=
    huAnalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero huZero huDeriv
  have haAnalytic : AnalyticAt ℂ a c := by
    simpa only [a] using B.unit_analyticAt hf
  have haNe : a c ≠ 0 := by
    simpa only [a, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using B.unit_ne_zero
  have haOrder : _root_.analyticOrderAt a c = 0 :=
    haAnalytic.analyticOrderAt_eq_zero.mpr haNe
  have hfactor :
      (fun w : ℂ ↦ f (UpperHalfPlane.ofComplex w) - value) =ᶠ[nhds (c : ℂ)]
        fun w ↦ u w ^ n * a w := by
    have hof : Filter.Tendsto UpperHalfPlane.ofComplex (nhds (c : ℂ)) (nhds c) := by
      have hof' := (UpperHalfPlane.mdifferentiableAt_ofComplex c.im_pos).continuousAt
      change Filter.Tendsto UpperHalfPlane.ofComplex (nhds (c : ℂ))
        (nhds (UpperHalfPlane.ofComplex (c : ℂ))) at hof'
      rw [UpperHalfPlane.ofComplex_apply c] at hof'
      exact hof'
    have hfac := hof.eventually B.factorization
    filter_upwards [hfac] with w hw
    simpa only [u, a, Function.comp_apply] using hw
  rw [analyticOrderAt_congr hfactor]
  change _root_.analyticOrderAt (u ^ n * a) c = n
  rw [analyticOrderAt_mul (huAnalytic.pow n) haAnalytic,
    analyticOrderAt_pow huAnalytic, huOrder, haOrder]
  simp

/-- A holomorphic upper-half-plane function is analytic in its ambient chart. -/
lemma MDifferentiable.analyticAt_comp_ofComplex
    {f : UpperHalfPlane → ℂ} (hf : MDiff f) (c : UpperHalfPlane) :
    AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) c := by
  exact (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds c.im_pos)

/-- The ambient inclusion of the upper half-plane, bundled with its smooth local inverse. -/
noncomputable def upperHalfPlaneCoePartialDiffeomorph :
    PartialDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      UpperHalfPlane ℂ ⊤ where
  toPartialEquiv :=
    UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph.toPartialEquiv
  open_source :=
    UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph.open_source
  open_target :=
    UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph.open_target
  contMDiffOn_toFun := UpperHalfPlane.contMDiff_coe.contMDiffOn
  contMDiffOn_invFun := by
    rintro w hw
    rcases hw with ⟨z, -, rfl⟩
    change ContMDiffWithinAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤ UpperHalfPlane.ofComplex
        UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph.target (z : ℂ)
    simpa only using
      (UpperHalfPlane.contMDiffAt_ofComplex (n := (⊤ : WithTop ℕ∞)) z.im_pos).contMDiffWithinAt

/-- The affine ambient coordinate is a complex local diffeomorphism on the upper half-plane. -/
lemma upperHalfPlane_sub_isLocalDiffeomorphAt (c : UpperHalfPlane) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ⊤
        (fun z : UpperHalfPlane ↦ (z : ℂ) - (c : ℂ)) c := by
  let T : ℂ ≃ₘ^⊤⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ :=
    { toEquiv := Equiv.addRight (-(c : ℂ))
      contMDiff_toFun := by
        change CMDiff ⊤ (fun z : ℂ ↦ z + -(c : ℂ))
        exact contMDiff_id.add contMDiff_const
      contMDiff_invFun := by
        change CMDiff ⊤ (fun z : ℂ ↦ z - -(c : ℂ))
        exact contMDiff_id.sub contMDiff_const }
  let Φ := upperHalfPlaneCoePartialDiffeomorph.trans T.toPartialDiffeomorph
  refine ⟨Φ, ?_, ?_⟩
  · change c ∈ (upperHalfPlaneCoePartialDiffeomorph.toPartialEquiv.trans
      T.toPartialDiffeomorph.toPartialEquiv).source
    rw [PartialEquiv.trans_source]
    constructor
    · simp [upperHalfPlaneCoePartialDiffeomorph]
    · change (c : ℂ) ∈ Set.univ
      trivial
  · intro z hz
    change (z : ℂ) - (c : ℂ) = (z : ℂ) + -(c : ℂ)
    rw [sub_eq_add_neg]

/-- Convert an ambient analytic-order computation into the project's exact branch interface. -/
noncomputable def hasExactHolomorphicBranchAt_of_analyticOrderAt
    {f : UpperHalfPlane → ℂ} {c : UpperHalfPlane} {value : ℂ} {n : ℕ}
    (hf : MDiff f) (hfc : f c = value) (hn : 0 < n)
    (horder : analyticOrderAt
      (fun w : ℂ ↦ f (UpperHalfPlane.ofComplex w) - value) c = n) :
    HasExactHolomorphicBranchAt f c value n := by
  let F : ℂ → ℂ := fun w ↦ f (UpperHalfPlane.ofComplex w) - value
  have hF : AnalyticAt ℂ F c := by
    dsimp only [F]
    rw [← hfc]
    exact (MDifferentiable.analyticAt_comp_ofComplex hf c).sub analyticAt_const
  have hex :=
    (hF.analyticOrderAt_eq_natCast (n := n)).mp (by simpa only [F] using horder)
  let a : ℂ → ℂ := Classical.choose hex
  have ha : AnalyticAt ℂ a c := (Classical.choose_spec hex).1
  have hane : a c ≠ 0 := (Classical.choose_spec hex).2.1
  have hfactor : ∀ᶠ w in nhds (c : ℂ), F w = (w - c) ^ n • a w :=
    (Classical.choose_spec hex).2.2
  refine
    { order_pos := hn
      uniformizer := fun z ↦ (z : ℂ) - (c : ℂ)
      uniformizer_center := by simp
      uniformizer_isLocalDiffeomorph := upperHalfPlane_sub_isLocalDiffeomorphAt c
      unit := fun z ↦ a (z : ℂ)
      unit_holomorphic := ?_
      unit_ne_zero := ?_
      factorization := ?_ }
  · exact ha.differentiableAt.mdifferentiableAt.comp c
      UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt
  · simpa using hane
  · have hcoe : Filter.Tendsto ((↑) : UpperHalfPlane → ℂ) (nhds c) (nhds (c : ℂ)) :=
      UpperHalfPlane.continuous_coe.continuousAt
    have hfactor' := hcoe.eventually hfactor
    filter_upwards [hfactor'] with z hz
    simpa only [F, UpperHalfPlane.ofComplex_apply, smul_eq_mul] using hz

/-- Ambient complex representative of the established modular lift. -/
def ambientEstablishedTau (E : EstablishedFuchsianModularParameter) (w : ℂ) : ℂ :=
  (E.modularParameter.tau (UpperHalfPlane.ofComplex w) : ℂ)

/-- Derivative of the ambient representative of the established modular lift. -/
def ambientEstablishedTauDeriv (E : EstablishedFuchsianModularParameter) (w : ℂ) : ℂ :=
  deriv (ambientEstablishedTau E) w

/-- Ambient representative of an upper-half-plane self-map. -/
def ambientUpperHalfPlaneMap (p : UpperHalfPlane → UpperHalfPlane) (w : ℂ) : ℂ :=
  (p (UpperHalfPlane.ofComplex w) : ℂ)

lemma ambientUpperHalfPlaneMap_analyticAt
    {p : UpperHalfPlane → UpperHalfPlane} (hp : MDiff p) (c : UpperHalfPlane) :
    AnalyticAt ℂ (ambientUpperHalfPlaneMap p) c := by
  have hpcoe : MDiff (fun z : UpperHalfPlane ↦ (p z : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp hp
  change AnalyticAt ℂ
    ((fun z : UpperHalfPlane ↦ (p z : ℂ)) ∘ UpperHalfPlane.ofComplex) c
  exact MDifferentiable.analyticAt_comp_ofComplex hpcoe c

lemma ambientUpperHalfPlaneMap_exists_open_injOn
    {p : UpperHalfPlane → UpperHalfPlane} (hp : Function.Injective p)
    (c : UpperHalfPlane) :
    ∃ U : Set ℂ, IsOpen U ∧ (c : ℂ) ∈ U ∧ U.InjOn (ambientUpperHalfPlaneMap p) := by
  let U : Set ℂ := ((↑) : UpperHalfPlane → ℂ) '' Set.univ
  have hUopen : IsOpen U :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap Set.univ isOpen_univ
  have hcU : (c : ℂ) ∈ U := ⟨c, Set.mem_univ c, rfl⟩
  refine ⟨U, hUopen, hcU, ?_⟩
  rintro a ⟨x, -, rfl⟩ b ⟨y, -, rfl⟩ hab
  apply congrArg ((↑) : UpperHalfPlane → ℂ)
  apply hp
  apply UpperHalfPlane.coe_injective
  simpa only [ambientUpperHalfPlaneMap, UpperHalfPlane.ofComplex_apply] using hab

lemma ambientUpperHalfPlaneMap_deriv_ne_zero
    {p : UpperHalfPlane → UpperHalfPlane} (hp : MDiff p)
    (hinj : Function.Injective p) (c : UpperHalfPlane) :
    deriv (ambientUpperHalfPlaneMap p) c ≠ 0 :=
  AnalyticLocalHomeo.AnalyticAt.deriv_ne_zero_of_exists_open_injOn
    (ambientUpperHalfPlaneMap_analyticAt hp c)
    (ambientUpperHalfPlaneMap_exists_open_injOn hinj c)

/-- Analytic order of an invariant holomorphic function is preserved along any injective smooth
upper-half-plane symmetry. -/
lemma analyticOrderAt_sub_eq_of_upperHalfPlaneMap
    {f : UpperHalfPlane → ℂ} {p : UpperHalfPlane → UpperHalfPlane}
    (hp : MDiff p) (hinj : Function.Injective p) (hinv : ∀ z, f (p z) = f z)
    (c : UpperHalfPlane) (value : ℂ) :
    analyticOrderAt (fun w : ℂ ↦ f (UpperHalfPlane.ofComplex w) - value) (p c) =
      analyticOrderAt (fun w : ℂ ↦ f (UpperHalfPlane.ofComplex w) - value) c := by
  let F : ℂ → ℂ := fun w ↦ f (UpperHalfPlane.ofComplex w) - value
  let A : ℂ → ℂ := ambientUpperHalfPlaneMap p
  have hA : AnalyticAt ℂ A c := by
    simpa only [A] using ambientUpperHalfPlaneMap_analyticAt hp c
  have hAderiv : deriv A c ≠ 0 := by
    simpa only [A] using ambientUpperHalfPlaneMap_deriv_ne_zero hp hinj c
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := F) hA hAderiv
  have hAc : A c = (p c : ℂ) := by
    simp only [A, ambientUpperHalfPlaneMap, UpperHalfPlane.ofComplex_apply]
  have heq : F ∘ A = F := by
    funext w
    simp only [F, A, ambientUpperHalfPlaneMap, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply]
    rw [hinv]
  calc
    analyticOrderAt F (p c) = analyticOrderAt F (A c) := by rw [hAc]
    _ = analyticOrderAt (F ∘ A) c := hcomp.symm
    _ = analyticOrderAt F c := by rw [heq]

lemma sourceCoordinate_analyticOrderAt_of_eq_zero
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 0) :
    analyticOrderAt
      (fun w : ℂ ↦ E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w)) z =
      (3 : ℕ∞) := by
  have horbit : ∃ g : Delta, fuchsianSourceAction g • fuchsianOneFixedPoint = z := by
    apply (E.sourceCoordinate.coordinate_eq_iff_orbit fuchsianOneFixedPoint z).mp
    rw [E.sourceCoordinate.coordinate_at_one, hz]
  obtain ⟨g, hg⟩ := horbit
  have htransport := analyticOrderAt_sub_eq_of_upperHalfPlaneMap
    (f := E.sourceCoordinate.coordinate)
    (p := fun x ↦ fuchsianSourceAction g • x)
    ((fuchsianSourceAction_contMDiff g (⊤ : WithTop ℕ∞)).mdifferentiable (by simp))
    (fuchsianSourceAction g).injective
    (E.sourceCoordinate.coordinate_invariant g) fuchsianOneFixedPoint 0
  rw [hg] at htransport
  calc
    analyticOrderAt
        (fun w : ℂ ↦ E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w)) z =
        analyticOrderAt
          (fun w : ℂ ↦ E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 0) z := by
            simp
    _ = analyticOrderAt
          (fun w : ℂ ↦ E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 0)
          fuchsianOneFixedPoint := htransport
    _ = (3 : ℕ∞) := by
      simpa only [sub_zero, Nat.cast_ofNat] using
        E.sourceCoordinate.branch_one.analyticOrderAt
          E.sourceCoordinate.coordinate_holomorphic

lemma sourceCoordinate_sub_one_analyticOrderAt_of_eq_one
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 1) :
    analyticOrderAt
      (fun w : ℂ ↦ E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1) z =
      (4 : ℕ∞) := by
  have horbit : ∃ g : Delta, fuchsianSourceAction g • fuchsianTwoFixedPoint = z := by
    apply (E.sourceCoordinate.coordinate_eq_iff_orbit fuchsianTwoFixedPoint z).mp
    rw [E.sourceCoordinate.coordinate_at_two, hz]
  obtain ⟨g, hg⟩ := horbit
  have htransport := analyticOrderAt_sub_eq_of_upperHalfPlaneMap
    (f := E.sourceCoordinate.coordinate)
    (p := fun x ↦ fuchsianSourceAction g • x)
    ((fuchsianSourceAction_contMDiff g (⊤ : WithTop ℕ∞)).mdifferentiable (by simp))
    (fuchsianSourceAction g).injective
    (E.sourceCoordinate.coordinate_invariant g) fuchsianTwoFixedPoint 1
  rw [hg] at htransport
  exact htransport.trans <| by
    simpa only [Nat.cast_ofNat] using
      E.sourceCoordinate.branch_two.analyticOrderAt
        E.sourceCoordinate.coordinate_holomorphic

lemma normalizedModularJCoordinate_analyticOrderAt_of_eq_zero
    (J : ExactNormalizedModularJUniformization) (z : UpperHalfPlane)
    (hz : normalizedModularJCoordinate z = 0) :
    analyticOrderAt
      (fun w : ℂ ↦ normalizedModularJCoordinate (UpperHalfPlane.ofComplex w)) z =
      (3 : ℕ∞) := by
  have horbit : ∃ g : ModularMatrix,
      Matrix.SpecialLinearGroup.mapGL ℝ g • ellipticThreeParameter = z := by
    apply (J.coordinate_eq_iff_orbit ellipticThreeParameter z).mp
    rw [J.coordinate_at_three, hz]
  obtain ⟨g, hg⟩ := horbit
  have htransport := analyticOrderAt_sub_eq_of_upperHalfPlaneMap
    (f := normalizedModularJCoordinate)
    (p := fun x ↦ Matrix.SpecialLinearGroup.mapGL ℝ g • x)
    (UpperHalfPlane.mdifferentiable_smul (by simp))
    (fun _ _ h ↦ smul_left_cancel _ h)
    (normalizedModularJCoordinate_invariant g) ellipticThreeParameter 0
  rw [hg] at htransport
  calc
    analyticOrderAt
        (fun w : ℂ ↦ normalizedModularJCoordinate (UpperHalfPlane.ofComplex w)) z =
        analyticOrderAt
          (fun w : ℂ ↦ normalizedModularJCoordinate (UpperHalfPlane.ofComplex w) - 0) z := by
            simp
    _ = analyticOrderAt
          (fun w : ℂ ↦ normalizedModularJCoordinate (UpperHalfPlane.ofComplex w) - 0)
          ellipticThreeParameter := htransport
    _ = (3 : ℕ∞) := by
      simpa only [sub_zero, Nat.cast_ofNat] using
        J.branch_three.analyticOrderAt normalizedModularJCoordinate_holomorphic

lemma normalizedModularJCoordinate_sub_one_analyticOrderAt_of_eq_one
    (J : ExactNormalizedModularJUniformization) (z : UpperHalfPlane)
    (hz : normalizedModularJCoordinate z = 1) :
    analyticOrderAt
      (fun w : ℂ ↦ normalizedModularJCoordinate (UpperHalfPlane.ofComplex w) - 1) z =
      (2 : ℕ∞) := by
  have horbit : ∃ g : ModularMatrix,
      Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I = z := by
    apply (J.coordinate_eq_iff_orbit UpperHalfPlane.I z).mp
    rw [J.coordinate_at_two, hz]
  obtain ⟨g, hg⟩ := horbit
  have htransport := analyticOrderAt_sub_eq_of_upperHalfPlaneMap
    (f := normalizedModularJCoordinate)
    (p := fun x ↦ Matrix.SpecialLinearGroup.mapGL ℝ g • x)
    (UpperHalfPlane.mdifferentiable_smul (by simp))
    (fun _ _ h ↦ smul_left_cancel _ h)
    (normalizedModularJCoordinate_invariant g) UpperHalfPlane.I 1
  rw [hg] at htransport
  exact htransport.trans <| by
    simpa only [Nat.cast_ofNat] using
      J.branch_two.analyticOrderAt normalizedModularJCoordinate_holomorphic

lemma ambientEstablishedTau_analyticAt (E : EstablishedFuchsianModularParameter)
    (z : UpperHalfPlane) :
    AnalyticAt ℂ (ambientEstablishedTau E) z := by
  have htau : MDiff (fun x : UpperHalfPlane ↦ (E.modularParameter.tau x : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp E.modularParameter.tau_holomorphic
  change AnalyticAt ℂ
    ((fun x : UpperHalfPlane ↦ (E.modularParameter.tau x : ℂ)) ∘
      UpperHalfPlane.ofComplex) z
  exact MDifferentiable.analyticAt_comp_ofComplex htau z

/-- At a regular source-orbifold point, equality of modular-lift values implies equality of
nearby source points, because the exact source coordinate is locally injective there. -/
lemma ambientEstablishedTau_exists_open_injOn_of_regular
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz0 : E.sourceCoordinate.coordinate z ≠ 0)
    (hz1 : E.sourceCoordinate.coordinate z ≠ 1) :
    ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ U.InjOn (ambientEstablishedTau E) := by
  have hzreg : E.sourceCoordinate.coordinate z ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp [hz0, hz1]
  have hloc := E.sourceCoordinate.regular_covering.isLocalHomeomorphOn
  obtain ⟨e, hze, heq⟩ := hloc z hzreg
  let U : Set ℂ := ((↑) : UpperHalfPlane → ℂ) '' e.source
  have hUopen : IsOpen U :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap e.source e.open_source
  have hzU : (z : ℂ) ∈ U := ⟨z, hze, rfl⟩
  refine ⟨U, hUopen, hzU, ?_⟩
  rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ htau
  have htauH : E.modularParameter.tau x = E.modularParameter.tau y := by
    apply UpperHalfPlane.coe_injective
    simpa only [ambientEstablishedTau, UpperHalfPlane.ofComplex_apply] using htau
  have hcoord : E.sourceCoordinate.coordinate x = E.sourceCoordinate.coordinate y := by
    rw [← E.induced_coordinate x, ← E.induced_coordinate y]
    simp only [FuchsianModularParameter.coordinate, htauH]
  have hexy : e x = e y := by
    rw [← congrFun heq x, ← congrFun heq y]
    exact hcoord
  exact congrArg ((↑) : UpperHalfPlane → ℂ) (e.injOn hx hy hexy)

/-- The established modular lift is unramified at every regular source-orbifold point. -/
lemma ambientEstablishedTauDeriv_ne_zero_of_regular
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz0 : E.sourceCoordinate.coordinate z ≠ 0)
    (hz1 : E.sourceCoordinate.coordinate z ≠ 1) :
    ambientEstablishedTauDeriv E z ≠ 0 := by
  exact AnalyticLocalHomeo.AnalyticAt.deriv_ne_zero_of_exists_open_injOn
    (ambientEstablishedTau_analyticAt E z)
    (ambientEstablishedTau_exists_open_injOn_of_regular E z hz0 hz1)

/-- The modular lift is unramified at the order-three source point: both the source and target
quotient coordinates have exact order three there. -/
lemma ambientEstablishedTau_sub_analyticOrderAt_one
    (E : EstablishedFuchsianModularParameter) :
    analyticOrderAt
      (fun w : ℂ ↦ ambientEstablishedTau E w -
        ambientEstablishedTau E fuchsianOneFixedPoint)
      fuchsianOneFixedPoint = (1 : ℕ∞) := by
  obtain ⟨J⟩ := establishedExactNormalizedModularJUniformization
  let Cdiff : ℂ → ℂ := fun w ↦
    E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w)
  let Jdiff : ℂ → ℂ := fun w ↦
    normalizedModularJCoordinate (UpperHalfPlane.ofComplex w)
  let t : ℂ → ℂ := ambientEstablishedTau E
  have ht : AnalyticAt ℂ t fuchsianOneFixedPoint := by
    simpa only [t] using ambientEstablishedTau_analyticAt E fuchsianOneFixedPoint
  have ht_one : t fuchsianOneFixedPoint = (ellipticThreeParameter : ℂ) := by
    simp only [t, ambientEstablishedTau, UpperHalfPlane.ofComplex_apply]
    exact congrArg ((↑) : UpperHalfPlane → ℂ) E.tau_at_one
  have hCorder : analyticOrderAt Cdiff fuchsianOneFixedPoint = (3 : ℕ∞) := by
    simpa only [Cdiff, sub_zero, Nat.cast_ofNat] using
      E.sourceCoordinate.branch_one.analyticOrderAt
        E.sourceCoordinate.coordinate_holomorphic
  have hJorder : analyticOrderAt Jdiff ellipticThreeParameter = (3 : ℕ∞) := by
    simpa only [Jdiff, sub_zero, Nat.cast_ofNat] using
      J.branch_three.analyticOrderAt normalizedModularJCoordinate_holomorphic
  have hJanalytic : AnalyticAt ℂ Jdiff ellipticThreeParameter := by
    exact MDifferentiable.analyticAt_comp_ofComplex
      normalizedModularJCoordinate_holomorphic ellipticThreeParameter
  have heq : Cdiff = Jdiff ∘ t := by
    funext w
    dsimp only [Cdiff, Jdiff, t, ambientEstablishedTau, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
    change E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) =
      normalizedJ (E.modularParameter.tau (UpperHalfPlane.ofComplex w)) / 1728
    rw [← E.induced_coordinate]
    rfl
  have hJanalytic_t : AnalyticAt ℂ Jdiff (t fuchsianOneFixedPoint) := by
    rw [ht_one]
    exact hJanalytic
  have hcomp := hJanalytic_t.analyticOrderAt_comp ht
  have hmul : (3 : ℕ∞) =
      (3 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t fuchsianOneFixedPoint)
        fuchsianOneFixedPoint := by
    calc
      (3 : ℕ∞) = analyticOrderAt Cdiff fuchsianOneFixedPoint := hCorder.symm
      _ = analyticOrderAt (Jdiff ∘ t) fuchsianOneFixedPoint := by rw [heq]
      _ = analyticOrderAt Jdiff (t fuchsianOneFixedPoint) *
          analyticOrderAt (fun w ↦ t w - t fuchsianOneFixedPoint)
            fuchsianOneFixedPoint := hcomp
      _ = (3 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t fuchsianOneFixedPoint)
            fuchsianOneFixedPoint := by rw [ht_one, hJorder]
  have horder : analyticOrderAt (fun w ↦ t w - t fuchsianOneFixedPoint)
      fuchsianOneFixedPoint = (1 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (3 : ℕ∞)) (by norm_num) (by simp)).injective
    calc
      (3 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t fuchsianOneFixedPoint)
          fuchsianOneFixedPoint = (3 : ℕ∞) := hmul.symm
      _ = (3 : ℕ∞) * (1 : ℕ∞) := by norm_num
  simpa only [t] using horder

/-- In particular the derivative of the modular lift is nonzero at the order-three point. -/
lemma ambientEstablishedTauDeriv_ne_zero_at_one
    (E : EstablishedFuchsianModularParameter) :
    ambientEstablishedTauDeriv E fuchsianOneFixedPoint ≠ 0 := by
  let g : ℂ → ℂ := fun w ↦ ambientEstablishedTau E w -
    ambientEstablishedTau E fuchsianOneFixedPoint
  have hg : AnalyticAt ℂ g fuchsianOneFixedPoint :=
    (ambientEstablishedTau_analyticAt E fuchsianOneFixedPoint).sub (by fun_prop)
  have horder : analyticOrderAt g fuchsianOneFixedPoint = (1 : ℕ∞) := by
    simpa only [g] using ambientEstablishedTau_sub_analyticOrderAt_one E
  have hdata := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mp horder
  simpa only [ambientEstablishedTauDeriv, g, iteratedDeriv_one, deriv_sub_const] using hdata.2

/-- The modular lift has local degree two at the order-four source point: the source quotient has
order four there, while the normalized modular quotient has order two at `I`. -/
lemma ambientEstablishedTau_sub_analyticOrderAt_two
    (E : EstablishedFuchsianModularParameter) :
    analyticOrderAt
      (fun w : ℂ ↦ ambientEstablishedTau E w -
        ambientEstablishedTau E fuchsianTwoFixedPoint)
      fuchsianTwoFixedPoint = (2 : ℕ∞) := by
  obtain ⟨J⟩ := establishedExactNormalizedModularJUniformization
  let Cdiff : ℂ → ℂ := fun w ↦
    E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1
  let Jdiff : ℂ → ℂ := fun w ↦
    normalizedModularJCoordinate (UpperHalfPlane.ofComplex w) - 1
  let t : ℂ → ℂ := ambientEstablishedTau E
  have ht : AnalyticAt ℂ t fuchsianTwoFixedPoint := by
    simpa only [t] using ambientEstablishedTau_analyticAt E fuchsianTwoFixedPoint
  have ht_two : t fuchsianTwoFixedPoint = (UpperHalfPlane.I : ℂ) := by
    simp only [t, ambientEstablishedTau, UpperHalfPlane.ofComplex_apply]
    exact congrArg ((↑) : UpperHalfPlane → ℂ) E.tau_at_two
  have hCorder : analyticOrderAt Cdiff fuchsianTwoFixedPoint = (4 : ℕ∞) := by
    simpa only [Cdiff, Nat.cast_ofNat] using
      E.sourceCoordinate.branch_two.analyticOrderAt
        E.sourceCoordinate.coordinate_holomorphic
  have hJorder : analyticOrderAt Jdiff UpperHalfPlane.I = (2 : ℕ∞) := by
    simpa only [Jdiff, Nat.cast_ofNat] using
      J.branch_two.analyticOrderAt normalizedModularJCoordinate_holomorphic
  have hJanalytic : AnalyticAt ℂ Jdiff UpperHalfPlane.I := by
    exact (MDifferentiable.analyticAt_comp_ofComplex
      normalizedModularJCoordinate_holomorphic UpperHalfPlane.I).sub (by fun_prop)
  have heq : Cdiff = Jdiff ∘ t := by
    funext w
    dsimp only [Cdiff, Jdiff, t, ambientEstablishedTau, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
    change E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1 =
      normalizedJ (E.modularParameter.tau (UpperHalfPlane.ofComplex w)) / 1728 - 1
    rw [← E.induced_coordinate]
    rfl
  have hJanalytic_t : AnalyticAt ℂ Jdiff (t fuchsianTwoFixedPoint) := by
    rw [ht_two]
    exact hJanalytic
  have hcomp := hJanalytic_t.analyticOrderAt_comp ht
  have hmul : (4 : ℕ∞) =
      (2 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t fuchsianTwoFixedPoint)
        fuchsianTwoFixedPoint := by
    calc
      (4 : ℕ∞) = analyticOrderAt Cdiff fuchsianTwoFixedPoint := hCorder.symm
      _ = analyticOrderAt (Jdiff ∘ t) fuchsianTwoFixedPoint := by rw [heq]
      _ = analyticOrderAt Jdiff (t fuchsianTwoFixedPoint) *
          analyticOrderAt (fun w ↦ t w - t fuchsianTwoFixedPoint)
            fuchsianTwoFixedPoint := hcomp
      _ = (2 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t fuchsianTwoFixedPoint)
            fuchsianTwoFixedPoint := by rw [ht_two, hJorder]
  have horder : analyticOrderAt (fun w ↦ t w - t fuchsianTwoFixedPoint)
      fuchsianTwoFixedPoint = (2 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (2 : ℕ∞)) (by norm_num) (by simp)).injective
    calc
      (2 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t fuchsianTwoFixedPoint)
          fuchsianTwoFixedPoint = (4 : ℕ∞) := hmul.symm
      _ = (2 : ℕ∞) * (2 : ℕ∞) := by norm_num
  simpa only [t] using horder

/-- Consequently the derivative of the modular lift has a simple zero at the order-four point. -/
lemma ambientEstablishedTauDeriv_analyticOrderAt_two
    (E : EstablishedFuchsianModularParameter) :
    analyticOrderAt (ambientEstablishedTauDeriv E) fuchsianTwoFixedPoint =
      (1 : ℕ∞) := by
  have ht := ambientEstablishedTau_analyticAt E fuchsianTwoFixedPoint
  have hsum := ht.analyticOrderAt_deriv_add_one
  have hsub := ambientEstablishedTau_sub_analyticOrderAt_two E
  change analyticOrderAt (deriv (ambientEstablishedTau E)) fuchsianTwoFixedPoint =
    (1 : ℕ∞)
  rw [hsub] at hsum
  exact (ENat.add_left_injective_of_ne_top (n := (1 : ℕ∞)) (by simp)) <| by
    calc
      analyticOrderAt (deriv (ambientEstablishedTau E)) fuchsianTwoFixedPoint + 1 =
          (2 : ℕ∞) := hsum
      _ = (1 : ℕ∞) + 1 := by norm_num

/-- Over the source value zero, the modular lift has local degree one at every point of the
elliptic orbit. -/
lemma ambientEstablishedTau_sub_analyticOrderAt_of_coordinate_eq_zero
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 0) :
    analyticOrderAt
      (fun w : ℂ ↦ ambientEstablishedTau E w - ambientEstablishedTau E z) z =
      (1 : ℕ∞) := by
  obtain ⟨J⟩ := establishedExactNormalizedModularJUniformization
  let Cdiff : ℂ → ℂ := fun w ↦
    E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w)
  let Jdiff : ℂ → ℂ := fun w ↦
    normalizedModularJCoordinate (UpperHalfPlane.ofComplex w)
  let t : ℂ → ℂ := ambientEstablishedTau E
  have ht : AnalyticAt ℂ t z := by
    simpa only [t] using ambientEstablishedTau_analyticAt E z
  have htz : t z = (E.modularParameter.tau z : ℂ) := by
    simp only [t, ambientEstablishedTau, UpperHalfPlane.ofComplex_apply]
  have htarget : normalizedModularJCoordinate (E.modularParameter.tau z) = 0 := by
    change E.modularParameter.coordinate z = 0
    rw [E.induced_coordinate z]
    exact hz
  have hCorder : analyticOrderAt Cdiff z = (3 : ℕ∞) := by
    simpa only [Cdiff] using sourceCoordinate_analyticOrderAt_of_eq_zero E z hz
  have hJorder : analyticOrderAt Jdiff (E.modularParameter.tau z) = (3 : ℕ∞) := by
    simpa only [Jdiff] using
      normalizedModularJCoordinate_analyticOrderAt_of_eq_zero J _ htarget
  have hJanalytic : AnalyticAt ℂ Jdiff (E.modularParameter.tau z) := by
    exact MDifferentiable.analyticAt_comp_ofComplex
      normalizedModularJCoordinate_holomorphic (E.modularParameter.tau z)
  have heq : Cdiff = Jdiff ∘ t := by
    funext w
    dsimp only [Cdiff, Jdiff, t, ambientEstablishedTau, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
    change E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) =
      normalizedJ (E.modularParameter.tau (UpperHalfPlane.ofComplex w)) / 1728
    rw [← E.induced_coordinate]
    rfl
  have hJanalytic_t : AnalyticAt ℂ Jdiff (t z) := by
    rw [htz]
    exact hJanalytic
  have hcomp := hJanalytic_t.analyticOrderAt_comp ht
  have hmul : (3 : ℕ∞) =
      (3 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t z) z := by
    calc
      (3 : ℕ∞) = analyticOrderAt Cdiff z := hCorder.symm
      _ = analyticOrderAt (Jdiff ∘ t) z := by rw [heq]
      _ = analyticOrderAt Jdiff (t z) *
          analyticOrderAt (fun w ↦ t w - t z) z := hcomp
      _ = (3 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t z) z := by
        rw [htz, hJorder]
  have horder : analyticOrderAt (fun w ↦ t w - t z) z = (1 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (3 : ℕ∞)) (by norm_num) (by simp)).injective
    calc
      (3 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t z) z = (3 : ℕ∞) := hmul.symm
      _ = (3 : ℕ∞) * (1 : ℕ∞) := by norm_num
  simpa only [t] using horder

/-- Over the source value one, the modular lift has local degree two at every point of the
order-four elliptic orbit. -/
lemma ambientEstablishedTau_sub_analyticOrderAt_of_coordinate_eq_one
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 1) :
    analyticOrderAt
      (fun w : ℂ ↦ ambientEstablishedTau E w - ambientEstablishedTau E z) z =
      (2 : ℕ∞) := by
  obtain ⟨J⟩ := establishedExactNormalizedModularJUniformization
  let Cdiff : ℂ → ℂ := fun w ↦
    E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1
  let Jdiff : ℂ → ℂ := fun w ↦
    normalizedModularJCoordinate (UpperHalfPlane.ofComplex w) - 1
  let t : ℂ → ℂ := ambientEstablishedTau E
  have ht : AnalyticAt ℂ t z := by
    simpa only [t] using ambientEstablishedTau_analyticAt E z
  have htz : t z = (E.modularParameter.tau z : ℂ) := by
    simp only [t, ambientEstablishedTau, UpperHalfPlane.ofComplex_apply]
  have htarget : normalizedModularJCoordinate (E.modularParameter.tau z) = 1 := by
    change E.modularParameter.coordinate z = 1
    rw [E.induced_coordinate z]
    exact hz
  have hCorder : analyticOrderAt Cdiff z = (4 : ℕ∞) := by
    simpa only [Cdiff] using sourceCoordinate_sub_one_analyticOrderAt_of_eq_one E z hz
  have hJorder : analyticOrderAt Jdiff (E.modularParameter.tau z) = (2 : ℕ∞) := by
    simpa only [Jdiff] using
      normalizedModularJCoordinate_sub_one_analyticOrderAt_of_eq_one J _ htarget
  have hJanalytic : AnalyticAt ℂ Jdiff (E.modularParameter.tau z) := by
    exact (MDifferentiable.analyticAt_comp_ofComplex
      normalizedModularJCoordinate_holomorphic (E.modularParameter.tau z)).sub (by fun_prop)
  have heq : Cdiff = Jdiff ∘ t := by
    funext w
    dsimp only [Cdiff, Jdiff, t, ambientEstablishedTau, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
    change E.sourceCoordinate.coordinate (UpperHalfPlane.ofComplex w) - 1 =
      normalizedJ (E.modularParameter.tau (UpperHalfPlane.ofComplex w)) / 1728 - 1
    rw [← E.induced_coordinate]
    rfl
  have hJanalytic_t : AnalyticAt ℂ Jdiff (t z) := by
    rw [htz]
    exact hJanalytic
  have hcomp := hJanalytic_t.analyticOrderAt_comp ht
  have hmul : (4 : ℕ∞) =
      (2 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t z) z := by
    calc
      (4 : ℕ∞) = analyticOrderAt Cdiff z := hCorder.symm
      _ = analyticOrderAt (Jdiff ∘ t) z := by rw [heq]
      _ = analyticOrderAt Jdiff (t z) *
          analyticOrderAt (fun w ↦ t w - t z) z := hcomp
      _ = (2 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t z) z := by
        rw [htz, hJorder]
  have horder : analyticOrderAt (fun w ↦ t w - t z) z = (2 : ℕ∞) := by
    apply (ENat.mul_right_strictMono (a := (2 : ℕ∞)) (by norm_num) (by simp)).injective
    calc
      (2 : ℕ∞) * analyticOrderAt (fun w ↦ t w - t z) z = (4 : ℕ∞) := hmul.symm
      _ = (2 : ℕ∞) * (2 : ℕ∞) := by norm_num
  simpa only [t] using horder

lemma ambientEstablishedTauDeriv_analyticAt
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    AnalyticAt ℂ (ambientEstablishedTauDeriv E) z := by
  exact (ambientEstablishedTau_analyticAt E z).deriv

/-- The derivative stays nonzero over the entire order-three elliptic orbit. -/
lemma ambientEstablishedTauDeriv_ne_zero_of_coordinate_eq_zero
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 0) :
    ambientEstablishedTauDeriv E z ≠ 0 := by
  let g : ℂ → ℂ := fun w ↦ ambientEstablishedTau E w - ambientEstablishedTau E z
  have hg : AnalyticAt ℂ g z :=
    (ambientEstablishedTau_analyticAt E z).sub (by fun_prop)
  have horder : analyticOrderAt g z = (1 : ℕ∞) := by
    simpa only [g] using
      ambientEstablishedTau_sub_analyticOrderAt_of_coordinate_eq_zero E z hz
  have hdata := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mp horder
  simpa only [ambientEstablishedTauDeriv, g, iteratedDeriv_one, deriv_sub_const] using hdata.2

/-- The derivative has a simple zero at every point over the source value one. -/
lemma ambientEstablishedTauDeriv_analyticOrderAt_of_coordinate_eq_one
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz : E.sourceCoordinate.coordinate z = 1) :
    analyticOrderAt (ambientEstablishedTauDeriv E) z = (1 : ℕ∞) := by
  have ht := ambientEstablishedTau_analyticAt E z
  have hsum := ht.analyticOrderAt_deriv_add_one
  have hsub := ambientEstablishedTau_sub_analyticOrderAt_of_coordinate_eq_one E z hz
  change analyticOrderAt (deriv (ambientEstablishedTau E)) z = (1 : ℕ∞)
  rw [hsub] at hsum
  exact (ENat.add_left_injective_of_ne_top (n := (1 : ℕ∞)) (by simp)) <| by
    calc
      analyticOrderAt (deriv (ambientEstablishedTau E)) z + 1 = (2 : ℕ∞) := hsum
      _ = (1 : ℕ∞) + 1 := by norm_num

/-- Away from the value-one orbit the derivative of the modular lift is nowhere zero. -/
lemma ambientEstablishedTauDeriv_ne_zero_of_coordinate_ne_one
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane)
    (hz1 : E.sourceCoordinate.coordinate z ≠ 1) :
    ambientEstablishedTauDeriv E z ≠ 0 := by
  by_cases hz0 : E.sourceCoordinate.coordinate z = 0
  · exact ambientEstablishedTauDeriv_ne_zero_of_coordinate_eq_zero E z hz0
  · exact ambientEstablishedTauDeriv_ne_zero_of_regular E z hz0 hz1

/-- Exact zero locus of the derivative: precisely the order-four source elliptic orbit. -/
lemma ambientEstablishedTauDeriv_eq_zero_iff
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    ambientEstablishedTauDeriv E z = 0 ↔ E.sourceCoordinate.coordinate z = 1 := by
  constructor
  · intro hd
    by_contra hz1
    exact ambientEstablishedTauDeriv_ne_zero_of_coordinate_ne_one E z hz1 hd
  · intro hz1
    apply apply_eq_zero_of_analyticOrderAt_ne_zero
    rw [ambientEstablishedTauDeriv_analyticOrderAt_of_coordinate_eq_one E z hz1]
    norm_num

/-- Complete pointwise analytic-order classification of the derivative. -/
lemma ambientEstablishedTauDeriv_analyticOrderAt
    (E : EstablishedFuchsianModularParameter) (z : UpperHalfPlane) :
    analyticOrderAt (ambientEstablishedTauDeriv E) z =
      if E.sourceCoordinate.coordinate z = 1 then (1 : ℕ∞) else 0 := by
  by_cases hz1 : E.sourceCoordinate.coordinate z = 1
  · simp only [hz1, if_pos]
    exact ambientEstablishedTauDeriv_analyticOrderAt_of_coordinate_eq_one E z hz1
  · simp only [hz1]
    exact (ambientEstablishedTauDeriv_analyticAt E z).analyticOrderAt_eq_zero.mpr
      (ambientEstablishedTauDeriv_ne_zero_of_coordinate_ne_one E z hz1)

end SphereSixComplex.Periods
