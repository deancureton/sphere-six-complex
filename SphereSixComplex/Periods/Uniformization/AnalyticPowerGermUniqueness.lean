module

public import SphereSixComplex.Periods.Uniformization.PowerNormalFormCurrent
import all SphereSixComplex.Periods.Uniformization.PowerNormalFormCurrent

@[expose] public section

/-!
# Uniqueness for analytic power germs with the same leading coefficient

This is the small local algebra needed to identify a marked branched lift.  After cancelling the
common vanishing power away from the center, local injectivity of `w ↦ w^m` near the common
nonzero leading coefficient forces the two unit factors to agree.
-/

noncomputable section

namespace TauCeti

open Complex Filter Set Topology

/-- A noncritical analytic germ factors by the centered linear coordinate, and the value of the
remaining unit is exactly the derivative. -/
theorem AnalyticAt.exists_linear_normalForm_of_deriv_ne_zero
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hderiv : deriv f a ≠ 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ u a = deriv f a ∧ u a ≠ 0 ∧
      (fun z ↦ f z - f a) =ᶠ[nhds a] fun z ↦ (z - a) * u z := by
  have hord := hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv
  obtain ⟨u, hu, hu0, hfactor⟩ :=
    (hf.sub analyticAt_const).analyticOrderAt_eq_natCast.mp hord
  have hfactor' : (fun z ↦ f z - f a) =ᶠ[nhds a]
      fun z ↦ (z - a) * u z := by
    filter_upwards [hfactor] with z hz
    simpa only [Pi.sub_apply, pow_one, smul_eq_mul] using hz
  have huderiv : u a = deriv f a := by
    have hd := Filter.EventuallyEq.deriv_eq hfactor'
    have hleft : deriv (fun z ↦ f z - f a) a = deriv f a := by
      simpa using hf.differentiableAt.deriv_sub_const (f a)
    have hright : deriv (fun z ↦ (z - a) * u z) a = u a := by
      have hprod := ((hasDerivAt_id a).sub_const a).mul hu.differentiableAt.hasDerivAt
      have hfun : (fun z ↦ (z - a) * u z) = (fun z ↦ z - a) * u := by
        funext z
        rfl
      rw [hfun]
      simpa using hprod.deriv
    rw [hleft, hright] at hd
    exact hd.symm
  exact ⟨u, hu, huderiv, huderiv.symm ▸ hderiv, hfactor'⟩

/-- If two analytic germs have the same simple zero, the second is the first times an analytic
unit; its value at the center is the quotient of the two derivatives. -/
theorem exists_mul_normalForm_of_common_simple_zero
    {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hf0 : f a = 0) (hg0 : g a = 0)
    (hfderiv : deriv f a ≠ 0) (hgderiv : deriv g a ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q a ∧
      q a = deriv g a / deriv f a ∧ q a ≠ 0 ∧
        g =ᶠ[nhds a] fun z ↦ f z * q z := by
  obtain ⟨p, hp, hpderiv, hp0, hpfactor⟩ :=
    AnalyticAt.exists_linear_normalForm_of_deriv_ne_zero hf hfderiv
  obtain ⟨r, hr, hrderiv, hr0, hrfactor⟩ :=
    AnalyticAt.exists_linear_normalForm_of_deriv_ne_zero hg hgderiv
  let q : ℂ → ℂ := fun z ↦ r z / p z
  have hq : AnalyticAt ℂ q a := hr.div hp hp0
  have hqa : q a = deriv g a / deriv f a := by simp only [q, hrderiv, hpderiv]
  have hqa0 : q a ≠ 0 := div_ne_zero hr0 hp0
  have hpne : ∀ᶠ z in nhds a, p z ≠ 0 := hp.continuousAt.eventually_ne hp0
  refine ⟨q, hq, hqa, hqa0, ?_⟩
  filter_upwards [hpfactor, hrfactor, hpne] with z hfz hgz hpz
  rw [show f z = (z - a) * p z by simpa only [hf0, sub_zero] using hfz]
  rw [show g z = (z - a) * r z by simpa only [hg0, sub_zero] using hgz]
  simp only [q]
  field_simp

/-- Two germs in the same exact normal form, with the same leading coefficient and equal
`m`-th powers, are equal. -/
theorem eventuallyEq_of_pow_eq_of_same_normalForm
    {X Y u v : ℂ → ℂ} {a : ℂ} {k m : ℕ}
    (hu : AnalyticAt ℂ u a) (hv : AnalyticAt ℂ v a)
    (huv : u a = v a) (hu0 : u a ≠ 0) (hm : m ≠ 0)
    (hX : X =ᶠ[nhds a] fun z ↦ (z - a) ^ k * u z)
    (hY : Y =ᶠ[nhds a] fun z ↦ (z - a) ^ k * v z)
    (hpow : (fun z ↦ X z ^ m) =ᶠ[nhds a] fun z ↦ Y z ^ m) :
    X =ᶠ[nhds a] Y := by
  have huvpowNE : (fun z ↦ u z ^ m) =ᶠ[nhdsWithin a ({a} : Set ℂ)ᶜ]
      fun z ↦ v z ^ m := by
    filter_upwards [hX.filter_mono nhdsWithin_le_nhds,
      hY.filter_mono nhdsWithin_le_nhds,
      hpow.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hXz hYz hpz hza
    have hza0 : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hza)
    have hcommon : (z - a) ^ (k * m) * u z ^ m =
        (z - a) ^ (k * m) * v z ^ m := by
      calc
        (z - a) ^ (k * m) * u z ^ m = ((z - a) ^ k * u z) ^ m := by
          rw [mul_pow, pow_mul]
        _ = X z ^ m := by rw [hXz]
        _ = Y z ^ m := hpz
        _ = ((z - a) ^ k * v z) ^ m := by rw [hYz]
        _ = (z - a) ^ (k * m) * v z ^ m := by rw [mul_pow, pow_mul]
    exact mul_left_cancel₀ (pow_ne_zero _ hza0) hcommon
  have huvpow : (fun z ↦ u z ^ m) =ᶠ[nhds a] fun z ↦ v z ^ m := by
    have huvpowImp : ∀ᶠ z in nhds a, z ∈ ({a} : Set ℂ)ᶜ → u z ^ m = v z ^ m :=
      eventually_nhdsWithin_iff.mp huvpowNE
    filter_upwards [huvpowImp] with z hz
    by_cases hza : z = a
    · subst z
      rw [huv]
    · exact hz hza
  let P : ℂ → ℂ := fun w ↦ w ^ m
  have hPan : AnalyticAt ℂ P (u a) := by fun_prop
  have hPderiv : deriv P (u a) ≠ 0 := by
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hderiv : deriv P (u a) = (m : ℂ) * (u a) ^ (m - 1) := by
      have hPid : P = (id : ℂ → ℂ) ^ m := by
        funext w
        rfl
      rw [hPid]
      simpa only [id_eq, mul_one] using ((hasDerivAt_id (u a)).pow m).deriv
    rw [hderiv]
    exact mul_ne_zero hmC (pow_ne_zero _ hu0)
  obtain ⟨S, hS, hPinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero hPan).mpr hPderiv
  have huS : ∀ᶠ z in nhds a, u z ∈ S := hu.continuousAt hS
  have hvS : ∀ᶠ z in nhds a, v z ∈ S := by
    have : S ∈ nhds (v a) := by simpa only [huv] using hS
    exact hv.continuousAt this
  have huvEq : u =ᶠ[nhds a] v := by
    filter_upwards [huvpow, huS, hvS] with z hp huz hvz
    exact hPinj huz hvz hp
  filter_upwards [hX, hY, huvEq] with z hXz hYz huvz
  rw [hXz, hYz, huvz]


end TauCeti
