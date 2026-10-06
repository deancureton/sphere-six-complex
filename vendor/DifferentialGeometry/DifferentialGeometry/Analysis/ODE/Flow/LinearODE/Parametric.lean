module

public import DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Inhomogeneous

@[expose] public section


noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

section VariationalSolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

noncomputable local instance parametricLinearODEEndoNormedAddCommGroup :
    NormedAddCommGroup (G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance parametricLinearODEEndoNormedSpace :
    NormedSpace ℝ (G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance parametricLinearODEDerivativeNormedAddCommGroup :
    NormedAddCommGroup (F →L[ℝ] G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance parametricLinearODEDerivativeNormedSpace :
    NormedSpace ℝ (F →L[ℝ] G →L[ℝ] G) :=
  ContinuousLinearMap.toNormedSpace

noncomputable def variationalForcing
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G)
    (x : F) (v : F) (t : ℝ) : G :=
  (fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)

noncomputable def variationalSolution
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G)
    (x : F) (v : F) : ℝ → G :=
  inhomogLinearODESolution A (fun y t => variationalForcing A a b' h₀ Z₀ y v t)
    a b' h₀ (fun y => (fderiv ℝ Z₀ y) v) x

omit [CompleteSpace G] in
theorem variationalW_initial
    (A : F → ℝ → (G →L[ℝ] G)) (a b' h₀ : ℝ) (Z₀ : F → G) (x : F) (v : F) :
    variationalSolution A a b' h₀ Z₀ x v h₀ = (fderiv ℝ Z₀ x) v := by
  unfold variationalSolution
  exact inhomogLinearODESolution_initial _ _ _ _ _ _ _

theorem variationalForcing_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) (v : F) :
    ContinuousOn (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hZ_cont : ContinuousOn (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont
  have happ : ContinuousOn
      (Function.uncurry fun x t => (fderiv ℝ (fun y => A y t) x) v)
      (U ×ˢ Set.Ioo a b') := by
    exact ContinuousOn.clm_apply hDA_cont continuousOn_const
  have hgoal : ContinuousOn
      (fun p : F × ℝ =>
        ((fderiv ℝ (fun y => A y p.2) p.1) v)
          (linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') :=
    ContinuousOn.clm_apply happ hZ_cont
  refine hgoal.congr ?_
  intro p _
  unfold variationalForcing
  rfl

theorem variationalW_hasDerivAt
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (v : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasDerivAt (variationalSolution A a b' h₀ Z₀ x v ·)
      ((fderiv ℝ (fun y => A y t) x) v (linearODESolution A a b' h₀ Z₀ x t)
        + A x t (variationalSolution A a b' h₀ Z₀ x v t)) t := by
  have hb_cont : ContinuousOn
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') :=
    variationalForcing_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont v
  have hderiv : HasDerivAt
      (inhomogLinearODESolution A
        (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
        (fun y => (fderiv ℝ Z₀ y) v) x ·)
      (A x t (inhomogLinearODESolution A
          (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
          (fun y => (fderiv ℝ Z₀ y) v) x t)
        + variationalForcing A a b' h₀ Z₀ x v t) t :=
    inhomogLinearODESolution_hasDerivAt h₀_mem hA_cont hb_cont hx ht
  have hderiv' : HasDerivAt
      (inhomogLinearODESolution A
        (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
        (fun y => (fderiv ℝ Z₀ y) v) x ·)
      (variationalForcing A a b' h₀ Z₀ x v t
        + A x t (inhomogLinearODESolution A
          (fun y t => variationalForcing A a b' h₀ Z₀ y v t) a b' h₀
          (fun y => (fderiv ℝ Z₀ y) v) x t)) t := by
    have := hderiv
    rwa [add_comm] at this
  exact hderiv'

theorem variationalW_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    (v : F)
    (hZ₀'_cont : ContinuousOn (fun x => (fderiv ℝ Z₀ x) v) U) :
    ContinuousOn
      (Function.uncurry (fun x t => variationalSolution A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hb_cont : ContinuousOn
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') :=
    variationalForcing_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont v
  exact inhomogLinearODESolution_continuousOn (Z₀ := fun y => (fderiv ℝ Z₀ y) v)
    h₀_mem hU hA_cont hb_cont hZ₀'_cont

theorem inhomogLinearODE_unique_on_Ioo
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A : ℝ → (G →L[ℝ] G)} {b : ℝ → G} {a b' h₀ : ℝ}
    (ht₀ : h₀ ∈ Set.Ioo a b')
    (hA_cont : ContinuousOn A (Set.Ioo a b'))
    {Z₁ Z₂ : ℝ → G}
    (hZ₁ : ∀ t ∈ Set.Ioo a b', HasDerivAt Z₁ (A t (Z₁ t) + b t) t)
    (hZ₂ : ∀ t ∈ Set.Ioo a b', HasDerivAt Z₂ (A t (Z₂ t) + b t) t)
    (heq : Z₁ h₀ = Z₂ h₀) :
    Set.EqOn Z₁ Z₂ (Set.Ioo a b') := by
  set D : ℝ → G := fun t => Z₁ t - Z₂ t with hD_def
  have hD_deriv : ∀ t ∈ Set.Ioo a b', HasDerivAt D (A t (D t)) t := by
    intro t ht
    have h₁ : HasDerivAt Z₁ (A t (Z₁ t) + b t) t := hZ₁ t ht
    have h₂ : HasDerivAt Z₂ (A t (Z₂ t) + b t) t := hZ₂ t ht
    have hsub : HasDerivAt D ((A t (Z₁ t) + b t) - (A t (Z₂ t) + b t)) t := h₁.sub h₂
    have h_eq : (A t (Z₁ t) + b t) - (A t (Z₂ t) + b t) = A t (D t) := by
      have hD_t : D t = Z₁ t - Z₂ t := rfl
      rw [hD_t, ContinuousLinearMap.map_sub]
      abel
    rw [h_eq] at hsub
    exact hsub
  have h0_deriv : ∀ t ∈ Set.Ioo a b', HasDerivAt (fun _ : ℝ => (0 : G)) (A t ((fun _ => 0) t))
    t := by
    intro t _
    have h0 : HasDerivAt (fun _ : ℝ => (0 : G)) 0 t := hasDerivAt_const _ _
    have h_eq : (A t ((fun _ : ℝ => (0 : G)) t)) = 0 := by
      change A t 0 = 0
      rw [ContinuousLinearMap.map_zero]
    rw [h_eq]
    exact h0
  have hD_initial : D h₀ = (fun _ : ℝ => (0 : G)) h₀ := by
    change Z₁ h₀ - Z₂ h₀ = 0
    rw [heq, sub_self]
  have hD_eq_zero : Set.EqOn D (fun _ : ℝ => (0 : G)) (Set.Ioo a b') :=
    linearODE_unique_on_Ioo ht₀ hA_cont hD_deriv h0_deriv hD_initial
  intro t ht
  have h : D t = 0 := hD_eq_zero ht
  have h' : Z₁ t - Z₂ t = 0 := h
  exact sub_eq_zero.mp h'

theorem variationalW_add_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (v₁ v₂ : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    variationalSolution A a b' h₀ Z₀ x (v₁ + v₂) t =
      variationalSolution A a b' h₀ Z₀ x v₁ t + variationalSolution A a b' h₀ Z₀ x v₂ t := by
  set Z₁ : ℝ → G := fun s => variationalSolution A a b' h₀ Z₀ x (v₁ + v₂) s with hZ₁_def
  set Z₂ : ℝ → G := fun s =>
    variationalSolution A a b' h₀ Z₀ x v₁ s + variationalSolution A a b' h₀ Z₀ x v₂ s with hZ₂_def
  set b : F → ℝ → G := fun y s => variationalForcing A a b' h₀ Z₀ y (v₁ + v₂) s with hb_def
  have hZ₁_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁
      ((fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
          (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (Z₁ s)) s := by
    intro s hs
    have := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx (v₁ + v₂) hs
    exact this
  have hZ₂_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂
      ((fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
          (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (Z₂ s)) s := by
    intro s hs
    have h1 := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v₁ hs
    have h2 := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v₂ hs
    have hsum := h1.add h2
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) v₁ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₁ s)
          + ((fderiv ℝ (fun y => A y s) x) v₂ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₂ s))
        = (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s) := by
      have hfderiv_add :
          (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            = (fderiv ℝ (fun y => A y s) x) v₁ + (fderiv ℝ (fun y => A y s) x) v₂ :=
        ContinuousLinearMap.map_add _ _ _
      rw [hfderiv_add]
      change
        (fderiv ℝ (fun y => A y s) x) v₁ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₁ s)
          + ((fderiv ℝ (fun y => A y s) x) v₂ (linearODESolution A a b' h₀ Z₀ x s)
            + A x s (variationalSolution A a b' h₀ Z₀ x v₂ s))
        = ((fderiv ℝ (fun y => A y s) x) v₁ + (fderiv ℝ (fun y => A y s) x) v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (variationalSolution A a b' h₀ Z₀ x v₁ s
              + variationalSolution A a b' h₀ Z₀ x v₂ s)
      rw [add_apply, ContinuousLinearMap.map_add]
      abel
    rw [← h_eq]
    exact hsum
  set Ax : ℝ → (G →L[ℝ] G) := fun s => A x s with hAx_def
  have hAx_cont : ContinuousOn Ax (Set.Ioo a b') := by
    intro s hs
    have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
      have : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hs⟩
      have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
      exact (hA_cont.continuousAt (hopen.mem_nhds this))
    have hAx_at : ContinuousAt Ax s := by
      have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
        Continuous.continuousAt (by continuity)
      exact h.comp hcurve
    exact hAx_at.continuousWithinAt
  set bs : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) (v₁ + v₂) (linearODESolution A a b' h₀ Z₀ x s)
    with hbs_def
  have hZ₁_deriv' : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁ (Ax s (Z₁ s) + bs s) s := by
    intro s hs
    have h := hZ₁_deriv s hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = Ax s (Z₁ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = A x s (Z₁ s)
          + (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₂_deriv' : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂ (Ax s (Z₂ s) + bs s) s := by
    intro s hs
    have h := hZ₂_deriv s hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s)
        = Ax s (Z₂ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₂ s)
        = A x s (Z₂ s)
          + (fderiv ℝ (fun y => A y s) x) (v₁ + v₂)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₁_initial : Z₁ h₀ = (fderiv ℝ Z₀ x) (v₁ + v₂) :=
    variationalW_initial A a b' h₀ Z₀ x (v₁ + v₂)
  have hZ₂_initial : Z₂ h₀ = (fderiv ℝ Z₀ x) v₁ + (fderiv ℝ Z₀ x) v₂ := by
    change variationalSolution A a b' h₀ Z₀ x v₁ h₀ + variationalSolution A a b' h₀ Z₀ x v₂ h₀
      = (fderiv ℝ Z₀ x) v₁ + (fderiv ℝ Z₀ x) v₂
    rw [variationalW_initial, variationalW_initial]
  have hinit_eq : Z₁ h₀ = Z₂ h₀ := by
    rw [hZ₁_initial, hZ₂_initial, ContinuousLinearMap.map_add]
  have heq := inhomogLinearODE_unique_on_Ioo h₀_mem hAx_cont hZ₁_deriv' hZ₂_deriv' hinit_eq
  exact heq ht

theorem variationalW_smul_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) (c : ℝ) (v : F) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    variationalSolution A a b' h₀ Z₀ x (c • v) t = c • variationalSolution A a b' h₀ Z₀ x v t := by
  set Z₁ : ℝ → G := fun s => variationalSolution A a b' h₀ Z₀ x (c • v) s with hZ₁_def
  set Z₂ : ℝ → G := fun s => c • variationalSolution A a b' h₀ Z₀ x v s with hZ₂_def
  set Ax : ℝ → (G →L[ℝ] G) := fun s => A x s with hAx_def
  have hAx_cont : ContinuousOn Ax (Set.Ioo a b') := by
    intro s hs
    have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
      have : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hs⟩
      have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
      exact (hA_cont.continuousAt (hopen.mem_nhds this))
    have hAx_at : ContinuousAt Ax s := by
      have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
        Continuous.continuousAt (by continuity)
      exact h.comp hcurve
    exact hAx_at.continuousWithinAt
  set bs : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) (c • v) (linearODESolution A a b' h₀ Z₀ x s)
    with hbs_def
  have hZ₁_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₁ (Ax s (Z₁ s) + bs s) s := by
    intro s hs
    have h := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx (c • v) hs
    have h_eq :
        (fderiv ℝ (fun y => A y s) x) (c • v)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = Ax s (Z₁ s) + bs s := by
      change
        (fderiv ℝ (fun y => A y s) x) (c • v)
            (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (Z₁ s)
        = A x s (Z₁ s)
          + (fderiv ℝ (fun y => A y s) x) (c • v)
              (linearODESolution A a b' h₀ Z₀ x s)
      abel
    rw [h_eq] at h
    exact h
  have hZ₂_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt Z₂ (Ax s (Z₂ s) + bs s) s := by
    intro s hs
    have h := variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v hs
    have hsmul : HasDerivAt (fun s' => c • variationalSolution A a b' h₀ Z₀ x v s')
        (c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (variationalSolution A a b' h₀ Z₀ x v s))) s := h.const_smul c
    have h_eq :
        c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
              + A x s (variationalSolution A a b' h₀ Z₀ x v s))
        = Ax s (Z₂ s) + bs s := by
      have hL :
          (fderiv ℝ (fun y => A y s) x) (c • v)
            = c • (fderiv ℝ (fun y => A y s) x) v :=
        ContinuousLinearMap.map_smul _ _ _
      change
        c • ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
              + A x s (variationalSolution A a b' h₀ Z₀ x v s))
        = A x s (c • variationalSolution A a b' h₀ Z₀ x v s)
          + (fderiv ℝ (fun y => A y s) x) (c • v)
              (linearODESolution A a b' h₀ Z₀ x s)
      rw [hL, smul_apply, ContinuousLinearMap.map_smul, smul_add]
      abel
    rw [← h_eq]
    exact hsmul
  have hZ₁_initial : Z₁ h₀ = (fderiv ℝ Z₀ x) (c • v) :=
    variationalW_initial A a b' h₀ Z₀ x (c • v)
  have hZ₂_initial : Z₂ h₀ = c • (fderiv ℝ Z₀ x) v := by
    change c • variationalSolution A a b' h₀ Z₀ x v h₀ = c • (fderiv ℝ Z₀ x) v
    rw [variationalW_initial]
  have hinit_eq : Z₁ h₀ = Z₂ h₀ := by
    rw [hZ₁_initial, hZ₂_initial, ContinuousLinearMap.map_smul]
  have heq := inhomogLinearODE_unique_on_Ioo h₀_mem hAx_cont hZ₁_deriv hZ₂_deriv hinit_eq
  exact heq ht

theorem variationalW_linear_in_v
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    (∀ v₁ v₂ : F, variationalSolution A a b' h₀ Z₀ x (v₁ + v₂) t =
        variationalSolution A a b' h₀ Z₀ x v₁ t + variationalSolution A a b' h₀ Z₀ x v₂ t) ∧
    (∀ (c : ℝ) (v : F), variationalSolution A a b' h₀ Z₀ x (c • v) t =
        c • variationalSolution A a b' h₀ Z₀ x v t) :=
  ⟨fun v₁ v₂ => variationalW_add_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont hx v₁ v₂ ht,
   fun c v => variationalW_smul_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont hx c v ht⟩

theorem portPrivate_b35c1e36_variationalW_norm_bound_on_Icc
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U)
    {α β : ℝ} (_hαβ : α ≤ β) (hα_lt : a < α) (hβ_lt : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    (M P Q R : ℝ) (hM_nn : 0 ≤ M) (hP_nn : 0 ≤ P) (hQ_nn : 0 ≤ Q) (hR_nn : 0 ≤ R)
    (hA_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M)
    (hDA_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun y => A y s) x‖ ≤ P)
    (hZ_bd : ∀ s ∈ Set.Icc α β, ‖linearODESolution A a b' h₀ Z₀ x s‖ ≤ Q)
    (hZ₀'_bd : ‖fderiv ℝ Z₀ x‖ ≤ R)
    (v : F) (t : ℝ) (ht : t ∈ Set.Icc α β) :
    ‖variationalSolution A a b' h₀ Z₀ x v t‖
      ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ := by
  set W : ℝ → G := variationalSolution A a b' h₀ Z₀ x v with hW_def
  have hsub_open : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hW_deriv : ∀ s ∈ Set.Icc α β,
      HasDerivAt W
        ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)) s := fun s hs =>
    variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont
      hx v (hsub_open hs)
  have hW_cont : ContinuousOn W (Set.Icc α β) := fun s hs =>
    ((hW_deriv s hs).continuousAt).continuousWithinAt
  have hW_initial : W h₀ = (fderiv ℝ Z₀ x) v := variationalW_initial A a b' h₀ Z₀ x v
  set bv : ℝ → G := fun s =>
    (fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s) with hbv_def
  have hbv_bd : ∀ s ∈ Set.Icc α β, ‖bv s‖ ≤ P * Q * ‖v‖ := by
    intro s hs
    have h1 : ‖(fderiv ℝ (fun y => A y s) x) v‖
        ≤ ‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖ :=
      (fderiv ℝ (fun y => A y s) x).le_opNorm v
    have h2 : ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)‖
        ≤ ‖(fderiv ℝ (fun y => A y s) x) v‖ * ‖linearODESolution A a b' h₀ Z₀ x s‖ :=
      ((fderiv ℝ (fun y => A y s) x) v).le_opNorm _
    have h3 : ‖(fderiv ℝ (fun y => A y s) x) v‖ * ‖linearODESolution A a b' h₀ Z₀ x s‖
        ≤ (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have h4 : (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖
        ≤ (P * ‖v‖) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hDA_bd s hs) (norm_nonneg _))
        (hZ_bd s hs) (norm_nonneg _) (by positivity)
    calc ‖bv s‖ ≤ ‖(fderiv ℝ (fun y => A y s) x) v‖
                  * ‖linearODESolution A a b' h₀ Z₀ x s‖ := h2
      _ ≤ (‖fderiv ℝ (fun y => A y s) x‖ * ‖v‖)
            * ‖linearODESolution A a b' h₀ Z₀ x s‖ := h3
      _ ≤ (P * ‖v‖) * Q := h4
      _ = P * Q * ‖v‖ := by ring
  have h_h₀_le_β : h₀ ≤ β := hh₀_mem.2
  have h_α_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
    ⟨le_trans h_α_le_h₀ hs.1, hs.2⟩
  have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
    ⟨hs.1, le_trans hs.2 h_h₀_le_β⟩
  have hW'_bound : ∀ s ∈ Set.Icc α β,
      ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
        + A x s (W s)‖ ≤ M * ‖W s‖ + P * Q * ‖v‖ := by
    intro s hs
    have ha : ‖A x s (W s)‖ ≤ M * ‖W s‖ := by
      have h1 : ‖A x s (W s)‖ ≤ ‖A x s‖ * ‖W s‖ := (A x s).le_opNorm (W s)
      have h2 : ‖A x s‖ * ‖W s‖ ≤ M * ‖W s‖ :=
        mul_le_mul_of_nonneg_right (hA_bd s hs) (norm_nonneg _)
      linarith
    have hb : ‖bv s‖ ≤ P * Q * ‖v‖ := hbv_bd s hs
    have h_tri := norm_add_le (bv s) (A x s (W s))
    calc ‖bv s + A x s (W s)‖
        ≤ ‖bv s‖ + ‖A x s (W s)‖ := h_tri
      _ ≤ P * Q * ‖v‖ + M * ‖W s‖ := by linarith
      _ = M * ‖W s‖ + P * Q * ‖v‖ := by ring
  have hW_initial_bd : ‖W h₀‖ ≤ R * ‖v‖ := by
    rw [hW_initial]
    calc ‖(fderiv ℝ Z₀ x) v‖
        ≤ ‖fderiv ℝ Z₀ x‖ * ‖v‖ := (fderiv ℝ Z₀ x).le_opNorm v
      _ ≤ R * ‖v‖ := mul_le_mul_of_nonneg_right hZ₀'_bd (norm_nonneg _)
  have hv_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have hPQ_nn : 0 ≤ P * Q := mul_nonneg hP_nn hQ_nn
  have h_gb_scale : ∀ y : ℝ,
      gronwallBound (R * ‖v‖) M (P * Q * ‖v‖) y
        = gronwallBound R M (P * Q) y * ‖v‖ := by
    intro y
    by_cases hM_eq : M = 0
    · simp only [gronwallBound_K0, hM_eq]
      ring
    · simp only [gronwallBound_of_K_ne_0 hM_eq]
      field_simp
  have h_gb_mono : ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ →
      gronwallBound R M (P * Q) y₁ ≤ gronwallBound R M (P * Q) y₂ :=
    fun y₁ y₂ hy => gronwallBound_mono hR_nn hPQ_nn hM_nn hy
  rcases le_total h₀ t with hh₀t | hth₀
  · have ht' : t ∈ Set.Icc h₀ β := ⟨hh₀t, ht.2⟩
    have hW_cont_fwd : ContinuousOn W (Set.Icc h₀ β) := hW_cont.mono hIcc_fwd_sub
    have hW_deriv_right : ∀ s ∈ Set.Ico h₀ β, HasDerivWithinAt W
        ((fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)) (Set.Ici s) s := fun s hs =>
      (hW_deriv s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have hbound_fwd : ∀ s ∈ Set.Ico h₀ β,
        ‖(fderiv ℝ (fun y => A y s) x) v (linearODESolution A a b' h₀ Z₀ x s)
          + A x s (W s)‖ ≤ M * ‖W s‖ + P * Q * ‖v‖ := fun s hs =>
      hW'_bound s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le
      hW_cont_fwd hW_deriv_right hW_initial_bd hbound_fwd t ht'
    rw [h_gb_scale (t - h₀)] at hgw
    have h_t_sub_le : t - h₀ ≤ β - α := by linarith [ht.2, h_α_le_h₀]
    have h_step : gronwallBound R M (P * Q) (t - h₀) ≤ gronwallBound R M (P * Q) (β - α) :=
      h_gb_mono _ _ h_t_sub_le
    calc ‖W t‖
        ≤ gronwallBound R M (P * Q) (t - h₀) * ‖v‖ := hgw
      _ ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ :=
          mul_le_mul_of_nonneg_right h_step hv_nn
  · have ht' : t ∈ Set.Icc α h₀ := ⟨ht.1, hth₀⟩
    set Wb : ℝ → G := fun s => W (2 * h₀ - s) with hWb_def
    have h_h₀_le_2h₀mt : h₀ ≤ 2 * h₀ - t := by linarith
    have h_dom_swap : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t), 2 * h₀ - s ∈ Set.Icc α h₀ := by
      intro s hs
      refine ⟨?_, ?_⟩
      · linarith [hs.2, ht'.1]
      · linarith [hs.1]
    have hWb_cont : ContinuousOn Wb (Set.Icc h₀ (2 * h₀ - t)) := by
      apply ContinuousOn.comp (hW_cont.mono hIcc_bwd_sub) (s := Set.Icc h₀ (2 * h₀ - t))
        (t := Set.Icc α h₀) (f := fun s => 2 * h₀ - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_swap
    have hWb_deriv : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        HasDerivAt Wb (-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))) s := by
      intro s hs
      have hd : HasDerivAt W
          ((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
            (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
          + A x (2 * h₀ - s) (W (2 * h₀ - s))) (2 * h₀ - s) :=
        hW_deriv (2 * h₀ - s) (hIcc_bwd_sub (h_dom_swap s hs))
      have h_chain : HasDerivAt (fun r : ℝ => 2 * h₀ - r) (-1 : ℝ) s := by
        refine (((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)).congr_of_eventuallyEq
          ?_).congr_deriv ?_
        · exact Filter.Eventually.of_forall fun r => by
            change 2 * h₀ - r = 2 * h₀ - r
            rfl
        · norm_num
      have hd' := hd.scomp s h_chain
      have h_eq_smul :
          (-1 : ℝ) • ((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))
          = -((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s))) :=
        neg_one_smul ℝ _
      rw [h_eq_smul] at hd'
      exact hd'
    have hWb_initial : Wb h₀ = W h₀ := by
      change W (2 * h₀ - h₀) = W h₀
      have : 2 * h₀ - h₀ = h₀ := by ring
      rw [this]
    have hWb'_bound : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        ‖-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))‖
          ≤ M * ‖Wb s‖ + P * Q * ‖v‖ := by
      intro s hs
      have h_in : 2 * h₀ - s ∈ Set.Icc α β := hIcc_bwd_sub (h_dom_swap s hs)
      have h := hW'_bound (2 * h₀ - s) h_in
      have hWbs_eq : Wb s = W (2 * h₀ - s) := rfl
      rw [norm_neg, hWbs_eq]
      exact h
    have hWb_initial_bd : ‖Wb h₀‖ ≤ R * ‖v‖ := by
      rw [hWb_initial]; exact hW_initial_bd
    have hWb_deriv_right : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        HasDerivWithinAt Wb (-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
            (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
          + A x (2 * h₀ - s) (W (2 * h₀ - s)))) (Set.Ici s) s := fun s hs =>
      (hWb_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hbound_bwd : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        ‖-((fderiv ℝ (fun y => A y (2 * h₀ - s)) x) v
              (linearODESolution A a b' h₀ Z₀ x (2 * h₀ - s))
            + A x (2 * h₀ - s) (W (2 * h₀ - s)))‖
          ≤ M * ‖Wb s‖ + P * Q * ‖v‖ := fun s hs =>
      hWb'_bound s (Set.Ico_subset_Icc_self hs)
    have hgw_bwd := norm_le_gronwallBound_of_norm_deriv_right_le
      hWb_cont hWb_deriv_right hWb_initial_bd hbound_bwd
      (2 * h₀ - t) (right_mem_Icc.mpr h_h₀_le_2h₀mt)
    have hWb_t : Wb (2 * h₀ - t) = W t := by
      change W (2 * h₀ - (2 * h₀ - t)) = W t
      have : 2 * h₀ - (2 * h₀ - t) = t := by ring
      rw [this]
    rw [hWb_t] at hgw_bwd
    have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
    rw [h_time] at hgw_bwd
    rw [h_gb_scale (h₀ - t)] at hgw_bwd
    have h_h₀mt_le : h₀ - t ≤ β - α := by linarith [ht.1, h_h₀_le_β]
    have h_step : gronwallBound R M (P * Q) (h₀ - t) ≤ gronwallBound R M (P * Q) (β - α) :=
      h_gb_mono _ _ h_h₀mt_le
    calc ‖W t‖
        ≤ gronwallBound R M (P * Q) (h₀ - t) * ‖v‖ := hgw_bwd
      _ ≤ gronwallBound R M (P * Q) (β - α) * ‖v‖ :=
          mul_le_mul_of_nonneg_right h_step hv_nn

noncomputable def variationalWClm
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ}
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    F →L[ℝ] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun v => variationalSolution A a b' h₀ Z₀ x v t
      map_add' := fun v₁ v₂ =>
        variationalW_add_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont hx v₁ v₂ ht
      map_smul' := fun c v => by
        have h := variationalW_smul_in_v h₀_mem hU hA_cont hDA_cont hZ₀_cont
          hx c v ht
        simpa using h }
    (by
      classical
      set α := (a + min t h₀) / 2 with hα_def
      set β := (b' + max t h₀) / 2 with hβ_def
      have hmin_lt : a < min t h₀ := lt_min ht.1 h₀_mem.1
      have hmax_lt : max t h₀ < b' := max_lt ht.2 h₀_mem.2
      have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
      have hmin_le_t₀ : min t h₀ ≤ h₀ := min_le_right _ _
      have ht_le_max : t ≤ max t h₀ := le_max_left _ _
      have ht₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
      have hα_lt_min : α < min t h₀ := by rw [hα_def]; linarith
      have ha_lt_α : a < α := by rw [hα_def]; linarith
      have hmax_lt_β : max t h₀ < β := by rw [hβ_def]; linarith
      have hβ_lt_b' : β < b' := by rw [hβ_def]; linarith
      have hα_le_β : α ≤ β := by linarith
      have hh₀_mem : h₀ ∈ Set.Icc α β :=
        ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t₀),
         le_of_lt (lt_of_le_of_lt ht₀_le_max hmax_lt_β)⟩
      have h_t_Icc : t ∈ Set.Icc α β :=
        ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t),
         le_of_lt (lt_of_le_of_lt ht_le_max hmax_lt_β)⟩
      have hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
        ⟨lt_of_lt_of_le ha_lt_α hs.1, lt_of_le_of_lt hs.2 hβ_lt_b'⟩
      have hIcc_compact : IsCompact (Set.Icc α β) := isCompact_Icc
      have hIcc_ne : (Set.Icc α β).Nonempty := ⟨α, left_mem_Icc.mpr hα_le_β⟩
      have hAx_cont_Icc : ContinuousOn (fun s => A x s) (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (fun p : F × ℝ => A p.1 p.2) (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hA_cont.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normA_cont : ContinuousOn (fun s => ‖A x s‖) (Set.Icc α β) :=
        continuous_norm.comp_continuousOn hAx_cont_Icc
      obtain ⟨σM, _, hM_bd⟩ := hIcc_compact.exists_isMaxOn hIcc_ne h_normA_cont
      let Mv : ℝ := ‖A x σM‖
      have hMv_nn : 0 ≤ Mv := norm_nonneg _
      have hMv_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ Mv := fun s hs => hM_bd hs
      have hDAx_cont_Icc : ContinuousOn (fun s => fderiv ℝ (fun y => A y s) x)
          (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (Function.uncurry fun x' t' => fderiv ℝ (fun y => A y t') x')
            (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hDA_cont.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normDA_cont : ContinuousOn (fun s => ‖fderiv ℝ (fun y => A y s) x‖)
          (Set.Icc α β) := by
        simpa only using hDAx_cont_Icc.norm
      obtain ⟨σP, _, hP_bd⟩ := hIcc_compact.exists_isMaxOn hIcc_ne h_normDA_cont
      let Pv : ℝ := ‖fderiv ℝ (fun y => A y σP) x‖
      have hPv_nn : 0 ≤ Pv := norm_nonneg _
      have hPv_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun y => A y s) x‖ ≤ Pv :=
        fun s hs => hP_bd hs
      have hZ_cont_full : ContinuousOn (Function.uncurry (linearODESolution A a b' h₀ Z₀))
          (U ×ˢ Set.Ioo a b') :=
        linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont
      have hZx_cont_Icc : ContinuousOn (linearODESolution A a b' h₀ Z₀ x) (Set.Icc α β) := by
        intro s hs
        have h : ContinuousAt (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (x, s) := by
          have hxs : (x, s) ∈ U ×ˢ Set.Ioo a b' := ⟨hx, hIcc_sub hs⟩
          have hopen : IsOpen (U ×ˢ Set.Ioo a b') := hU.prod isOpen_Ioo
          exact hZ_cont_full.continuousAt (hopen.mem_nhds hxs)
        have hcurve : ContinuousAt (fun s' : ℝ => ((x, s') : F × ℝ)) s :=
          Continuous.continuousAt (by continuity)
        exact (h.comp hcurve).continuousWithinAt
      have h_normZ_cont : ContinuousOn (fun s => ‖linearODESolution A a b' h₀ Z₀ x s‖)
          (Set.Icc α β) := continuous_norm.comp_continuousOn hZx_cont_Icc
      obtain ⟨σQ, _, hQ_bd⟩ := hIcc_compact.exists_isMaxOn hIcc_ne h_normZ_cont
      let Qv : ℝ := ‖linearODESolution A a b' h₀ Z₀ x σQ‖
      have hQv_nn : 0 ≤ Qv := norm_nonneg _
      have hQv_bd : ∀ s ∈ Set.Icc α β, ‖linearODESolution A a b' h₀ Z₀ x s‖ ≤ Qv :=
        fun s hs => hQ_bd hs
      let Rv : ℝ := ‖fderiv ℝ Z₀ x‖
      have hRv_nn : 0 ≤ Rv := norm_nonneg _
      refine ⟨gronwallBound Rv Mv (Pv * Qv) (β - α), fun v => ?_⟩
      have h := portPrivate_b35c1e36_variationalW_norm_bound_on_Icc h₀_mem hU hA_cont hDA_cont hZ₀_cont
        hx hα_le_β ha_lt_α hβ_lt_b' hh₀_mem Mv Pv Qv Rv hMv_nn hPv_nn hQv_nn hRv_nn
        hMv_bd hPv_bd hQv_bd le_rfl v t h_t_Icc
      simpa using h)

@[simp]
theorem variationalW_clm_apply
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ}
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') (v : F) :
    variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht v
      = variationalSolution A a b' h₀ Z₀ x v t := rfl

omit [NormedSpace ℝ F] in
theorem linearODESolution_dist_le
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    {x₁ x₂ : F} (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U)
    {α β : ℝ} (hα_lt : a < α) (hβ_lt : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    {K η : ℝ} (hK_nn : 0 ≤ K)
    (hA₁_bd : ∀ s ∈ Set.Icc α β, ‖A x₁ s‖ ≤ K)
    (hdiff_bd : ∀ s ∈ Set.Icc α β,
      ‖(A x₂ s - A x₁ s) (linearODESolution A a b' h₀ Z₀ x₂ s)‖ ≤ η)
    {t : ℝ} (ht : t ∈ Set.Icc α β) :
    ‖linearODESolution A a b' h₀ Z₀ x₁ t - linearODESolution A a b' h₀ Z₀ x₂ t‖
      ≤ gronwallBound ‖Z₀ x₁ - Z₀ x₂‖ K η |t - h₀| := by
  set Z : F → ℝ → G := linearODESolution A a b' h₀ Z₀ with hZ_def
  have hZ_deriv₁ : ∀ s ∈ Set.Ioo a b', HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
    fun s hs => linearODESolution_hasDerivAt h₀_mem hA_cont hx₁ hs
  have hZ_deriv₂ : ∀ s ∈ Set.Ioo a b', HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
    fun s hs => linearODESolution_hasDerivAt h₀_mem hA_cont hx₂ hs
  have hZ_initial₁ : Z x₁ h₀ = Z₀ x₁ := linearODESolution_initial A a b' h₀ Z₀ x₁
  have hZ_initial₂ : Z x₂ h₀ = Z₀ x₂ := linearODESolution_initial A a b' h₀ Z₀ x₂
  have hIcc_sub_Ioo : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le hα_lt hs.1, lt_of_le_of_lt hs.2 hβ_lt⟩
  have hZ_cont₁ : ContinuousOn (Z x₁) (Set.Icc α β) := fun s hs =>
    ((hZ_deriv₁ s (hIcc_sub_Ioo hs)).continuousAt).continuousWithinAt
  have hZ_cont₂ : ContinuousOn (Z x₂) (Set.Icc α β) := fun s hs =>
    ((hZ_deriv₂ s (hIcc_sub_Ioo hs)).continuousAt).continuousWithinAt
  have hα_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have hh₀_le_β : h₀ ≤ β := hh₀_mem.2
  rcases le_total h₀ t with hht | hth
  · have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
      ⟨le_trans hα_le_h₀ hs.1, hs.2⟩
    have hZ₁_cont_fwd : ContinuousOn (Z x₁) (Set.Icc h₀ β) := hZ_cont₁.mono hIcc_fwd_sub
    have hZ₂_cont_fwd : ContinuousOn (Z x₂) (Set.Icc h₀ β) := hZ_cont₂.mono hIcc_fwd_sub
    have hZ₁_deriv_fwd : ∀ s ∈ Set.Icc h₀ β, HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
      fun s hs => hZ_deriv₁ s (hIcc_sub_Ioo (hIcc_fwd_sub hs))
    have hZ₂_deriv_fwd : ∀ s ∈ Set.Icc h₀ β, HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
      fun s hs => hZ_deriv₂ s (hIcc_sub_Ioo (hIcc_fwd_sub hs))
    have hA₁_bd_fwd : ∀ s ∈ Set.Icc h₀ β, ‖A x₁ s‖ ≤ K := fun s hs =>
      hA₁_bd s (hIcc_fwd_sub hs)
    have hdiff_bd_fwd : ∀ s ∈ Set.Icc h₀ β,
        ‖(A x₂ s - A x₁ s) (Z x₂ s)‖ ≤ η := fun s hs =>
      hdiff_bd s (hIcc_fwd_sub hs)
    have hres := linearODE_gronwall_forward (A₁ := A x₁) (A₂ := A x₂)
      (Z₁ := Z x₁) (Z₂ := Z x₂) (h₀ := h₀) (β := β) (K := K) (η := η)
      hK_nn hZ₁_cont_fwd hZ₂_cont_fwd hZ₁_deriv_fwd hZ₂_deriv_fwd
      hA₁_bd_fwd hdiff_bd_fwd t ⟨hht, ht.2⟩
    have h_initial_eq : ‖Z x₁ h₀ - Z x₂ h₀‖ = ‖Z₀ x₁ - Z₀ x₂‖ := by
      rw [hZ_initial₁, hZ_initial₂]
    rw [h_initial_eq] at hres
    have h_abs : |t - h₀| = t - h₀ := abs_of_nonneg (by linarith)
    rw [h_abs]
    exact hres
  · have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
      ⟨hs.1, le_trans hs.2 hh₀_le_β⟩
    have hZ₁_cont_bwd : ContinuousOn (Z x₁) (Set.Icc α h₀) := hZ_cont₁.mono hIcc_bwd_sub
    have hZ₂_cont_bwd : ContinuousOn (Z x₂) (Set.Icc α h₀) := hZ_cont₂.mono hIcc_bwd_sub
    have hZ₁_deriv_bwd : ∀ s ∈ Set.Icc α h₀, HasDerivAt (Z x₁) (A x₁ s (Z x₁ s)) s :=
      fun s hs => hZ_deriv₁ s (hIcc_sub_Ioo (hIcc_bwd_sub hs))
    have hZ₂_deriv_bwd : ∀ s ∈ Set.Icc α h₀, HasDerivAt (Z x₂) (A x₂ s (Z x₂ s)) s :=
      fun s hs => hZ_deriv₂ s (hIcc_sub_Ioo (hIcc_bwd_sub hs))
    have hA₁_bd_bwd : ∀ s ∈ Set.Icc α h₀, ‖A x₁ s‖ ≤ K := fun s hs =>
      hA₁_bd s (hIcc_bwd_sub hs)
    have hdiff_bd_bwd : ∀ s ∈ Set.Icc α h₀,
        ‖(A x₂ s - A x₁ s) (Z x₂ s)‖ ≤ η := fun s hs =>
      hdiff_bd s (hIcc_bwd_sub hs)
    have hres := linearODE_gronwall_backward (A₁ := A x₁) (A₂ := A x₂)
      (Z₁ := Z x₁) (Z₂ := Z x₂) (α := α) (h₀ := h₀) (K := K) (η := η)
      hα_le_h₀ hK_nn hZ₁_cont_bwd hZ₂_cont_bwd hZ₁_deriv_bwd hZ₂_deriv_bwd
      hA₁_bd_bwd hdiff_bd_bwd t ⟨ht.1, hth⟩
    have h_initial_eq : ‖Z x₁ h₀ - Z x₂ h₀‖ = ‖Z₀ x₁ - Z₀ x₂‖ := by
      rw [hZ_initial₁, hZ_initial₂]
    rw [h_initial_eq] at hres
    have h_abs : |t - h₀| = h₀ - t := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [h_abs]
    exact hres

omit [CompleteSpace G] in
theorem norm_le_gronwallBound_on_Icc
    {R R' : ℝ → G} {α β h₀ t r₀ K η : ℝ}
    (hh₀_mem : h₀ ∈ Set.Icc α β) (ht_mem : t ∈ Set.Icc α β)
    (hr₀_nn : 0 ≤ r₀) (hK_nn : 0 ≤ K) (hη_nn : 0 ≤ η)
    (hR_cont : ContinuousOn R (Set.Icc α β))
    (hR_deriv : ∀ s ∈ Set.Icc α β, HasDerivAt R (R' s) s)
    (hR_initial : ‖R h₀‖ ≤ r₀)
    (hR_bd : ∀ s ∈ Set.Icc α β, ‖R' s‖ ≤ K * ‖R s‖ + η) :
    ‖R t‖ ≤ gronwallBound r₀ K η (β - α) := by
  have h_α_le_h₀ : α ≤ h₀ := hh₀_mem.1
  have h_h₀_le_β : h₀ ≤ β := hh₀_mem.2
  rcases le_total h₀ t with hht | hth
  · have ht_fwd : t ∈ Set.Icc h₀ β := ⟨hht, ht_mem.2⟩
    have hIcc_fwd_sub : Set.Icc h₀ β ⊆ Set.Icc α β := fun s hs =>
      ⟨le_trans h_α_le_h₀ hs.1, hs.2⟩
    have hR_cont_fwd : ContinuousOn R (Set.Icc h₀ β) :=
      hR_cont.mono hIcc_fwd_sub
    have hR_deriv_within_right : ∀ s ∈ Set.Ico h₀ β,
        HasDerivWithinAt R (R' s) (Set.Ici s) s := fun s hs =>
      (hR_deriv s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))).hasDerivWithinAt
    have h_bound_fwd : ∀ s ∈ Set.Ico h₀ β,
        ‖R' s‖ ≤ K * ‖R s‖ + η := fun s hs =>
      hR_bd s (hIcc_fwd_sub (Set.Ico_subset_Icc_self hs))
    have hgw := norm_le_gronwallBound_of_norm_deriv_right_le
      hR_cont_fwd hR_deriv_within_right hR_initial h_bound_fwd t ht_fwd
    have h_t_sub_le : t - h₀ ≤ β - α := by
      linarith [ht_mem.2, h_α_le_h₀]
    have h_mono :
        gronwallBound r₀ K η (t - h₀) ≤
          gronwallBound r₀ K η (β - α) :=
      gronwallBound_mono hr₀_nn hη_nn hK_nn h_t_sub_le
    exact hgw.trans h_mono
  · have ht_bwd : t ∈ Set.Icc α h₀ := ⟨ht_mem.1, hth⟩
    have hIcc_bwd_sub : Set.Icc α h₀ ⊆ Set.Icc α β := fun s hs =>
      ⟨hs.1, le_trans hs.2 h_h₀_le_β⟩
    let Rb : ℝ → G := fun s => R (2 * h₀ - s)
    have h_h₀_le_2h₀_t : h₀ ≤ 2 * h₀ - t := by linarith
    have h_dom_swap :
        ∀ s ∈ Set.Icc h₀ (2 * h₀ - t), 2 * h₀ - s ∈ Set.Icc α h₀ := by
      intro s hs
      refine ⟨?_, ?_⟩ <;> linarith [hs.1, hs.2, ht_bwd.1]
    have hRb_cont : ContinuousOn Rb (Set.Icc h₀ (2 * h₀ - t)) := by
      apply ContinuousOn.comp (hR_cont.mono hIcc_bwd_sub)
        (s := Set.Icc h₀ (2 * h₀ - t)) (t := Set.Icc α h₀)
        (f := fun s => 2 * h₀ - s)
      · exact (continuous_const.sub continuous_id).continuousOn
      · exact h_dom_swap
    have hRb_deriv : ∀ s ∈ Set.Icc h₀ (2 * h₀ - t),
        HasDerivAt Rb (-(R' (2 * h₀ - s))) s := by
      intro s hs
      have hd := hR_deriv (2 * h₀ - s)
        (hIcc_bwd_sub (h_dom_swap s hs))
      have hchain : HasDerivAt (fun r : ℝ => 2 * h₀ - r) (-1 : ℝ) s := by
        refine (((hasDerivAt_const s (2 * h₀)).sub (hasDerivAt_id s)).congr_of_eventuallyEq
          ?_).congr_deriv ?_
        · exact Filter.Eventually.of_forall fun r => by
            change 2 * h₀ - r = 2 * h₀ - r
            rfl
        · norm_num
      have hd' := hd.scomp s hchain
      rw [show ((-1 : ℝ) • R' (2 * h₀ - s) : G) =
        -(R' (2 * h₀ - s)) by exact neg_one_smul ℝ _] at hd'
      exact hd'
    have hRb_deriv_within_right : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        HasDerivWithinAt Rb (-(R' (2 * h₀ - s))) (Set.Ici s) s :=
      fun s hs => (hRb_deriv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt
    have hRb_initial : Rb h₀ = R h₀ := by
      change R (2 * h₀ - h₀) = R h₀
      congr 1
      ring
    have hRb_initial_bd : ‖Rb h₀‖ ≤ r₀ := by
      rw [hRb_initial]
      exact hR_initial
    have hRb_bd : ∀ s ∈ Set.Ico h₀ (2 * h₀ - t),
        ‖-(R' (2 * h₀ - s))‖ ≤ K * ‖Rb s‖ + η := by
      intro s hs
      have hin : 2 * h₀ - s ∈ Set.Icc α β :=
        hIcc_bwd_sub (h_dom_swap s (Set.Ico_subset_Icc_self hs))
      have hbound := hR_bd (2 * h₀ - s) hin
      rw [norm_neg]
      exact hbound
    have hgw_bwd := norm_le_gronwallBound_of_norm_deriv_right_le
      hRb_cont hRb_deriv_within_right hRb_initial_bd hRb_bd (2 * h₀ - t)
      (right_mem_Icc.mpr h_h₀_le_2h₀_t)
    have hRb_t : Rb (2 * h₀ - t) = R t := by
      change R (2 * h₀ - (2 * h₀ - t)) = R t
      congr 1
      ring
    rw [hRb_t] at hgw_bwd
    have h_time : 2 * h₀ - t - h₀ = h₀ - t := by ring
    rw [h_time] at hgw_bwd
    have h_h₀_sub_t_le : h₀ - t ≤ β - α := by
      linarith [ht_bwd.1, h_h₀_le_β]
    have h_mono :
        gronwallBound r₀ K η (h₀ - t) ≤
          gronwallBound r₀ K η (β - α) :=
      gronwallBound_mono hr₀_nn hη_nn hK_nn h_h₀_sub_t_le
    exact hgw_bwd.trans h_mono

theorem linearODESolution_local_lipschitz_on_Icc
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F}
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    {x : F} {α β δ M P Q L : ℝ}
    (hx : x ∈ U)
    (ha_lt_α : a < α) (hβ_lt_b' : β < b')
    (hh₀_mem : h₀ ∈ Set.Icc α β)
    (hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b')
    (hclosedBall_sub : Metric.closedBall x δ ⊆ U)
    (hδ_nn : 0 ≤ δ) (hM_nn : 0 ≤ M) (hP_nn : 0 ≤ P)
    (hQ_nn : 0 ≤ Q) (hL_nn : 0 ≤ L)
    (hAx_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M)
    (hDA_bd : ∀ y ∈ Metric.closedBall x δ, ∀ s ∈ Set.Icc α β,
      ‖fderiv ℝ (fun z => A z s) y‖ ≤ P)
    (hZ_bd : ∀ y ∈ Metric.closedBall x δ, ∀ s ∈ Set.Icc α β,
      ‖linearODESolution A a b' h₀ Z₀ y s‖ ≤ Q)
    (hDZ₀_bd : ∀ y ∈ Metric.closedBall x δ, ‖fderiv ℝ Z₀ y‖ ≤ L)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) :
    ∀ h : F, ‖h‖ ≤ δ → ∀ s ∈ Set.Icc α β,
      ‖linearODESolution A a b' h₀ Z₀ (x + h) s -
          linearODESolution A a b' h₀ Z₀ x s‖ ≤
        gronwallBound L M (P * Q) (β - α) * ‖h‖ := by
  intro h hh_bd s hs
  have hdist_xh_x : dist (x + h) x = ‖h‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  have hxh_ball : x + h ∈ Metric.closedBall x δ := by
    rw [Metric.mem_closedBall, hdist_xh_x]
    exact hh_bd
  have hxh_U : x + h ∈ U := hclosedBall_sub hxh_ball
  have hConvergence : Convex ℝ (Metric.closedBall x δ) := convex_closedBall _ _
  have hZ₀_lip : ‖Z₀ (x + h) - Z₀ x‖ ≤ L * ‖h‖ := by
    have hdiff : ∀ y ∈ Metric.closedBall x δ, DifferentiableAt ℝ Z₀ y :=
      fun y hy => (hZ₀_diff y (hclosedBall_sub hy)).differentiableAt
    have hres := hConvergence.norm_image_sub_le_of_norm_fderiv_le
      hdiff hDZ₀_bd (Metric.mem_closedBall_self hδ_nn) hxh_ball
    have hsub_eq : x + h - x = h := by abel
    rw [hsub_eq] at hres
    exact hres
  have h_force : ∀ s' ∈ Set.Icc α β,
      ‖(A (x + h) s' - A x s')
          (linearODESolution A a b' h₀ Z₀ (x + h) s')‖ ≤
        (P * Q) * ‖h‖ := by
    intro s' hs'
    have hZxh_bd :
        ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ ≤ Q :=
      hZ_bd (x + h) hxh_ball s' hs'
    have hAdiff_bd : ‖A (x + h) s' - A x s'‖ ≤ P * ‖h‖ := by
      have hbd : ∀ y ∈ Metric.closedBall x δ,
          ‖fderiv ℝ (fun z => A z s') y‖ ≤ P :=
        fun y hy => hDA_bd y hy s' hs'
      have hdiff : ∀ y ∈ Metric.closedBall x δ,
          DifferentiableAt ℝ (fun z => A z s') y := fun y hy =>
        (hA_diff y (hclosedBall_sub hy) s' (hIcc_sub hs')).differentiableAt
      have hres := hConvergence.norm_image_sub_le_of_norm_fderiv_le
        hdiff hbd (Metric.mem_closedBall_self hδ_nn) hxh_ball
      have hsub_eq : x + h - x = h := by abel
      rw [hsub_eq] at hres
      exact hres
    have h1 :
        ‖(A (x + h) s' - A x s')
            (linearODESolution A a b' h₀ Z₀ (x + h) s')‖ ≤
          ‖A (x + h) s' - A x s'‖ *
            ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ :=
      (A (x + h) s' - A x s').le_opNorm _
    have h2 :
        ‖A (x + h) s' - A x s'‖ *
            ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ ≤
          (P * ‖h‖) * Q :=
      mul_le_mul hAdiff_bd hZxh_bd (norm_nonneg _)
        (mul_nonneg hP_nn (norm_nonneg _))
    calc
      ‖(A (x + h) s' - A x s')
          (linearODESolution A a b' h₀ Z₀ (x + h) s')‖
          ≤ ‖A (x + h) s' - A x s'‖ *
              ‖linearODESolution A a b' h₀ Z₀ (x + h) s'‖ := h1
      _ ≤ (P * ‖h‖) * Q := h2
      _ = P * Q * ‖h‖ := by ring
  have hgw := linearODESolution_dist_le (A := A) (Z₀ := Z₀)
    h₀_mem hA_cont hx hxh_U ha_lt_α hβ_lt_b' hh₀_mem
    hM_nn hAx_bd h_force hs
  have h_initial_bd : ‖Z₀ x - Z₀ (x + h)‖ ≤ L * ‖h‖ := by
    rw [show Z₀ x - Z₀ (x + h) = -(Z₀ (x + h) - Z₀ x) by abel, norm_neg]
    exact hZ₀_lip
  have h_abs_le : |s - h₀| ≤ β - α := by
    rcases le_total h₀ s with hle | hle
    · rw [abs_of_nonneg (by linarith)]
      linarith [hh₀_mem.1, hs.2]
    · rw [abs_of_nonpos (by linarith)]
      linarith [hs.1, hh₀_mem.2]
  rw [show linearODESolution A a b' h₀ Z₀ x s -
      linearODESolution A a b' h₀ Z₀ (x + h) s =
      -(linearODESolution A a b' h₀ Z₀ (x + h) s -
        linearODESolution A a b' h₀ Z₀ x s) by abel, norm_neg] at hgw
  have h_gb_mono_δ :
      gronwallBound ‖Z₀ x - Z₀ (x + h)‖ M (P * Q * ‖h‖) |s - h₀| ≤
        gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| := by
    by_cases hMeq : M = 0
    · simp only [gronwallBound_K0, hMeq]
      linarith
    · simp only [gronwallBound_of_K_ne_0 hMeq]
      have hexp_nn : 0 ≤ Real.exp (M * |s - h₀|) := (Real.exp_pos _).le
      have hmul : ‖Z₀ x - Z₀ (x + h)‖ * Real.exp (M * |s - h₀|) ≤
          (L * ‖h‖) * Real.exp (M * |s - h₀|) :=
        mul_le_mul_of_nonneg_right h_initial_bd hexp_nn
      linarith
  have h_gb_mono_x :
      gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| ≤
        gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) :=
    gronwallBound_mono (mul_nonneg hL_nn (norm_nonneg _))
      (mul_nonneg (mul_nonneg hP_nn hQ_nn) (norm_nonneg _))
      hM_nn h_abs_le
  have h_gb_scale :
      gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) =
        ‖h‖ * gronwallBound L M (P * Q) (β - α) := by
    by_cases hMeq : M = 0
    · rw [hMeq]
      simp only [gronwallBound_K0]
      ring
    · simp only [gronwallBound_of_K_ne_0 hMeq]
      field_simp
  calc
    ‖linearODESolution A a b' h₀ Z₀ (x + h) s -
        linearODESolution A a b' h₀ Z₀ x s‖
        ≤ gronwallBound ‖Z₀ x - Z₀ (x + h)‖ M
            (P * Q * ‖h‖) |s - h₀| := hgw
    _ ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) |s - h₀| := h_gb_mono_δ
    _ ≤ gronwallBound (L * ‖h‖) M (P * Q * ‖h‖) (β - α) := h_gb_mono_x
    _ = ‖h‖ * gronwallBound L M (P * Q) (β - α) := h_gb_scale
    _ = gronwallBound L M (P * Q) (β - α) * ‖h‖ := mul_comm _ _

theorem linearODESolution_hasFDerivAt_param
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y)
    {x : F} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Set.Ioo a b') :
    HasFDerivAt (fun y => linearODESolution A a b' h₀ Z₀ y t)
      (variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) x := by
  classical
  set Z : F → ℝ → G := linearODESolution A a b' h₀ Z₀ with hZ_def
  set α := (a + min t h₀) / 2 with hα_def
  set β := (b' + max t h₀) / 2 with hβ_def
  have hmin_lt_a : a < min t h₀ := lt_min ht.1 h₀_mem.1
  have hmax_lt_b' : max t h₀ < b' := max_lt ht.2 h₀_mem.2
  have hmin_le_t : min t h₀ ≤ t := min_le_left _ _
  have hmin_le_h₀ : min t h₀ ≤ h₀ := min_le_right _ _
  have ht_le_max : t ≤ max t h₀ := le_max_left _ _
  have hh₀_le_max : h₀ ≤ max t h₀ := le_max_right _ _
  have hα_lt_min : α < min t h₀ := by rw [hα_def]; linarith
  have ha_lt_α : a < α := by rw [hα_def]; linarith
  have hmax_lt_β : max t h₀ < β := by rw [hβ_def]; linarith
  have hβ_lt_b' : β < b' := by rw [hβ_def]; linarith
  have hα_le_β : α ≤ β := by linarith
  have hh₀_mem_Icc : h₀ ∈ Set.Icc α β :=
    ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_h₀),
     le_of_lt (lt_of_le_of_lt hh₀_le_max hmax_lt_β)⟩
  have ht_mem_Icc : t ∈ Set.Icc α β :=
    ⟨le_of_lt (lt_of_lt_of_le hα_lt_min hmin_le_t),
     le_of_lt (lt_of_le_of_lt ht_le_max hmax_lt_β)⟩
  have hIcc_sub : Set.Icc α β ⊆ Set.Ioo a b' := fun s hs =>
    ⟨lt_of_lt_of_le ha_lt_α hs.1, lt_of_le_of_lt hs.2 hβ_lt_b'⟩
  have hIcc_compact : IsCompact (Set.Icc α β) := isCompact_Icc
  have hIcc_ne : (Set.Icc α β).Nonempty := ⟨α, left_mem_Icc.mpr hα_le_β⟩
  obtain ⟨ε_open, hε_open_pos, hball_sub⟩ :=
    Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  set δ₀ : ℝ := ε_open / 2 with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_lt : δ₀ < ε_open := by rw [hδ₀_def]; linarith
  have hclosedBall_sub : Metric.closedBall x δ₀ ⊆ U := fun y hy =>
    hball_sub (Metric.closedBall_subset_ball hδ₀_lt hy)
  have hclosedBall_compact : IsCompact (Metric.closedBall x δ₀) :=
    isCompact_closedBall x δ₀
  set K : Set (F × ℝ) := Metric.closedBall x δ₀ ×ˢ Set.Icc α β with hK_def
  have hK_compact : IsCompact K := hclosedBall_compact.prod hIcc_compact
  have hK_sub : K ⊆ U ×ˢ Set.Ioo a b' := fun p hp =>
    ⟨hclosedBall_sub hp.1, hIcc_sub hp.2⟩
  have hx_ball : x ∈ Metric.closedBall x δ₀ := Metric.mem_closedBall_self hδ₀_pos.le
  have hK_ne : K.Nonempty :=
    ⟨(x, α), hx_ball, left_mem_Icc.mpr hα_le_β⟩
  have hA_cont_K : ContinuousOn (Function.uncurry A) K := hA_cont.mono hK_sub
  have hAnorm_cont_K : ContinuousOn (fun p : F × ℝ => ‖A p.1 p.2‖) K :=
    continuous_norm.comp_continuousOn hA_cont_K
  obtain ⟨pM, _, hM_bd⟩ := hK_compact.exists_isMaxOn hK_ne hAnorm_cont_K
  set M : ℝ := ‖A pM.1 pM.2‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hM_bd' : ∀ p ∈ K, ‖A p.1 p.2‖ ≤ M := fun p hp => hM_bd hp
  have hDA_cont_K : ContinuousOn
      (Function.uncurry fun y s => fderiv ℝ (fun z => A z s) y) K :=
    hDA_cont.mono hK_sub
  have hDAnorm_cont_K : ContinuousOn
      (fun p : F × ℝ => ‖fderiv ℝ (fun z => A z p.2) p.1‖) K :=
    by
      refine hDA_cont_K.norm.congr ?_
      intro p _
      rfl
  obtain ⟨pP, _, hP_bd⟩ := hK_compact.exists_isMaxOn hK_ne hDAnorm_cont_K
  set P : ℝ := ‖fderiv ℝ (fun z => A z pP.2) pP.1‖ with hP_def
  have hP_nn : 0 ≤ P := norm_nonneg _
  have hP_bd' : ∀ p ∈ K, ‖fderiv ℝ (fun z => A z p.2) p.1‖ ≤ P :=
    fun p hp => hP_bd hp
  have hZ_cont_K : ContinuousOn (Function.uncurry Z) K :=
    (linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont).mono hK_sub
  have hZnorm_cont_K : ContinuousOn (fun p : F × ℝ => ‖Z p.1 p.2‖) K :=
    continuous_norm.comp_continuousOn hZ_cont_K
  obtain ⟨pQ, _, hQ_bd⟩ := hK_compact.exists_isMaxOn hK_ne hZnorm_cont_K
  set Q : ℝ := ‖Z pQ.1 pQ.2‖ with hQ_def
  have hQ_nn : 0 ≤ Q := norm_nonneg _
  have hQ_bd' : ∀ p ∈ K, ‖Z p.1 p.2‖ ≤ Q := fun p hp => hQ_bd hp
  have hDZ₀_cont_ball : ContinuousOn (fun y => fderiv ℝ Z₀ y)
      (Metric.closedBall x δ₀) := hDZ₀_cont.mono hclosedBall_sub
  have hDZ₀norm_cont_ball : ContinuousOn (fun y => ‖fderiv ℝ Z₀ y‖)
      (Metric.closedBall x δ₀) :=
    continuous_norm.comp_continuousOn hDZ₀_cont_ball
  obtain ⟨pL, _, hL_bd⟩ := hclosedBall_compact.exists_isMaxOn
    ⟨x, hx_ball⟩ hDZ₀norm_cont_ball
  set L : ℝ := ‖fderiv ℝ Z₀ pL‖ with hL_def
  have hL_nn : 0 ≤ L := norm_nonneg _
  have hL_bd' : ∀ y ∈ Metric.closedBall x δ₀, ‖fderiv ℝ Z₀ y‖ ≤ L :=
    fun y hy => hL_bd hy
  have hAx_bd : ∀ s ∈ Set.Icc α β, ‖A x s‖ ≤ M := fun s hs =>
    hM_bd' (x, s) ⟨hx_ball, hs⟩
  have hDAx_bd : ∀ s ∈ Set.Icc α β, ‖fderiv ℝ (fun z => A z s) x‖ ≤ P :=
    fun s hs => hP_bd' (x, s) ⟨hx_ball, hs⟩
  have hZx_bd : ∀ s ∈ Set.Icc α β, ‖Z x s‖ ≤ Q := fun s hs =>
    hQ_bd' (x, s) ⟨hx_ball, hs⟩
  have hZ₀x_bd : ‖fderiv ℝ Z₀ x‖ ≤ L := hL_bd' x hx_ball
  set C_stab : ℝ := gronwallBound L M (P * Q) (β - α) with hC_stab_def
  have hPQ_nn : 0 ≤ P * Q := mul_nonneg hP_nn hQ_nn
  have hβα_nn : 0 ≤ β - α := by linarith
  have hC_stab_nn : 0 ≤ C_stab := by
    rw [hC_stab_def]
    have h0 : gronwallBound L M (P * Q) 0 = L := gronwallBound_x0 _ _ _
    have hmono : gronwallBound L M (P * Q) 0 ≤ gronwallBound L M (P * Q) (β - α) :=
      gronwallBound_mono hL_nn hPQ_nn hM_nn hβα_nn
    linarith
  have h_stab : ∀ h : F, ‖h‖ ≤ δ₀ → ∀ s ∈ Set.Icc α β,
      ‖Z (x + h) s - Z x s‖ ≤ C_stab * ‖h‖ := by
    simpa only [hZ_def, hC_stab_def] using
      (linearODESolution_local_lipschitz_on_Icc (A := A) (Z₀ := Z₀)
        h₀_mem hA_cont hA_diff (x := x) (α := α) (β := β)
        (δ := δ₀) (M := M) (P := P) (Q := Q) (L := L) hx
        ha_lt_α hβ_lt_b' hh₀_mem_Icc hIcc_sub hclosedBall_sub
        hδ₀_pos.le hM_nn hP_nn hQ_nn hL_nn hAx_bd
        (fun y hy s hs => hP_bd' (y, s) ⟨hy, hs⟩)
        (fun y hy s hs => by
          simpa only [hZ_def] using hQ_bd' (y, s) ⟨hy, hs⟩)
        hL_bd' hZ₀_diff)
  have hUC : UniformContinuousOn
      (fun p : F × ℝ => fderiv ℝ (fun z => A z p.2) p.1) K :=
    hK_compact.uniformContinuousOn_of_continuous hDA_cont_K
  have h_taylor : ∀ ε > (0 : ℝ), ∃ δ_ε > (0 : ℝ), δ_ε ≤ δ₀ ∧
      ∀ h : F, ‖h‖ ≤ δ_ε → ∀ s ∈ Set.Icc α β,
        ‖A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h‖ ≤ ε * ‖h‖ := by
    intro ε hε
    rw [Metric.uniformContinuousOn_iff_le] at hUC
    obtain ⟨δ', hδ'_pos, hδ'_uniform⟩ := hUC ε hε
    refine ⟨min δ₀ δ', lt_min hδ₀_pos hδ'_pos, min_le_left _ _, ?_⟩
    intro h hh_bd s hs
    have hh_le_δ₀ : ‖h‖ ≤ δ₀ := le_trans hh_bd (min_le_left _ _)
    have hh_le_δ' : ‖h‖ ≤ δ' := le_trans hh_bd (min_le_right _ _)
    have hball_sub_K : ∀ y ∈ Metric.closedBall x ‖h‖, y ∈ Metric.closedBall x δ₀ :=
      fun y hy => Metric.closedBall_subset_closedBall hh_le_δ₀ hy
    have hConvergence_h : Convex ℝ (Metric.closedBall x ‖h‖) := convex_closedBall _ _
    have hx_in_h : x ∈ Metric.closedBall x ‖h‖ :=
      Metric.mem_closedBall_self (norm_nonneg _)
    have hxh_in_h : x + h ∈ Metric.closedBall x ‖h‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : x + h - x = h := by abel
      rw [this]
    have h_pt_bd : ∀ y ∈ Metric.closedBall x ‖h‖,
        ‖fderiv ℝ (fun z => A z s) y - fderiv ℝ (fun z => A z s) x‖ ≤ ε := by
      intro y hy
      have hy_K : (y, s) ∈ K := ⟨hball_sub_K y hy, hs⟩
      have hx_K : (x, s) ∈ K := ⟨hx_ball, hs⟩
      have hdist_le : dist (y, s) (x, s) ≤ δ' := by
        rw [Prod.dist_eq]
        have : dist s s = 0 := dist_self _
        rw [this]
        have hys_dist : dist y x ≤ ‖h‖ := hy
        exact max_le (le_trans hys_dist hh_le_δ') (le_of_lt hδ'_pos)
      have huniform := hδ'_uniform (y, s) hy_K (x, s) hx_K hdist_le
      rw [dist_eq_norm] at huniform
      exact huniform
    have hHasFDeriv : ∀ y ∈ Metric.closedBall x ‖h‖,
        HasFDerivWithinAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y)
          (Metric.closedBall x ‖h‖) y := fun y hy =>
      (hA_diff y (hclosedBall_sub (hball_sub_K y hy)) s (hIcc_sub hs)).hasFDerivWithinAt
    have hres := hConvergence_h.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hHasFDeriv h_pt_bd hx_in_h hxh_in_h
    have hsub_eq : x + h - x = h := by abel
    rw [hsub_eq] at hres
    exact hres
  have hW_deriv : ∀ h : F, ∀ s ∈ Set.Ioo a b',
      HasDerivAt (variationalSolution A a b' h₀ Z₀ x h ·)
        ((fderiv ℝ (fun y => A y s) x) h (Z x s)
          + A x s (variationalSolution A a b' h₀ Z₀ x h s)) s := fun h s hs =>
    variationalW_hasDerivAt h₀_mem hU hA_cont hDA_cont hZ₀_cont hx h hs
  have hW_initial_eq : ∀ h : F,
      variationalSolution A a b' h₀ Z₀ x h h₀ = (fderiv ℝ Z₀ x) h := fun h =>
    variationalW_initial A a b' h₀ Z₀ x h
  have hZ_deriv : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasDerivAt (Z y ·) (A y s (Z y s)) s := fun y hy s hs =>
    linearODESolution_hasDerivAt h₀_mem hA_cont hy hs
  have hZ_initial_eq : ∀ y : F, Z y h₀ = Z₀ y := fun y =>
    linearODESolution_initial A a b' h₀ Z₀ y
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set E_T : ℝ := if M = 0 then β - α else (Real.exp (M * (β - α)) - 1) / M
    with hET_def
  set E_δ : ℝ := if M = 0 then 1 else Real.exp (M * (β - α)) with hEδ_def
  have hgb_eq : ∀ δ ε : ℝ,
      gronwallBound δ M ε (β - α) = δ * E_δ + ε * E_T := by
    intro δ ε
    by_cases hMeq : M = 0
    · have hEδ_val : E_δ = 1 := by rw [hEδ_def, ite_eq_left hMeq]
      have hET_val : E_T = β - α := by rw [hET_def, ite_eq_left hMeq]
      rw [hMeq, hEδ_val, hET_val, gronwallBound_K0]; ring
    · have hEδ_val : E_δ = Real.exp (M * (β - α)) := by
        rw [hEδ_def, ite_eq_right hMeq]
      have hET_val : E_T = (Real.exp (M * (β - α)) - 1) / M := by
        rw [hET_def, ite_eq_right hMeq]
      rw [hEδ_val, hET_val, gronwallBound_of_K_ne_0 hMeq]
      field_simp
  have hET_nn : 0 ≤ E_T := by
    by_cases hMeq : M = 0
    · have : E_T = β - α := by rw [hET_def, ite_eq_left hMeq]
      rw [this]; linarith
    · have : E_T = (Real.exp (M * (β - α)) - 1) / M := by
        rw [hET_def, ite_eq_right hMeq]
      rw [this]
      have hexp_ge : 1 ≤ Real.exp (M * (β - α)) :=
        Real.one_le_exp (mul_nonneg hM_nn hβα_nn)
      have : 0 ≤ Real.exp (M * (β - α)) - 1 := by linarith
      exact div_nonneg this hM_nn
  have hEδ_pos : 0 < E_δ := by
    by_cases hMeq : M = 0
    · have : E_δ = 1 := by rw [hEδ_def, ite_eq_left hMeq]
      rw [this]; norm_num
    · have : E_δ = Real.exp (M * (β - α)) := by rw [hEδ_def, ite_eq_right hMeq]
      rw [this]; exact Real.exp_pos _
  have hEδ_nn : 0 ≤ E_δ := hEδ_pos.le
  set c₁ : ℝ := c / (2 * E_δ) with hc₁_def
  have hc₁_pos : 0 < c₁ := by
    rw [hc₁_def]; positivity
  set c₂ : ℝ := c / (2 * (E_T + 1)) with hc₂_def
  have hET_inc : 0 < E_T + 1 := by linarith
  have hc₂_pos : 0 < c₂ := by
    rw [hc₂_def]; positivity
  have hEδ_ne : E_δ ≠ 0 := ne_of_gt hEδ_pos
  have hET_inc_ne : (E_T + 1 : ℝ) ≠ 0 := ne_of_gt hET_inc
  have h_bound_compose : c₁ * E_δ + c₂ * E_T ≤ c := by
    have h1 : c₁ * E_δ = c / 2 := by
      rw [hc₁_def, div_mul_eq_mul_div, mul_div_assoc]
      have : E_δ / (2 * E_δ) = 1 / 2 := by
        rw [div_eq_iff (by positivity)]; ring
      rw [this]; ring
    have h2 : c₂ * E_T ≤ c / 2 := by
      rw [hc₂_def]
      have hET_le : E_T ≤ E_T + 1 := by linarith
      have hstep : c / (2 * (E_T + 1)) * E_T ≤ c / (2 * (E_T + 1)) * (E_T + 1) :=
        mul_le_mul_of_nonneg_left hET_le (by positivity)
      have hfinal : c / (2 * (E_T + 1)) * (E_T + 1) = c / 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        have : (E_T + 1) / (2 * (E_T + 1)) = 1 / 2 := by
          rw [div_eq_iff (by positivity)]; ring
        rw [this]; ring
      linarith
    linarith
  have hZ₀_at : HasFDerivAt Z₀ (fderiv ℝ Z₀ x) x := hZ₀_diff x hx
  have hZ₀_lit : (fun h : F => Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h) =o[𝓝 0]
      (fun h : F => h) :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hZ₀_at
  have hZ₀_bd_event : ∀ᶠ h : F in 𝓝 0,
      ‖Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h‖ ≤ c₁ * ‖h‖ :=
    (Asymptotics.isLittleO_iff.mp hZ₀_lit) hc₁_pos
  set ε₁ : ℝ := c₂ / (2 * (Q + 1)) with hε₁_def
  have hQ_inc : 0 < Q + 1 := by linarith
  have hε₁_pos : 0 < ε₁ := by rw [hε₁_def]; positivity
  obtain ⟨δ_tay, hδ_tay_pos, hδ_tay_le_δ₀, h_tay_bd⟩ := h_taylor ε₁ hε₁_pos
  set δ_pcs : ℝ := c₂ / (2 * (P * C_stab + 1)) with hδ_pcs_def
  have hPCS_inc : 0 < P * C_stab + 1 := by
    have : 0 ≤ P * C_stab := mul_nonneg hP_nn hC_stab_nn
    linarith
  have hδ_pcs_pos : 0 < δ_pcs := by rw [hδ_pcs_def]; positivity
  set δ_force : ℝ := min δ_tay δ_pcs with hδ_force_def
  have hδ_force_pos : 0 < δ_force :=
    lt_min hδ_tay_pos hδ_pcs_pos
  have hδ_force_le_δ_tay : δ_force ≤ δ_tay := min_le_left _ _
  have hδ_force_le_δ_pcs : δ_force ≤ δ_pcs := min_le_right _ _
  have h_force_total : ∀ h : F, ‖h‖ ≤ δ_force →
      ε₁ * Q + P * C_stab * ‖h‖ ≤ c₂ := by
    intro h hh_le
    have h1 : ε₁ * Q ≤ c₂ / 2 := by
      rw [hε₁_def]
      have hQ_le : Q ≤ Q + 1 := by linarith
      have hQ1_pos : (0 : ℝ) < Q + 1 := hQ_inc
      have hstep : c₂ / (2 * (Q + 1)) * Q ≤ c₂ / (2 * (Q + 1)) * (Q + 1) :=
        mul_le_mul_of_nonneg_left hQ_le (by positivity)
      have hfinal : c₂ / (2 * (Q + 1)) * (Q + 1) = c₂ / 2 := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        field_simp
      linarith
    have h2 : P * C_stab * ‖h‖ ≤ c₂ / 2 := by
      have hh_le_δ_pcs : ‖h‖ ≤ δ_pcs := le_trans hh_le hδ_force_le_δ_pcs
      have hpcs_nn : 0 ≤ P * C_stab := mul_nonneg hP_nn hC_stab_nn
      have : P * C_stab * ‖h‖ ≤ P * C_stab * δ_pcs :=
        mul_le_mul_of_nonneg_left hh_le_δ_pcs hpcs_nn
      have h_step2 : P * C_stab * δ_pcs ≤ c₂ / 2 := by
        rw [hδ_pcs_def]
        have hPCS_le : P * C_stab ≤ P * C_stab + 1 := by linarith
        have hPCS_pos : (0 : ℝ) < P * C_stab + 1 := hPCS_inc
        have hPCS_ne : (P * C_stab + 1 : ℝ) ≠ 0 := ne_of_gt hPCS_inc
        have hstep1 : P * C_stab * (c₂ / (2 * (P * C_stab + 1)))
            ≤ (P * C_stab + 1) * (c₂ / (2 * (P * C_stab + 1))) :=
          mul_le_mul_of_nonneg_right hPCS_le (by positivity)
        have hfinal : (P * C_stab + 1) * (c₂ / (2 * (P * C_stab + 1))) = c₂ / 2 := by
          rw [mul_div_assoc']
          field_simp
        linarith
      linarith
    linarith
  rw [Metric.eventually_nhds_iff]
  rw [Metric.eventually_nhds_iff] at hZ₀_bd_event
  obtain ⟨δ_initial, hδ_initial_pos, hδ_initial_bd⟩ := hZ₀_bd_event
  set δ_final : ℝ := min δ_force δ_initial with hδ_final_def
  have hδ_final_pos : 0 < δ_final := lt_min hδ_force_pos hδ_initial_pos
  refine ⟨δ_final, hδ_final_pos, ?_⟩
  intro h hh_lt
  rw [dist_zero_right] at hh_lt
  have hh_le_force : ‖h‖ ≤ δ_force := le_of_lt (lt_of_lt_of_le hh_lt (min_le_left _ _))
  have hh_lt_initial : dist h 0 < δ_initial :=
    lt_of_lt_of_le (by rw [dist_zero_right]; exact hh_lt) (min_le_right _ _)
  have hh_le_δ₀ : ‖h‖ ≤ δ₀ :=
    le_trans (le_trans hh_le_force hδ_force_le_δ_tay) hδ_tay_le_δ₀
  have hh_le_δ_tay : ‖h‖ ≤ δ_tay := le_trans hh_le_force hδ_force_le_δ_tay
  have hdist_xh_x : dist (x + h) x = ‖h‖ := by
    rw [dist_eq_norm]; congr 1; abel
  have hxh_ball : x + h ∈ Metric.closedBall x δ₀ := by
    rw [Metric.mem_closedBall, hdist_xh_x]; exact hh_le_δ₀
  have hxh_U : x + h ∈ U := hclosedBall_sub hxh_ball
  set R : ℝ → G := fun s => Z (x + h) s - Z x s - variationalSolution A a b' h₀ Z₀ x h s
    with hR_def
  set Force : ℝ → G := fun s =>
    (A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h) (Z (x + h) s)
      + (fderiv ℝ (fun z => A z s) x) h (Z (x + h) s - Z x s)
    with hForce_def
  set Rderiv : ℝ → G := fun s => A x s (R s) + Force s with hRderiv_def
  have hR_deriv : ∀ s ∈ Set.Ioo a b', HasDerivAt R (Rderiv s) s := by
    intro s hs
    have h1 := hZ_deriv (x + h) hxh_U s hs
    have h2 := hZ_deriv x hx s hs
    have h3 := hW_deriv h s hs
    have hRderiv := (h1.sub h2).sub h3
    have h_eq :
        A (x + h) s (Z (x + h) s) - A x s (Z x s)
            - ((fderiv ℝ (fun y => A y s) x) h (Z x s)
              + A x s (variationalSolution A a b' h₀ Z₀ x h s))
        = Rderiv s := by
      change _ = A x s (R s) + Force s
      have hRs : R s = Z (x + h) s - Z x s - variationalSolution A a b' h₀ Z₀ x h s := rfl
      have hForce_val : Force s
          = (A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h) (Z (x + h) s)
            + (fderiv ℝ (fun z => A z s) x) h (Z (x + h) s - Z x s) := rfl
      rw [hRs, hForce_val]
      rw [show Z (x + h) s - Z x s - variationalSolution A a b' h₀ Z₀ x h s
          = (Z (x + h) s - Z x s) + (-variationalSolution A a b' h₀ Z₀ x h s) by abel,
        ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub,
        ContinuousLinearMap.map_neg]
      rw [sub_apply, sub_apply,
        ContinuousLinearMap.map_sub]
      abel
    rw [h_eq] at hRderiv
    exact hRderiv
  have hR_initial : R h₀ = Z₀ (x + h) - Z₀ x - (fderiv ℝ Z₀ x) h := by
    change Z (x + h) h₀ - Z x h₀ - variationalSolution A a b' h₀ Z₀ x h h₀ = _
    rw [hZ_initial_eq (x + h), hZ_initial_eq x, hW_initial_eq h]
  have hR_initial_bd : ‖R h₀‖ ≤ c₁ * ‖h‖ := by
    rw [hR_initial]; exact hδ_initial_bd hh_lt_initial
  have h_force_bd : ∀ s ∈ Set.Icc α β,
      ‖Force s‖ ≤ (ε₁ * Q + P * C_stab * ‖h‖) * ‖h‖ := by
    intro s hs
    have h_tay := h_tay_bd h hh_le_δ_tay s hs
    have hZxh_bd : ‖Z (x + h) s‖ ≤ Q := hQ_bd' (x + h, s) ⟨hxh_ball, hs⟩
    have h_stab_s := h_stab h hh_le_δ₀ s hs
    have hP_s_bd : ‖fderiv ℝ (fun z => A z s) x‖ ≤ P := hDAx_bd s hs
    let diffA : G →L[ℝ] G :=
      A (x + h) s - A x s - (fderiv ℝ (fun z => A z s) x) h
    let dxA : F →L[ℝ] (G →L[ℝ] G) := fderiv ℝ (fun z => A z s) x
    let piece1 : G := diffA (Z (x + h) s)
    let piece2 : G := dxA h (Z (x + h) s - Z x s)
    have hp1 : ‖piece1‖ ≤ (ε₁ * Q) * ‖h‖ := by
      change ‖diffA (Z (x + h) s)‖ ≤ _
      have hop : ‖diffA (Z (x + h) s)‖ ≤ ‖diffA‖ * ‖Z (x + h) s‖ := diffA.le_opNorm _
      have hbd : ‖diffA‖ * ‖Z (x + h) s‖ ≤ (ε₁ * ‖h‖) * Q :=
        mul_le_mul h_tay hZxh_bd (norm_nonneg _) (by positivity)
      calc ‖diffA (Z (x + h) s)‖
          ≤ ‖diffA‖ * ‖Z (x + h) s‖ := hop
        _ ≤ (ε₁ * ‖h‖) * Q := hbd
        _ = (ε₁ * Q) * ‖h‖ := by ring
    have hp2 : ‖piece2‖ ≤ (P * C_stab * ‖h‖) * ‖h‖ := by
      change ‖dxA h (Z (x + h) s - Z x s)‖ ≤ _
      have hop1 : ‖dxA h (Z (x + h) s - Z x s)‖
          ≤ ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ := (dxA h).le_opNorm _
      have hop2 : ‖dxA h‖ ≤ ‖dxA‖ * ‖h‖ := dxA.le_opNorm h
      have h2 : ‖dxA h‖ ≤ P * ‖h‖ :=
        le_trans hop2 (mul_le_mul_of_nonneg_right hP_s_bd (norm_nonneg _))
      have h3 : ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ ≤ (P * ‖h‖) * (C_stab * ‖h‖) :=
        mul_le_mul h2 h_stab_s (norm_nonneg _) (mul_nonneg hP_nn (norm_nonneg _))
      calc ‖dxA h (Z (x + h) s - Z x s)‖
          ≤ ‖dxA h‖ * ‖Z (x + h) s - Z x s‖ := hop1
        _ ≤ (P * ‖h‖) * (C_stab * ‖h‖) := h3
        _ = (P * C_stab * ‖h‖) * ‖h‖ := by ring
    change ‖piece1 + piece2‖ ≤ _
    calc ‖piece1 + piece2‖
        ≤ ‖piece1‖ + ‖piece2‖ := norm_add_le _ _
      _ ≤ (ε₁ * Q) * ‖h‖ + (P * C_stab * ‖h‖) * ‖h‖ := add_le_add hp1 hp2
      _ = (ε₁ * Q + P * C_stab * ‖h‖) * ‖h‖ := by ring
  set ε_total : ℝ := ε₁ * Q + P * C_stab * ‖h‖ with hε_total_def
  have hε_total_nn : 0 ≤ ε_total := by
    rw [hε_total_def]
    have h1 : 0 ≤ ε₁ * Q := mul_nonneg hε₁_pos.le hQ_nn
    have h2 : 0 ≤ P * C_stab * ‖h‖ :=
      mul_nonneg (mul_nonneg hP_nn hC_stab_nn) (norm_nonneg _)
    linarith
  have hε_total_le_c₂ : ε_total ≤ c₂ := h_force_total h hh_le_force
  have hR_deriv_norm_bd : ∀ s ∈ Set.Icc α β,
      ‖Rderiv s‖ ≤ M * ‖R s‖ + ε_total * ‖h‖ := by
    intro s hs
    have hAR : ‖A x s (R s)‖ ≤ M * ‖R s‖ := by
      have h1 : ‖A x s (R s)‖ ≤ ‖A x s‖ * ‖R s‖ := (A x s).le_opNorm _
      have h2 : ‖A x s‖ * ‖R s‖ ≤ M * ‖R s‖ :=
        mul_le_mul_of_nonneg_right (hAx_bd s hs) (norm_nonneg _)
      linarith
    have hFB : ‖Force s‖ ≤ ε_total * ‖h‖ := h_force_bd s hs
    have hR_val : Rderiv s = A x s (R s) + Force s := rfl
    rw [hR_val]
    calc ‖A x s (R s) + Force s‖
        ≤ ‖A x s (R s)‖ + ‖Force s‖ := norm_add_le _ _
      _ ≤ M * ‖R s‖ + ε_total * ‖h‖ := by linarith
  have hR_cont : ContinuousOn R (Set.Icc α β) := fun s hs =>
    ((hR_deriv s (hIcc_sub hs)).continuousAt).continuousWithinAt
  have hRt_bd :
      ‖R t‖ ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) :=
    norm_le_gronwallBound_on_Icc hh₀_mem_Icc ht_mem_Icc
      (mul_nonneg hc₁_pos.le (norm_nonneg _)) hM_nn
      (mul_nonneg hε_total_nn (norm_nonneg _)) hR_cont
      (fun s hs => hR_deriv s (hIcc_sub hs)) hR_initial_bd hR_deriv_norm_bd
  have h_final : ‖R t‖ ≤ c * ‖h‖ := by
    have hgb_evald : gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α)
        = (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T := hgb_eq _ _
    have h_step :
        (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T
          = ‖h‖ * (c₁ * E_δ + ε_total * E_T) := by ring
    have h_ε_le : ε_total * E_T ≤ c₂ * E_T :=
      mul_le_mul_of_nonneg_right hε_total_le_c₂ hET_nn
    have h_combo :
        c₁ * E_δ + ε_total * E_T ≤ c₁ * E_δ + c₂ * E_T :=
      add_le_add_right h_ε_le _
    have h_bound_final :
        ‖h‖ * (c₁ * E_δ + ε_total * E_T) ≤ ‖h‖ * c := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact h_combo.trans h_bound_compose
    calc ‖R t‖
        ≤ gronwallBound (c₁ * ‖h‖) M (ε_total * ‖h‖) (β - α) := hRt_bd
      _ = (c₁ * ‖h‖) * E_δ + (ε_total * ‖h‖) * E_T := hgb_evald
      _ = ‖h‖ * (c₁ * E_δ + ε_total * E_T) := h_step
      _ ≤ ‖h‖ * c := h_bound_final
      _ = c * ‖h‖ := by ring
  have h_clm_apply :
      (variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) h
        = variationalSolution A a b' h₀ Z₀ x h t :=
    variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht h
  change ‖linearODESolution A a b' h₀ Z₀ (x + h) t
        - linearODESolution A a b' h₀ Z₀ x t
        - (variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht) h‖
      ≤ c * ‖h‖
  rw [h_clm_apply]
  change ‖R t‖ ≤ c * ‖h‖
  exact h_final

omit [NormedSpace ℝ F] in
theorem portPrivate_b35c1e36_linearODESolution_partial_t_continuousOn
    {A : F → ℝ → (G →L[ℝ] G)} {a b' h₀ : ℝ} {Z₀ : F → G}
    (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U) :
    ContinuousOn
      (fun p : F × ℝ => A p.1 p.2 (linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
  have hZ_cont : ContinuousOn
      (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (U ×ˢ Set.Ioo a b') :=
    linearODESolution_continuousOn h₀_mem hU hA_cont hZ₀_cont
  have h_app_cont : Continuous fun q : (G →L[ℝ] G) × G => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have h_pair_cont : ContinuousOn
      (fun p : F × ℝ => (A p.1 p.2, linearODESolution A a b' h₀ Z₀ p.1 p.2))
      (U ×ˢ Set.Ioo a b') :=
    ContinuousOn.prodMk hA_cont hZ_cont
  exact h_app_cont.comp_continuousOn h_pair_cont

open Classical in
theorem portPrivate_b35c1e36_variationalW_clm_continuousOn
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ}
    {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U) :
    ContinuousOn
      (fun p : F × ℝ =>
        if hx : p.1 ∈ U then
          if ht : p.2 ∈ Set.Ioo a b' then
            variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
          else 0
        else 0)
      (U ×ˢ Set.Ioo a b') := by
  rw [continuousOn_clm_apply]
  intro v
  have h_eq : ∀ p ∈ U ×ˢ Set.Ioo a b',
      (if hx : p.1 ∈ U then
        if ht : p.2 ∈ Set.Ioo a b' then
          variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
        else 0
      else 0) v =
      variationalSolution A a b' h₀ Z₀ p.1 v p.2 := by
    intro ⟨x, t⟩ ⟨hxU, htI⟩
    change (if hx : x ∈ U then if ht : t ∈ Set.Ioo a b' then
            variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
          else 0 else 0) v = _
    rw [dite_eq_left hxU, dite_eq_left htI]
    exact variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont hxU htI v
  refine ContinuousOn.congr ?_ h_eq
  have hZ₀'_cont : ContinuousOn (fun x => (fderiv ℝ Z₀ x) v) U :=
    (ContinuousLinearMap.apply ℝ G v).continuous.comp_continuousOn hDZ₀_cont
  exact variationalW_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont v hZ₀'_cont

theorem portPrivate_b35c1e36_linearODESolution_hasFDerivAt_joint
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y)
    {x₀ : F} (hx₀ : x₀ ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b') :
    HasFDerivAt (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      ((variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
          (A x₀ t₀ (linearODESolution A a b' h₀ Z₀ x₀ t₀))))
      (x₀, t₀) := by
  set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
  set v₀ := A x₀ t₀ (Z x₀ t₀) with hv₀_def
  set L_x := variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀
  set L := L_x.coprod (ContinuousLinearMap.toSpanSingleton ℝ v₀)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have hx_param := linearODESolution_hasFDerivAt_param h₀_mem hU hA_cont hDA_cont
    hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx₀ ht₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hx_param
  have hx_param_bd := hx_param.bound (show (0 : ℝ) < c / 2 by linarith)
  obtain ⟨δ_x, hδ_x_pos, hδ_x_bd⟩ := Metric.eventually_nhds_iff.mp hx_param_bd
  have ht_partial_cont :
      ContinuousOn (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) (U ×ˢ Set.Ioo a b') :=
    portPrivate_b35c1e36_linearODESolution_partial_t_continuousOn h₀_mem hU hA_cont hZ₀_cont
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have hx₀t₀_mem : (x₀, t₀) ∈ U ×ˢ Set.Ioo a b' := ⟨hx₀, ht₀⟩
  have ht_partial_cont_at : ContinuousAt
      (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) (x₀, t₀) :=
    (ht_partial_cont (x₀, t₀) hx₀t₀_mem).continuousAt (hS_open.mem_nhds hx₀t₀_mem)
  rw [Metric.continuousAt_iff] at ht_partial_cont_at
  obtain ⟨δ_t, hδ_t_pos, hδ_t_bd⟩ := ht_partial_cont_at (c / 2) (by linarith)
  have h_add_nhds : ∀ᶠ p : F × ℝ in 𝓝 (0, 0),
      x₀ + p.1 ∈ U ∧ t₀ + p.2 ∈ Set.Ioo a b' := by
    have h1 : ∀ᶠ q : F in 𝓝 0, x₀ + q ∈ U := by
      have : Continuous (fun q : F => x₀ + q) := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx₀)
    have h2 : ∀ᶠ r : ℝ in 𝓝 0, t₀ + r ∈ Set.Ioo a b' := by
      have : Continuous (fun r : ℝ => t₀ + r) := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using isOpen_Ioo.mem_nhds ht₀)
    rw [nhds_prod_eq]
    exact h1.prod_mk h2
  obtain ⟨δ₀, hδ₀_pos, hδ₀_bd⟩ := Metric.eventually_nhds_iff.mp h_add_nhds
  set δ := min δ₀ (min δ_x δ_t) with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ₀_pos (lt_min hδ_x_pos hδ_t_pos)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, fun ⟨h, s⟩ h_dist => ?_⟩
  simp only [dist_zero_right] at h_dist
  have hh_lt : ‖h‖ < δ := lt_of_le_of_lt (le_max_left _ _) h_dist
  have hs_lt : ‖s‖ < δ := lt_of_le_of_lt (le_max_right _ _) h_dist
  have hh_lt_δ₀ : ‖h‖ < δ₀ := lt_of_lt_of_le hh_lt (min_le_left _ _)
  have hs_lt_δ₀ : ‖s‖ < δ₀ := lt_of_lt_of_le hs_lt (min_le_left _ _)
  have hh_lt_δx : ‖h‖ < δ_x :=
    lt_of_lt_of_le hh_lt ((min_le_right _ _).trans (min_le_left _ _))
  have hhs_lt_δt : max ‖h‖ ‖s‖ < δ_t :=
    lt_of_lt_of_le h_dist ((min_le_right _ _).trans (min_le_right _ _))
  have hprod_mem : x₀ + h ∈ U ∧ t₀ + s ∈ Set.Ioo a b' := by
    have h_dist_pair : dist (h, s) (0, 0) < δ₀ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
      exact max_lt hh_lt_δ₀ hs_lt_δ₀
    exact hδ₀_bd h_dist_pair
  obtain ⟨hxh_U, hts_Ioo⟩ := hprod_mem
  change ‖uncurry Z ((x₀, t₀) + (h, s)) - uncurry Z (x₀, t₀) - L (h, s)‖ ≤ c * ‖(h, s)‖
  simp only [uncurry, Prod.mk_add_mk]
  have hL_eq : L (h, s) = L_x h + s • v₀ := by
    simp [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hL_eq]
  have h_split :
      Z (x₀ + h) (t₀ + s) - Z x₀ t₀ - (L_x h + s • v₀)
        = (Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀)
          + (Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h) := by abel
  rw [h_split]
  calc ‖(Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀)
        + (Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h)‖
      ≤ ‖Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀‖
        + ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖(h, s)‖ + c / 2 * ‖(h, s)‖ := by
        apply add_le_add
        · have hZ_deriv_at : ∀ r ∈ Set.Ioo a b',
              HasDerivAt (Z (x₀ + h) ·) (A (x₀ + h) r (Z (x₀ + h) r)) r :=
            fun r hr => linearODESolution_hasDerivAt h₀_mem hA_cont hxh_U hr
          set χ : ℝ → G := fun r => Z (x₀ + h) r - (r - t₀) • v₀ with hχ_def
          have hχ_diff : ∀ r ∈ Set.Ioo a b', DifferentiableAt ℝ χ r := by
            intro r hr
            exact (hZ_deriv_at r hr).differentiableAt.sub
              (((hasDerivAt_id r).sub (hasDerivAt_const r t₀)).smul_const v₀).differentiableAt
          have hχ_deriv : ∀ r ∈ Set.Ioo a b',
              deriv χ r = A (x₀ + h) r (Z (x₀ + h) r) - v₀ := by
            intro r hr
            have hd : HasDerivAt χ (A (x₀ + h) r (Z (x₀ + h) r) - v₀) r := by
              have hd1 := hZ_deriv_at r hr
              have hd2 : HasDerivAt (fun r => (r - t₀) • v₀) v₀ r := by
                have h_base := ((hasDerivAt_id r).sub (hasDerivAt_const r t₀)).smul_const v₀
                refine (h_base.congr_of_eventuallyEq ?_).congr_deriv ?_
                · exact Filter.Eventually.of_forall fun y => by
                    change (y - t₀) • v₀ = (y - t₀) • v₀
                    rfl
                · simp
              exact hd1.sub hd2
            exact hd.deriv
          have h_uIcc_sub : Set.uIcc t₀ (t₀ + s) ⊆ Set.Ioo a b' := by
            intro r hr
            rw [Set.mem_uIcc] at hr
            constructor
            · rcases hr with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [ht₀.1, hts_Ioo.1]
            · rcases hr with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith [ht₀.2, hts_Ioo.2]
          have hχ_deriv_bd : ∀ r ∈ Set.uIcc t₀ (t₀ + s), ‖deriv χ r‖ ≤ c / 2 := by
            intro r hr
            rw [hχ_deriv r (h_uIcc_sub hr)]
            have h_r_bound : ‖r - t₀‖ ≤ ‖s‖ := by
              rw [Set.mem_uIcc] at hr
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
              rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
              · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
            have h_dist_prod : dist (x₀ + h, r) (x₀, t₀) < δ_t := by
              rw [Prod.dist_eq, dist_eq_norm, show x₀ + h - x₀ = h from add_sub_cancel_left _ _,
                dist_eq_norm]
              exact lt_of_le_of_lt (max_le_max le_rfl h_r_bound) hhs_lt_δt
            have := hδ_t_bd h_dist_prod
            rw [dist_eq_norm] at this
            exact le_of_lt this
          have hχ_diff_uI : ∀ r ∈ Set.uIcc t₀ (t₀ + s),
              DifferentiableAt ℝ χ r :=
            fun r hr => hχ_diff r (h_uIcc_sub hr)
          have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le
            (𝕜 := ℝ)
            hχ_diff_uI
            hχ_deriv_bd
            (convex_uIcc t₀ (t₀ + s))
            (Set.left_mem_uIcc) (Set.right_mem_uIcc)
          have hχ_diff_eq :
              χ (t₀ + s) - χ t₀
                = Z (x₀ + h) (t₀ + s) - Z (x₀ + h) t₀ - s • v₀ := by
            simp [hχ_def]; ring_nf; abel
          rw [← hχ_diff_eq]
          have hs_eq : ‖t₀ + s - t₀‖ = ‖s‖ := by rw [add_sub_cancel_left]
          rw [hs_eq] at h_mvt
          calc ‖χ (t₀ + s) - χ t₀‖
              ≤ c / 2 * ‖s‖ := h_mvt
            _ ≤ c / 2 * ‖(h, s)‖ :=
                mul_le_mul_of_nonneg_left (norm_snd_le (h, s)) (by linarith)
        · have h_param_bd : ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖ ≤ c / 2 * ‖h‖ := by
            have := hδ_x_bd (show dist h 0 < δ_x by rwa [dist_zero_right])
            have hLx : L_x h = variationalSolution A a b' h₀ Z₀ x₀ h t₀ := by
              exact variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont hx₀ ht₀ h
            rw [hLx]
            simpa [hZ_def] using this
          calc ‖Z (x₀ + h) t₀ - Z x₀ t₀ - L_x h‖
              ≤ c / 2 * ‖h‖ := h_param_bd
            _ ≤ c / 2 * ‖(h, s)‖ :=
                mul_le_mul_of_nonneg_left (norm_fst_le (h, s)) (by linarith)
    _ = c * ‖(h, s)‖ := by ring

theorem portPrivate_b35c1e36_linearODESolution_contDiffOn_one
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA_cont : ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hDA_cont : ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b'))
    (hA_diff : ∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y)
    (hZ₀_cont : ContinuousOn Z₀ U)
    (hDZ₀_cont : ContinuousOn (fun x => fderiv ℝ Z₀ x) U)
    (hZ₀_diff : ∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) :
    ContDiffOn ℝ 1
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  classical
  set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  change ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) _ _
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hS_open]
  have hdiff : DifferentiableOn ℝ (Function.uncurry Z) (U ×ˢ Set.Ioo a b') := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    exact (portPrivate_b35c1e36_linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont hA_diff
      hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).differentiableAt.differentiableWithinAt
  have htop : (0 : WithTop ℕ∞) = ⊤ →
      AnalyticOn ℝ (Function.uncurry Z) (U ×ˢ Set.Ioo a b') := by
    intro h_absurd
    exact absurd h_absurd (by simp)
  have hfderiv_cont : ContDiffOn ℝ 0 (fderiv ℝ (Function.uncurry Z))
      (U ×ˢ Set.Ioo a b') := by
    rw [contDiffOn_zero]
    have h_coprod_bilin : Continuous
        (fun (p : (F →L[ℝ] G) × (ℝ →L[ℝ] G)) => p.1.coprod p.2) :=
      (ContinuousLinearMap.coprodEquivL ℝ).continuous
    have h_clm_cont : ContinuousOn
        (fun p : F × ℝ =>
          if hx : p.1 ∈ U then
            if ht : p.2 ∈ Set.Ioo a b' then
              variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
            else 0
          else 0)
        (U ×ˢ Set.Ioo a b') :=
      portPrivate_b35c1e36_variationalW_clm_continuousOn h₀_mem hU hA_cont hDA_cont hZ₀_cont hDZ₀_cont
    have h_toSpan_cont : ContinuousOn
        (fun p : F × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
          (A p.1 p.2 (Z p.1 p.2)))
        (U ×ˢ Set.Ioo a b') :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).continuous.comp_continuousOn
        (portPrivate_b35c1e36_linearODESolution_partial_t_continuousOn h₀_mem hU hA_cont hZ₀_cont)
    have h_formula_cont :=
      h_coprod_bilin.comp_continuousOn (h_clm_cont.prodMk h_toSpan_cont)
    apply h_formula_cont.congr
    intro p hp
    obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
    have h_eq : (if hx' : p.1 ∈ U then
        if ht' : p.2 ∈ Set.Ioo a b' then
          variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
        else 0
      else 0) = variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht := by
      rw [dite_eq_left hx, dite_eq_left ht]
    change fderiv ℝ (uncurry Z) p
        = ((if hx' : p.1 ∈ U then
              if ht' : p.2 ∈ Set.Ioo a b' then
                variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
              else 0
            else 0).coprod
            (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
    rw [h_eq, hZ_def]
    conv_lhs => rw [show p = (p.1, p.2) from Prod.mk.eta.symm]
    exact (portPrivate_b35c1e36_linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont
      hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).fderiv
  exact ⟨hdiff, htop, hfderiv_cont⟩

omit [CompleteSpace G] in
theorem portPrivate_b35c1e36_inhomogAugmentedCoeff_contDiffOn
    {n : ℕ∞}
    {A : F → ℝ → (G →L[ℝ] G)} {b : F → ℝ → G}
    {U : Set F} {a b' : ℝ}
    (hA : ContDiffOn ℝ n (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hb : ContDiffOn ℝ n (Function.uncurry b) (U ×ˢ Set.Ioo a b')) :
    ContDiffOn ℝ n (Function.uncurry (inhomogAugmentedCoeff A b))
      (U ×ˢ Set.Ioo a b') := by
  have h_first : ContDiffOn ℝ n
      (fun p : F × ℝ => (A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ))
      (U ×ˢ Set.Ioo a b') :=
    hA.clm_comp contDiffOn_const
  have h_second : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        (ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2))
      (U ×ˢ Set.Ioo a b') := by
    have h_smul_cont : ContDiff ℝ n
        (fun y : G => (ContinuousLinearMap.snd ℝ G ℝ).smulRight y) :=
      (ContinuousLinearMap.smulRightL ℝ (G × ℝ) G
        (ContinuousLinearMap.snd ℝ G ℝ)).contDiff
    exact h_smul_cont.comp_contDiffOn hb
  have h_sum : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        ((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)))
      (U ×ˢ Set.Ioo a b') := h_first.add h_second
  have h_prodL : ContDiff ℝ n
      (fun q : ((G × ℝ) →L[ℝ] G) × ((G × ℝ) →L[ℝ] ℝ) => q.1.prod q.2) :=
    (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := G × ℝ) (F := G) (G := ℝ) ℝ).contDiff
  have h_pair : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        (((A p.1 p.2).comp (ContinuousLinearMap.fst ℝ G ℝ)) +
          ((ContinuousLinearMap.snd ℝ G ℝ).smulRight (b p.1 p.2)),
        (0 : (G × ℝ) →L[ℝ] ℝ)))
      (U ×ˢ Set.Ioo a b') := h_sum.prodMk contDiffOn_const
  exact h_prodL.comp_contDiffOn h_pair

omit [CompleteSpace G] in
theorem portPrivate_b35c1e36_extract_C1_hypotheses
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {n : ℕ}
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (↑(n + 1) : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ (↑(n + 1) : ℕ∞) Z₀ U) :
    ContinuousOn (Function.uncurry A) (U ×ˢ Set.Ioo a b') ∧
    ContinuousOn
      (Function.uncurry fun x t => fderiv ℝ (fun y => A y t) x)
      (U ×ˢ Set.Ioo a b') ∧
    (∀ y ∈ U, ∀ s ∈ Set.Ioo a b',
      HasFDerivAt (fun z => A z s) (fderiv ℝ (fun z => A z s) y) y) ∧
    ContinuousOn Z₀ U ∧
    ContinuousOn (fun x => fderiv ℝ Z₀ x) U ∧
    (∀ y ∈ U, HasFDerivAt Z₀ (fderiv ℝ Z₀ y) y) := by
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have hA_ge1 : ContDiffOn ℝ 1 (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
    hA.of_le (by norm_cast; omega)
  have hZ₀_ge1 : ContDiffOn ℝ 1 Z₀ U := hZ₀.of_le (by norm_cast; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA_ge1.continuousOn
  · have h_fderiv_cont : ContinuousOn (fderiv ℝ (Function.uncurry A))
        (U ×ˢ Set.Ioo a b') :=
      hA_ge1.continuousOn_fderiv_of_isOpen hS_open le_rfl
    have h_eq : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
        fderiv ℝ (fun y => A y p.2) p.1
          = (fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ) := by
      intro ⟨x, t⟩ ⟨hx, ht⟩
      have h_eq_comp : (fun y => A y t) = Function.uncurry A ∘ (fun y => (y, t)) := by
        ext y; simp [Function.uncurry]
      have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (x, t) := by
        apply (hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
          (x, t) (Set.mem_prod.mpr ⟨hx, ht⟩)).differentiableAt
        exact hS_open.mem_nhds (Set.mem_prod.mpr ⟨hx, ht⟩)
      rw [h_eq_comp]
      rw [fderiv_comp x h_diffA (hasFDerivAt_prodMk_left x t).differentiableAt]
      simp [hasFDerivAt_prodMk_left x t |>.fderiv]
    refine (h_fderiv_cont.clm_comp continuousOn_const).congr h_eq
  · intro y hy s hs
    have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (y, s) := by
      apply (hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
        (y, s) (Set.mem_prod.mpr ⟨hy, hs⟩)).differentiableAt
      exact hS_open.mem_nhds (Set.mem_prod.mpr ⟨hy, hs⟩)
    have h_diff_partial : DifferentiableAt ℝ (fun z => A z s) y := by
      have : (fun z => A z s) = Function.uncurry A ∘ (fun z => (z, s)) := by
        ext z; simp [Function.uncurry]
      rw [this]
      exact h_diffA.comp y (hasFDerivAt_prodMk_left y s).differentiableAt
    exact h_diff_partial.hasFDerivAt
  · exact hZ₀_ge1.continuousOn
  · exact hZ₀_ge1.continuousOn_fderiv_of_isOpen hU le_rfl
  · intro y hy
    exact ((hZ₀_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0) y hy).differentiableAt
      (hU.mem_nhds hy)).hasFDerivAt

omit [CompleteSpace G] in
theorem portPrivate_b35c1e36_variationalForcing_contDiffOn_of_Z_contDiffOn
    {n : ℕ∞}
    {A : F → ℝ → (G →L[ℝ] G)} {a b' : ℝ} {h₀ : ℝ} {Z₀ : F → G}
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ (n + 1) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ : ContDiffOn ℝ n (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b'))
    (v : F) :
    ContDiffOn ℝ n
      (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
      (U ×ˢ Set.Ioo a b') := by
  have hS_open : IsOpen (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) := hU.prod isOpen_Ioo
  have h_fderivA : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry A))
      (U ×ˢ Set.Ioo a b') :=
    hA.fderiv_of_isOpen hS_open le_rfl
  have h_partial : ContDiffOn ℝ n
      (fun p : F × ℝ => (fderiv ℝ (Function.uncurry A) p).comp
        (ContinuousLinearMap.inl ℝ F ℝ))
      (U ×ˢ Set.Ioo a b') :=
    h_fderivA.clm_comp contDiffOn_const
  have h_eval_v : ContDiffOn ℝ n
      (fun p : F × ℝ =>
        ((fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ)) v)
      (U ×ˢ Set.Ioo a b') :=
    h_partial.clm_apply contDiffOn_const
  have h_agree : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
      (fderiv ℝ (fun y => A y p.2) p.1)
        = (fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ) := by
    intro ⟨x, t⟩ ⟨hx, ht⟩
    have hA_ge1 : ContDiffOn ℝ 1 (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
      hA.of_le (by simp)
    have h_diffA : DifferentiableAt ℝ (Function.uncurry A) (x, t) := by
      exact ((hA_ge1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
        (x, t) (Set.mem_prod.mpr ⟨hx, ht⟩)).differentiableAt
        (hS_open.mem_nhds (Set.mem_prod.mpr ⟨hx, ht⟩))
    have h_eq_comp : (fun y => A y t) = Function.uncurry A ∘ (fun y => (y, t)) := by
      ext y; simp [Function.uncurry]
    rw [h_eq_comp, fderiv_comp x h_diffA (hasFDerivAt_prodMk_left x t).differentiableAt]
    simp [hasFDerivAt_prodMk_left x t |>.fderiv]
  have h_forcing_eq : ∀ p : F × ℝ, p ∈ U ×ˢ Set.Ioo a b' →
      Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t) p
        = ((fderiv ℝ (Function.uncurry A) p).comp (ContinuousLinearMap.inl ℝ F ℝ)) v
            (linearODESolution A a b' h₀ Z₀ p.1 p.2) := by
    intro ⟨x, t⟩ hp
    simp only [Function.uncurry, variationalForcing]
    rw [h_agree (x, t) hp]
  exact (h_eval_v.clm_apply hZ).congr h_forcing_eq

end VariationalSolution

theorem linearODESolution_contDiffOn
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (n : ℕ)
    (hA : ContDiffOn ℝ (n : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ (n : ℕ∞) Z₀ U) :
    ContDiffOn ℝ (n : ℕ∞)
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  classical
  induction n generalizing G with
  | zero =>
    exact (contDiffOn_zero.mpr
      (linearODESolution_continuousOn h₀_mem hU hA.continuousOn hZ₀.continuousOn))
  | succ n ih =>
    have hA_n : ContDiffOn ℝ (n : ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b') :=
      hA.of_le (by norm_cast; omega)
    have hZ₀_n : ContDiffOn ℝ (n : ℕ∞) Z₀ U := hZ₀.of_le (by norm_cast; omega)
    have hZ_n : ContDiffOn ℝ (n : ℕ∞)
        (Function.uncurry (linearODESolution A a b' h₀ Z₀)) (U ×ˢ Set.Ioo a b') :=
      ih hA_n hZ₀_n
    have ⟨hA_cont, hDA_cont, hA_diff, hZ₀_cont, hDZ₀_cont, hZ₀_diff⟩ :=
      portPrivate_b35c1e36_extract_C1_hypotheses hU hA hZ₀
    set Z := linearODESolution A a b' h₀ Z₀ with hZ_def
    set S := (U ×ˢ Set.Ioo a b' : Set (F × ℝ)) with hS_def
    have hS_open : IsOpen S := hU.prod isOpen_Ioo
    suffices h_goal : ContDiffOn ℝ ((↑(↑n : ℕ∞) : WithTop ℕ∞) + 1) (Function.uncurry Z) S by
      exact_mod_cast h_goal
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hS_open]
    refine ⟨?_, ?_, ?_⟩
    · intro ⟨x, t⟩ ⟨hx, ht⟩
      exact (portPrivate_b35c1e36_linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont hA_diff
        hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).differentiableAt.differentiableWithinAt
    · intro h_absurd
      exact absurd h_absurd WithTop.coe_ne_top
    · have h_AZ_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => A p.1 p.2 (Z p.1 p.2)) S :=
        hA_n.clm_apply hZ_n
      have h_toSpan_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
            (A p.1 p.2 (Z p.1 p.2))) S :=
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := G)).contDiff.comp_contDiffOn
          h_AZ_n
      have h_varW_v_n : ∀ v : F, ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ => variationalSolution A a b' h₀ Z₀ p.1 v p.2) S := by
        intro v
        have h_forcing_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (fun x t => variationalForcing A a b' h₀ Z₀ x v t))
            S :=
          portPrivate_b35c1e36_variationalForcing_contDiffOn_of_Z_contDiffOn hU (by exact_mod_cast hA) hZ_n v
        have hZ₀_fderiv_n : ContDiffOn ℝ (↑n : ℕ∞) (fderiv ℝ Z₀) U :=
          hZ₀.fderiv_of_isOpen hU (by norm_cast)
        have h_augIC_n : ContDiffOn ℝ (↑n : ℕ∞)
            (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))) U :=
          (hZ₀_fderiv_n.clm_apply contDiffOn_const).prodMk contDiffOn_const
        have h_Ahat_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (inhomogAugmentedCoeff A
              (fun y t => variationalForcing A a b' h₀ Z₀ y v t))) S :=
          portPrivate_b35c1e36_inhomogAugmentedCoeff_contDiffOn hA_n h_forcing_n
        have h_aug_solution_n : ContDiffOn ℝ (↑n : ℕ∞)
            (Function.uncurry (linearODESolution
              (inhomogAugmentedCoeff A (fun y t => variationalForcing A a b' h₀ Z₀ y v t))
              a b' h₀ (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))))) S :=
          ih (G := G × ℝ) h_Ahat_n h_augIC_n
        have h_fst_n : ContDiffOn ℝ (↑n : ℕ∞)
            (fun p : F × ℝ =>
              (linearODESolution
                (inhomogAugmentedCoeff A (fun y t => variationalForcing A a b' h₀ Z₀ y v t))
                a b' h₀ (fun y => ((fderiv ℝ Z₀ y) v, (1 : ℝ))) p.1 p.2).1) S :=
          contDiff_fst.comp_contDiffOn h_aug_solution_n
        exact h_fst_n.congr (fun _ _ => rfl)
      have h_clm_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ =>
            if hx : p.1 ∈ U then
              if ht : p.2 ∈ Set.Ioo a b' then
                variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
              else 0
            else 0)
          S := by
        rw [contDiffOn_clm_apply]
        intro v'
        refine (h_varW_v_n v').congr (fun p hp => ?_)
        obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
        simp only [dite_eq_left hx, dite_eq_left ht]
        exact (variationalW_clm_apply h₀_mem hU hA_cont hDA_cont hZ₀_cont
          hx ht v').symm
      have h_coprod_n : ContDiffOn ℝ (↑n : ℕ∞)
          (fun p : F × ℝ =>
            (if hx : p.1 ∈ U then
              if ht : p.2 ∈ Set.Ioo a b' then
                variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht
              else 0
            else 0).coprod
              (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
          S := by
        exact (ContinuousLinearMap.coprodEquivL ℝ
          (E := F) (F := ℝ) (G := G)).contDiff.comp_contDiffOn
          (h_clm_n.prodMk h_toSpan_n)
      refine h_coprod_n.congr (fun p hp => ?_)
      obtain ⟨hx, ht⟩ := Set.mem_prod.mp hp
      have h_eq : (if hx' : p.1 ∈ U then
          if ht' : p.2 ∈ Set.Ioo a b' then
            variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
          else 0
        else 0) = variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx ht := by
        rw [dite_eq_left hx, dite_eq_left ht]
      change fderiv ℝ (Function.uncurry Z) p
          = ((if hx' : p.1 ∈ U then
                if ht' : p.2 ∈ Set.Ioo a b' then
                  variationalWClm h₀_mem hU hA_cont hDA_cont hZ₀_cont hx' ht'
                else 0
              else 0).coprod
              (ContinuousLinearMap.toSpanSingleton ℝ (A p.1 p.2 (Z p.1 p.2))))
      rw [h_eq, hZ_def]
      conv_lhs => rw [show p = (p.1, p.2) from Prod.mk.eta.symm]
      exact (portPrivate_b35c1e36_linearODESolution_hasFDerivAt_joint h₀_mem hU hA_cont hDA_cont
        hA_diff hZ₀_cont hDZ₀_cont hZ₀_diff hx ht).fderiv

section CInfinityRegularity

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem linearODESolution_contDiffOn_top
    [FiniteDimensional ℝ F]
    {A : F → ℝ → (G →L[ℝ] G)} {Z₀ : F → G}
    {a b' : ℝ} {h₀ : ℝ} (h₀_mem : h₀ ∈ Set.Ioo a b')
    {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry A) (U ×ˢ Set.Ioo a b'))
    (hZ₀ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z₀ U) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (linearODESolution A a b' h₀ Z₀))
      (U ×ˢ Set.Ioo a b') := by
  rw [contDiffOn_infty]
  intro k
  exact linearODESolution_contDiffOn h₀_mem hU k
    (hA.of_le (by exact_mod_cast le_top)) (hZ₀.of_le (by exact_mod_cast le_top))

end CInfinityRegularity

end Flow
end ODE
end Analysis
end DifferentialGeometry

end
