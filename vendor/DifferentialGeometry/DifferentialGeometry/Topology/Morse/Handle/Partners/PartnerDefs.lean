module

public import DifferentialGeometry.Topology.Morse.Cancellation.FirstCancellation
public import DifferentialGeometry.Topology.Morse.Rearrangement.SelfIndexing
public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.Isolate
public import DifferentialGeometry.Topology.Morse.Strip.Terminal
public import DifferentialGeometry.Topology.Morse.Rearrangement.EqualIndexPosition
public import DifferentialGeometry.Topology.Morse.Rearrangement.DistinctSelfIndexing
public import DifferentialGeometry.Topology.Morse.Cancellation.Setup.Bridge
public import DifferentialGeometry.Topology.Morse.Strip.Substrip
public import DifferentialGeometry.Topology.Manifold.GeneralPosition.GeneralPosition

@[expose] public section

set_option autoImplicit false

open Set Filter Function

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart)

namespace IndexOnePartner

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

def circ2 (t : ℝ) : Fin 2 → ℝ :=
  ![Real.cos (2 * Real.pi * t), Real.sin (2 * Real.pi * t)]

def isLevelLoop (I : ModelWithCorners ℝ (Fin n → ℝ) H) (f : M → ℝ) (c : ℝ) (γ : ℝ → M) :
    Prop :=
  Periodic γ 1 ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ (∀ θ, mfderiv 𝓘(ℝ, ℝ) I γ θ (1 : ℝ) ≠ 0) ∧
    (∀ θ θ', γ θ = γ θ' → ∃ k : ℤ, θ' = θ + k) ∧ ∀ θ, f (γ θ) = c

def isEmbeddedSlice (I : ModelWithCorners ℝ (Fin n → ℝ) H) (h : ℝ → ℝ → M) (s : ℝ) : Prop :=
  (∀ θ, mfderiv 𝓘(ℝ, ℝ) I (fun θ' => h θ' s) θ (1 : ℝ) ≠ 0) ∧
    ∀ θ θ', h θ s = h θ' s → ∃ k : ℤ, θ' = θ + k

def isLevelHomotopy (f : M → ℝ) (c : ℝ) (H : ℝ → ℝ → M) (γ β : ℝ → M) : Prop :=
  Continuous (uncurry H) ∧ (∀ θ s, H (θ + 1) s = H θ s) ∧ (∀ θ s, f (H θ s) = c) ∧
    (∀ θ, H θ 0 = γ θ) ∧ ∀ θ, H θ 1 = β θ

def isThin (I : ModelWithCorners ℝ (Fin n → ℝ) H) (d : ℕ) (T : Set M) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (U : ι → Set (Fin d → ℝ)) (g : ι → (Fin d → ℝ) → M),
    (∀ i, IsOpen (U i)) ∧ (∀ i, ContMDiffOn 𝓘(ℝ, Fin d → ℝ) I 1 (g i) (U i)) ∧
      T ⊆ ⋃ i, g i '' U i

def isEmbeddedOn (I : ModelWithCorners ℝ (Fin n → ℝ) H) (h : ℝ → ℝ → M) (Q : Set (ℝ × ℝ)) :
    Prop :=
  (∀ z ∈ Q, mfderiv 𝓘(ℝ, ℝ) I (fun θ => h θ z.2) z.1 (1 : ℝ) ≠ 0) ∧
    ∀ θ θ' s, (θ, s) ∈ Q → (θ', s) ∈ Q → h θ s = h θ' s → ∃ k : ℤ, θ' = θ + k

def boxSet (i₀ : Fin n) (ρ L : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < ρ) ∧ -ρ < y i₀ ∧ y i₀ < L + ρ}

def innerBox (i₀ : Fin n) (ρ L : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < ρ / 2) ∧ L / 4 < y i₀ ∧ y i₀ < 3 * L / 4}

def midBox (i₀ : Fin n) (ρ L : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < 3 * ρ / 4) ∧ L / 8 < y i₀ ∧ y i₀ < 7 * L / 8}

def bottomFace (i₀ : Fin n) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j, j ≠ i₀ → |y j| < ρ) ∧ y i₀ = 0}

def offAxisSq (i₀ : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∑ j, if j = i₀ then 0 else y j ^ 2

def diagQuad (i₀ : Fin n) (w : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ j, if j = i₀ then 0 else w j * y j ^ 2

def taperedModel (i₀ : Fin n) (w : Fin n → ℝ) (s a b γ : ℝ → ℝ) (y : Fin n → ℝ) : ℝ :=
  y i₀ + s (y i₀) * a (offAxisSq i₀ y) + γ (y i₀) * diagQuad i₀ w y * b (offAxisSq i₀ y)

section Strip

variable {I : ModelWithCorners ℝ (Fin n → ℝ) H} [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]
  {f : M → ℝ} {a b : ℝ} {crit : Finset M}

def descendsFreely (D : GradientLikeStrip I f a b crit) (T : ℝ) (x : M) : Prop :=
  ∀ s ∈ Icc 0 T, ∀ p (hp : p ∈ crit), D.flow s x ∉ D.closedSmallBall p hp

def ascendsFreely (D : GradientLikeStrip I f a b crit) (T : ℝ) (x : M) : Prop :=
  ∀ s ∈ Icc (-T) 0, ∀ p (hp : p ∈ crit), D.flow s x ∉ D.closedSmallBall p hp

def isFineAt (D : GradientLikeStrip I f a b crit) (δ : ℝ) : Prop :=
  ∀ x (hx : x ∈ crit),
    (D.chart x hx).χ '' Metric.ball 0 (D.chart x hx).R' ⊆ f ⁻¹' Ioo (f x - δ) (f x + δ)

def leftPt (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit)
    (hk : (D.chart q hq).k = 2) (ε t : ℝ) : M :=
  (D.chart q hq).χ ((D.chart q hq).sphereParam ε (fun i => circ2 t (Fin.cast hk i)))

def leftLoop (D : GradientLikeStrip I f a b crit) (q : M) (hq : q ∈ crit)
    (hk : (D.chart q hq).k = 2) (ε c : ℝ) : ℝ → M :=
  fun t => D.flow (f q - ε - c) (leftPt D q hq hk ε t)

def rightFun (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε c : ℝ) (x : M) :
    EuclideanSpace ℝ (Fin (D.chart p hp).k) :=
  ModelField.scaledNegativePart (D.chart p hp).hk ((D.chart p hp).χ.symm (D.flow (c - (f p + ε)) x))

def rightDom (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε c : ℝ) : Set M :=
  {x | D.flow (c - (f p + ε)) x ∈ (D.chart p hp).χ '' {y | morseNorm n y < (D.chart p hp).R}}

def meetsRightOnce (D : GradientLikeStrip I f a b crit) (p : M) (hp : p ∈ crit) (ε c : ℝ)
    (γ : ℝ → M) : Prop :=
  ∃ t₀ : ℝ, γ t₀ ∈ rightDom D p hp ε c ∧ rightFun D p hp ε c (γ t₀) = 0 ∧
    (∀ t, γ t ∈ rightDom D p hp ε c → rightFun D p hp ε c (γ t) = 0 → ∃ m : ℤ, t = t₀ + m) ∧
    ∃ v, HasDerivAt (fun t => rightFun D p hp ε c (γ t)) v t₀ ∧ v ≠ 0

def isLevelAnnulus (D : GradientLikeStrip I f a b crit) (c c' : ℝ) (A : ℝ → ℝ → M)
    (γ β : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (uncurry A) ∧ (∀ θ s, A (θ + 1) s = A θ s) ∧
    (∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, f (A θ s) = c + s * (c' - c)) ∧
    (∀ θ θ', ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, A θ s = A θ' s' →
      s = s' ∧ ∃ k : ℤ, θ' = θ + k) ∧
    (∀ θ, ∀ s ∈ Icc (0 : ℝ) 1, mfderiv 𝓘(ℝ, ℝ) I (fun θ' => A θ' s) θ (1 : ℝ) ≠ 0) ∧
    ∃ η > 0, (∀ θ, ∀ s ∈ Icc 0 η, A θ s = D.flow (-(s * (c' - c))) (γ θ)) ∧
      ∀ θ, ∀ s ∈ Icc (1 - η) 1, A θ s = D.flow ((1 - s) * (c' - c)) (β θ)

structure FlowBox (D : GradientLikeStrip I f a b crit) (x₀ : M) (c L ρ : ℝ) where
  ψ : OpenPartialHomeomorph (Fin n → ℝ) M
  i₀ : Fin n
  map_zero : ψ 0 = x₀
  box_subset : boxSet i₀ ρ L ⊆ ψ.source
  smooth : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) I ∞ ψ ψ.source
  smooth_symm : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm ψ.target
  level : ∀ y ∈ boxSet i₀ ρ L, f (ψ y) = c + y i₀
  vertical : ∀ y ∈ boxSet i₀ ρ L, ∀ s : ℝ, y - s • Pi.single i₀ (1 : ℝ) ∈ boxSet i₀ ρ L →
    D.flow s (ψ y) = ψ (y - s • Pi.single i₀ (1 : ℝ))
  avoid : ∀ y ∈ boxSet i₀ ρ L, ∀ p (hp : p ∈ crit),
    ψ y ∉ (D.chart p hp).χ '' Metric.ball 0 (D.chart p hp).R'

end Strip

end

end IndexOnePartner

end DifferentialGeometry.Topology
