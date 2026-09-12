module

public import SphereSixComplex.Paper.Periods.EstablishedOrbifoldAffineTorsorAnalyticDescentProof
public import SphereSixComplex.Paper.TriangleGroup.FuchsianArithmeticTermination
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section

noncomputable section

open SphereSixComplex.TriangleGroup
open scoped Manifold

namespace SphereSixComplex.TriangleGroup

public theorem delta_generator_induction {motive : Delta → Prop}
    (one : motive 1) (three : motive g₁) (four : motive g₂)
    (mul : ∀ x y, motive x → motive y → motive (x * y)) (g : Delta) : motive g := by
  have powers : ∀ x, motive x → ∀ n : ℕ, motive (x ^ n) := by
    intro x hx n
    induction n with
    | zero => simpa using one
    | succ n ih => simpa only [pow_succ] using mul _ _ ih hx
  have cyclic {k : ℕ} [NeZero k] (x : Multiplicative (ZMod k)) :
      x = Multiplicative.ofAdd (1 : ZMod k) ^ x.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  refine Monoid.Coprod.induction_on (motive := motive) g ?_ ?_ mul
  · intro x
    rw [cyclic x, map_pow]
    exact powers g₁ three _
  · intro x
    rw [cyclic x, map_pow]
    exact powers g₂ four _

end SphereSixComplex.TriangleGroup

namespace SphereSixComplex.Periods.OrbifoldAffineDescentData

public def affineOneSkew (P : OrbifoldAffineDescentData)
    (p : UpperHalfPlane × ℂ) : UpperHalfPlane × ℂ :=
  (fuchsianSourceAction g₁ • p.1, P.affineOne p.1 p.2)

public theorem affineOneSkew_cube (P : OrbifoldAffineDescentData)
    (p : UpperHalfPlane × ℂ) :
    P.affineOneSkew (P.affineOneSkew (P.affineOneSkew p)) = p := by
  apply Prod.ext
  · change fuchsianSourceAction g₁ • (fuchsianSourceAction g₁ •
      (fuchsianSourceAction g₁ • p.1)) = p.1
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
      ← pow_two, ← pow_succ, g₁_pow_three, map_one, one_smul]
  · change P.affineOne (fuchsianSourceAction g₁ • (fuchsianSourceAction g₁ • p.1))
      (P.affineOne (fuchsianSourceAction g₁ • p.1) (P.affineOne p.1 p.2)) = p.2
    rw [← mul_smul, ← map_mul, ← pow_two]
    exact P.affineOne_cycle p.1 p.2

public def affineOnePerm (P : OrbifoldAffineDescentData) :
    Equiv.Perm (UpperHalfPlane × ℂ) where
  toFun := P.affineOneSkew
  invFun := fun p ↦ P.affineOneSkew (P.affineOneSkew p)
  left_inv := P.affineOneSkew_cube
  right_inv := P.affineOneSkew_cube

public theorem affineOnePerm_pow_three (P : OrbifoldAffineDescentData) :
    P.affineOnePerm ^ 3 = 1 := by
  apply Equiv.ext
  intro p
  exact P.affineOneSkew_cube p

public def affineTwoSkew (P : OrbifoldAffineDescentData)
    (p : UpperHalfPlane × ℂ) : UpperHalfPlane × ℂ :=
  (fuchsianSourceAction g₂ • p.1, P.affineTwo p.1 p.2)

public theorem affineTwoSkew_fourth (P : OrbifoldAffineDescentData)
    (p : UpperHalfPlane × ℂ) :
    P.affineTwoSkew (P.affineTwoSkew (P.affineTwoSkew (P.affineTwoSkew p))) = p := by
  have h₂ : ∀ z : UpperHalfPlane, fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • z) =
      fuchsianSourceAction (g₂ ^ 2) • z := by
    intro z
    rw [pow_two, map_mul, mul_smul]
  have h₃ : ∀ z : UpperHalfPlane, fuchsianSourceAction g₂ •
      (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • z)) =
      fuchsianSourceAction (g₂ ^ 3) • z := by
    intro z
    rw [pow_succ, map_mul, mul_smul, h₂]
  apply Prod.ext
  · change fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ •
      (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • p.1))) = p.1
    rw [h₃, ← mul_smul, ← map_mul, ← pow_succ, g₂_pow_four, map_one, one_smul]
  · change P.affineTwo (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ •
        (fuchsianSourceAction g₂ • p.1)))
      (P.affineTwo (fuchsianSourceAction g₂ • (fuchsianSourceAction g₂ • p.1))
        (P.affineTwo (fuchsianSourceAction g₂ • p.1) (P.affineTwo p.1 p.2))) = p.2
    rw [h₃, h₂]
    exact P.affineTwo_cycle p.1 p.2

public def affineTwoPerm (P : OrbifoldAffineDescentData) :
    Equiv.Perm (UpperHalfPlane × ℂ) where
  toFun := P.affineTwoSkew
  invFun := fun p ↦ P.affineTwoSkew (P.affineTwoSkew (P.affineTwoSkew p))
  left_inv := P.affineTwoSkew_fourth
  right_inv := P.affineTwoSkew_fourth

public theorem affineTwoPerm_pow_four (P : OrbifoldAffineDescentData) :
    P.affineTwoPerm ^ 4 = 1 := by
  apply Equiv.ext
  intro p
  exact P.affineTwoSkew_fourth p

public def affineTransport (P : OrbifoldAffineDescentData) :
    Delta →* Equiv.Perm (UpperHalfPlane × ℂ) :=
  Monoid.Coprod.lift
    (cyclicRepresentation 3 P.affineOnePerm P.affineOnePerm_pow_three)
    (cyclicRepresentation 4 P.affineTwoPerm P.affineTwoPerm_pow_four)

@[simp] public theorem affineTransport_g₁ (P : OrbifoldAffineDescentData) :
    P.affineTransport g₁ = P.affineOnePerm := by
  simp [affineTransport, g₁, cyclicRepresentation_generator]

@[simp] public theorem affineTransport_g₂ (P : OrbifoldAffineDescentData) :
    P.affineTransport g₂ = P.affineTwoPerm := by
  simp [affineTransport, g₂, cyclicRepresentation_generator]

public theorem affineTransport_fst (P : OrbifoldAffineDescentData)
    (g : Delta) (p : UpperHalfPlane × ℂ) :
    (P.affineTransport g p).1 = fuchsianSourceAction g • p.1 := by
  induction g using delta_generator_induction generalizing p with
  | one => simp
  | three => rfl
  | four => rfl
  | mul g h hg hh =>
      rw [map_mul, Equiv.Perm.mul_apply, hg, hh, map_mul, mul_smul]

public def transportSection (P : OrbifoldAffineDescentData)
    (g : Delta) (s : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (P.affineTransport g (fuchsianSourceAction g⁻¹ • z,
    s (fuchsianSourceAction g⁻¹ • z))).2

@[simp] public theorem transportSection_one (P : OrbifoldAffineDescentData)
    (s : UpperHalfPlane → ℂ) : P.transportSection 1 s = s := by
  funext z
  simp [transportSection]

public theorem transportSection_mul (P : OrbifoldAffineDescentData)
    (g h : Delta) (s : UpperHalfPlane → ℂ) :
    P.transportSection (g * h) s = P.transportSection g (P.transportSection h s) := by
  funext z
  simp only [transportSection, mul_inv_rev, map_mul, mul_smul, Equiv.Perm.mul_apply]
  congr 2
  apply Prod.ext
  · rw [P.affineTransport_fst]
    simp
  · rfl

public theorem transportSection_holomorphic (P : OrbifoldAffineDescentData)
    (g : Delta) (s : UpperHalfPlane → ℂ) (hs : MDiff s) :
    MDiff (P.transportSection g s) := by
  induction g using delta_generator_induction generalizing s with
  | one => simpa using hs
  | three =>
      exact (P.affineOne_holomorphic s hs).comp
        ((fuchsianSourceAction_contMDiff g₁⁻¹ ⊤).mdifferentiable (by simp))
  | four =>
      exact (P.affineTwo_holomorphic s hs).comp
        ((fuchsianSourceAction_contMDiff g₂⁻¹ ⊤).mdifferentiable (by simp))
  | mul g h hg hh =>
      rw [P.transportSection_mul]
      exact hg _ (hh s hs)

public theorem regular_fixed_eq_one (P : OrbifoldAffineDescentData)
    {z : UpperHalfPlane} (hz : P.quotient.coordinate z ∉ ({0, 1} : Set ℂ))
    {g : Delta} (hg : fuchsianSourceAction g • z = z) : g = 1 := by
  apply FuchsianProperFreeness.fuchsian_fixed_regular_eq_one
    FuchsianArithmeticTermination.fuchsianSourceAction_properlyDiscontinuous ?_ hg
  intro h
  constructor
  · intro he
    apply hz
    have hv := P.quotient.coordinate_invariant h z
    rw [he, P.quotient.coordinate_at_one] at hv
    simp [← hv]
  · intro he
    apply hz
    have hv := P.quotient.coordinate_invariant h z
    rw [he, P.quotient.coordinate_at_two] at hv
    simp [← hv]

public theorem regular_action_injective (P : OrbifoldAffineDescentData)
    {z : UpperHalfPlane} (hz : P.quotient.coordinate z ∉ ({0, 1} : Set ℂ)) :
    Function.Injective (fun g : Delta ↦ fuchsianSourceAction g • z) := by
  intro g h he
  change fuchsianSourceAction g • z = fuchsianSourceAction h • z at he
  have hf : fuchsianSourceAction (h⁻¹ * g) • z = z := by
    rw [map_mul, mul_smul, he, map_inv, inv_smul_smul]
  exact (inv_mul_eq_one.mp (P.regular_fixed_eq_one hz hf)).symm

public theorem sheet_translate_unique (P : OrbifoldAffineDescentData)
    {S : Set UpperHalfPlane} (hS : S.InjOn P.quotient.coordinate)
    (hreg : ∀ z ∈ S, P.quotient.coordinate z ∉ ({0, 1} : Set ℂ))
    {g h : Delta} {z : UpperHalfPlane}
    (hg : fuchsianSourceAction g⁻¹ • z ∈ S)
    (hh : fuchsianSourceAction h⁻¹ • z ∈ S) : g = h := by
  have he : fuchsianSourceAction g⁻¹ • z = fuchsianSourceAction h⁻¹ • z := by
    apply hS hg hh
    rw [P.quotient.coordinate_invariant, P.quotient.coordinate_invariant]
  have hz : P.quotient.coordinate z ∉ ({0, 1} : Set ℂ) := by
    simpa only [P.quotient.coordinate_invariant] using hreg _ hg
  exact inv_injective (P.regular_action_injective hz he)

public theorem exists_equivariant_section_on_sheet_saturation
    (P : OrbifoldAffineDescentData) {S : Set UpperHalfPlane}
    (hopen : IsOpen S) (hinj : S.InjOn P.quotient.coordinate)
    (hreg : ∀ z ∈ S, P.quotient.coordinate z ∉ ({0, 1} : Set ℂ)) :
    ∃ s : UpperHalfPlane → ℂ,
      (∀ z, (∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S) → MDiffAt s z) ∧
      (∀ z ∈ S, s z = 0) ∧
      (∀ h z, (∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S) →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  classical
  let deck (z : UpperHalfPlane) : Delta :=
    if hz : ∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S then hz.choose else 1
  have hdeck {z : UpperHalfPlane} {g : Delta}
      (hg : fuchsianSourceAction g⁻¹ • z ∈ S) : deck z = g := by
    have hz : ∃ h : Delta, fuchsianSourceAction h⁻¹ • z ∈ S := ⟨g, hg⟩
    simp only [deck, dite_eq_left hz]
    exact P.sheet_translate_unique hinj hreg hz.choose_spec hg
  let s : UpperHalfPlane → ℂ := fun z ↦ P.transportSection (deck z) (fun _ ↦ 0) z
  have hs {z : UpperHalfPlane} {g : Delta}
      (hg : fuchsianSourceAction g⁻¹ • z ∈ S) :
      s z = P.transportSection g (fun _ ↦ 0) z := by
    dsimp only [s]
    rw [hdeck hg]
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro z ⟨g, hg⟩
    have hn : ∀ᶠ w in nhds z, fuchsianSourceAction g⁻¹ • w ∈ S :=
      (fuchsianSourceAction_contMDiff g⁻¹ 0).continuous.continuousAt
        (hopen.mem_nhds hg)
    apply (P.transportSection_holomorphic g (fun _ ↦ 0) mdifferentiable_const).mdifferentiableAt.congr_of_eventuallyEq
    filter_upwards [hn] with w hw
    exact hs hw
  · intro z hz
    have hm : fuchsianSourceAction (1 : Delta)⁻¹ • z ∈ S := by simpa using hz
    rw [hs hm, P.transportSection_one]
  · rintro h z ⟨g, hg⟩
    have hhg : fuchsianSourceAction (h * g)⁻¹ • (fuchsianSourceAction h • z) ∈ S := by
      simpa only [mul_inv_rev, map_mul, mul_smul, map_inv, inv_smul_smul] using hg
    rw [hs hhg, hs hg]
    simp only [transportSection, mul_inv_rev, map_mul, mul_smul, map_inv,
      inv_smul_smul, Equiv.Perm.mul_apply]
    congr 2
    apply Prod.ext
    · rw [P.affineTransport_fst]
      simp
    · rfl

public theorem exists_regular_local_equivariant_section
    (P : OrbifoldAffineDescentData) {z₀ : UpperHalfPlane}
    (hz₀ : P.quotient.coordinate z₀ ∉ ({0, 1} : Set ℂ)) :
    ∃ W : Set ℂ, IsOpen W ∧ P.quotient.coordinate z₀ ∈ W ∧
      W ⊆ ({0, 1} : Set ℂ)ᶜ ∧ ∃ s : UpperHalfPlane → ℂ,
      (∀ z, P.quotient.coordinate z ∈ W → MDiffAt s z) ∧ s z₀ = 0 ∧
      (∀ h z, P.quotient.coordinate z ∈ W →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  obtain ⟨e, hze, he⟩ := P.quotient.regular_covering.isLocalHomeomorphOn z₀ hz₀
  let S := e.source ∩ P.quotient.coordinate ⁻¹' ({0, 1} : Set ℂ)ᶜ
  have hopen : IsOpen S := e.open_source.inter
    ((show IsClosed ({0, 1} : Set ℂ) from isClosed_singleton.union isClosed_singleton).isOpen_compl.preimage
      P.quotient.coordinate_holomorphic.continuous)
  have hinj : S.InjOn P.quotient.coordinate := by
    intro x hx y hy hxy
    apply e.injOn hx.1 hy.1
    simpa only [← he] using hxy
  have hreg : ∀ z ∈ S, P.quotient.coordinate z ∉ ({0, 1} : Set ℂ) :=
    fun _ hz ↦ hz.2
  obtain ⟨s, hdiff, hzero, hequiv⟩ :=
    P.exists_equivariant_section_on_sheet_saturation hopen hinj hreg
  have hsat {z : UpperHalfPlane} (hz : P.quotient.coordinate z ∈
      P.quotient.coordinate '' S) : ∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S := by
    obtain ⟨x, hx, hcoord⟩ := hz
    obtain ⟨g, hg⟩ := (P.quotient.coordinate_eq_iff_orbit x z).mp hcoord
    refine ⟨g, ?_⟩
    rw [← hg, map_inv, inv_smul_smul]
    exact hx
  refine ⟨P.quotient.coordinate '' S, ?_, ⟨z₀, ⟨hze, hz₀⟩, rfl⟩, ?_,
    s, fun z hz ↦ hdiff z (hsat hz), hzero z₀ ⟨hze, hz₀⟩,
    fun h z hz ↦ hequiv h z (hsat hz)⟩
  · rw [he]
    exact e.isOpen_image_of_subset_source hopen Set.inter_subset_left
  · rintro q ⟨z, hz, rfl⟩
    exact hz.2

end SphereSixComplex.Periods.OrbifoldAffineDescentData
