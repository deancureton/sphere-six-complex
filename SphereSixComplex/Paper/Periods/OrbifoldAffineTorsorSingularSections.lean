module

public import SphereSixComplex.Paper.Periods.OrbifoldAffineTorsorTransport
import all SphereSixComplex.Paper.TriangleGroup.Representation

@[expose] public section

noncomputable section

open SphereSixComplex.TriangleGroup SphereSixComplex.Geometry
open scoped Manifold

namespace SphereSixComplex.Periods.OrbifoldAffineDescentData

public theorem transportSection_pow_fixed (P : OrbifoldAffineDescentData)
    {g : Delta} {t : UpperHalfPlane → ℂ} (ht : P.transportSection g t = t) (n : ℕ) :
    P.transportSection (g ^ n) t = t := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, P.transportSection_mul, ht, hn]

public theorem transportSection_ellipticOne_fixed (P : OrbifoldAffineDescentData)
    (a : CyclicThree) : P.transportSection (Monoid.Coprod.inl a) P.ellipticOne = P.ellipticOne := by
  have ht : P.transportSection g₁ P.ellipticOne = P.ellipticOne := by
    funext z
    simpa [transportSection, affineOnePerm, affineOneSkew] using
      (P.ellipticOne_equivariant (fuchsianSourceAction g₁⁻¹ • z)).symm
  have ha : a = Multiplicative.ofAdd (1 : ZMod 3) ^ a.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  rw [ha, map_pow]
  exact P.transportSection_pow_fixed ht _

public theorem transportSection_ellipticTwo_fixed (P : OrbifoldAffineDescentData)
    (a : CyclicFour) : P.transportSection (Monoid.Coprod.inr a) P.ellipticTwo = P.ellipticTwo := by
  have ht : P.transportSection g₂ P.ellipticTwo = P.ellipticTwo := by
    funext z
    simpa [transportSection, affineTwoPerm, affineTwoSkew] using
      (P.ellipticTwo_equivariant (fuchsianSourceAction g₂⁻¹ • z)).symm
  have ha : a = Multiplicative.ofAdd (1 : ZMod 4) ^ a.toAdd.val := by
    apply Multiplicative.toAdd.injective
    simp
  rw [ha, map_pow]
  exact P.transportSection_pow_fixed ht _

public theorem exists_equivariant_section_on_precise_saturation
    (P : OrbifoldAffineDescentData) {S : Set UpperHalfPlane}
    (hopen : IsOpen S) (t : UpperHalfPlane → ℂ) (ht : MDiff t)
    (hprecise : ∀ g x, x ∈ S → fuchsianSourceAction g • x ∈ S →
      P.transportSection g t = t) :
    ∃ s : UpperHalfPlane → ℂ,
      (∀ z, (∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S) → MDiffAt s z) ∧
      (∀ z ∈ S, s z = t z) ∧
      (∀ h z, (∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S) →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  classical
  let deck (z : UpperHalfPlane) : Delta :=
    if hz : ∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S then hz.choose else 1
  have hdeck {z : UpperHalfPlane} (hz : ∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S) :
      fuchsianSourceAction (deck z)⁻¹ • z ∈ S := by
    simpa only [deck, dite_eq_left hz] using hz.choose_spec
  let s : UpperHalfPlane → ℂ := fun z ↦ P.transportSection (deck z) t z
  have hs {z : UpperHalfPlane} {g : Delta}
      (hg : fuchsianSourceAction g⁻¹ • z ∈ S) : s z = P.transportSection g t z := by
    have hz : ∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S := ⟨g, hg⟩
    have hm : fuchsianSourceAction ((deck z)⁻¹ * g) •
        (fuchsianSourceAction g⁻¹ • z) ∈ S := by
      simpa only [map_mul, mul_smul, map_inv, smul_inv_smul] using hdeck hz
    have he := congrArg (P.transportSection (deck z))
      (hprecise ((deck z)⁻¹ * g) _ hg hm)
    rw [← P.transportSection_mul, mul_inv_cancel_left] at he
    exact congrFun he.symm z
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro z ⟨g, hg⟩
    have hn : ∀ᶠ w in nhds z, fuchsianSourceAction g⁻¹ • w ∈ S :=
      (fuchsianSourceAction_contMDiff g⁻¹ 0).continuous.continuousAt (hopen.mem_nhds hg)
    apply (P.transportSection_holomorphic g t ht).mdifferentiableAt.congr_of_eventuallyEq
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

public theorem coordinate_image_mem_iff_saturation
    (P : OrbifoldAffineDescentData) (S : Set UpperHalfPlane) (z : UpperHalfPlane) :
    P.quotient.coordinate z ∈ P.quotient.coordinate '' S ↔
      ∃ g : Delta, fuchsianSourceAction g⁻¹ • z ∈ S := by
  constructor
  · rintro ⟨x, hx, hcoord⟩
    obtain ⟨g, hg⟩ := (P.quotient.coordinate_eq_iff_orbit x z).mp hcoord
    refine ⟨g, ?_⟩
    rw [← hg, map_inv, inv_smul_smul]
    exact hx
  · rintro ⟨g, hg⟩
    exact ⟨_, hg, P.quotient.coordinate_invariant _ z⟩

public theorem coordinate_isOpenMap (P : OrbifoldAffineDescentData) :
    IsOpenMap P.quotient.coordinate := by
  intro S hS
  apply P.quotient.coordinate_isQuotientMap.isCoinducing.isOpen_preimage.mp
  have he : P.quotient.coordinate ⁻¹' (P.quotient.coordinate '' S) =
      ⋃ g : Delta, (fun z ↦ fuchsianSourceAction g⁻¹ • z) ⁻¹' S := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, P.coordinate_image_mem_iff_saturation]
  rw [he]
  exact isOpen_iUnion (fun g ↦ hS.preimage
    (fuchsianSourceAction_contMDiff g⁻¹ 0).continuous)

public theorem exists_local_equivariant_section_of_stabilizer_fixed
    (P : OrbifoldAffineDescentData) (z₀ : UpperHalfPlane)
    (t : UpperHalfPlane → ℂ) (ht : MDiff t)
    (hfixed : ∀ g : Delta, fuchsianSourceAction g • z₀ = z₀ → P.transportSection g t = t) :
    ∃ W : Set ℂ, IsOpen W ∧ P.quotient.coordinate z₀ ∈ W ∧
      ∃ s : UpperHalfPlane → ℂ,
      (∀ z, P.quotient.coordinate z ∈ W → MDiffAt s z) ∧
      (∀ᶠ z in nhds z₀, s z = t z) ∧
      (∀ h z, P.quotient.coordinate z ∈ W →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  let _ : MulAction Delta UpperHalfPlane := FuchsianProperFreeness.fuchsianSourceMulAction
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    FuchsianArithmeticTermination.fuchsianSourceAction_properlyDiscontinuous
  obtain ⟨S, hS, hz₀, _, htranslate⟩ := exists_open_stabilizer_slice (G := Delta) z₀
  have hprecise : ∀ g x, x ∈ S → fuchsianSourceAction g • x ∈ S →
      P.transportSection g t = t := by
    intro g x hx hgx
    apply hfixed g
    exact (htranslate g).mp ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  obtain ⟨s, hdiff, heq, hequiv⟩ :=
    P.exists_equivariant_section_on_precise_saturation hS t ht hprecise
  refine ⟨P.quotient.coordinate '' S, P.coordinate_isOpenMap S hS, ⟨z₀, hz₀, rfl⟩,
    s, fun z hz ↦ hdiff z ((P.coordinate_image_mem_iff_saturation S z).mp hz), ?_,
    fun h z hz ↦ hequiv h z ((P.coordinate_image_mem_iff_saturation S z).mp hz)⟩
  filter_upwards [hS.mem_nhds hz₀] with z hz
  exact heq z hz

public theorem exists_ellipticOne_local_equivariant_section
    (P : OrbifoldAffineDescentData) :
    ∃ W : Set ℂ, IsOpen W ∧ 0 ∈ W ∧ ∃ s : UpperHalfPlane → ℂ,
      (∀ z, P.quotient.coordinate z ∈ W → MDiffAt s z) ∧
      (∀ᶠ z in nhds fuchsianOneFixedPoint, s z = P.ellipticOne z) ∧
      (∀ h z, P.quotient.coordinate z ∈ W →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  simpa only [P.quotient.coordinate_at_one] using
    P.exists_local_equivariant_section_of_stabilizer_fixed fuchsianOneFixedPoint
      P.ellipticOne P.ellipticOne_holomorphic (by
        intro g hg
        obtain ⟨a, rfl⟩ := (fuchsianOneFixed_iff_mem_range_inl g).mp hg
        exact P.transportSection_ellipticOne_fixed a)

public theorem exists_ellipticTwo_local_equivariant_section
    (P : OrbifoldAffineDescentData) :
    ∃ W : Set ℂ, IsOpen W ∧ 1 ∈ W ∧ ∃ s : UpperHalfPlane → ℂ,
      (∀ z, P.quotient.coordinate z ∈ W → MDiffAt s z) ∧
      (∀ᶠ z in nhds fuchsianTwoFixedPoint, s z = P.ellipticTwo z) ∧
      (∀ h z, P.quotient.coordinate z ∈ W →
        s (fuchsianSourceAction h • z) = (P.affineTransport h (z, s z)).2) := by
  simpa only [P.quotient.coordinate_at_two] using
    P.exists_local_equivariant_section_of_stabilizer_fixed fuchsianTwoFixedPoint
      P.ellipticTwo P.ellipticTwo_holomorphic (by
        intro g hg
        obtain ⟨a, rfl⟩ := (fuchsianTwoFixed_iff_mem_range_inr g).mp hg
        exact P.transportSection_ellipticTwo_fixed a)

end SphereSixComplex.Periods.OrbifoldAffineDescentData
