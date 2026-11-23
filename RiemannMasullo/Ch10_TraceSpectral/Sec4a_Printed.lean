module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Quotient
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # False assertions in §§10.4.1–10.4.2 -/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "W(" F ", " s ")" => CompactIntervalSobolev (ideleClassTamagawaMeasure F)
  (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ)) 0 0 s

/-- Paper: Remark 10.4.1.4, p. 457. At the singleton base and nonnegative
even degree an equivalent Hilbert metric makes all left translations conformal.
The parallelogram identity expresses the requirement that the norm be Hilbertian. -/
def Printed.hardySobolevTranslation_conformal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ),
    let s : ℝ := 2 * n
    let T := hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F)) 0 0 s le_rfl
      (mul_nonneg zero_le_two (Nat.cast_nonneg n))
    ∃ (p : Seminorm ℂ (W(F, s))) (b B : ℝ), 0 < b ∧ 0 < B ∧
      (∀ u, b * ‖u‖ ≤ p u ∧ p u ≤ B * ‖u‖) ∧
      (∀ u v, p (u + v) ^ 2 + p (u - v) ^ 2 = 2 * (p u ^ 2 + p v ^ 2)) ∧
      ∀ g : C𝔽(F), ∃ c : ℝ, 0 < c ∧ ∀ u, p (T g u) = c * p u

/-- Paper: Remark 10.4.1.4, p. 457. Take F = ℚ and s = 2. The powers of a
class of logarithmic norm one and of its inverse have polynomial norm bounds,
so its dilation factor in any equivalent conformal norm must equal one.
On the indicator of the log-norm band [0, 1], the norms of the translates by
positive powers grow without bound in the weighted Hilbert norm. -/
theorem Printed.hardySobolevTranslation_conformal_false :
    ¬ Printed.hardySobolevTranslation_conformal := by sorry

section ApproximateLifts

local notation "closedSpan(" u ")" => (Submodule.span ℂ (Set.range u)).topologicalClosure

/-- Paper: Lemma 10.4.2.5, p. 461. A normalized Schauder or Markushevich
quotient basis has bounded biorthogonal lifts forming a normalized Schauder
basis of their closed span, stable under small perturbations in the kernel.
The Banach-space Markushevich condition uses point separation by the dual
family, equivalently weak-star density of its span. -/
def Printed.epsilonBasisLift_schauder : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]
    (x : ℕ → E ⧸ E₀) (f : ℕ → StrongDual ℂ (E ⧸ E₀)),
    ((∃ b : _root_.SchauderBasis ℂ (E ⧸ E₀), b.basis = x ∧ b.coord = f) ∨
      ((∀ m n, f m (x n) = if m = n then 1 else 0) ∧
        Dense (Submodule.span ℂ (range x) : Set (E ⧸ E₀)) ∧
        ∀ v, (∀ m, f m v = 0) → v = 0)) →
    IsNormalizedSpectralFamily x →
    ∀ (r r' : ℝ), 0 < r → 0 < r' → (∀ m, ‖x m‖ ∈ Icc r r') →
      E₀ ≤ (V ⊓ E₀).topologicalClosure → (∀ m, x m ∈ V.map E₀.mkQ) →
      ∃ (u : ℕ → E) (ε : ℝ), IsEpsilonBasisLift E₀ V x f r r' ε u ∧
        IsNormalizedSpectralFamily u ∧
        (∃ b : _root_.SchauderBasis ℂ (closedSpan(u)), ∀ m, (b m).val = u m) ∧
        ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧
          ∀ y : ℕ → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
            IsEpsilonBasisLift E₀ V x f r r' ε (fun m ↦ u m + y m) ∧
            ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
              ∀ (v : closedSpan(u)) (m : ℕ), v.val = u m → (T v).val = u m + y m

/-- Paper: Lemma 10.4.2.5, p. 461. In complex ℓ² take E₀ = 0 and V = E.
With its standard unit vectors eⱼ, choose x₂ₖ = e₂ₖ and
x₂ₖ₊₁ = (e₂ₖ + dₖ e₂ₖ₊₁)/sqrt(1 + dₖ²), where dₖ = 1/(k+1).
The inverse change of coordinates on each two-dimensional block gives
continuous biorthogonal functionals whose common kernel is zero. The
partial-sum projection up to x₂ₖ sends e₂ₖ₊₁ to −(k+1)e₂ₖ, so these
projections are unbounded. Biorthogonality forces the lift to be x itself.

Even Schauder input can fail. Take the convergent complex sequences with sup norm,
divide by the constants, and take V = E. The classes of 2eₙ form a Schauder basis
of quotient norm one. Set r = r' = 1. Every collar lift has form 2eₙ + cₙ1 with
|2 + cₙ| ≤ 1 + ε, hence Re cₙ ≤ ε − 1 < 0. A subsequence of the bounded Cesàro
means of the cₙ converges to a nonzero c. The corresponding means of the 2eₙ
tend to zero in sup norm, so c1 belongs to the closed span of the lifts. Every
pulled-back coordinate vanishes on this constant. By density it would be the
corresponding Schauder coordinate on that span, which is impossible. -/
theorem Printed.epsilonBasisLift_schauder_false : ¬ Printed.epsilonBasisLift_schauder := by sorry

/-- Paper: Remark 10.4.2.7, p. 463. If V has dense image in the quotient and
its intersection with the kernel is dense in the kernel, a normalized quotient
Schauder basis has a Schauder lift in V that is stable under kernel perturbations. -/
def Printed.epsilonBasisLift_of_dense_image : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]
    (b : _root_.SchauderBasis ℂ (E ⧸ E₀)), IsNormalizedSpectralFamily b.basis →
    E₀ ≤ (V ⊓ E₀).topologicalClosure → Dense (V.map E₀.mkQ : Set (E ⧸ E₀)) →
    ∃ (u : ℕ → E) (r r' ε : ℝ),
      0 < r ∧ 0 < r' ∧ (∀ m, ‖b m‖ ∈ Icc r r') ∧ IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε u ∧
      (∃ b' : _root_.SchauderBasis ℂ (closedSpan(u)), ∀ m, (b' m).val = u m) ∧
      ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧
        ∀ y : ℕ → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
          IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε (fun m ↦ u m + y m) ∧
          ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
            ∀ (v : closedSpan(u)) (m : ℕ), v.val = u m → (T v).val = u m + y m

/-- A dense subspace of ℓ² need not contain its first standard basis vector. -/
private theorem epsilonBasisLift_of_dense_image_missing :
    ∃ V : Submodule ℂ (lp (fun _ : ℕ ↦ ℂ) 2),
      Dense (V : Set (lp (fun _ : ℕ ↦ ℂ) 2)) ∧ lp.single 2 0 (1 : ℂ) ∉ V := by
  let e : ℕ → (lp (fun _ : ℕ ↦ ℂ) 2) := fun n ↦ lp.single 2 n (1 : ℂ)
  let a : ℕ → ℂ := fun n ↦ (1 / 2 : ℂ)^n
  let v : ℕ → (lp (fun _ : ℕ ↦ ℂ) 2) := fun n ↦ e 0 + a n • e (n+1)
  let V : Submodule ℂ (lp (fun _ : ℕ ↦ ℂ) 2) := Submodule.span ℂ (Set.range v)
  have hn : e 0 ∉ V := by
    intro h
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h
    have hcz (n : ℕ) : c n = 0 := by
      let ev : (lp (fun _ : ℕ ↦ ℂ) 2) →ₗ[ℂ] ℂ := lp.evalₗ (fun _ : ℕ ↦ ℂ) 2 (n+1)
      have hh := congrArg ev hc
      change ev (∑ i ∈ c.support, c i • v i) = ev (e 0) at hh
      simp only [map_sum, map_smul, v, map_add, e, ev, lp.evalₗ_apply, lp.single_apply] at hh
      simp [Pi.single_apply, a, Finsupp.mem_support_iff] at hh
      exact hh
    have hc0 : c = 0 := Finsupp.ext hcz
    subst c
    have hh := congrArg (fun f : (lp (fun _ : ℕ ↦ ℂ) 2) ↦ f 0) hc
    simp [e] at hh
  have hvlim : Filter.Tendsto v Filter.atTop (nhds (e 0)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa [v, e, a, norm_smul, lp.norm_single, norm_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))
  have h0 : e 0 ∈ V.topologicalClosure := by
    apply V.isClosed_topologicalClosure.mem_of_tendsto hvlim
    exact Filter.Eventually.of_forall (fun n ↦ V.le_topologicalClosure (Submodule.subset_span ⟨n, rfl⟩))
  have he (n : ℕ) : e n ∈ V.topologicalClosure := by
    cases n with
    | zero => exact h0
    | succ n =>
      have hvn : v n ∈ V.topologicalClosure := V.le_topologicalClosure (Submodule.subset_span ⟨n, rfl⟩)
      have ha : a n ≠ 0 := pow_ne_zero n (by norm_num)
      have hsub : a n • e (n+1) ∈ V.topologicalClosure := by
        simpa [v] using V.topologicalClosure.sub_mem hvn h0
      simpa [ha] using V.topologicalClosure.smul_mem (a n)⁻¹ hsub
  have hspan : (Submodule.span ℂ (range e)).topologicalClosure = ⊤ := by
    let b := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℕ ↦ ℂ) 2))
    have hb : (b : ℕ → _) = e := by
      funext n
      rw [← b.repr_symm_single n]
      rfl
    rw [← hb]
    exact b.dense_span
  have hd : Dense (V : Set (lp (fun _ : ℕ ↦ ℂ) 2)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    apply top_unique
    rw [← hspan]
    apply Submodule.topologicalClosure_minimal _ _ V.isClosed_topologicalClosure
    exact Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact he n)
  exact ⟨V, hd, hn⟩

/-- The quotient by the zero submodule is linearly isometric to the original space. -/
private theorem epsilonBasisLift_of_dense_image_quotientBot (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∃ q : (E ⧸ (⊥ : Submodule ℂ E)) ≃ₗᵢ[ℂ] E,
      ∀ x : E, q ((⊥ : Submodule ℂ E).mkQ x) = x := by
  let e := (⊥ : Submodule ℂ E).quotEquivOfEqBot rfl
  have hn (x : E ⧸ (⊥ : Submodule ℂ E)) : ‖e x‖ = ‖x‖ := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change ‖x‖ = ‖(QuotientAddGroup.mk x : E ⧸ (⊥ : AddSubgroup E))‖
      simp [QuotientAddGroup.norm_mk]
  exact ⟨{ toLinearEquiv := e, norm_map' := hn }, fun _ ↦ rfl⟩

/-- Paper: Remark 10.4.2.7, p. 463. Take complex ℓ², E₀ = 0, and V the
dense subspace of finitely supported sequences. Choose an orthonormal basis
starting with the normalization of (2⁻ʲ)ⱼ. Its first lift would have to equal
that vector by biorthogonality, but the vector has infinite support. -/
theorem Printed.epsilonBasisLift_of_dense_image_false :
    ¬ Printed.epsilonBasisLift_of_dense_image := by
  obtain ⟨V, hV, hmissing⟩ := epsilonBasisLift_of_dense_image_missing
  let H : Type := lp (fun _ : ℕ ↦ ℂ) 2
  let : NormedSpace ℂ H := InnerProductSpace.toNormedSpace
  have : IsClosed ((⊥ : Submodule ℂ H) : Set H) := by
    simp
  obtain ⟨q, hq⟩ := epsilonBasisLift_of_dense_image_quotientBot (E := H)
  let B := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)
  let T := q.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let S := q.toContinuousLinearEquiv.toContinuousLinearMap
  let b : SchauderBasis ℂ (H ⧸ (⊥ : Submodule ℂ H)) :=
    { basis := fun n ↦ q.symm (B n)
      coord := fun n ↦ (B.toSchauderBasis.coord n).comp S
      ortho := by intro i j; simpa [S] using B.toSchauderBasis.ortho i j
      expansion := by
        intro x
        have hh := T.hasSum (B.toSchauderBasis.expansion (q x))
        simpa [T, S] using hh }
  have hb (n : ℕ) : q (b n) = B n := q.apply_symm_apply _
  have hnorm (n : ℕ) : ‖b n‖ = 1 := by
    rw [← q.norm_map, hb]
    exact B.orthonormal.norm_eq_one n
  have hnormalized : IsNormalizedSpectralFamily b.basis :=
    ⟨⟨1, fun n ↦ (hnorm n).le⟩, 1, zero_lt_one, fun n ↦ (hnorm n).ge⟩
  have hdense : Dense ((V.map (⊥ : Submodule ℂ H).mkQ) : Set (H ⧸ (⊥ : Submodule ℂ H))) := by
    change Dense ((⊥ : Submodule ℂ H).mkQ '' (V : Set H))
    exact (Submodule.mkQ_surjective (⊥ : Submodule ℂ H)).denseRange.dense_image
      (Submodule.continuous_mkQ _) hV
  intro h
  obtain ⟨u, r, r', ε, hr, hr', hbounds, hlift, _⟩ :=
    h H ⊥ V b hnormalized bot_le hdense
  have hu := hlift.2.2.1 0
  have heq : u 0 = lp.single 2 0 (1 : ℂ) := by
    have hh := congrArg q hu.2.1
    rw [hq, hb] at hh
    have hB : B 0 = lp.single 2 0 (1 : ℂ) := by rw [← B.repr_symm_single 0]; rfl
    exact hh.trans hB
  exact hmissing (heq ▸ hu.1)

/-- Paper: Remark 10.4.2.7, p. 463. Under the dense-image hypothesis in the
Hilbert case the lift can be chosen with closed span isomorphic to the kernel's
orthogonal complement, and small kernel perturbations preserve this conclusion. -/
def Printed.hilbertEpsilonBasisLift_of_dense_image : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (E₀ V : Submodule ℂ E) [IsClosed (E₀ : Set E)]
    (b : _root_.SchauderBasis ℂ (E ⧸ E₀)), IsNormalizedSpectralFamily b.basis →
    E₀ ≤ (V ⊓ E₀).topologicalClosure → Dense (V.map E₀.mkQ : Set (E ⧸ E₀)) →
    ∃ (u : ℕ → E) (r r' ε : ℝ),
      0 < r ∧ 0 < r' ∧ (∀ m, ‖b m‖ ∈ Icc r r') ∧
      IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε u ∧
      (∃ B : _root_.SchauderBasis ℂ (closedSpan(u)), ∀ m, (B m).val = u m) ∧
      Nonempty (closedSpan(u) ≃L[ℂ] E₀.orthogonal) ∧
      ∃ δ : ℕ → ℝ, (∀ m, 0 < δ m) ∧
        ∀ y : ℕ → E, (∀ m, y m ∈ V ⊓ E₀ ∧ ‖y m‖ < δ m) →
          IsEpsilonBasisLift E₀ V b.basis b.coord r r' ε (fun m ↦ u m + y m) ∧
          ∃! T : closedSpan(u) ≃L[ℂ] closedSpan(fun m ↦ u m + y m),
            ∀ (v : closedSpan(u)) (m : ℕ), v.val = u m → (T v).val = u m + y m

/-- Paper: Remark 10.4.2.7, p. 463. In ℓ² with zero kernel take V to be c₀₀
and start an orthonormal basis with the normalization of (2⁻ʲ)ⱼ. Its first
quotient vector has no representative in V. -/
theorem Printed.hilbertEpsilonBasisLift_of_dense_image_false :
    ¬ Printed.hilbertEpsilonBasisLift_of_dense_image := by
  obtain ⟨V, hV, hmissing⟩ := epsilonBasisLift_of_dense_image_missing
  let H : Type := lp (fun _ : ℕ ↦ ℂ) 2
  let : NormedSpace ℂ H := InnerProductSpace.toNormedSpace
  have : IsClosed ((⊥ : Submodule ℂ H) : Set H) := by
    simp
  obtain ⟨q, hq⟩ := epsilonBasisLift_of_dense_image_quotientBot (E := H)
  let B := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)
  let T := q.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let S := q.toContinuousLinearEquiv.toContinuousLinearMap
  let b : SchauderBasis ℂ (H ⧸ (⊥ : Submodule ℂ H)) :=
    { basis := fun n ↦ q.symm (B n)
      coord := fun n ↦ (B.toSchauderBasis.coord n).comp S
      ortho := by intro i j; simpa [S] using B.toSchauderBasis.ortho i j
      expansion := by
        intro x
        have hh := T.hasSum (B.toSchauderBasis.expansion (q x))
        simpa [T, S] using hh }
  have hb (n : ℕ) : q (b n) = B n := q.apply_symm_apply _
  have hnorm (n : ℕ) : ‖b n‖ = 1 := by
    rw [← q.norm_map, hb]
    exact B.orthonormal.norm_eq_one n
  have hnormalized : IsNormalizedSpectralFamily b.basis :=
    ⟨⟨1, fun n ↦ (hnorm n).le⟩, 1, zero_lt_one, fun n ↦ (hnorm n).ge⟩
  have hdense : Dense ((V.map (⊥ : Submodule ℂ H).mkQ) : Set (H ⧸ (⊥ : Submodule ℂ H))) := by
    change Dense ((⊥ : Submodule ℂ H).mkQ '' (V : Set H))
    exact (Submodule.mkQ_surjective (⊥ : Submodule ℂ H)).denseRange.dense_image
      (Submodule.continuous_mkQ _) hV
  intro h
  obtain ⟨u, r, r', ε, hr, hr', hbounds, hlift, _⟩ :=
    h H ⊥ V b hnormalized bot_le hdense
  have hu := hlift.2.2.1 0
  have heq : u 0 = lp.single 2 0 (1 : ℂ) := by
    have hh := congrArg q hu.2.1
    rw [hq, hb] at hh
    have hB : B 0 = lp.single 2 0 (1 : ℂ) := by rw [← B.repr_symm_single 0]; rfl
    exact hh.trans hB
  exact hmissing (heq ▸ hu.1)

end ApproximateLifts

end RiemannMasullo
