import SPR.N4.Construction
import SPR.N4.Hurwitz

/-!
# Complete quartic interval SPR synthesis

The explicit real pairing is identified with the complex quotient.
The synthesis theorem covers the original full box and every real frequency.
-/
namespace SPR.N4
open Polynomial
noncomputable section
/-- The complex real pairing is exactly the constructed real residual. -/
theorem candidate_pairing (a : Poly4) (x y ε w : ℝ) (hε : ε ≠ 0) :
    ε * (((candidate x y ε).poly.eval₂ (algebraMap ℝ ℂ)
        ((w : ℂ) * Complex.I)).re *
        (a.poly.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I)).re +
      ((candidate x y ε).poly.eval₂ (algebraMap ℝ ℂ)
        ((w : ℂ) * Complex.I)).im *
        (a.poly.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I)).im) =
      correctedPairing a x y ε (w ^ 2) := by
  rw [eval_imaginary, eval_imaginary]
  simp [candidate, evenPart, correctedPairing, residual, pow_succ,
    Complex.mul_re, Complex.mul_im]
  field_simp [hε]
  ring

/-- Positive real pairing implies positivity of the complex quotient. -/
theorem quotient_positive {a : Poly4} {x y ε : ℝ} (hε : 0 < ε)
    (hQ : ∀ t : ℝ, 0 ≤ t → 0 < correctedPairing a x y ε t) :
    FrequencySPR a.poly (candidate x y ε).poly := by
  intro w
  let A := a.poly.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I)
  let B := (candidate x y ε).poly.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I)
  have hpair : 0 < B.re * A.re + B.im * A.im := by
    have h := hQ (w ^ 2) (sq_nonneg w)
    rw [← candidate_pairing a x y ε w (ne_of_gt hε)] at h
    exact (mul_pos_iff_of_pos_left hε).mp h
  have hA : A ≠ 0 := by
    intro hz
    simp [hz] at hpair
  have hn : 0 < Complex.normSq A := Complex.normSq_pos.mpr hA
  change 0 < (B / A).re
  rw [Complex.div_re, ← add_div]
  exact div_pos hpair hn

/-- Every strictly Hurwitz quartic independent interval box has a single monic
exact-degree-four numerator whose quotient is strictly positive at every real frequency. -/
theorem synthesis (K : Box4) (hK : K.RobustlyHurwitz) :
    ∃ b : ℝ[X], b.Monic ∧ b.natDegree = 4 ∧
      ∀ a : Poly4, K.Contains a → FrequencySPR a.poly b := by
  obtain ⟨α, β, hα, hab, hA, hC, hlo, hhi, hl1, hl4, hU⟩ := stable_box_band hK
  let x := weight K.lower.a1 K.upper.a1
  let y := middle K.lower.a1 K.upper.a1 α β
  let m := margin K x y α β
  obtain ⟨hm, hF⟩ := uniform_margin hl1 hab hA hC hlo hhi
  let U := K.upper.a2
  let ε := m / (2 * U * (U ^ 2 + 1))
  have hden : 0 < 2 * U * (U ^ 2 + 1) := by positivity
  have hε : 0 < ε := div_pos hm hden
  have hsmall : ε * (U * (U ^ 2 + 1)) ≤ m / 2 := by
    dsimp [ε]
    have hh := div_mul_cancel₀ m (ne_of_gt hden)
    nlinarith [hh]
  refine ⟨(candidate x y ε).poly, (poly_degree _).2, (poly_degree _).1, ?_⟩
  intro a ha
  apply quotient_positive hε
  intro t ht
  have ha2 : a.a2 ≤ U := ha.2.2.2.1
  have ha4 : 0 < a.a4 := hl4.trans_le ha.2.2.2.2.2.2.1
  exact correction_positive hm hU hε hsmall ha2 ha4 ht (hF a ha t ht)

end
end SPR.N4
