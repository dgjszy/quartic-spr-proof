import SPR.N4.Basic

/-!
# Strict Hurwitz stability supplies the common even root band

The third determinant along translation has no nonnegative real zero and
positive leading coefficient. Two actual vertices then supply the synthesis band.
-/
namespace SPR.N4
open Polynomial
noncomputable section
/-- A monic quartic has its represented coefficient in each of the four slots. -/
theorem poly_coeff (a : Poly4) :
    a.poly.coeff 3 = a.a1 ∧ a.poly.coeff 2 = a.a2 ∧
    a.poly.coeff 1 = a.a3 ∧ a.poly.coeff 0 = a.a4 := by
  simp [Poly4.poly]

/-- The represented polynomial has actual degree four and leading coefficient one. -/
theorem poly_degree (a : Poly4) : a.poly.natDegree = 4 ∧ a.poly.Monic := by
  constructor
  · unfold Poly4.poly
    compute_degree!
  · unfold Poly4.poly
    monicity!

/-- Stability gives positivity of all four actual coefficients. -/
theorem hurwitz_coefficients {a : Poly4} (ha : SPR.IsHurwitz a.poly) :
    0 < a.a1 ∧ 0 < a.a2 ∧ 0 < a.a3 ∧ 0 < a.a4 := by
  rcases poly_coeff a with ⟨h1, h2, h3, h4⟩
  have hdeg := (poly_degree a).1
  have hlc : 0 < a.poly.leadingCoeff := by rw [(poly_degree a).2.leadingCoeff]; norm_num
  constructor
  · simpa [h1] using SPR.Hurwitz.hurwitz_coeff_pos ha hlc 3 (by omega)
  constructor
  · simpa [h2] using SPR.Hurwitz.hurwitz_coeff_pos ha hlc 2 (by omega)
  constructor
  · simpa [h3] using SPR.Hurwitz.hurwitz_coeff_pos ha hlc 1 (by omega)
  · simpa [h4] using SPR.Hurwitz.hurwitz_coeff_pos ha hlc 0 (by omega)

/-- Coefficients after translating the frequency line into the right half-plane. -/
def shifted (a : Poly4) (r : ℝ) : Poly4 :=
  ⟨a.a1 + 4 * r, a.a2 + 3 * a.a1 * r + 6 * r ^ 2,
    a.a3 + 2 * a.a2 * r + 3 * a.a1 * r ^ 2 + 4 * r ^ 3,
    a.a4 + a.a3 * r + a.a2 * r ^ 2 + a.a1 * r ^ 3 + r ^ 4⟩

/-- Evaluation of the quartic on the imaginary axis, with signs made explicit. -/
theorem eval_imaginary (a : Poly4) (w : ℝ) :
    a.poly.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I) =
      (evenPart a (w ^ 2) : ℂ) +
        ((w * (a.a3 - a.a1 * w ^ 2) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Poly4.poly, evenPart, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

/-- Translation is a polynomial identity, so no stability criterion is assumed. -/
theorem eval_shifted (a : Poly4) (r : ℝ) (z : ℂ) :
    (shifted a r).poly.eval₂ (algebraMap ℝ ℂ) z =
      a.poly.eval₂ (algebraMap ℝ ℂ) ((r : ℂ) + z) := by
  simp [Poly4.poly, shifted]
  ring

/-- The third Hurwitz determinant of a tuple. -/
def determinant (a : Poly4) : ℝ := a.a1 * a.a2 * a.a3 - a.a3 ^ 2 - a.a1 ^ 2 * a.a4

/-- The determinant along a nonnegative translation, expanded with leading term 64. -/
def determinantPolynomial (a : Poly4) : ℝ[X] :=
  C (determinant a) +
    C (2 * a.a1 * a.a2 ^ 2 + 2 * a.a1 ^ 2 * a.a3 - 8 * a.a1 * a.a4) * X +
    C (4 * a.a2 ^ 2 + 8 * a.a1 ^ 2 * a.a2 + 4 * a.a1 * a.a3 - 16 * a.a4) * X ^ 2 +
    C (8 * a.a1 ^ 3 + 32 * a.a1 * a.a2) * X ^ 3 +
    C (48 * a.a1 ^ 2 + 32 * a.a2) * X ^ 4 + C (96 * a.a1) * X ^ 5 + C 64 * X ^ 6

/-- Static expansion of the shifted determinant. -/
theorem determinantPolynomial_eval (a : Poly4) (r : ℝ) :
    (determinantPolynomial a).eval r = determinant (shifted a r) := by
  simp [determinantPolynomial, determinant, shifted]
  ring

/-- A zero determinant with positive first and third coefficients forces an imaginary root. -/
theorem determinant_zero_root {a : Poly4} (ha1 : 0 < a.a1) (ha3 : 0 < a.a3)
    (hd : determinant a = 0) :
    a.poly.eval₂ (algebraMap ℝ ℂ)
      ((Real.sqrt (a.a3 / a.a1) : ℂ) * Complex.I) = 0 := by
  have ht : 0 < a.a3 / a.a1 := div_pos ha3 ha1
  have hw : (Real.sqrt (a.a3 / a.a1)) ^ 2 = a.a3 / a.a1 := Real.sq_sqrt ht.le
  have he : evenPart a (a.a3 / a.a1) = 0 := by
    unfold evenPart determinant at *
    field_simp
    nlinarith
  have ho : a.a3 - a.a1 * (a.a3 / a.a1) = 0 := by field_simp; ring
  rw [eval_imaginary, hw, he, ho]
  simp

/-- A Hurwitz quartic has strictly positive third determinant.

The proof excludes nonnegative real roots of the determinant along translation.
Its positive leading coefficient then fixes the sign at zero. This is independent
of any pre-existing quartic synthesis or quartic stability classification.
-/
theorem hurwitz_determinant {a : Poly4} (ha : SPR.IsHurwitz a.poly) :
    0 < determinant a := by
  rcases hurwitz_coefficients ha with ⟨ha1, ha2, ha3, ha4⟩
  have hdeg : (determinantPolynomial a).natDegree = 6 := by
    unfold determinantPolynomial
    compute_degree!
  have hlc : (determinantPolynomial a).leadingCoeff = 64 := by
    rw [← coeff_natDegree, hdeg]
    simp only [determinantPolynomial, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  have hroots : ∀ r, (determinantPolynomial a).IsRoot r → r < 0 := by
    intro r hr
    by_contra hneg
    have hr0 : 0 ≤ r := le_of_not_gt hneg
    have hs1 : 0 < (shifted a r).a1 := by dsimp [shifted]; positivity
    have hs3 : 0 < (shifted a r).a3 := by dsimp [shifted]; positivity
    have hd : determinant (shifted a r) = 0 := by
      rw [← determinantPolynomial_eval]
      exact hr
    have hz := determinant_zero_root hs1 hs3 hd
    rw [eval_shifted] at hz
    have hroot : (a.poly.map (algebraMap ℝ ℂ)).IsRoot
        ((r : ℂ) + (Real.sqrt ((shifted a r).a3 / (shifted a r).a1) : ℂ) * Complex.I) := by
      simpa only [Polynomial.IsRoot, ← eval₂_eq_eval_map] using hz
    have h := ha _ hroot
    simp at h
    linarith
  have h := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (P := determinantPolynomial a) (x := 0) hroots (by rw [hlc]; norm_num)
  simpa [determinantPolynomial] using h

/-- The lower endpoint tuple is an actual member, even when intervals degenerate. -/
theorem lower_contains (K : Box4) : K.Contains K.lower :=
  ⟨le_rfl, K.ordered1, le_rfl, K.ordered2, le_rfl, K.ordered3, le_rfl, K.ordered4⟩

/-- A negative value of the worst even quadratic supplies two positive roots. -/
theorem root_band {A C r : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hr : r ^ 2 - A * r + C < 0) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ A = α + β ∧ C = α * β ∧
      ∀ q : ℝ, q ^ 2 - A * q + C < 0 → α < q ∧ q < β := by
  have hD : 0 < A ^ 2 - 4 * C := by nlinarith [sq_nonneg (2 * r - A)]
  have hs : 0 < Real.sqrt (A ^ 2 - 4 * C) := Real.sqrt_pos.mpr hD
  have hs2 := Real.sq_sqrt hD.le
  let α := (A - Real.sqrt (A ^ 2 - 4 * C)) / 2
  let β := (A + Real.sqrt (A ^ 2 - 4 * C)) / 2
  have hα : 0 < α := by dsimp [α]; nlinarith
  have hαβ : α < β := by dsimp [α, β]; linarith
  have heA : A = α + β := by dsimp [α, β]; ring
  have heC : C = α * β := by dsimp [α, β]; nlinarith
  refine ⟨α, β, hα, hαβ, heA, heC, ?_⟩
  intro q hq
  rw [heA, heC] at hq
  constructor <;> nlinarith

/-- The determinant inequality is the strict even-root test at the odd-part root. -/
theorem determinant_ratio {a : Poly4} (ha1 : 0 < a.a1) (hd : 0 < determinant a) :
    (a.a3 / a.a1) ^ 2 - a.a2 * (a.a3 / a.a1) + a.a4 < 0 := by
  have hid : (a.a3 / a.a1) ^ 2 - a.a2 * (a.a3 / a.a1) + a.a4 =
      -determinant a / a.a1 ^ 2 := by
    unfold determinant
    field_simp
    ring
  rw [hid]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hd) (sq_pos_of_pos ha1)

/-- Two actual vertices place all possible odd-part roots in the same even root band. -/
theorem stable_box_band {K : Box4} (hK : K.RobustlyHurwitz) :
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ K.lower.a2 = α + β ∧ K.upper.a4 = α * β ∧
      K.upper.a1 * α < K.lower.a3 ∧ K.upper.a3 < K.lower.a1 * β ∧
      0 < K.lower.a1 ∧ 0 < K.lower.a4 ∧ 0 < K.upper.a2 := by
  rcases hurwitz_coefficients (hK _ (lower_contains K)) with ⟨hl1, hl2, hl3, hl4⟩
  have hu1 : 0 < K.upper.a1 := hl1.trans_le K.ordered1
  have hu2 : 0 < K.upper.a2 := hl2.trans_le K.ordered2
  have hu4 : 0 < K.upper.a4 := hl4.trans_le K.ordered4
  let aL : Poly4 := ⟨K.upper.a1, K.lower.a2, K.lower.a3, K.upper.a4⟩
  let aR : Poly4 := ⟨K.lower.a1, K.lower.a2, K.upper.a3, K.upper.a4⟩
  have hL : K.Contains aL :=
    ⟨K.ordered1, le_rfl, le_rfl, K.ordered2, le_rfl, K.ordered3, K.ordered4, le_rfl⟩
  have hR : K.Contains aR :=
    ⟨le_rfl, K.ordered1, le_rfl, K.ordered2, K.ordered3, le_rfl, K.ordered4, le_rfl⟩
  have hrL := determinant_ratio (a := aL) hu1 (hurwitz_determinant (hK _ hL))
  have hrR := determinant_ratio (a := aR) hl1 (hurwitz_determinant (hK _ hR))
  obtain ⟨α, β, hα, hab, hA, hC, hband⟩ := root_band hl2 hu4 hrL
  have hleft := (hband _ hrL).1
  have hright := (hband _ hrR).2
  have hlo : K.upper.a1 * α < K.lower.a3 := by
    have h := (lt_div_iff₀ hu1).mp hleft
    simpa [aL, mul_comm] using h
  have hhi : K.upper.a3 < K.lower.a1 * β := by
    have h := (div_lt_iff₀ hl1).mp hright
    simpa [aR, mul_comm] using h
  exact ⟨α, β, hα, hab, hA, hC, hlo, hhi, hl1, hl4, hu2⟩


end
end SPR.N4
