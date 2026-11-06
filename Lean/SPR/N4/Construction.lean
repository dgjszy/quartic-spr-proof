import SPR.N4.Basic

/-!
# Uniform real-frequency quartic synthesis

Two worst-corner square identities give a uniform positive residual.
One explicit perturbation restores zero frequency and exact degree four.
-/
namespace SPR.N4
open Polynomial
noncomputable section
/-- Positive weights place the candidate root strictly inside the even root band. -/
theorem weights {l u α β : ℝ} (hl : 0 < l) (hu : 0 < u) (hab : α < β) :
    0 < weight l u ∧ weight l u < l ∧ weight l u < u ∧
    α < middle l u α β ∧ middle l u α β < β ∧
    u * middle l u α β - weight l u * β = (u - weight l u) * α ∧
    l * middle l u α β - weight l u * α = (l - weight l u) * β := by
  have hs : 0 < l + u := add_pos hl hu
  have hx : 0 < weight l u := div_pos (mul_pos hl hu) hs
  have hxl : weight l u < l := by
    unfold weight
    apply (div_lt_iff₀ hs).mpr
    nlinarith [sq_pos_of_pos hl]
  have hxu : weight l u < u := by
    unfold weight
    apply (div_lt_iff₀ hs).mpr
    nlinarith [sq_pos_of_pos hu]
  have hya : α < middle l u α β := by
    unfold middle
    apply (lt_div_iff₀ hs).mpr
    nlinarith [mul_pos hl (sub_pos.mpr hab)]
  have hyb : middle l u α β < β := by
    unfold middle
    apply (div_lt_iff₀ hs).mpr
    nlinarith [mul_pos hu (sub_pos.mpr hab)]
  refine ⟨hx, hxl, hxu, hya, hyb, ?_, ?_⟩ <;>
    unfold middle weight <;> field_simp <;> ring

/-- Below the candidate root, the upper first and lower third coefficients are worst. -/
theorem residual_lower_left {K : Box4} {a : Poly4} (ha : K.Contains a)
    {x y α β t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (hty : t ≤ y)
    (hA : K.lower.a2 = α + β) (hC : K.upper.a4 = α * β)
    (hidentity : K.upper.a1 * y - x * β = (K.upper.a1 - x) * α) :
    (K.upper.a1 - x) * (t - α) ^ 2 +
      (K.lower.a3 - K.upper.a1 * α) * (y - t) ≤ residual a x y t := by
  rcases ha with ⟨ha1l, ha1u, ha2l, ha2u, ha3l, ha3u, ha4l, ha4u⟩
  have h1 := mul_nonneg (sub_nonneg.mpr ha1u)
    (mul_nonneg (sub_nonneg.mpr hty) ht)
  have h3 := mul_nonneg (sub_nonneg.mpr ha3l) (sub_nonneg.mpr hty)
  have h2 := mul_nonneg hx (mul_nonneg (sub_nonneg.mpr ha2l) ht)
  have h4 := mul_nonneg hx (sub_nonneg.mpr ha4u)
  have hid := congrArg (fun z : ℝ => z * (t - α)) hidentity
  unfold residual evenPart
  rw [hA] at h2
  rw [hC] at h4
  nlinarith

/-- Above the candidate root, the lower first and upper third coefficients are worst. -/
theorem residual_lower_right {K : Box4} {a : Poly4} (ha : K.Contains a)
    {x y α β t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) (hyt : y ≤ t)
    (hA : K.lower.a2 = α + β) (hC : K.upper.a4 = α * β)
    (hidentity : K.lower.a1 * y - x * α = (K.lower.a1 - x) * β) :
    (K.lower.a1 - x) * (t - β) ^ 2 +
      (K.lower.a1 * β - K.upper.a3) * (t - y) ≤ residual a x y t := by
  rcases ha with ⟨ha1l, ha1u, ha2l, ha2u, ha3l, ha3u, ha4l, ha4u⟩
  have h1 := mul_nonneg (sub_nonneg.mpr ha1l)
    (mul_nonneg (sub_nonneg.mpr hyt) ht)
  have h3 := mul_nonneg (sub_nonneg.mpr ha3u) (sub_nonneg.mpr hyt)
  have h2 := mul_nonneg hx (mul_nonneg (sub_nonneg.mpr ha2l) ht)
  have h4 := mul_nonneg hx (sub_nonneg.mpr ha4u)
  have hid := congrArg (fun z : ℝ => z * (t - β)) hidentity
  unfold residual evenPart
  rw [hA] at h2
  rw [hC] at h4
  nlinarith

/-- A square plus a strictly positive one-sided slack has an explicit uniform margin. -/
theorem left_margin {c δ α y t : ℝ} (hc : 0 < c) (hd : 0 < δ)
    (hay : α < y) (ht : t ≤ y) :
    min (δ * (y - α) / 2) (c * (y - α) ^ 2 / 4) ≤
      c * (t - α) ^ 2 + δ * (y - t) := by
  have hs := mul_nonneg hc.le (sq_nonneg (t - α))
  have hr := mul_nonneg hd.le (sub_nonneg.mpr ht)
  by_cases ht' : t ≤ (α + y) / 2
  · have h := min_le_left (δ * (y - α) / 2) (c * (y - α) ^ 2 / 4)
    nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ y - t - (y - α) / 2)]
  · have h := min_le_right (δ * (y - α) / 2) (c * (y - α) ^ 2 / 4)
    have hh : (y - α) ^ 2 / 4 ≤ (t - α) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh hc.le
    nlinarith

/-- The upper half of the root band has the symmetric explicit margin. -/
theorem right_margin {c δ β y t : ℝ} (hc : 0 < c) (hd : 0 < δ)
    (hyb : y < β) (ht : y ≤ t) :
    min (δ * (β - y) / 2) (c * (β - y) ^ 2 / 4) ≤
      c * (t - β) ^ 2 + δ * (t - y) := by
  have hs := mul_nonneg hc.le (sq_nonneg (t - β))
  have hr := mul_nonneg hd.le (sub_nonneg.mpr ht)
  by_cases ht' : (β + y) / 2 ≤ t
  · have h := min_le_left (δ * (β - y) / 2) (c * (β - y) ^ 2 / 4)
    nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ t - y - (β - y) / 2)]
  · have h := min_le_right (δ * (β - y) / 2) (c * (β - y) ^ 2 / 4)
    have hh : (β - y) ^ 2 / 4 ≤ (t - β) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh hc.le
    nlinarith

/-- Both endpoint slacks imply a uniform lower bound at every squared frequency. -/
theorem uniform_margin {K : Box4} {α β : ℝ}
    (hl : 0 < K.lower.a1) (hab : α < β)
    (hA : K.lower.a2 = α + β) (hC : K.upper.a4 = α * β)
    (hlo : K.upper.a1 * α < K.lower.a3)
    (hhi : K.upper.a3 < K.lower.a1 * β) :
    let x := weight K.lower.a1 K.upper.a1
    let y := middle K.lower.a1 K.upper.a1 α β
    0 < margin K x y α β ∧
    ∀ a, K.Contains a → ∀ t, 0 ≤ t → margin K x y α β ≤ residual a x y t := by
  dsimp only
  have hu : 0 < K.upper.a1 := hl.trans_le K.ordered1
  rcases weights hl hu hab with ⟨hx, hxl, hxu, hya, hyb, hidl, hidr⟩
  constructor
  · unfold margin
    apply lt_min <;> apply lt_min <;> positivity
  · intro a ha t ht
    by_cases hty : t ≤ middle K.lower.a1 K.upper.a1 α β
    · exact (min_le_left _ _).trans
        ((left_margin (by linarith) (by linarith) hya hty).trans
          (residual_lower_left ha hx.le ht hty hA hC hidl))
    · have hyt : middle K.lower.a1 K.upper.a1 α β ≤ t := le_of_lt (lt_of_not_ge hty)
      exact (min_le_right _ _).trans
        ((right_margin (by linarith) (by linarith) hyb hyt).trans
          (residual_lower_right ha hx.le ht hyt hA hC hidr))

/-- Real pairing after adding the constant and highest-degree perturbation. -/
def correctedPairing (a : Poly4) (x y ε t : ℝ) : ℝ :=
  t * residual a x y t + ε * (t ^ 2 + 1) * evenPart a t

/-- A single explicit small perturbation restores zero frequency and exact degree four. -/
theorem correction_positive {a : Poly4} {x y m U ε t : ℝ}
    (hm : 0 < m) (hU : 0 < U) (hε : 0 < ε)
    (hsmall : ε * (U * (U ^ 2 + 1)) ≤ m / 2)
    (ha2 : a.a2 ≤ U) (ha4 : 0 < a.a4) (ht : 0 ≤ t)
    (hF : m ≤ residual a x y t) : 0 < correctedPairing a x y ε t := by
  by_cases ht0 : t = 0
  · subst t
    simp only [correctedPairing, evenPart, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_mul, sub_zero, zero_add, mul_one]
    exact mul_pos hε ha4
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have htm : m * t ≤ t * residual a x y t := by nlinarith
  by_cases hE : 0 ≤ evenPart a t
  · unfold correctedPairing
    have hcorr := mul_nonneg (mul_nonneg hε.le (by positivity : 0 ≤ t ^ 2 + 1)) hE
    nlinarith [mul_pos hm htp]
  · have hEn : evenPart a t < 0 := lt_of_not_ge hE
    have htU : t < U := by
      unfold evenPart at hEn
      nlinarith [mul_le_mul_of_nonneg_right ha2 ht]
    have hEb : -U * t ≤ evenPart a t := by
      unfold evenPart
      nlinarith [mul_le_mul_of_nonneg_right ha2 ht, sq_nonneg t]
    have hsq : t ^ 2 + 1 ≤ U ^ 2 + 1 := by nlinarith
    have hfirst := mul_le_mul_of_nonneg_left hEb (by positivity : 0 ≤ t ^ 2 + 1)
    have hsecond := mul_le_mul_of_nonpos_right hsq (by nlinarith : -U * t ≤ 0)
    have hbound : -(U * (U ^ 2 + 1)) * t ≤ (t ^ 2 + 1) * evenPart a t := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hbound hε.le
    have hbudget := mul_le_mul_of_nonneg_right hsmall ht
    unfold correctedPairing
    nlinarith [mul_pos hm htp]


end
end SPR.N4
