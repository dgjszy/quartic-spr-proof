import SPR.Common.Hurwitz

/-!
# Quartic independent coefficient boxes

Definitions of the original closed box, strict root stability, complex-frequency
SPR condition, and the explicit candidate parameters.
-/
namespace SPR.N4
open Polynomial
noncomputable section

/-- A real monic quartic, in descending coefficient order. -/
structure Poly4 where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ

/-- The polynomial represented by a coefficient tuple. -/
def Poly4.poly (a : Poly4) : ℝ[X] :=
  X ^ 4 + C a.a1 * X ^ 3 + C a.a2 * X ^ 2 + C a.a3 * X + C a.a4

/-- A closed independent coefficient box; widths may vanish. -/
structure Box4 where
  lower : Poly4
  upper : Poly4
  ordered1 : lower.a1 ≤ upper.a1
  ordered2 : lower.a2 ≤ upper.a2
  ordered3 : lower.a3 ≤ upper.a3
  ordered4 : lower.a4 ≤ upper.a4

/-- Membership keeps all four coefficients independently in their intervals. -/
def Box4.Contains (K : Box4) (a : Poly4) : Prop :=
  K.lower.a1 ≤ a.a1 ∧ a.a1 ≤ K.upper.a1 ∧
  K.lower.a2 ≤ a.a2 ∧ a.a2 ≤ K.upper.a2 ∧
  K.lower.a3 ≤ a.a3 ∧ a.a3 ≤ K.upper.a3 ∧
  K.lower.a4 ≤ a.a4 ∧ a.a4 ≤ K.upper.a4

/-- Strict Hurwitz stability of every actual member. -/
def Box4.RobustlyHurwitz (K : Box4) : Prop :=
  ∀ a, K.Contains a → SPR.IsHurwitz a.poly

/-- The even part at squared frequency. -/
def evenPart (a : Poly4) (t : ℝ) : ℝ := t ^ 2 - a.a2 * t + a.a4

/-- The cubic candidate pairing divided by squared frequency. -/
def residual (a : Poly4) (x y t : ℝ) : ℝ :=
  a.a1 * (t - y) * t + a.a3 * (y - t) - x * evenPart a t

/-- Harmonic weight used for the fixed cubic candidate. -/
def weight (l u : ℝ) : ℝ := l * u / (l + u)

/-- The common odd-part root of the cubic candidate. -/
def middle (l u α β : ℝ) : ℝ := (u * α + l * β) / (l + u)

/-- The explicit positive margin used for the same cubic across the whole box. -/
def margin (K : Box4) (x y α β : ℝ) : ℝ :=
  min (min ((K.lower.a3 - K.upper.a1 * α) * (y - α) / 2)
    ((K.upper.a1 - x) * (y - α) ^ 2 / 4))
    (min ((K.lower.a1 * β - K.upper.a3) * (β - y) / 2)
      ((K.lower.a1 - x) * (β - y) ^ 2 / 4))

/-- Imaginary-axis strict positivity in the original complex quotient. -/
def FrequencySPR (a b : ℝ[X]) : Prop :=
  ∀ w : ℝ, 0 < ((b.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I)) /
    (a.eval₂ (algebraMap ℝ ℂ) ((w : ℂ) * Complex.I))).re

/-- The fixed, normalized, exact-degree-four candidate. -/
def candidate (x y ε : ℝ) : Poly4 := ⟨1 / ε, x / ε, y / ε, 1⟩

/-- The original quartic interval synthesis statement, with a monic witness. -/
def RobustSPRStatement : Prop :=
  ∀ K : Box4, K.RobustlyHurwitz →
    ∃ b : ℝ[X], b.Monic ∧ b.natDegree = 4 ∧
      ∀ a : Poly4, K.Contains a → FrequencySPR a.poly b


end
end SPR.N4
