import SPR.N4.Synthesis

/-!
# 四阶独立区间族的鲁棒严格正实综合

本文件保留公开主定理的实际声明与最终组装。
精确命题定义位于 `SPR.N4.Basic`；完整构造位于 `SPR.N4.Synthesis`。
-/

namespace SPR.N4.Direct

/-- Every strictly Hurwitz real monic quartic independent closed interval box,
including degenerate intervals, admits one monic exact-degree-four numerator
strictly positive real for every member at every real frequency. -/
theorem robustSPR : SPR.N4.RobustSPRStatement := SPR.N4.synthesis

end SPR.N4.Direct
