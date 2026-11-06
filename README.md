# 四阶区间族的鲁棒严格正实综合（Lean 4）

这是四阶区间多项式族 SPR 综合定理的独立 Lean 工程，包含完整证明、必要公共工具、
原命题类型核验及传递公理审计。数学源码共 5 个模块；连同入口和核验代码共 9 个 Lean 文件。

## 定理内容

考虑首一四阶分母

$$
a(s)=s^4+a_1s^3+a_2s^2+a_3s+a_4,
\qquad a_i\in[\ell_i,u_i]\subset\mathbb R.
$$

四个系数区间彼此独立，均为有限闭区间，允许任意退化区间。
假设箱内**每一个分母都是严格 Hurwitz 的**，即所有复根的实部均小于零。
本工程证明：存在**同一个**实系数首一多项式 $b$，实际次数恰为四，使得

$$
\operatorname{Re}\frac{b(i\omega)}{a(i\omega)}>0
\qquad\text{对所有箱内分母 }a\text{ 和所有 }\omega\in\mathbb R.
$$

结论包含零频率和所有非零频率。根带、系数正性及构造余量均从全箱 Hurwitz 前提推出，
不作为额外证书假设输入。这里证明的是四阶独立区间族的结论。

## 版本和构建

- Lean：`leanprover/lean4:v4.30.0`。
- mathlib：`v4.30.0`，精确提交和传递依赖由 `lake-manifest.json` 锁定。
- 正式证明与验收只依赖 Lean / Lake，不需要 Python、外部求解器或运行时生成源码。

安装 [elan](https://github.com/leanprover/elan) 后，进入仓库根目录执行：

```sh
lake exe cache get
lake build
```

首次运行需要联网获取工具链、锁定依赖和 mathlib 编译缓存。
请保留锁文件，无需执行 `lake update`。
默认构建包含数学证明、`Audit.lean` 和 `Verify.lean`。也可以单独显示核验结果：

```sh
lake env lean Lean/Verify.lean
lake env lean Lean/Audit.lean
```

## 主定理与调用示例

公开定理位于 `Lean/Main.lean`：

```lean
theorem SPR.N4.Direct.robustSPR : SPR.N4.RobustSPRStatement
```

在本工程内使用：

```lean
import SPR

example (K : SPR.N4.Box4) (hK : K.RobustlyHurwitz) :
    ∃ b : Polynomial ℝ, b.Monic ∧ b.natDegree = 4 ∧
      ∀ a : SPR.N4.Poly4, K.Contains a → SPR.N4.FrequencySPR a.poly b :=
  SPR.N4.Direct.robustSPR K hK
```

`Box4`、`RobustlyHurwitz`、`FrequencySPR` 和 `RobustSPRStatement` 的定义位于
`Lean/SPR/N4/Basic.lean`。`Lean/Verify.lean` 展开全箱稳定性、同一个分子及全实频率
量词，检查公开定理与这个完整陈述的类型匹配。

## 文件结构和阅读顺序

```text
Lean/
├── Main.lean                  # 公开主定理和最终组装
├── SPR.lean                   # 公共导入入口
├── Audit.lean                 # 全部导入 SPR 定理的传递公理审计
├── Verify.lean                # 完整原命题的展开类型核验
└── SPR/
    ├── Common/Hurwitz.lean     # 不依赖固定阶数的稳定性工具
    └── N4/
        ├── Basic.lean         # 四阶分母、独立区间箱和精确结论
        ├── Hurwitz.lean       # 系数正性、Hurwitz 不等式和共同根带
        ├── Construction.lean  # 显式参数、两段平方下界和严格提升
        └── Synthesis.lean     # 复数商桥接与全箱综合
```

建议先读 `Main.lean` 和 `Basic.lean`，再依次阅读 `Hurwitz.lean`、
`Construction.lean`、`Synthesis.lean`。

## 构造思路

由两个实际箱顶点的稳定性得到共同正根带，构造三次候选
$s^3+xs^2+ys$，再证明其频率残余在全箱、全半轴上具有统一正余量。
取足够小的同一个正参数 $\varepsilon$，加入 $\varepsilon(s^4+1)$，
同时处理零频严格性和实际四次分子要求，最后首一化：

$$
b(s)=s^4+\varepsilon^{-1}s^3+(x/\varepsilon)s^2+(y/\varepsilon)s+1.
$$

整个构造及其对原频域命题的桥接均由静态 Lean 证明完成。
代码中的 `noncomputable` 使用实数的经典存在性构造；本仓库提供的是内核可检查的存在性证明。

## 证明可信范围

`Audit.lean` 检查全部导入的 SPR 定理及其传递公理，只允许：

```text
propext
Classical.choice
Quot.sound
```

发现其他公理时审计报错。工程不使用 `sorry`、`admit`、自定义数学公理或 `native_decide`。
本仓库仅保留四阶证明所需源码与核验入口；依赖和编译产物由 Lake 在本地获取。
本次独立验证结果见 [VERIFICATION.md](VERIFICATION.md)。
