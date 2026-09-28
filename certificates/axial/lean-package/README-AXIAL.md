# 轴代数 Lean 交付包（任务 13）

这是完整冻结 v2 的 A、B、C、P 与总推论包。验收结论以 `receipt.json` 为准；本目录不含既有论文的整棵发布树。

## 内容

- `Research/AxialMSZ/Challenge.lean`：冻结 v2 原件，SHA-256 `0d88e7321e0f0931f953ea250f2c5dc1d6d5773cd8f78e3080e0d6eeceb13ee1`，逐字保持。
- `SupplementDChallenge.lean`：独立审查并于 2026-09-27T23:55:54Z 冻结的两条 D 补充陈述，SHA-256 `afd751c0df8ba036995314a0efd7a5b60d6b333ab9958111a879724d81fc9175`。
- `ChallengeTests.lean`：冻结的已知答案与反例测试，亦保持原件。
- `Proof/`：20 个证明模块。与工作区已验收源相比，只更改显式 import 路径；逆向替换后逐字相等，记录在 `package-manifest.json`。
- `Check.lean`：17 个完整具名出口，含 10 个原冻结目标（包括别名）、4 个从 S 独立导出的全称命题否定、P 的直接存在结论与 2 个 D 补充目标。
- `Audit.lean`：打印关键定义、全部冻结目标及 Check 类型，供论文陈述比对。
- `verify-package.py`、`verification/`、`receipt.json`：复现程序、运行证据和机器收据。

| 冻结目标 | 完整 Check 出口（前缀 `AxialMSZ.Check.`） |
|---|---|
| `Laws_facts` | `check_Laws_facts` |
| `ExS.Statement`、`TheoremA` | `check_ExS_Statement`、`check_TheoremA` |
| `ExE.Statement`、`TheoremB` | `check_ExE_Statement`、`check_TheoremB` |
| `ExD.Statement`、`TheoremC` | `check_ExD_Statement`、`check_TheoremC` |
| `ExP.Statement`、`RemarkP` | `check_ExP_Statement`、`check_RemarkP` |
| `Corollary` | `check_Corollary` |
| `¬ MS_Conjecture_3_16` | `check_not_MS_Conjecture_3_16` |
| `¬ FinestSumDecomposition_connected` | `check_not_FinestSumDecomposition_connected` |
| `¬ Indecomposable_connected` | `check_not_Indecomposable_connected` |
| `¬ Simple_connected` | `check_not_Simple_connected` |
| `Dominance_nonsymmetric` | `check_Dominance_nonsymmetric` |
| 补充 `ExD_axes_in_block` | `check_ExD_axes_in_block` |
| 补充 `ExD_block_not_axial_on_contained_axes` | `check_ExD_block_not_axial_on_contained_axes` |

`Proof/SFourNegations.lean` 的四项只使用已证 TheoremA、Laws_facts，以及证明了的“非零单代数不可分解”引理。其 import 链不依赖 E、D 或完整总推论。

## 复现及复制

工具链为 Lean 4.34.1 / Mathlib v4.34.1，Mathlib 固定提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。`verify-package.py --help` 给出参数；程序需要唯一 Lean 窗口和项目的 `codex-task13-root` A 锁。所有时刻通过 `date -u` 取得。

程序从空目录开始，复用已固定的 Mathlib/工具链缓存，重新构建本包全部 25 个模块。每个模块先检查所有依赖已就绪，再单独 `lake --wfail build`，随后运行 `lake env leanchecker`。不调用总入口 `Research.lean`，不重编 CirculantQ3。源码禁词扫描、17 个 Check 的公理审计及冻结哈希必须全部通过。

Claude 复制 `Research/AxialMSZ/` 到发布树 `lean/Research/AxialMSZ/`，按清单核对每个源文件 SHA，再把 `import Research.AxialMSZ.Check` 加到总入口，并完成既有发布模块与本包一起的整树重放。可把本包其余文件放在发布树的验证证据目录。现有发布文件总数应现场清点，不使用任务单的历史估计数。

## 验证与研究范围

- `leanchecker` 使用 Lean 自身内核；本收据不宣称已用独立内核、comparator 或全部 Mathlib 依赖从源码重建。
- 本包验证冻结 v2 的数学内容，不等于新论文全部文字已通过审稿；D 的两项补充已经单独冻结并纳入；旧候选 `SupplementChallenge` 的其余四项未纳入。
- 四个否定反驳允许任意有限对称融合律的**一般全称命题**；不声称每种固定融合律都有反例，不解决 Monster、Seress 或 Majorana 限制版本。GS 3.12 只涉及其一般融合律类比。
- B/P 中非对称支配的先前工作归 KMP、Peng；这里不主张该现象的新颖性。新颖性检索另见 Claude 的 G3 报告。
- 冻结陈述仅经 AI 审查；本地 Lean 验收不构成人类专家审阅或对外发布批准。
