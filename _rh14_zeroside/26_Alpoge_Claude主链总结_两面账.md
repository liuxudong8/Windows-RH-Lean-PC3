# Alpöge–Claude 库主链总结：源码面与机器面的两面账

本文是 08 号《主链逐层解剖》的继任版。08 逐层切开了源码，回答“它靠什么站住”；本文把它压成一张账，回答“它站到什么程度”。差别只在一处：08 只读了源码，本文把 17–20 号与 23 号的机器实测并进来，于是同一条链有了两个不同的完成度。

## §0 一句话结论

**源码面：16 层无缝，1/2 写死在定义体里，承重只有 `ch_core` 与 `proposition_size_bound` 两处，全链数学天花板是 1944 年。机器面：`Main.lean` 的闭包 175 191 个文件、1.03 GB 源码，全库只有 175 个 olean（0.0999%），顶层从未编译成功；245 个缺产物文件的实编是 189 通过、56 失败。**

两面账不矛盾，它们量的是两件事：一边是“写出来的东西读起来对不对”，一边是“写出来的东西跑不跑得起来”。

## §1 两面账总表

| 项目 | 源码面（读） | 机器面（编） |
| --- | --- | --- |
| 闭包规模 | 175 191 个库内文件 | 1 030 531 854 B 源码；olean 175 个 |
| 覆盖率 | 全链 16 层逐层有证明体 | \(175/175\,191 \approx 0.0999\%\) |
| 顶层 | `Main.lean` 有 `riemannHypothesis` | 无 `Main.olean`，从未编出 |
| 空洞 | 静态扫 0 处 `sorry`；`: Prop := True` 9 处；`:= trivial` 1 处 | 编译回执无法确认空洞与否 |
| 局部实编 | — | 245 文件：189 通过（77.1%）、56 失败 |
| 失败结构 | — | 3 个根错、53 个级联、放大 1 : 54 |
| `RowSrc` 子树 | 66 168 文件、197 层依赖 | 第一层抽 200 个试编即 5 处硬错，阻断 1 313 文件 |

五处硬错全部落在 elaboration 层（实例合成、隐式参数推断、`rewrite` 失配、心跳超时），没有一处是“命题为假”。这个指纹比任何数值都说明问题：**代码是写出来的，不是跑出来的。**

## §2 主链压成五段

16 层不必逐层读，压成五段就够。

| 段 | 层 | 主张 | 源码证据 | 机器状态 |
| --- | --- | --- | --- | --- |
| S1 | L1–L4 | 顶层目标化为 GRH-L | `rh_of_every` 三行取 \(\chi=1\) | 上游未编 |
| S2 | L5–L9 | 七槽总装输出 `ZeroFreeAll` | `TopPlug` + `EveryCharacterOfLiteratureOfVWin` | 上游未编 |
| S3 | L10–L14 | 窗口不等式转增长控制 | `la` 是窗口宽度；\(\theta \to 1/2+\delta\) | 上游未编 |
| S4 | L15 | 三段组装 | `ch_core` 约 100 行 | 闭包含 66 168 文件子树，未编 |
| S5 | L16 | 纯算术 | `proposition_size_bound` 86 行 | 未编 |

S1 到 S3 是接口搬运：`EveryCharacter` 就是 GRH-L 的逐字陈述，`ZeroFreeAll` 展开后是

\[
\forall \psi\, \forall s,\quad \tfrac{1}{2} < \operatorname{Re} s \;\Rightarrow\; L(\psi.\chi, s) \neq 0
\]

`1/2` 不在参数里，在 `ZeroFreeOn` 的定义体里。这一点是干净的：任何输出 `ZeroFreeAll` 的定理，都必须已经拿到 \(\operatorname{Re} s > 1/2\) 的零自由，取极限绕不过类型检查。S3 的 \(\theta \to 1/2+\delta\) 技巧也合法——对每个 \(\delta>0\) 有 `ZeroFreeAbove(1/2+δ)`，就顶住了 `ZeroFreeAbove(1/2)`，不需要 \(\theta\) 恰等于 \(1/2\)。

## §3 承重三件

### 3.1 `ch_core`：一百行，一个移项

`ChCore.lean:343-351` 是签名，`:352-442` 是证明。真正承重的四行：

```lean
:426  set G : ℝ := GmA D ell Kp c x - SigA D ell A0 Kp x
:440  have hc' := CharacterBalanceMoves.core ... hTop hY
:441  have hz := proposition_size_bound _ _ _ _ _ _ _ _ _ _ _ G hW hc'
:442  linarith
```

`:426` 的 `G := GmA − SigA` 说明结论里的 `+ SigA` 不是未消误差，是移项搬出来的。`:367-370` 现场构造 `SizeWindows`，用的是 `hSize`（即 `RestSize`）、`hm` 与 `hxm` 三个输入。其余部分是 `Real.log_le_rpow_div`、`mul_le_mul_of_nonneg_left`、`linarith` 这类初等估计。

### 3.2 `proposition_size_bound`：86 行恒真算术

`LipschitzWeightAndMinimum.lean:507` 起。`hW` 拆出 16 个分量，恰好是 `SizeWindows` 的 16 个合取项，一个不多一个不少。唯一的 \(1/2\) 入口在 `:522-526`：

```lean
have hxX : x ≤ x ^ ((1 : ℝ) / 2 + ε) * m
```

只用了 `hm1 : x^(1/2-ε) ≤ m`；`hm2` 在这条证明里没有出现。其余是 `ring` 与 `linarith` 的尺寸搬运，收在

\[
G_x \;\le\; 4\,x^{1/2+\varepsilon} \;+\; 22\,P\,Y\,x^{\varepsilon}
\]

主项的常数 4 来自 `one_char` 那一侧（`:419`），不是这 86 行内部长出来的。**这 86 行本身没有一处引用零点事实。**

### 3.3 `core_gm` 与 Landau 转换

`CoreGm.lean:12` 的结论是

\[
\Lambda.G_m(x) \;\le\; x^{\,1/2+(e_D+e_L+7)\varepsilon},\qquad \varepsilon>0 \text{ 任意}
\]

前提只有 `EAtH` 与 `CoreAtH` 两个 Host 条件。把它换成 RH 形态的是 `ChebyshevGrowthImpliesZeroFree`：

\[
\Big(\forall y \ge y_0,\; \Lambda.G_m(y) \le y^{\theta}\Big) \;\Longrightarrow\; \Lambda.\text{ZeroFreeAbove}(\theta)
\]

这是 Landau 型显式公式的合法步骤，对 \(\theta \in (0,1)\) 全称，不预设 RH。

## §4 `1/2` 的完整来源链

\(1/2\) 既不是输入，也不是论证结果，而是一条假设经初等算术后浮到结论常数位置：

1. `SizeWindows` 的 `hm1 : x^(1/2-ε) ≤ m`——**这是假设**；
2. `hxX` 从 `hm1` 得 \(x \le x^{1/2+\varepsilon} m\)；
3. 尺寸引理把这一个 \(1/2\) 传成 \(G_x \le x^{1/2+(C+21/8)\varepsilon}\)；
4. `core_gm` 变成 \(G_m \le x^{1/2+(e_D+e_L+7)\varepsilon}\)；
5. `level_of_tiedWin` 用 \(\theta \to 1/2+\delta\) 收成 `ZeroFreeAbove(1/2)`。

**结论：`m` 不是被算术约束在 \(\sqrt{x}\) 的，是被 `SizeWindows` 的一条合取项钉在那里的。** 换一个值就得到另一条零自由区域常数——这正是 08 号最初直觉成立的地方，也是这条链唯一真正需要外部输入的位置。

## §5 机器实测账

一、闭包与产物。`Main.lean` 的完整依赖闭包是 175 191 个库内文件、1 030 531 854 B 源码；本机 `.lake/build/lib/lean` 下只有 175 个 olean。覆盖率 \(0.0999\%\)。**顶层从未编译。**

二、局部实编。取 8 个子树的并集、去掉已有产物的，得 245 个待建文件，24.9 分钟实编：189 通过、56 失败。

三、失败结构。56 个里只有 3 个根错：`LocalRingCardinality/DataLevel.lean:137`（A 类）、`DegreeSingleAdd.lean:121`（B 类）、`NegOneNeOneUnitsZmodFour.lean:154` 的 `eGamE`（C 类，归约发散：四次实验 `whnf` 与 `isDefEq` 全部超时）。其余 53 个全是级联，且全部由 `NegOneNeOneUnitsZmodFour` 连坐——**放大 1 : 54**。这解释了为什么抽样口径（200 样本、硬错率 2.5%）与稠密口径（3/245、1.22%）给出不同直觉：级联会把一个根错铺成一整片红。

四、子树验证。`RowSrc.lean` 只有 6 行、两个 `import`，闭包却是 66 168 个文件、197 层、417 MB，占全库 37.8%。在第一层 3 076 个可编文件里抽 200 个试编，5 处硬错，阻断 1 313 个文件。全建按单文件 18–22 秒估，单线程 13.8 天。

五、唯一修好的根错。`Formalism/GaloisCohomology/Statement.lean:97`（D 类，实例搜索塌陷）已修：`abbrev LocH2` + `@[instance_reducible]` + `letI`，olean 779 984 B，EXIT=0。A、B、C 三类未动。

**读法：这组数字不是“它错了”，是“它没跑”。** 命题真假在源码里读不出来，只能编出来；编不出来的时候，源码面的一切结论都只剩参考价值。

## §6 08 号的四处订正

1. **“类型层完整闭合，无 sorry、无 axiom”**——降为“源码面静态未见 `sorry`/`axiom` 空洞；机器面未验证”。两句不是一回事，08 把它们写成了一句。
2. **“主链共 9 层”与 §1 表 L1–L16** 自相矛盾——统一为 16 层。
3. **§5.2 的“最大嫌疑是 `ch_core` 七个假设藏强度”**——结论升级：缺口不在藏强度，在编不到底。强度嫌疑仍在账上（`HypsAlt` 的 `aAtG`、`irrC`、`zL`、`tie` 未逐条比对文献），但它不是主要矛盾。
4. **§3.4 的“空槽只有 9 处”**——该计数只对 `: Prop := True` 成立，不构成“可编译性”证据。9 处是明写的空位，规模上确实不构成偷塞假设；但它与“能编出来”没有关系。

08 号 §4 的三个撤回（`SizeWindows` 不孤岛、`Green` 非外部参数、`TLift_k` 不靠 `swFull`）**仍然成立**，本文不改。它们是源码层结论，与机器层无关。

## §7 对两条线的交接

**可学三样。** 其一，把要证的常数写进定义体（`ZeroFreeOn` 的 `1/2`），不给取极限留口子。其二，struct 填充 + 单点总装：196 条包装收成 6 包，6 包收成 1 个 `Nonempty Hyps`，最后三个参数喂 `plugWin`——形式化大工程只有这一种组织方式能撑住。其三，Landau 型转换的用法：增长控制到零自由的桥，对 \(\theta\) 全称，可直接借用。

**不可信三样。** 其一，编译状态，任何“闭合”的说法都要有 olean 与 `#print axioms` 的回执。其二，接口靠猜：`first | A | B | C` 那种三选一试的证明体，是接口匹配而非推理。其三，未核的深层数据包：`hS.2.2.2.2.2.1` 这种五层嵌套按位置取字段的写法，某一层宽于文献就无人可见。

**对 BSD 主线**：这条线与 `C:\proj2` 的 BSD 台账不交叉。BSD 侧继续走自己的 G2/G5/环债序列，本文只贡献两条方法论——常数写进定义、每次探针必须给 olean 大小与 `#print axioms` 回执。RH 侧维持“停投”，只保留 D 类实例搜索塌陷的修法作为工程经验。

## 附录 A 关键文件

| 文件 | 作用 |
| --- | --- |
| `Main.lean` | 顶层 `riemannHypothesis` |
| `CharacterBoxes/EveryCharacter.lean` | GRH-L 定义 |
| `TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean` | `ZeroFreeOn`、`Gm`、Landau 转换 |
| `TotientGaloisClasses/TopWin.lean` | `level_of_tiedWin`、`zeroFreeOn_of_tiedWin_cyc` |
| `DedekindLFunctions/LandauTheorems/ChCore.lean` | `ch_core` |
| `ChainSlopeWindows/LipschitzWeightAndMinimum.lean` | `proposition_size_bound` |
| `PrimitiveCosets/CoreGm.lean` | `core_gm` |
| `Formalism/GaloisCohomology/Statement.lean` | D 类已修（`LocH2`） |
| `LocalRingCardinality/DataLevel.lean` | A 类未修（`:137`） |
| `NegOneNeOneUnitsZmodFour.lean` | C 类未修（`:154` `eGamE`） |

## 附录 B 复现

```powershell
# 闭包与产物计数
(Get-ChildItem 'F:\F\BSD_GRH_RH\RH_14\lean\src' -Recurse -Filter *.lean).Count
(Get-ChildItem 'F:\F\BSD_GRH_RH\RH_14\lean\.lake\build\lib\lean' -Recurse -Filter *.olean).Count

# 245 实编与分类
python C:\proj2\_rh14_zeroside\_build_down.py
python C:\proj2\_rh14_zeroside\_classify_down.py
```

声明索引缓存 `_declidx.pkl` 在 `C:\proj2\_rh14_zeroside`，结构为 `短名 -> [(kind, full_name, path, start_offset, end_offset)]`。
