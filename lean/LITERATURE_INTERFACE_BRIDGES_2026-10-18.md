# 文献原始形式到现有 Lean 接口（2026-10-18）

本轮目标是把两类文献输入中的数学转换移入 Lean。原有接口和主定理保留，
另增 `SRWTightness.source_main_claims_from_literature` 作为文献形式的主入口。
六类文献定理本身仍作为显式参数，本文不宣称已在 Lean 内证明它们。

## 正调和估计

文献：[Lawler–Limic, Theorem 6.3.8(b), (6.19)](https://www.math.uchicago.edu/~lawler/srwbook.pdf)。

- 原始形式输入：`LLPositiveHarmonicDifferenceInput`。只使用简单随机游走、r=1 的
  一阶差分条款，保留“存在整数 N，对所有 n>=N”的大尺度量词。
- 内部转换：`ll_positive_harmonic_local` 使用整数半径 floor(B/2)，显式证明局部球包含，
  并从非负调和方程推出小尺度的邻点比较。
- 内部转换：`positive_harmonic_relative_of_literature` 构造先水平后竖直的坐标路径，
  证明路径长度、位置和单位步长界；再以指数上界控制路径值并求和，得到原有
  `PositiveHarmonicRelativeInput`。
- 常数只依赖文献定理的 c、N，对函数、位置、A、B 一致；不除以 f(b)，因此覆盖 f(b)=0。

这里沿路径内部证明了所需函数值比较，无需再把 Harnack 定理作为外部参数。
这比此前人工核对中“差分界加 Harnack”的推导需要更少的文献条款。

## DGFF 方格最大值上尾

文献：[Bramson–Ding–Zeitouni, (1), Lemma 3.8 (39)](https://arxiv.org/html/1301.6669v5)。

- 原始形式输入：`BDZLiteratureDyadicMaximumInput`，位于原点方格，N=2^n，n>=2，z>=1。
  保留原始 m_N、sqrt(2*pi) 指数系数、z 前因子和 z^2/n 项。
- 原始场：`bdzLiteratureFieldLaw`，以 Dirichlet 精度矩阵 I-P_D 的逆作为协方差。
  `bdzLiteratureValue` 在方格边界补零，外部输入的最大值确实包括这些边界点。
- 内部模型识别：`bdz_literature_field_eq_green` 使用已经证明的
  `greenMatrix_eq_inverse`，得到该场等于实际 killed SRW Green 场。
- 内部平移：`gaussian_green_translation` 以坐标重标号的线性等距同构、均值及协方差
  唯一性证明场的分布对应；`gaussian_green_maximum_translation` 推出最大值事件概率相等。
  `latticeSquareInterior_translate` 验证方格边界位置的平移。
- 内部归一化：`bdz_sqrt_normalization` 和
  `bdz_dyadic_square_maximum_of_literature` 代入 z=sqrt(2/pi)*u，得到 e^(-2u)。
  n=log_2 N 的换算给出正的统一二次指数常数。
- 对 sqrt(2/pi)*u<1 的有界高度区间，使用概率不超过1和统一扩大前因子；
  不把这一范围扩展写进文献输入。内部最大值事件是整方格事件的子事件，亦在 Lean 内处理。

## 文件与兼容性

新增文件均在 `SRWTightness/`：

1. `LiteraturePositiveHarmonic.lean`
2. `GaussianGreenTranslation.lean`
3. `LiteratureBDZSquareMaximum.lean`
4. `SourceMainLiteratureInputs.lean`

根模块导入新入口，统一 `Audit.lean` 对九条新增公开定理直接进行公理审计。
没有改变旧主定理的签名、原有六类接口的定义或文稿中的数学陈述。

## 验证

完整 `./check.sh` 已通过（exit 0）：

- 完整构建 6544 项，包括新增主入口。
- 统一公理审计 5001 条，覆盖 2718 个根导入模块；仅有标准公理
  `propext`、`Classical.choice`、`Quot.sound`。
- 九条新增公开定理全部直接审计。
- 原稿 189 条记录的证书检查通过；状态仍为 98 内部、89 条件性、2 外部、0 未完成。
- 根导入图未出现 `sorry`、`admit`、自定义 `axiom` 或 `native_decide`。
- 原稿校验和保持，旧接口与旧主定理签名保持。

完整成功日志：`logs/literature-interface-bridges-2026-10-18-check-repaired.log`。
本轮早期因新增平移文件与已有文件重名导致的兼容问题已修复：旧
`GaussianTranslation.lean` 逐字恢复，新证明独立放入 `GaussianGreenTranslation.lean`；
最终完整检查使用的是修复后的文件。

结论：两处“文献原始结论 → 项目接口”的转换已由 Lean 内部证明，
不再藏在新主入口的外部前提中。六类文献定理本身仍是显式参数。
