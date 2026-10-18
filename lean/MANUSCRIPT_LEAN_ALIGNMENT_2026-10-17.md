# 文稿与 Lean 对应修订（2026-10-17）

状态：本轮定点对应修订完成；修改区间独立复核、编译、版面检查和新版完整复验通过。

注意：历史源标签名不等于当前 PDF 显示编号。本文沿用源标签定位：

| 源标签 | 当前 PDF 编号 |
|---|---|
| `eq:2.15` | (3.12) |
| `eq:2.24` | (3.23) |
| `eq:2.25` | (3.25) |
| `eq:2.26` | (3.26) |
| `eq:7.17` | (6.24) |

这些显示编号在本轮前后保持；附录为 A。

## 范围与依据

- 用户授权：修正文稿，使其与已有 Lean 证明对应。
- 当前正文：`source/SRW_max_local_time.tex`。
- 当前修订稿 SHA256：
  `522bdfaea66d101c17e6228f23ef993413928d517afccd66b784c66f89fefb74`。
- 历史原稿：提交 `2aa150a35af3a321428a19b43004123bd223e92e`，SHA256
  `9952ce4896eb2b667fcc6b004ccd92c631d175bfe734d0b6d388d161eb0233b4`。
- 数学依据：现有 Lean 声明及其明确的前提；历史范围核对见
  `SOURCE_FULL_RECORD_SCOPE_REVIEW.md`、`SOURCE_UNIFORM_ENTRANCE_REVIEW.md`。
- 保留主定理、全部既有编号公式、全部189个非章节标签及六类外部输入。
  本轮不修改 Lean 的定义、定理签名或证明。
- 本记录作为本轮修订状态、修改约束、问题和对应关系的统一记录；历史进度不改写。

## 数学修改及对应

### 终端入口、零标记和 (2.24)

正文先在 `0<a<=m/2`、`0<=H<=m/8`、固定充分大 `m` 下建立统一比较。
以包围圆盘 `L=B(b,m-H)` 的容量归一化，使用入口调和函数的 Harnack 链和
equilibrium sweeping。正标记沿用同一首次入口后的 killed-path kernel。
实际零标记由避开半径 `m/2` 的圆盘得到固定正下界；参考零标记上界比较
明确要求 `q=alpha*cap_D(K)<=1/2`。先比较完整标记，再推前到任意指定投影。

小观察半径的精细比较采用固定充分大的包围半径，避免直接对微小格点圆盘
使用渐近式。指数比较区分 `a<=m/4` 与 `m/4<a<=m/2`；前者还区分相对误差
是否超过 `1/2`。误差大时使用独立正下界，保留 (2.24) 的完整半径范围。

对应声明（均已有直接公理审计）：

- `SRWTightness.source_entrance_boundary_harnack`
- `SRWTightness.entrance_atom_equilibrium_sweep`
- `SRWTightness.buffered_capacity_normalization`
- `SRWTightness.source_uniform_entrance_atoms`
- `SRWTightness.source_entrance_all_positive_radii`
- `SRWTightness.source_terminal_zero_mass`
- `SRWTightness.source_ordered_word_uniform_lower`
- `SRWTightness.source_ordered_word_uniform_upper`
- `SRWTightness.relative_probability_wide_exponential`
- `SRWTightness.half_radius_terminal_error`
- `SRWTightness.source_terminal_ordered_word_all_radii`
- (2.24) 的原有完整记录归纳、实际计数误差和参考 GW 识别绑定保持。

### 根返回及 (2.25)

加入固定阈值后的 `4/a` 环域分子误差，说明 `H0>=8` 的缓冲如何吸收误差，
以及分母如何被 `k+log(32)+2log(2)+2` 控制。固定移位可取
`log(32)+2log(2)+3` 或更大值。后面的实际根层应用改为引用此定量证明。
这补足全范围对应，不把原来较窄参数下的渐近应用判为错误。

对应 `SRWTightness.annulus_universal_return_bound`、
`SRWTightness.buffered_log_surplus`、
`SRWTightness.source_root_return_rate_universal`、
`SRWTightness.source_general_root_return_universal`。

### Bessel 命中及 (7.17)

用实际 killed-Brownian/Doob 路线推导有限时间严格下穿公式，再取递增时间极限，
通过连续性和邻近水平夹逼得到恰好命中。逆半径矩同时处理从水平下方出发的情形。
这替换原来一句未展开的停时说明，保留 (7.17) 的两个等式。

对应 `SRWTightness.bessel_strict_hitting_exact`、
`SRWTightness.global_bessel_infinite_strict_hitting`、
`SRWTightness.global_bessel_level_hitting`、
`SRWTightness.source_bessel_level_hitting_identity_internal`。

### 形式化范围说明

增加仅含 `sec:` 章节标签的附录，披露六类文献接口，说明势核常数的替代推导、
上述补充路线以及语义对应与 Lean 内核验收的界限。势核常数仍保留原文献引用。
主声明仍为 `SRWTightness.source_main_claims_internal_reflection`。

## 对应记录与复验

已更新 SHA256、全部189项登记行号及本轮新增论证的直接声明绑定。
校验器新增源标签唯一性和登记行号一致性检查，原有范围、状态和公理检查保持。
这是一轮针对已发现差异的同步修订，不构成全文每一句推理的独立重审。

## 本轮检查状态

- 修改区间独立数学复核：通过；包括精确 sweeping、包围集容量、三分支指数化、
  缓冲吸收及 Bessel 有限时间极限。已将正/零分解明确为完整标记，再传递至投影。
- 189个带标签的编号公式/定理环境：与历史原稿逐字相同；非章节标签及顺序完全相同。
  所有引用和文献键有定义，唯一新增标签为 `sec:formalization`。
- 内置 LaTeX 编译器：首次返回忙，重试及最终源稿编译均成功。
- 可交付 PDF：40页；最终编译没有未定义引用、重跑警告、Overfull 或 Underfull。
  已查看第7、8、9、11、12、13、19、26、27、39页的版面，重点页另作完整尺寸检查。
  日志：`logs/manuscript-alignment-2026-10-17-latex.log`。
- 新版 `./check.sh`：exit 0。
  完整构建6540项通过；新生成4992条声明审计，检查2714个根导入模块。
  189项义务仍为98内部、89条件、2显式外部、0未完成；公理仅为标准三项。
  源稿哈希、所有直接声明绑定、标签覆盖、登记行号和证明闭包检查通过。
  日志：`logs/manuscript-alignment-2026-10-17-check.log`。
- `git diff --check`：通过。没有修改任何 `.lean` 文件。

## 功能覆盖复盘

范围覆盖上述数学衔接、形式化范围说明及其版本绑定；对照的原稿、Lean 声明和
参数前提已核实，主结论及外部接口保留。采用理论论文的“前提—推导—边界—结论”
核查，完成修改区间结构、证据和范围、叙述及交付四类检查。变更传播至相关正文应用、
附录、义务表、哈希、验收脚本和恢复记录；旧版本和历史日志仍可追溯。

本轮修改范围内无未解决阻断问题，可用于本次文稿与 Lean 对应修订的交付。
此结论不扩大为新文献真实性认证、全文逐句重审或投稿就绪认证。
仍保留六类显式文献输入，均已在文稿附录披露。
