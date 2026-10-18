# Literature-interface bridges (2026-10-18)

The current main entry `source_main_claims_from_literature` includes both internally proved
literature-to-interface conversions. Full validation passed: 6544 build jobs,
5001 axiom-audit entries, 2718 rooted modules, standard logical axioms only.
The six literature results remain explicit hypotheses. See the
[bridge report](LITERATURE_INTERFACE_BRIDGES_2026-10-18.md).

The previous certification record follows; its counts refer to the earlier main entry.

# 最终条件性认证

状态：完成用户选择的“最小外部假设接口”路线。此处的完成指相对于下列显式文献接口的Lean认证。

2026-10-17 文稿同步修订：正文补入统一终端入口比较、完整半径范围的指数比较、
缓冲吸收根返回误差以及有限时间 Bessel 命中证明，并增加形式化对应附录。
主结论、全部189个既有带标签的编号公式/定理内容和六类外部输入保持。
Lean 定义、定理接口和证明均未修改；对应表补充已有直接审计的辅助声明并刷新行号。
本轮修改、语义核对和最新复验状态见
[MANUSCRIPT_LEAN_ALIGNMENT_2026-10-17.md](MANUSCRIPT_LEAN_ALIGNMENT_2026-10-17.md)。
这里的认证针对已登记数学声明；本轮局部修订及核对不等于全文每一句推理的独立重审。
本轮新版 `./check.sh` 已通过（exit 0）：完整构建6540项、新审计4992条、根导入模块2714个；
189项义务及所有登记行号、源稿哈希和绑定均通过。日志为
`logs/manuscript-alignment-2026-10-17-check.log`。
内置 LaTeX 编译成功，40页交付 PDF 的修改页已检查，最终无引用或溢出警告。

## 最终结论

`SRWTightness.source_main_claims_internal_reflection` 同时证明：

- `DiskTightnessClaim`：圆盘停止模型的紧性；
- `DiskTailClaim`：圆盘模型尾界；
- `TimeTightnessClaim`：确定时间模型紧性；
- `TimeTailClaim`：确定时间模型尾界；
- `InclusiveTimeTightnessClaim`：闭端点时间约定下的紧性。

声明位置：`SRWTightness/SourceMainInternalReflection.lean`。
本文核心上尾和种子命题已内部推导，未作为外部输入。

## 保留的精确文献接口

| Lean参数 | 作用 |
|---|---|
| `PotentialKernelAsymptoticInput` | SRW势核精细渐近 |
| `PositiveHarmonicRelativeInput` | 正调和相对差分估计 |
| `GWBarrierUpperInput` | 临界几何GW屏障上界 |
| `∀ K k ι, RaicConvexCLTInput (MarkSamples K k) ι` | 有限维独立向量凸集CLT，保留有限维类型条件 |
| `GWBarrierLowerInput` | 临界几何GW屏障下界 |
| `BDZDyadicSquareMaximumInput` | 归一化DGFF方格最大值上界 |

没有新增或替换输入家族。文献匹配和模型约定见
`SOURCE_BASELINE_LITERATURE_BINDINGS_REVIEW.md`、`GW_INTERFACE_AUDIT.md`、
`BDZ_SQUARE_INTERFACE_REVIEW.md`、`SOURCE_BDZ_GENERAL_SIZE_REVIEW.md`及外部接口记录。
标准Lean依赖限于`propext`、`Classical.choice`、`Quot.sound`。

## 原稿义务和最后三个缺口

`obligations.json`覆盖源稿全部189个非章节标签，逐项保留可追踪的Lean声明。
最终98项内部认证、89项条件性认证、2项显式外部输入、0项未完成。
已证比例为187/189=98.9%；外部输入占2/189=1.1%，不虚计为已内部证明。
显式外部条目是(2.13)与(3.4)。文献输入家族数与原稿标签数是不同统计。

- (2.24)：覆盖全部0<a<=m/2的完整有序记录、任意非负函数和可测投影；误差具有原文正向层级及实际计数形式。
- (2.25)：保留实际J=j及联合事件，给出返回因子rho^(j-1)，并对位置相关根层级得到rho=1-1/(k+K)。
- (2.26)：保留实际J=1及出口相关的不返回因子，给出环带根中心下的双侧比较。

终端误差小于1/2、较强半径分离、随总深度增长的额外尺度条件均已从完整伴随结论中移除。
保留的q<=1/2、域包含及起点排除来自原稿明确设置；固定阈值和后代小误差条件由固定大m/H比值统一保证。
H>=8弱于原稿H0=4r+10；下界的R/m阈值由原稿深度趋于无穷保证。
详细证明范围见`SOURCE_FULL_RECORD_SCOPE_REVIEW.md`。

## 最终验证

Full6540/Audit4992/4991distinct/26axiom-free/graph2714。上一完整范围证明批次加入26个模块、27个声明，另补充8个早期声明的直接公理审计；本轮文稿修订没有新增 Lean 声明。
所有187项内部或条件性原稿绑定均出现在统一审计中；全部非章节源标签恰好登记一次。
递归导入闭包中没有sorry、admit、自定义axiom或native_decide。
当前修订稿SHA256为`522bdfaea66d101c17e6228f23ef993413928d517afccd66b784c66f89fefb74`。
历史原稿SHA256为`9952ce4896eb2b667fcc6b004ccd92c631d175bfe734d0b6d388d161eb0233b4`，
对应提交`2aa150a35af3a321428a19b43004123bd223e92e`；历史验收日志保持原样。

工具链固定为Lean4 v4.32.0，mathlib提交为`81a5d257c8e410db227a6665ed08f64fea08e997`。
一键复验：在项目根目录运行`./check.sh`。它构建、运行公理审计，并以`verify_certificate.py`核对全部源标签、绑定及证明闭包。
也可在`formalization`目录运行`lake build`与`lake env lean SRWTightness/Audit.lean`；
在`source`目录运行`shasum -a 256 -c SHA256SUMS`。
日志：`logs/build-full-record-scope-gate.log`、`logs/axioms-full-record-scope.log`；最终绑定检查见`logs/final-certificate-check.log`。

本地历史草稿与中间日志中未被根模块导入的内容不作为证明证据。
此前完整范围证明通过新增伴随定理完成。本轮在这些已有证明基础上修正文稿，
没有新增或修改 Lean 定理。源稿版本变化及本轮复验与上述历史批次分别记录。
