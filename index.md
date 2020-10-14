---
title          : 目录
layout         : page
translators    : ["Rongxiao Fu", "Oling Cat"]
---

[本书][PLFA-zh]是 Philip Wadler 和 Wen Kokke 所著的《Programming Language Foundations in Agda》的中文翻译。英文原书请见 [PLFA]。

This is a Chinese translation of "Programming Language Foundations in Agda" by Philip Wadler and Wen Kokke. The original book is located at [PLFA].

**本书在线版可访问 [PLFA-zh] 阅读。**

目前第一部分已翻译完毕，欢迎各位参与翻译和审校。详情请参考[翻译规范][TransSpec]。
由于译者水平有限，错漏之处在所难免，欢迎读者提出修改建议。如有问题可在 [Issue]
发起讨论或直接发起 PR。项目源码可访问 [Github][Github-zh] 获取。

**以下为原书主页内容：**

---

<!---
This book is an introduction to programming language theory using the
proof assistant Agda.
--->

本书是对编程语言理论的介绍。书中的程序使用证明助理 Agda 编写。

<!---
Comments on all matters---organisation, material to add, material to
remove, parts that require better explanation, good exercises, errors,
and typos---are welcome.  The book repository is on [GitHub].
Pull requests are encouraged.
--->

欢迎对本书各方面的评论和建议（章节组织，可以添加/移除的材料，解释不够清楚的部分，
有价值的习题，内容或拼写错误等）。
本书的源码托管在 [GitHub]。欢迎拉取请求。

<!---
## Front matter

  - [Dedication]({{ site.baseurl }}/Dedication/)
  - [Preface]({{ site.baseurl }}/Preface/)
  - [Getting Started]({{ site.baseurl }}/GettingStarted/)
--->

## 前言
  - [题献]({{ site.baseurl }}/Dedication/)
  - [前言]({{ site.baseurl }}/Preface/)
  - [使用说明]({{ site.baseurl }}/GettingStarted/)

<!---
## Part 1: Logical Foundations

  - [Naturals]({{ site.baseurl }}/Naturals/): Natural numbers
  - [Induction]({{ site.baseurl }}/Induction/): Proof by induction
  - [Relations]({{ site.baseurl }}/Relations/): Inductive definition of relations
  - [Equality]({{ site.baseurl }}/Equality/): Equality and equational reasoning
  - [Isomorphism]({{ site.baseurl }}/Isomorphism/): Isomorphism and embedding
  - [Connectives]({{ site.baseurl }}/Connectives/): Conjunction, disjunction, and implication
  - [Negation]({{ site.baseurl }}/Negation/): Negation, with intuitionistic and classical logic
  - [Quantifiers]({{ site.baseurl }}/Quantifiers/): Universals and existentials
  - [Decidable]({{ site.baseurl }}/Decidable/): Booleans and decision procedures
  - [Lists]({{ site.baseurl }}/Lists/): Lists and higher-order functions
--->

## 第一分册：逻辑基础

  - [Naturals]({{ site.baseurl }}/Naturals/): 自然数
  - [Induction]({{ site.baseurl }}/Induction/): 归纳证明
  - [Relations]({{ site.baseurl }}/Relations/): 关系的归纳定义
  - [Equality]({{ site.baseurl }}/Equality/): 相等性与等式推理
  - [Isomorphism]({{ site.baseurl }}/Isomorphism/): 同构与嵌入
  - [Connectives]({{ site.baseurl }}/Connectives/): 合取、析取与蕴涵
  - [Negation]({{ site.baseurl }}/Negation/): 直觉逻辑与命题逻辑中的否定
  - [Quantifiers]({{ site.baseurl }}/Quantifiers/): 全称量词与存在量词
  - [Decidable]({{ site.baseurl }}/Decidable/): 布尔值与判定过程
  - [Lists]({{ site.baseurl }}/Lists/): 列表与高阶函数

<!---
## Part 2: Programming Language Foundations

  - [Lambda]({{ site.baseurl }}/Lambda/): Introduction to Lambda Calculus
  - [Properties]({{ site.baseurl }}/Properties/): Progress and Preservation
  - [DeBruijn]({{ site.baseurl }}/DeBruijn/): Intrinsically-typed de Bruijn representation
  - [More]({{ site.baseurl }}/More/): Additional constructs of simply-typed lambda calculus
  - [Bisimulation]({{ site.baseurl }}/Bisimulation/): Relating reductions systems
  - [Inference]({{ site.baseurl }}/Inference/): Bidirectional type inference
  - [Untyped]({{ site.baseurl }}/Untyped/): Untyped lambda calculus with full normalisation
  - [Confluence]({{ site.baseurl }}/Confluence/): Confluence of untyped lambda calculus
  - [BigStep]({{ site.baseurl }}/BigStep/): Big-step semantics of untyped lambda calculus
--->

## 第二分册：编程语言基础

  - [Lambda]({{ site.baseurl }}/Lambda/): λ-演算简介
  - [Properties]({{ site.baseurl }}/Properties/): 可进性与保型性
  - [DeBruijn]({{ site.baseurl }}/DeBruijn/): 固有类型的 de Bruijn 表示
  - [More]({{ site.baseurl }}/More/): 简单类型 λ-演算的附加构造
  - [Bisimulation]({{ site.baseurl }}/Bisimulation/) : 关系归约系统
  - [Inference]({{ site.baseurl }}/Inference/): 双向类型推断
  - [Untyped]({{ site.baseurl }}/Untyped/): 无类型 λ-演算及其完整范式
  - [Confluence]({{ site.baseurl }}/Confluence/): 无类型 λ-演算的汇合性
  - [BigStep]({{ site.baseurl }}/BigStep/): 无类型 λ-演算的大步语义

<!--
## Part 3: Denotational Semantics

  - [Denotational]({{ site.baseurl }}/Denotational/): Denotational semantics of untyped lambda calculus
  - [Compositional]({{ site.baseurl }}/Compositional/): The denotational semantics is compositional
  - [Soundness]({{ site.baseurl }}/Soundness/): Soundness of reduction with respect to denotational semantics
  - [Adequacy]({{ site.baseurl }}/Adequacy/): Adequacy of denotational semantics with respect to operational semantics
  - [ContextualEquivalence]({{ site.baseurl }}/ContextualEquivalence/): Denotational equality implies contextual equivalence
-->

## 第三分册：指称语义

  - [Denotational]({{ site.baseurl }}/Denotational/): 无类型 λ-演算的指称语义
  - [Compositional]({{ site.baseurl }}/Compositional/): 指称语义具有复合性
  - [Soundness]({{ site.baseurl }}/Soundness/): 从指称语义看归约的可靠性
  - [Adequacy]({{ site.baseurl }}/Adequacy/): 从操作语义看指称语义的充分性
  - [ContextualEquivalence]({{ site.baseurl }}/ContextualEquivalence/): 指称相等蕴含上下文等价

<!--
## Appendix

  - [Substitution]({{ site.baseurl }}/Substitution/): Substitution in untyped lambda calculus
-->

## 附录

  - [Substitution]({{ site.baseurl }}/Substitution/): 无类型 λ-演算中的代换

<!---
## Backmatter

  - [Acknowledgements]({{ site.baseurl }}/Acknowledgements/)
  - [Fonts]({{ site.baseurl }}/Fonts/): Test page for fonts
--->

## 后记

  - [Acknowledgements]({{ site.baseurl }}/Acknowledgements/): 鸣谢
  - [Fonts]({{ site.baseurl }}/Fonts/): 字体测试页

<!--
## Related

### Mailing lists
-->

## 相关资源

### 邮件列表

  * [plfa-interest@inf.ed.ac.uk](http://lists.inf.ed.ac.uk/mailman/listinfo/plfa-interest): <br />
    A mailing list for users of the book. <br />
    This is the place to ask and answer questions, or comment on the content of the book.
  * [plfa-dev@inf.ed.ac.uk](http://lists.inf.ed.ac.uk/mailman/listinfo/plfa-dev): <br />
    A mailing list for contributors. <br />
    This is the place to discuss changes and new additions to the book in excruciating detail.

<!--
### Courses taught from the textbook
-->

### 使用本书教学的课程

#### 2020
  * [William Cook, University of Texas][UT-2020]
  * [Jeremy Siek, Indiana University][IU-2020]
  * [John Maraist, University of Wisconsin-La Crosse][UWL-2020]

#### 2019
  * [Dan Ghica, University of Birmingham][BHAM-2019]
  * [Adrian King, San Francisco Types, Theorems, and Programming Languages Meetup][SFPL-Meetup-2020]
  * [Prabhakar Ragde, University of Waterloo][UW-2019]
  * [Philip Wadler, University of Edinburgh][TSPL-2019]
  * [Philip Wadler, Pontifícia Universidade Católica do Rio de Janeiro][PUC-2019]

#### 2018
  * [Philip Wadler, University of Edinburgh][TSPL-2018]
  * [David Darais, University of Vermont][UVM-2018]
  * John Leo, Google Seattle

<!--
Please tell us of others!
-->

请告诉我们其他的资源！

[TSPL-2018]: https://plfa.github.io/19.08/TSPL/2018/
[PUC-2019]: https://plfa.github.io/20.07/PUC/2019/
[TSPL-2019]: https://plfa.github.io/20.07/TSPL/2019/
[GitHub]: https://github.com/plfa/plfa.github.io/
[UVM-2018]: https://web.archive.org/web/20190324115921/http://david.darais.com/courses/fa2018-cs295A/
[IU-2020]: https://jsiek.github.io/B522-PL-Foundations/
[SFPL-Meetup-2020]: http://meet.meetup.com/wf/click?upn=ZDzXt-2B-2BZmzYir6Bq5X7vEQ2iNYdgjN9-2FU9nWKp99AU8rZjrncUsSYODqOGn6kV-2BqW71oirCo-2Bk8O1q2FtDFhYZR-2B737CPhNWBjt58LuSRC-2BWTj61VZCHquysW8z7dVtQWxB5Sorl3chjZLDptP70L7aBZL14FTERnKJcRQdrMtc-3D_IqHN4t3hH47BvE1Cz0BakIxV4odHudhr6IVs-2Fzslmv-2FBuORsh-2FwQmOxMBdyMHsSBndQDQmt47hobqsLp-2Bm04Y9LwgV66MGyucsd0I9EgDEUB-2FjzdtSgRv-2Fxng8Pgsa3AZIEYILOhLpQ5ige5VFYTEHVN1pEqnujCHovmTxJkqAK9H-2BIL15-2FPxx97RfHcz7M30YNyqp6TOYfgTxyUHc6lufYKFA75Y7MV6MeDJMxw9-2FYUxR6CEjdoagQBmaGkBVzN
[UW-2019]: https://cs.uwaterloo.ca/~plragde/842/
[UT-2020]: https://www.cs.utexas.edu/~wcook/Courses/386L/Sp2020-GradPL.pdf
[BHAM-2019]: https://www.cs.bham.ac.uk/internal/modules/2019/06-26943/
[EUSA-2020]: https://www.eusa.ed.ac.uk/representation/campaigns/teachingawards2020/
[SBMF]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
[SCP]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#scf
[NextJournal]: https://nextjournal.com/plfa/ToC
[UWL-2020]: https://github.com/jphmrst/PLC/tree/fall2020

[PLFA]: https://plfa.github.io/
[PLFA-zh]: https://agda-zh.github.io/PLFA-zh/
[Issue]: https://github.com/Agda-zh/plfa-zh/issues
[TransSpec]: https://github.com/Agda-zh/PLFA-zh/issues/1
[Github-zh]: https://github.com/Agda-zh/PLFA-zh
