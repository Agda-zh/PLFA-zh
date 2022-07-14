---
title     : 目录
permalink : /
translators: ["Rongxiao Fu", "Oling Cat"]
next      : /Dedication/
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
This book is an introduction to programming language theory using the proof
assistant Agda.
--->

本书是对编程语言理论的介绍。书中的程序使用证明助理 Agda 编写。

<!---
Comments on all matters---organisation, material to add, material to remove,
parts that require better explanation, good exercises, errors, and typos---are
welcome.  The book repository is on [GitHub]. Pull requests are encouraged.
There is a private repository of answers to selected questions on github. Please
contact one of the authors if you would like to access it.
--->

欢迎对本书各方面的评论和建议（章节组织，可以添加/移除的材料，解释不够清楚的部分，
有价值的习题，内容或拼写错误等）。
本书的源码托管在 [GitHub]。欢迎拉取请求。
GitHub 上有带有习题答案的私有仓库。如果你想要获取访问权限，请联系作者之一。


$for(toc.part)$
## $toc.part.title$
$for(toc.part.chapter)$
$if(toc.part.chapter.titlerunning)$
  * [$toc.part.chapter.titlerunning$]($toc.part.chapter.url$): $toc.part.chapter.subtitle$
$else$
  * [$toc.part.chapter.title$]($toc.part.chapter.url$)
$endif$
$endfor$

$endfor$

<!-- NOTE: The Mailing Lists are Deprecated -->
<!--
### Mailing lists
  * [plfa-interest@inf.ed.ac.uk](https://lists.inf.ed.ac.uk/mailman/listinfo/plfa-interest): <br />
    A mailing list for users of the book. <br />
    This is the place to ask and answer questions, or comment on the content of the book.
  * [plfa-dev@inf.ed.ac.uk](https://lists.inf.ed.ac.uk/mailman/listinfo/plfa-dev): <br />
    A mailing list for contributors. <br />
    This is the place to discuss changes and new additions to the book in excruciating detail.
-->

<!--
## Related
-->

## 相关资源


<!--
### Courses taught from the textbook
-->

### 使用本书教学的课程

#### 2022
  * [Andrej Bauer, University of Ljubljana][UL-2022]
  * [Peter Thiemann, Albert-Ludwigs University][Freiburg-2022]
  * Michael Shulman, University of San Diego

#### 2021
  * Favonia, University of Minnesota
    <!-- The course website is not public. -->

#### 2020
  * [William Cook, University of Texas][UT-2020]
  * [Jeremy Siek, Indiana University][IU-2020]
  * [Maria Emilia Maietti and Ingo Blechschmidt, Università di Padova][Padova-2020]
  * [John Maraist, University of Wisconsin-La Crosse][UWL-2020]
  * Ugo de'Liguoro, Università di Torino

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

[GitHub]: https://github.com/plfa/plfa.github.io/
[SBMF]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
[SCP]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#scf
[NextJournal]: https://nextjournal.com/plfa/ToC
[EUSA-2020]: https://www.eusa.ed.ac.uk/representation/campaigns/teachingawards2020/
[TSPL-2018]: https://plfa.github.io/19.08/TSPL/2018/
[UVM-2018]: https://web.archive.org/web/20190324115921/https://david.darais.com/courses/fa2018-cs295A/
[PUC-2019]: https://plfa.github.io/20.07/PUC/2019/
[TSPL-2019]: https://plfa.github.io/20.07/TSPL/2019/
[IU-2020]: https://jsiek.github.io/B522-PL-Foundations/
[SFPL-Meetup-2020]: https://meet.meetup.com/wf/click?upn=ZDzXt-2B-2BZmzYir6Bq5X7vEQ2iNYdgjN9-2FU9nWKp99AU8rZjrncUsSYODqOGn6kV-2BqW71oirCo-2Bk8O1q2FtDFhYZR-2B737CPhNWBjt58LuSRC-2BWTj61VZCHquysW8z7dVtQWxB5Sorl3chjZLDptP70L7aBZL14FTERnKJcRQdrMtc-3D_IqHN4t3hH47BvE1Cz0BakIxV4odHudhr6IVs-2Fzslmv-2FBuORsh-2FwQmOxMBdyMHsSBndQDQmt47hobqsLp-2Bm04Y9LwgV66MGyucsd0I9EgDEUB-2FjzdtSgRv-2Fxng8Pgsa3AZIEYILOhLpQ5ige5VFYTEHVN1pEqnujCHovmTxJkqAK9H-2BIL15-2FPxx97RfHcz7M30YNyqp6TOYfgTxyUHc6lufYKFA75Y7MV6MeDJMxw9-2FYUxR6CEjdoagQBmaGkBVzN
[UW-2019]: https://cs.uwaterloo.ca/~plragde/842/
[UT-2020]: https://www.cs.utexas.edu/~wcook/Courses/386L/Sp2020-GradPL.pdf
[BHAM-2019]: https://www.cs.bham.ac.uk/internal/modules/2019/06-26943/
[UWL-2020]: https://github.com/jphmrst/PLC/tree/fall2020
[Padova-2020]: https://www.math.unipd.it/~maietti/typ21.html
[UL-2022]: https://web.archive.org/web/20220222095923/https://www.andrej.com/zapiski/ISRM-LOGRAC-2022/00-introduction.html
[PLFA]: https://plfa.github.io/
[PLFA-zh]: https://agda-zh.github.io/PLFA-zh/
[Issue]: https://github.com/Agda-zh/plfa-zh/issues
[TransSpec]: https://github.com/Agda-zh/PLFA-zh/issues/1
[Github-zh]: https://github.com/Agda-zh/PLFA-zh
[Freiburg-2022]: https://proglang.informatik.uni-freiburg.de/teaching/proglang/2022ss/
