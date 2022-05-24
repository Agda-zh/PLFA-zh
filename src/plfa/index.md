---
title          : 目录
layout         : page
translators    : ["Rongxiao Fu", "Oling Cat"]
permalink      : /
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

$for(parts)$
## $title$
<ul>
$for(sections)$
$if(titlerunning)$
<li><a href="$url$">$titlerunning$</a>: $subtitle$</li>
$else$
<li><a href="$url$">$title$</a></li>
$endif$
$endfor$
</ul>
$endfor$

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

#### 2022
  * [Andrej Bauer, University of Ljubljana][UL-2022]

#### 2021
  * Favonia, University of Minnesota _(The course website is not pubilc; here is the [link to Favonia's homepage](https://favonia.org).)_

#### 2020
  * [William Cook, University of Texas][UT-2020]
  * [Jeremy Siek, Indiana University][IU-2020]
  * [Maria Emilia Maietti and Ingo Blechschmidt, Università di Padova][Padova-2020]
  * [John Maraist, University of Wisconsin-La Crosse][UWL-2020]
  * [Ugo de'Liguoro, Università di Torino][Torino-2020]

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
[UVM-2018]: https://web.archive.org/web/20190324115921/http://david.darais.com/courses/fa2018-cs295A/
[PUC-2019]: https://plfa.github.io/20.07/PUC/2019/
[TSPL-2019]: https://plfa.github.io/20.07/TSPL/2019/
[IU-2020]: https://jsiek.github.io/B522-PL-Foundations/
[SFPL-Meetup-2020]: http://meet.meetup.com/wf/click?upn=ZDzXt-2B-2BZmzYir6Bq5X7vEQ2iNYdgjN9-2FU9nWKp99AU8rZjrncUsSYODqOGn6kV-2BqW71oirCo-2Bk8O1q2FtDFhYZR-2B737CPhNWBjt58LuSRC-2BWTj61VZCHquysW8z7dVtQWxB5Sorl3chjZLDptP70L7aBZL14FTERnKJcRQdrMtc-3D_IqHN4t3hH47BvE1Cz0BakIxV4odHudhr6IVs-2Fzslmv-2FBuORsh-2FwQmOxMBdyMHsSBndQDQmt47hobqsLp-2Bm04Y9LwgV66MGyucsd0I9EgDEUB-2FjzdtSgRv-2Fxng8Pgsa3AZIEYILOhLpQ5ige5VFYTEHVN1pEqnujCHovmTxJkqAK9H-2BIL15-2FPxx97RfHcz7M30YNyqp6TOYfgTxyUHc6lufYKFA75Y7MV6MeDJMxw9-2FYUxR6CEjdoagQBmaGkBVzN
[UW-2019]: https://cs.uwaterloo.ca/~plragde/842/
[UT-2020]: https://www.cs.utexas.edu/~wcook/Courses/386L/Sp2020-GradPL.pdf
[BHAM-2019]: https://www.cs.bham.ac.uk/internal/modules/2019/06-26943/
[UWL-2020]: https://github.com/jphmrst/PLC/tree/fall2020
[Torino-2020]: http://laurea.educ.di.unito.it/index.php/offerta-formativa/insegnamenti/elenco-completo/elenco-completo/scheda-insegnamento?cod=MFN0633&codA=&year=2020&orienta=NSE
[Padova-2020]: https://www.math.unipd.it/~maietti/typ21.html
[UL-2022]: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/00-introduction.html
[PLFA]: https://plfa.github.io/
[PLFA-zh]: https://agda-zh.github.io/PLFA-zh/
[Issue]: https://github.com/Agda-zh/plfa-zh/issues
[TransSpec]: https://github.com/Agda-zh/PLFA-zh/issues/1
[Github-zh]: https://github.com/Agda-zh/PLFA-zh
