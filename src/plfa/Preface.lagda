---
title     : "Preface: 前言"
layout    : page
prev      : /Dedication/
permalink : /Preface/
next      : /Naturals/
translators : ["Oling Cat"]
---

{::comment}
The most profound connection between logic and computation is a pun.
The doctrine of Propositions as Types asserts that a certain kind of
formal structure may be read in two ways: either as a proposition in
logic or as a type in computing.  Further, a related structure may be
read as either the proof of the proposition or as a programme of the
corresponding type.  Further still, simplification of proofs
corresponds to evaluation of programs.
{:/}

逻辑与计算之间最深刻的联系是一种双关。「命题即类型」的学说断言，
形式化的结构可以按两种方式看待：可以看做逻辑中的命题，也可以看做计算中的类型。
此外，相关的结构可以看做命题的证明或者其相应类型的程序。更进一步来说，
证明的化简与程序的求值对应。

{::comment}
Accordingly, the title of this book also has two readings.  It may be
parsed as "(Programming Language) Foundations in Agda" or "Programming
(Language Foundations) in Agda" — the specifications we will write in
the proof assistant Agda both describe programming languages and are
themselves programmes.
{:/}

与此相应，本书的名字也有两种含义。它可以看做「编程语言的基础」，也可以看做
「编程的语言基础」。我们在 Agda 证明助理中编写的规范（Specification）
同时描述了编程语言以及该语言编写的程序自身。

{::comment}
The book is aimed at students in the last year of an undergraduate
honours programme or the first year of a master or doctorate degree.
It aims to teach the fundamentals of operational semantics of
programming languages, with simply-typed lambda calculus as the
central example.  The textbook is written as a literate script in
Agda.  The hope is that using a proof assistant will make the
development more concrete and accessible to students, and give them
rapid feedback to find and correct misapprehensions.
{:/}

本书面向本科最后一年学有余力的学生，或者一年级的研究生或博士生。
本书以简单类型 λ-演算（Simply-Typed Lambda Calculus，简称 STLC）作为核心示例，
旨在教授编程语言的操作语义基础。全书以 Agda 文学脚本的形式写成。
使用证明助理可以让开发过程变得更加具体而清晰易懂，还可以给予学生即时反馈，
帮助学生发现理解有误的地方并及时纠正。

{::comment}
The book is broken into two parts. The first part, Logical
Foundations, develops the needed formalisms.  The second part,
Programming Language Foundations, introduces basic methods of
operational semantics.
{:/}

本书分为两册。第一分册为逻辑基础，发展了所需的形式化工具。第二分册为编程语言基础，
介绍了操作语义的基本方法。

{::comment}
## Personal remarks
{:/}

## 个人言论

{::comment}
Since 2013, I have taught a course on Types and Semantics for
Programming Languages to fourth-year undergraduates and masters
students at the University of Edinburgh.  An earlier version of that
course was based on Benjamin Pierce's excellent [TAPL][tapl].  My
version was based of Pierce's subsequent textbook, [Software
Foundations][sf], written in collaboration with others and based on
Coq.  I am convinced of Pierce's claim that basing a course around a
proof assistant aids learning, as summarised in his ICFP Keynote,
[Lambda, The Ultimate TA][ta].
{:/}

从 2013 年开始，我在爱丁堡大学为四年制本科生和研究生教授编程语言的类型和语义的课程。
该课程的早期版本基于 Benjamin Pierce 的著作 [TAPL][tapl]。我的版本则基于
Pierce 的后续教材 [Software Foundations][sf]（中文版[《软件基础》][sf-zh]），此书为
Pierce 与他人合著，基于 Coq 编写。正如 Pierce 在 ICFP 的主题演讲
[Lambda, The Ultimate TA][ta] 中所言，我也相信基于证明助理的课程会对学习有所帮助。

{::comment}
However, after five years of experience, I have come to the conclusion
that Coq is not the best vehicle.  Too much of the course needs to
focus on learning tactics for proof derivation, to the cost of
learning the fundamentals of programming language theory.  Every
concept has to be learned twice: e.g., both the product data type, and
the corresponding tactics for introduction and elimination of
conjunctions.  The rules Coq applies to generate induction hypotheses
can sometimes seem mysterious.  While the `notation` construct permits
pleasingly flexible syntax, it can be confusing that the same concept
must always be given two names, e.g., both `subst N x M` and `N [x :=
M]`.  Names of tactics are sometimes short and sometimes long; naming
conventions in the standard library can be wildly inconsistent.
*Propositions as types* as a foundation of proof is present but
hidden.
{:/}

然而有了五年的教学经验后，我得出了 Coq 并不是最好的授课载体的结论。
对于学习编程语言理论的基础而言，我们花费了太多课程去专门学习证明推导的策略（Tactic）。
每个概念都需要学习两遍：例如，在学过一遍积数据类型（Product Data Type）之后，
我们还要再学一遍与之对应的连词（Conjunction）的引入（Introduction）和消除（Elimination）策略。
Coq 用来生成归纳假设（Induction Hypothesis）的规则有时看起来很玄学。而 `notation`
构造则允许直观但灵活多变的语法，同一个概念总是有两个名字有时会令人迷惑，
例如，`subst N x M` 和 `N [x := M]`。策略的名字时短时长；标准库中的命名约定则非常不一致。
**命题即类型**作为证明的基础虽然存在，但却被雪藏了。

{::comment}
I found myself keen to recast the course in Agda.  In Agda, there is
no longer any need to learn about tactics: there is just
dependently-typed programming, plain and simple. Introduction is
always by a constructor, elimination is always by pattern
matching. Induction is no longer a mysterious separate concept, but
corresponds to the familiar notion of recursion. Mixfix syntax is
flexible while using just one name for each concept, e.g.,
substitution is `_[_:=_]`. The standard library is not perfect, but
there is a fair attempt at consistency. *Propositions as types* as a
foundation of proof is on proud display.
{:/}

我发现自己热衷于用 Agda 重构此课程。在 Agda 中，我们不再需要学习策略了：
这里只有依赖类型编程，简单纯粹。我们总是通过构造子来引入，通过模式匹配来消除。
归纳不再是谜之独立的概念，它与我们熟悉的递归概念直接对应。混缀语法十分灵活，
但每个概念只需要一个名字，例如代换就是 `_[_:=_]`。标准库虽不完美，但它的一致性却很合理。
**命题即类型**作为证明的基础则被骄傲地展示了出来。

{::comment}
Alas, there is no textbook for programming language theory in
Agda.  Stump's [Verified Functional Programming in Agda][stump] covers
related ground, but focusses more on programming with dependent
types than on the theory of programming languages.
{:/}

然而，此前还没有 Agda 描述的编程语言理论教材。虽然 Stump 的
[Verified Functional Programming in Agda][stump] 涵盖了相关的范围，
但比起编程语言理论，却更多关注于依赖类型编程。

{::comment}
The original goal was to simply adapt *Software Foundations*,
maintaining the same text but transposing the code from Coq to Agda.
But it quickly became clear to me that after five years in the
classroom I had my own ideas about how to present the material.  They
say you should never write a book unless you cannot *not* write the
book, and I soon found that this was a book I could not not write.
{:/}

本书最初的目标只是简单地改编**《软件基础》**，保持同样的内容，而只是将代码从
Coq 翻译成 Agda。但五年的课堂经验让我很快就明白了，自己有一些关于如何展示这些材料的想法。
有人说除非你**不得不**写书，否则绝对不要写书。而我很快就发现这是一本我不得不写的书。

{::comment}
I am fortunate that my student, [Wen Kokke][wen], was keen to help.
She guided me as a newbie to Agda and provided an infrastructure that
is easy to use and produces pages that are a pleasure to view.
{:/}

我很幸运地得到了我的学生 [Wen Kokke][wen] 的热情帮助。她引导着我站在 Agda
新手的视角写书，还提供了一些十分易用的工具来产生清晰易读的的页面。

{::comment}
Most of the text was written during a sabbatical in the first half of 2018.
{:/}

这里的大部分内容都是在 2018 年上半年的休假期间写的。

— Philip Wadler, Rio de Janeiro, January–June 2018

[tapl]: https://www.cis.upenn.edu/~bcpierce/tapl/
[sf]: https://softwarefoundations.cis.upenn.edu/
[sf-zh]: https://coq-zh.github.io/SF-zh/
[ta]: https://www.cis.upenn.edu/~bcpierce/papers/plcurriculum.pdf
[stump]: https://www.morganclaypoolpublishers.com/catalog_Orig/product_info.php?cPath=24&products_id=908
[wen]: https://github.com/wenkokke
[phil]: https://homepages.inf.ed.ac.uk/wadler/

{::comment}
## A word on the exercises
{:/}

## 习题说明

{::comment}
Exercises labelled "(recommended)" are the ones students are
required to do in the class taught at Edinburgh from this textbook.
{:/}

标有（推荐）的习题是爱丁堡大学使用本教材的课程中学生需要做的。

{::comment}
Exercises labelled "(stretch)" are there to provide an extra challenge.
Few students do all of these, but most attempt at least a few.
{:/}

标有（延伸）的习题提供了额外的挑战。很少有学生全部做完，但大部分练习至少应该尝试一下。

{::comment}
Exercises without a label are included for those who want extra practice.
{:/}

没有标记的习题供想要更多实践的学生练习。
