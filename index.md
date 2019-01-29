---
title          : 目录
layout         : home
translators : ["Rongxiao Fu"]
---

本书是 Philip Wadler 和 Wen Kokke 所著的《Programming Language Foundations in Agda》的中文翻译。英文原书请见 [PLFA]。

This is a Chinese translation of "Programming Language Foundations in Agda" by Philip Wadler and Wen Kokke。The original book is located at [PLFA].

目前翻译过程刚刚开始，仅试译了正文第一章和使用说明。欢迎参与到翻译规范的拟定中。欢迎指出译文的错漏之处。项目地址 [PLFA-zh]。

以下为原书目录翻译：

本书是对编程语言理论的介绍。书中的程序使用证明助理 Agda 编写。
<!---
This book is an introduction to programming language theory using the
proof assistant Agda.
--->

欢迎对本书各方面的评论和建议（章节组织，可以添加/移除的材料，解释不够清楚的部分，有价值的习题，内容或拼写错误等）。
本书的源码托管在 [GitHub]。欢迎拉取请求。
<!---
Comments on all matters---organisation, material to add, material to
remove, parts that require better explanation, good exercises, errors,
and typos---are welcome.  The book repository is on [GitHub].
Pull requests are encouraged.  
--->

## 前言
<!---
Front matter
--->

  - [Dedication](/Dedication/)
  - [Preface](/Preface/)

## 第一册：逻辑基础
<!---
Part 1: Logical Foundations
--->

  - [自然数](/Naturals/): 自然数
  - [Induction](/Induction/): Proof by induction
  - [Relations](/Relations/): Inductive definition of relations
  - [Equality](/Equality/): Equality and equational reasoning
  - [Isomorphism](/Isomorphism/): Isomorphism and embedding
  - [Connectives](/Connectives/): Conjunction, disjunction, and implication
  - [Negation](/Negation/): Negation, with intuitionistic and classical logic
  - [Quantifiers](/Quantifiers/): Universals and existentials
  - [Decidable](/Decidable/): Booleans and decision procedures
  - [Lists](/Lists/): Lists and higher-order functions

<!---
[Naturals](/Naturals/): Natural numbers
[Induction](/Induction/): Proof by induction
[Relations](/Relations/): Inductive definition of relations
[Equality](/Equality/): Equality and equational reasoning
[Isomorphism](/Isomorphism/): Isomorphism and embedding
[Connectives](/Connectives/): Conjunction, disjunction, and implication
[Negation](/Negation/): Negation, with intuitionistic and classical logic
[Quantifiers](/Quantifiers/): Universals and existentials
[Decidable](/Decidable/): Booleans and decision procedures
[Lists](/Lists/): Lists and higher-order functions
--->

## 第二册：编程语言基础
<!---
Part 2: Programming Language Foundations
--->

  - [Lambda](/Lambda/): Introduction to Lambda Calculus
  - [Properties](/Properties/): Progress and Preservation
  - [DeBruijn](/DeBruijn/): Inherently typed De Bruijn representation
  - [More](/More/): Additional constructs of simply-typed lambda calculus
  - [Bisimulation](/Bisimulation/) : Relating reductions systems
  - [Inference](/Inference/): Bidirectional type inference
  - [Untyped](/Untyped/): Untyped lambda calculus with full normalisation

## 后记
<!---
Backmatter
--->

  - [Acknowledgements](/Acknowledgements/)
  - [Fonts](/Fonts/): Test page for fonts
  - [Statistics](/Statistics/): Line counts for each chapter

## 相关
<!---
Related
--->

  - A paper describing the book appears in [SBMF][sbmf].
  - Courses taught from the textbook:
    * Philip Wadler, University of Edinburgh,
      [2018](http://plfa.inf.ed.ac.uk/TSPL/)
    * David Darais, University of Vermont,
      [2018](http://david.darais.com/courses/uvm-cs295A-fa2018/)
    * John Leo, Google Seattle, 2018--2019

[wen]: https://github.com/wenkokke
[phil]: https://homepages.inf.ed.ac.uk/wadler/
[GitHub]: https://github.com/plfa/plfa.github.io/
[sbmf]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
[PLFA]: https://plfa.github.io/
[PLFA-zh]: https://github.com/Agda-zh/plfa-zh

