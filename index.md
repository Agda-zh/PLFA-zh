---
title          : 目录
layout         : home
translators    : ["Rongxiao Fu"]
---

本书是 Philip Wadler 和 Wen Kokke 所著的《Programming Language Foundations in Agda》的中文翻译。英文原书请见 [PLFA]。

This is a Chinese translation of "Programming Language Foundations in Agda" by Philip Wadler and Wen Kokke。The original book is located at [PLFA].

目前翻译刚刚开始，欢迎各位参与到翻译规范的拟定中。
由于译者水平有限，错漏之处在所难免，欢迎读者提出修改建议。如有问题可在 [Issue]
发起讨论或直接发起 PR。项目地址 [PLFA-zh]。

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

欢迎对本书各方面的评论和建议（章节组织，可以添加/移除的材料，解释不够清楚的部分，有价值的习题，内容或拼写错误等）。
本书的源码托管在 [GitHub]。欢迎拉取请求。

<!---
Front matter

  - [Dedication]({{ site.baseurl }}/Dedication/)
  - [Preface]({{ site.baseurl }}/Preface/)
--->

{%- assign Dedication = site.pages | where:"permalink", "/Dedication/"  | first -%}
{%- assign Preface = site.pages | where:"permalink", "/Preface/"  | first -%}

## 前言

  - [题献]({{ site.baseurl }}/Dedication/) <span class = "progress" >{{ Dedication.progress | ceil }}</span>
  - [前言]({{ site.baseurl }}/Preface/) <span class = "progress" >{{ Preface.progress | ceil }}</span>

<!---
Part 1: Logical Foundations

  - [Naturals](/Naturals/): Natural numbers
  - [Induction](/Induction/): Proof by induction
  - [Relations](/Relations/): Inductive definition of relations
  - [Equality](/Equality/): Equality and equational reasoning
  - [Isomorphism](/Isomorphism/): Isomorphism and embedding
  - [Connectives](/Connectives/): Conjunction, disjunction, and implication
  - [Negation](/Negation/): Negation, with intuitionistic and classical logic
  - [Quantifiers](/Quantifiers/): Universals and existentials
  - [Decidable](/Decidable/): Booleans and decision procedures
  - [Lists](/Lists/): Lists and higher-order functions
--->

{%- assign Naturals = site.pages | where:"permalink", "/Naturals/"  | first -%}
{%- assign Induction = site.pages | where:"permalink", "/Induction/"  | first -%}
{%- assign Relations = site.pages | where:"permalink", "/Relations/"  | first -%}
{%- assign Equality = site.pages | where:"permalink", "/Equality/"  | first -%}
{%- assign Isomorphism = site.pages | where:"permalink", "/Isomorphism/"  | first -%}
{%- assign Connectives = site.pages | where:"permalink", "/Connectives/"  | first -%}
{%- assign Negation = site.pages | where:"permalink", "/Negation/"  | first -%}
{%- assign Quantifiers = site.pages | where:"permalink", "/Quantifiers/"  | first -%}
{%- assign Decidable = site.pages | where:"permalink", "/Decidable/"  | first -%}
{%- assign Lists = site.pages | where:"permalink", "/Lists/"  | first -%}

## 第一分册：逻辑基础

  - [Naturals]({{ site.baseurl }}/Naturals/): 自然数 <span class = "progress" >{{ Naturals.progress | ceil }}</span>
  - [Induction]({{ site.baseurl }}/Induction/): 归纳证明 <span class = "progress" >{{ Induction.progress | ceil }}</span>
  - [Relations]({{ site.baseurl }}/Relations/): 关系的归纳定义 <span class = "progress" >{{ Relations.progress | ceil }}</span>
  - [Equality]({{ site.baseurl }}/Equality/): 相等性与等式推理 <span class = "progress" >{{ Equality.progress | ceil }}</span>
  - [Isomorphism]({{ site.baseurl }}/Isomorphism/): 同构与嵌入 <span class = "progress" >{{ Isomorphism.progress | ceil }}</span>
  - [Connectives]({{ site.baseurl }}/Connectives/): 合取、析取和蕴含 <span class = "progress" >{{ Connectives.progress | ceil }}</span>
  - [Negation]({{ site.baseurl }}/Negation/): 直觉逻辑与命题逻辑中的否定 <span class = "progress" >{{ Negation.progress | ceil }}</span>
  - [Quantifiers]({{ site.baseurl }}/Quantifiers/): 全称量词与存在量词 <span class = "progress" >{{ Quantifiers.progress | ceil }}</span>
  - [Decidable]({{ site.baseurl }}/Decidable/): 布尔值与判定过程 <span class = "progress" >{{ Decidable.progress | ceil }}</span>
  - [Lists]({{ site.baseurl }}/Lists/): 列表与高阶函数 <span class = "progress" >{{ Lists.progress | ceil }}</span>

<!---
Part 2: Programming Language Foundations

  - [Lambda]({{ site.baseurl }}/Lambda/): Introduction to Lambda Calculus
  - [Properties]({{ site.baseurl }}/Properties/): Progress and Preservation
  - [DeBruijn]({{ site.baseurl }}/DeBruijn/): Inherently typed De Bruijn representation
  - [More]({{ site.baseurl }}/More/): Additional constructs of simply-typed lambda calculus
  - [Bisimulation]({{ site.baseurl }}/Bisimulation/) : Relating reductions systems
  - [Inference]({{ site.baseurl }}/Inference/): Bidirectional type inference
  - [Untyped]({{ site.baseurl }}/Untyped/): Untyped lambda calculus with full normalisation
--->

{%- assign Lambda = site.pages | where:"permalink", "/Lambda/"  | first -%}
{%- assign Properties = site.pages | where:"permalink", "/Properties/"  | first -%}
{%- assign DeBruijn = site.pages | where:"permalink", "/DeBruijn/"  | first -%}
{%- assign More = site.pages | where:"permalink", "/More/"  | first -%}
{%- assign Bisimulation = site.pages | where:"permalink", "/Bisimulation/"  | first -%}
{%- assign Inference = site.pages | where:"permalink", "/Inference/"  | first -%}
{%- assign Untyped = site.pages | where:"permalink", "/Untyped/"  | first -%}

## 第二分册：编程语言基础

  - [Lambda]({{ site.baseurl }}/Lambda/): λ-演算简介 <span class = "progress" >{{ Lambda.progress | ceil }}</span>
  - [Properties]({{ site.baseurl }}/Properties/): 可进性与保型性 <span class = "progress" >{{ Properties.progress | ceil }}</span>
  - [DeBruijn]({{ site.baseurl }}/DeBruijn/): 固有类型的 De Bruijn 表示 <span class = "progress" >{{ DeBruijn.progress | ceil }}</span>
  - [More]({{ site.baseurl }}/More/): 简单类型 λ-演算的附加构造 <span class = "progress" >{{ More.progress | ceil }}</span>
  - [Bisimulation]({{ site.baseurl }}/Bisimulation/) : 关系归约系统 <span class = "progress" >{{ Bisimulation.progress | ceil }}</span>
  - [Inference]({{ site.baseurl }}/Inference/): 双向类型推断 <span class = "progress" >{{ Inference.progress | ceil }}</span>
  - [Untyped]({{ site.baseurl }}/Untyped/): 无类型 λ-演算及其完整范式 <span class = "progress" >{{ Untyped.progress | ceil }}</span>

<!---
Backmatter

  - [Acknowledgements]({{ site.baseurl }}/Acknowledgements/)
  - [Fonts]({{ site.baseurl }}/Fonts/): Test page for fonts
  - [Statistics]({{ site.baseurl }}/Statistics/): Line counts for each chapter
--->

{%- assign Acknowledgements = site.pages | where:"permalink", "/Acknowledgements/"  | first -%}
{%- assign Fonts = site.pages | where:"permalink", "/Fonts/"  | first -%}
{%- assign Statistics = site.pages | where:"permalink", "/Statistics/"  | first -%}

## 后记

  - [Acknowledgements]({{ site.baseurl }}/Acknowledgements/): 鸣谢 <span class = "progress" >{{ Acknowledgements.progress | ceil }}</span>
  - [Fonts]({{ site.baseurl }}/Fonts/): 字体测试页 <span class = "progress" >{{ Fonts.progress | ceil }}</span>
  - [Statistics]({{ site.baseurl }}/Statistics/): 每章行数统计 <span class = "progress" >{{ Statistics.progress | ceil }}</span>

<!---
Related
--->

## 相关资源

  - A paper describing the book appears in [SBMF][sbmf].
  - Courses taught from the textbook:
    * Philip Wadler, University of Edinburgh,
      [2018](http://plfa.inf.ed.ac.uk/TSPL/)
    * David Darais, University of Vermont,
      [2018](http://david.darais.com/courses/fa2018-cs295A/)
    * John Leo, Google Seattle, 2018--2019

[wen]: https://github.com/wenkokke
[phil]: https://homepages.inf.ed.ac.uk/wadler/
[GitHub]: https://github.com/plfa/plfa.github.io/
[sbmf]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
[PLFA]: https://plfa.github.io/
[PLFA-zh]: https://github.com/Agda-zh/PLFA-zh
[Issue]: https://github.com/Agda-zh/plfa-zh/issues
