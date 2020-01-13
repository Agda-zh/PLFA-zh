---
title          : Table of Contents (Beta)
layout         : page
permalink      : /beta/
---

This book is an introduction to programming language theory using the
proof assistant Agda.

Comments on all matters---organisation, material to add, material to
remove, parts that require better explanation, good exercises, errors,
and typos---are welcome.  The book repository is on [GitHub].
Pull requests are encouraged.

## Front matter

  - [Dedication]({{ site.baseurl }}/Dedication/)
  - [Preface]({{ site.baseurl }}/Preface/)

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

## Part 2: Operational Semantics

  - [Lambda]({{ site.baseurl }}/Lambda/): Introduction to Lambda Calculus
  - [Properties]({{ site.baseurl }}/Properties/): Progress and Preservation
  - [DeBruijn]({{ site.baseurl }}/DeBruijn/): Intrinsically-typed de Bruijn representation
  - [More]({{ site.baseurl }}/More/): Additional constructs of simply-typed lambda calculus
  - [Bisimulation]({{ site.baseurl }}/Bisimulation/): Relating reductions systems
  - [Inference]({{ site.baseurl }}/Inference/): Bidirectional type inference
  - [Untyped]({{ site.baseurl }}/Untyped/): Untyped lambda calculus with full normalisation
  - [Confluence]({{ site.baseurl }}/Confluence/): Confluence of untyped lambda calculus 🚧
  - [BigStep]({{ site.baseurl }}/BigStep/): Big-step semantics of untyped lambda calculus 🚧

## Part 3: Denotational Semantics

  - [Denotational]({{ site.baseurl }}/Denotational/): Denotational semantics of untyped lambda calculus 🚧
  - [Compositional]({{ site.baseurl }}/Compositional/): The denotational semantics is compositional 🚧
  - [Soundness]({{ site.baseurl }}/Soundness/): Soundness of reduction with respect to denotational semantics 🚧
  - [Adequacy]({{ site.baseurl }}/Adequacy/): Adequacy of denotational semantics with respect to operational semantics 🚧
  - [ContextualEquivalence]({{ site.baseurl }}/ContextualEquivalence/): Denotational equality implies contextual equivalence 🚧

## Appendix

  - [Substitution]({{ site.baseurl }}/Substitution/): Substitution in untyped lambda calculus

## Backmatter

  - [Acknowledgements]({{ site.baseurl }}/Acknowledgements/)
  - [Fonts]({{ site.baseurl }}/Fonts/): Test page for fonts
  - [Statistics]({{ site.baseurl }}/Statistics/): Line counts for each chapter

## Related

  - Courses taught from the textbook:
    * Philip Wadler, University of Edinburgh,
      [2018]({{ site.baseurl }}/TSPL/2018/),
	  [2019]({{ site.baseurl }}/TSPL/2019/)
    * David Darais, University of Vermont,
      [2018](http://david.darais.com/courses/fa2018-cs295A/)
    * John Leo, Google Seattle, 2018--2019
    * Philip Wadler, Pontifícia Universidade Católica do Rio de Janeiro (PUC-Rio),
      [2019]({{ site.baseurl }}/PUC/2019/)
    * Prabhakar Ragde, University of Waterloo,
      [2019](https://cs.uwaterloo.ca/~plragde/842/)
    * Jeremy Siek, Indiana University,
	  [2020](https://jsiek.github.io/B522-PL-Foundations/)
  - A paper describing the book appeared in [SBMF][sbmf].

[wen]: https://wenkokke.github.io
[phil]: https://homepages.inf.ed.ac.uk/wadler/
[jeremy]: http://homes.sice.indiana.edu/jsiek/
[GitHub]: https://github.com/plfa/plfa.github.io/
[sbmf]: https://homepages.inf.ed.ac.uk/wadler/topics/agda.html#sbmf
