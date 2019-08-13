---
src       : "src/plfa/Lambda.lagda.md"
title     : "Lambda: Introduction to Lambda Calculus"
layout    : page
prev      : /Lists/
permalink : /Lambda/
next      : /Properties/
---

{% raw %}<pre class="Agda"><a id="151" class="Keyword">module</a> <a id="158" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}" class="Module">plfa.Lambda</a> <a id="170" class="Keyword">where</a>
</pre>{% endraw %}
The _lambda-calculus_, first published by the logician Alonzo Church in
1932, is a core calculus with only three syntactic constructs:
variables, abstraction, and application.  It captures the key concept of
_functional abstraction_, which appears in pretty much every programming
language, in the form of either functions, procedures, or methods.
The _simply-typed lambda calculus_ (or STLC) is a variant of the
lambda calculus published by Church in 1940.  It has the three
constructs above for function types, plus whatever else is required
for base types. Church had a minimal base type with no operations.
We will instead echo Plotkin's _Programmable Computable
Functions_ (PCF), and add operations on natural numbers and
recursive function definitions.

This chapter formalises the simply-typed lambda calculus, giving its
syntax, small-step semantics, and typing rules.  The next chapter
[Properties]({{ site.baseurl }}/Properties/)
proves its main properties, including
progress and preservation.  Following chapters will look at a number
of variants of lambda calculus.

Be aware that the approach we take here is _not_ our recommended
approach to formalisation.  Using de Bruijn indices and
inherently-typed terms, as we will do in
Chapter [DeBruijn]({{ site.baseurl }}/DeBruijn/),
leads to a more compact formulation.  Nonetheless, we begin with named
variables, partly because such terms are easier to read and partly
because the development is more traditional.

The development in this chapter was inspired by the corresponding
development in Chapter _Stlc_ of _Software Foundations_
(_Programming Language Foundations_).  We differ by
representing contexts explicitly (as lists pairing identifiers with
types) rather than as partial maps (which take identifiers to types),
which corresponds better to our subsequent development of DeBruijn
notation. We also differ by taking natural numbers as the base type
rather than booleans, allowing more sophisticated examples. In
particular, we will be able to show (twice!) that two plus two is
four.

## Imports

{% raw %}<pre class="Agda"><a id="2256" class="Keyword">open</a> <a id="2261" class="Keyword">import</a> <a id="2268" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="2306" class="Keyword">using</a> <a id="2312" class="Symbol">(</a><a id="2313" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="2316" class="Symbol">;</a> <a id="2318" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">_≢_</a><a id="2321" class="Symbol">;</a> <a id="2323" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="2327" class="Symbol">)</a>
<a id="2329" class="Keyword">open</a> <a id="2334" class="Keyword">import</a> <a id="2341" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.html" class="Module">Data.String</a> <a id="2353" class="Keyword">using</a> <a id="2359" class="Symbol">(</a><a id="2360" href="Agda.Builtin.String.html#206" class="Postulate">String</a><a id="2366" class="Symbol">;</a> <a id="2368" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">_≟_</a><a id="2371" class="Symbol">)</a>
<a id="2373" class="Keyword">open</a> <a id="2378" class="Keyword">import</a> <a id="2385" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="2394" class="Keyword">using</a> <a id="2400" class="Symbol">(</a><a id="2401" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="2402" class="Symbol">;</a> <a id="2404" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="2408" class="Symbol">;</a> <a id="2410" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="2413" class="Symbol">)</a>
<a id="2415" class="Keyword">open</a> <a id="2420" class="Keyword">import</a> <a id="2427" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html" class="Module">Data.Empty</a> <a id="2438" class="Keyword">using</a> <a id="2444" class="Symbol">(</a><a id="2445" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a><a id="2446" class="Symbol">;</a> <a id="2448" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a><a id="2454" class="Symbol">)</a>
<a id="2456" class="Keyword">open</a> <a id="2461" class="Keyword">import</a> <a id="2468" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html" class="Module">Relation.Nullary</a> <a id="2485" class="Keyword">using</a> <a id="2491" class="Symbol">(</a><a id="2492" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#605" class="Datatype">Dec</a><a id="2495" class="Symbol">;</a> <a id="2497" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a><a id="2500" class="Symbol">;</a> <a id="2502" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a><a id="2504" class="Symbol">;</a> <a id="2506" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬_</a><a id="2508" class="Symbol">)</a>
<a id="2510" class="Keyword">open</a> <a id="2515" class="Keyword">import</a> <a id="2522" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.html" class="Module">Data.List</a> <a id="2532" class="Keyword">using</a> <a id="2538" class="Symbol">(</a><a id="2539" href="Agda.Builtin.List.html#121" class="Datatype">List</a><a id="2543" class="Symbol">;</a> <a id="2545" href="Agda.Builtin.List.html#173" class="InductiveConstructor Operator">_∷_</a><a id="2548" class="Symbol">;</a> <a id="2550" href="https://agda.github.io/agda-stdlib/v1.1/Data.List.Base.html#8786" class="InductiveConstructor">[]</a><a id="2552" class="Symbol">)</a>
</pre>{% endraw %}
## Syntax of terms

Terms have seven constructs. Three are for the core lambda calculus:

  * Variables `` ` x ``
  * Abstractions `ƛ x ⇒ N`
  * Applications `L · M`

Three are for the naturals:

  * Zero `` `zero ``
  * Successor `` `suc ``
  * Case `` case L [zero⇒ M |suc x ⇒ N ] ``

And one is for recursion:

  * Fixpoint `μ x ⇒ M`

Abstraction is also called _lambda abstraction_, and is the construct
from which the calculus takes its name.

With the exception of variables and fixpoints, each term
form either constructs a value of a given type (abstractions yield functions,
zero and successor yield natural numbers) or deconstructs it (applications use functions,
case terms use naturals). We will see this again when we come
to the rules for assigning types to terms, where constructors
correspond to introduction rules and deconstructors to eliminators.

Here is the syntax of terms in Backus-Naur Form (BNF):

    L, M, N  ::=
      ` x  |  ƛ x ⇒ N  |  L · M  |
      `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
      μ x ⇒ M

And here it is formalised in Agda:
{% raw %}<pre class="Agda"><a id="Id"></a><a id="3647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3647" class="Function">Id</a> <a id="3650" class="Symbol">:</a> <a id="3652" class="PrimitiveType">Set</a>
<a id="3656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3647" class="Function">Id</a> <a id="3659" class="Symbol">=</a> <a id="3661" href="Agda.Builtin.String.html#206" class="Postulate">String</a>

<a id="3669" class="Keyword">infix</a>  <a id="3676" class="Number">5</a>  <a id="3679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ_⇒_</a>
<a id="3684" class="Keyword">infix</a>  <a id="3691" class="Number">5</a>  <a id="3694" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4035" class="InductiveConstructor Operator">μ_⇒_</a>
<a id="3699" class="Keyword">infixl</a> <a id="3706" class="Number">7</a>  <a id="3709" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33660" class="InductiveConstructor Operator">_·_</a>
<a id="3713" class="Keyword">infix</a>  <a id="3720" class="Number">8</a>  <a id="3723" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc_</a>
<a id="3729" class="Keyword">infix</a>  <a id="3736" class="Number">9</a>  <a id="3739" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`_</a>

<a id="3743" class="Keyword">data</a> <a id="Term"></a><a id="3748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3748" class="Datatype">Term</a> <a id="3753" class="Symbol">:</a> <a id="3755" class="PrimitiveType">Set</a> <a id="3759" class="Keyword">where</a>
  <a id="Term.`_"></a><a id="3767" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`_</a>                      <a id="3791" class="Symbol">:</a>  <a id="3794" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="3797" class="Symbol">→</a> <a id="3799" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
  <a id="Term.ƛ_⇒_"></a><a id="3806" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ_⇒_</a>                    <a id="3830" class="Symbol">:</a>  <a id="3833" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="3836" class="Symbol">→</a> <a id="3838" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="3843" class="Symbol">→</a> <a id="3845" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
  <a id="Term._·_"></a><a id="3852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">_·_</a>                     <a id="3876" class="Symbol">:</a>  <a id="3879" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="3884" class="Symbol">→</a> <a id="3886" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="3891" class="Symbol">→</a> <a id="3893" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
  <a id="Term.`zero"></a><a id="3900" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3900" class="InductiveConstructor">`zero</a>                   <a id="3924" class="Symbol">:</a>  <a id="3927" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
  <a id="Term.`suc_"></a><a id="3934" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc_</a>                   <a id="3958" class="Symbol">:</a>  <a id="3961" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="3966" class="Symbol">→</a> <a id="3968" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
  <a id="Term.case_[zero⇒_|suc_⇒_]"></a><a id="3975" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case_[zero⇒_|suc_⇒_]</a>    <a id="3999" class="Symbol">:</a>  <a id="4002" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="4007" class="Symbol">→</a> <a id="4009" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="4014" class="Symbol">→</a> <a id="4016" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="4019" class="Symbol">→</a> <a id="4021" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="4026" class="Symbol">→</a> <a id="4028" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
  <a id="Term.μ_⇒_"></a><a id="4035" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4035" class="InductiveConstructor Operator">μ_⇒_</a>                    <a id="4059" class="Symbol">:</a>  <a id="4062" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="4065" class="Symbol">→</a> <a id="4067" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="4072" class="Symbol">→</a> <a id="4074" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
</pre>{% endraw %}We represent identifiers by strings.  We choose precedence so that
lambda abstraction and fixpoint bind least tightly, then application,
then successor, and tightest of all is the constructor for variables.
Case expressions are self-bracketing.


### Example terms

Here are some example terms: the natural number two,
a function that adds naturals,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="two"></a><a id="4476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4476" class="Function">two</a> <a id="4480" class="Symbol">:</a> <a id="4482" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="4487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4476" class="Function">two</a> <a id="4491" class="Symbol">=</a> <a id="4493" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="4498" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="4503" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>

<a id="plus"></a><a id="4510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4510" class="Function">plus</a> <a id="4515" class="Symbol">:</a> <a id="4517" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="4522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4510" class="Function">plus</a> <a id="4527" class="Symbol">=</a> <a id="4529" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">μ</a> <a id="4531" class="String">&quot;+&quot;</a> <a id="4535" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="4537" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="4539" class="String">&quot;m&quot;</a> <a id="4543" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="4545" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="4547" class="String">&quot;n&quot;</a> <a id="4551" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
         <a id="4562" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="4567" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="4569" class="String">&quot;m&quot;</a>
           <a id="4584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="4591" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="4593" class="String">&quot;n&quot;</a>
           <a id="4608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">|suc</a> <a id="4613" class="String">&quot;m&quot;</a> <a id="4617" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="4619" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="4624" class="Symbol">(</a><a id="4625" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="4627" class="String">&quot;+&quot;</a> <a id="4631" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="4633" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="4635" class="String">&quot;m&quot;</a> <a id="4639" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="4641" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="4643" class="String">&quot;n&quot;</a><a id="4646" class="Symbol">)</a> <a id="4648" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>
</pre>{% endraw %}The recursive definition of addition is similar to our original
definition of `_+_` for naturals, as given in
Chapter [Naturals]({{ site.baseurl }}/Naturals/#plus).
Here variable "m" is bound twice, once in a lambda abstraction and once in
the successor branch of the case; the first use of "m" refers to
the former and the second to the latter.  Any use of "m" in the successor branch
must refer to the latter binding, and so we say that the latter binding _shadows_
the former.  Later we will confirm that two plus two is four, in other words that
the term

    plus · two · two

reduces to `` `suc `suc `suc `suc `zero ``.

As a second example, we use higher-order functions to represent
natural numbers.  In particular, the number _n_ is represented by a
function that accepts two arguments and applies the first _n_ times to the
second.  This is called the _Church representation_ of the
naturals.  Here are some example terms: the Church numeral two, a
function that adds Church numerals, a function to compute successor,
and a term that computes two plus two:
{% raw %}<pre class="Agda"><a id="twoᶜ"></a><a id="5725" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5725" class="Function">twoᶜ</a> <a id="5730" class="Symbol">:</a> <a id="5732" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="5737" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5725" class="Function">twoᶜ</a> <a id="5742" class="Symbol">=</a>  <a id="5745" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5747" class="String">&quot;s&quot;</a> <a id="5751" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="5753" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5755" class="String">&quot;z&quot;</a> <a id="5759" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="5761" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5763" class="String">&quot;s&quot;</a> <a id="5767" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="5769" class="Symbol">(</a><a id="5770" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5772" class="String">&quot;s&quot;</a> <a id="5776" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="5778" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5780" class="String">&quot;z&quot;</a><a id="5783" class="Symbol">)</a>

<a id="plusᶜ"></a><a id="5786" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5786" class="Function">plusᶜ</a> <a id="5792" class="Symbol">:</a> <a id="5794" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="5799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5786" class="Function">plusᶜ</a> <a id="5805" class="Symbol">=</a>  <a id="5808" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5810" class="String">&quot;m&quot;</a> <a id="5814" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="5816" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5818" class="String">&quot;n&quot;</a> <a id="5822" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="5824" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5826" class="String">&quot;s&quot;</a> <a id="5830" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="5832" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5834" class="String">&quot;z&quot;</a> <a id="5838" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
         <a id="5849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="5851" class="String">&quot;m&quot;</a> <a id="5855" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="5857" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5859" class="String">&quot;s&quot;</a> <a id="5863" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="5865" class="Symbol">(</a><a id="5866" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5868" class="String">&quot;n&quot;</a> <a id="5872" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="5874" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5876" class="String">&quot;s&quot;</a> <a id="5880" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="5882" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5884" class="String">&quot;z&quot;</a><a id="5887" class="Symbol">)</a>

<a id="sucᶜ"></a><a id="5890" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5890" class="Function">sucᶜ</a> <a id="5895" class="Symbol">:</a> <a id="5897" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="5902" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5890" class="Function">sucᶜ</a> <a id="5907" class="Symbol">=</a> <a id="5909" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="5911" class="String">&quot;n&quot;</a> <a id="5915" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="5917" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="5922" class="Symbol">(</a><a id="5923" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="5925" class="String">&quot;n&quot;</a><a id="5928" class="Symbol">)</a>
</pre>{% endraw %}The Church numeral for two takes two arguments `s` and `z`
and applies `s` twice to `z`.
Addition takes two numerals `m` and `n`, a
function `s` and an argument `z`, and it uses `m` to apply `s` to the
result of using `n` to apply `s` to `z`; hence `s` is applied `m` plus
`n` times to `z`, yielding the Church numeral for the sum of `m` and
`n`.  For convenience, we define a function that computes successor.
To convert a Church numeral to the corresponding natural, we apply
it to the `sucᶜ` function and the natural number zero.
Again, later we will confirm that two plus two is four,
in other words that the term

    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

reduces to `` `suc `suc `suc `suc `zero ``.


#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.  Your definition may use `plus` as
defined earlier.

{% raw %}<pre class="Agda"><a id="6810" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ`

Write out the definition of a lambda term that multiplies
two natural numbers represented as Church numerals. Your
definition may use `plusᶜ` as defined earlier (or may not
— there are nice definitions both ways).

{% raw %}<pre class="Agda"><a id="7080" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `primed` (stretch)

Some people find it annoying to write `` ` "x" `` instead of `x`.
We can make examples with lambda terms slightly easier to write
by adding the following definitions:
{% raw %}<pre class="Agda"><a id="ƛ′_⇒_"></a><a id="7314" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7314" class="Function Operator">ƛ′_⇒_</a> <a id="7320" class="Symbol">:</a> <a id="7322" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7327" class="Symbol">→</a> <a id="7329" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7334" class="Symbol">→</a> <a id="7336" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="7341" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7314" class="Function Operator">ƛ′</a> <a id="7344" class="Symbol">(</a><a id="7345" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="7347" href="plfa.Lambda.html#7347" class="Bound">x</a><a id="7348" class="Symbol">)</a> <a id="7350" href="plfa.Lambda.html#7314" class="Function Operator">⇒</a> <a id="7352" href="plfa.Lambda.html#7352" class="Bound">N</a>  <a id="7355" class="Symbol">=</a>  <a id="7358" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="7360" href="plfa.Lambda.html#7347" class="Bound">x</a> <a id="7362" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="7364" href="plfa.Lambda.html#7352" class="Bound">N</a>
<a id="7366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7314" class="CatchallClause Function Operator">ƛ′</a><a id="7368" class="CatchallClause"> </a><a id="7369" class="CatchallClause Symbol">_</a><a id="7370" class="CatchallClause"> </a><a id="7371" href="plfa.Lambda.html#7314" class="CatchallClause Function Operator">⇒</a><a id="7372" class="CatchallClause"> </a><a id="7373" class="CatchallClause Symbol">_</a>      <a id="7380" class="Symbol">=</a>  <a id="7383" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7390" href="plfa.Lambda.html#7419" class="Postulate">impossible</a>
  <a id="7403" class="Keyword">where</a> <a id="7409" class="Keyword">postulate</a> <a id="7419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7419" class="Postulate">impossible</a> <a id="7430" class="Symbol">:</a> <a id="7432" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="case′_[zero⇒_|suc_⇒_]"></a><a id="7435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7435" class="Function Operator">case′_[zero⇒_|suc_⇒_]</a> <a id="7457" class="Symbol">:</a> <a id="7459" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7464" class="Symbol">→</a> <a id="7466" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7471" class="Symbol">→</a> <a id="7473" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7478" class="Symbol">→</a> <a id="7480" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7485" class="Symbol">→</a> <a id="7487" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="7492" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7435" class="Function Operator">case′</a> <a id="7498" href="plfa.Lambda.html#7498" class="Bound">L</a> <a id="7500" href="plfa.Lambda.html#7435" class="Function Operator">[zero⇒</a> <a id="7507" href="plfa.Lambda.html#7507" class="Bound">M</a> <a id="7509" href="plfa.Lambda.html#7435" class="Function Operator">|suc</a> <a id="7514" class="Symbol">(</a><a id="7515" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="7517" href="plfa.Lambda.html#7517" class="Bound">x</a><a id="7518" class="Symbol">)</a> <a id="7520" href="plfa.Lambda.html#7435" class="Function Operator">⇒</a> <a id="7522" href="plfa.Lambda.html#7522" class="Bound">N</a> <a id="7524" href="plfa.Lambda.html#7435" class="Function Operator">]</a>  <a id="7527" class="Symbol">=</a>  <a id="7530" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">case</a> <a id="7535" href="plfa.Lambda.html#7498" class="Bound">L</a> <a id="7537" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="7544" href="plfa.Lambda.html#7507" class="Bound">M</a> <a id="7546" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="7551" href="plfa.Lambda.html#7517" class="Bound">x</a> <a id="7553" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="7555" href="plfa.Lambda.html#7522" class="Bound">N</a> <a id="7557" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>
<a id="7559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7435" class="CatchallClause Function Operator">case′</a><a id="7564" class="CatchallClause"> </a><a id="7565" class="CatchallClause Symbol">_</a><a id="7566" class="CatchallClause"> </a><a id="7567" href="plfa.Lambda.html#7435" class="CatchallClause Function Operator">[zero⇒</a><a id="7573" class="CatchallClause"> </a><a id="7574" class="CatchallClause Symbol">_</a><a id="7575" class="CatchallClause"> </a><a id="7576" href="plfa.Lambda.html#7435" class="CatchallClause Function Operator">|suc</a><a id="7580" class="CatchallClause"> </a><a id="7581" class="CatchallClause Symbol">_</a><a id="7582" class="CatchallClause"> </a><a id="7583" href="plfa.Lambda.html#7435" class="CatchallClause Function Operator">⇒</a><a id="7584" class="CatchallClause"> </a><a id="7585" class="CatchallClause Symbol">_</a><a id="7586" class="CatchallClause"> </a><a id="7587" href="plfa.Lambda.html#7435" class="CatchallClause Function Operator">]</a>      <a id="7594" class="Symbol">=</a>  <a id="7597" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7604" href="plfa.Lambda.html#7633" class="Postulate">impossible</a>
  <a id="7617" class="Keyword">where</a> <a id="7623" class="Keyword">postulate</a> <a id="7633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7633" class="Postulate">impossible</a> <a id="7644" class="Symbol">:</a> <a id="7646" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>

<a id="μ′_⇒_"></a><a id="7649" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7649" class="Function Operator">μ′_⇒_</a> <a id="7655" class="Symbol">:</a> <a id="7657" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7662" class="Symbol">→</a> <a id="7664" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="7669" class="Symbol">→</a> <a id="7671" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="7676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7649" class="Function Operator">μ′</a> <a id="7679" class="Symbol">(</a><a id="7680" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="7682" href="plfa.Lambda.html#7682" class="Bound">x</a><a id="7683" class="Symbol">)</a> <a id="7685" href="plfa.Lambda.html#7649" class="Function Operator">⇒</a> <a id="7687" href="plfa.Lambda.html#7687" class="Bound">N</a>  <a id="7690" class="Symbol">=</a>  <a id="7693" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">μ</a> <a id="7695" href="plfa.Lambda.html#7682" class="Bound">x</a> <a id="7697" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="7699" href="plfa.Lambda.html#7687" class="Bound">N</a>
<a id="7701" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7649" class="CatchallClause Function Operator">μ′</a><a id="7703" class="CatchallClause"> </a><a id="7704" class="CatchallClause Symbol">_</a><a id="7705" class="CatchallClause"> </a><a id="7706" href="plfa.Lambda.html#7649" class="CatchallClause Function Operator">⇒</a><a id="7707" class="CatchallClause"> </a><a id="7708" class="CatchallClause Symbol">_</a>      <a id="7715" class="Symbol">=</a>  <a id="7718" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="7725" href="plfa.Lambda.html#7754" class="Postulate">impossible</a>
  <a id="7738" class="Keyword">where</a> <a id="7744" class="Keyword">postulate</a> <a id="7754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7754" class="Postulate">impossible</a> <a id="7765" class="Symbol">:</a> <a id="7767" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}The definition of `plus` can now be written as follows:
{% raw %}<pre class="Agda"><a id="plus′"></a><a id="7833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7833" class="Function">plus′</a> <a id="7839" class="Symbol">:</a> <a id="7841" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="7846" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7833" class="Function">plus′</a> <a id="7852" class="Symbol">=</a> <a id="7854" href="plfa.Lambda.html#7649" class="Function Operator">μ′</a> <a id="7857" href="plfa.Lambda.html#7964" class="Function">+</a> <a id="7859" href="plfa.Lambda.html#7649" class="Function Operator">⇒</a> <a id="7861" href="plfa.Lambda.html#7314" class="Function Operator">ƛ′</a> <a id="7864" href="plfa.Lambda.html#7978" class="Function">m</a> <a id="7866" href="plfa.Lambda.html#7314" class="Function Operator">⇒</a> <a id="7868" href="plfa.Lambda.html#7314" class="Function Operator">ƛ′</a> <a id="7871" href="plfa.Lambda.html#7992" class="Function">n</a> <a id="7873" href="plfa.Lambda.html#7314" class="Function Operator">⇒</a>
          <a id="7885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7435" class="Function Operator">case′</a> <a id="7891" href="plfa.Lambda.html#7978" class="Function">m</a>
            <a id="7905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7435" class="Function Operator">[zero⇒</a> <a id="7912" href="plfa.Lambda.html#7992" class="Function">n</a>
            <a id="7926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7435" class="Function Operator">|suc</a> <a id="7931" href="plfa.Lambda.html#7978" class="Function">m</a> <a id="7933" href="plfa.Lambda.html#7435" class="Function Operator">⇒</a> <a id="7935" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="7940" class="Symbol">(</a><a id="7941" href="plfa.Lambda.html#7964" class="Function">+</a> <a id="7943" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="7945" href="plfa.Lambda.html#7978" class="Function">m</a> <a id="7947" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="7949" href="plfa.Lambda.html#7992" class="Function">n</a><a id="7950" class="Symbol">)</a> <a id="7952" href="plfa.Lambda.html#7435" class="Function Operator">]</a>
  <a id="7956" class="Keyword">where</a>
  <a id="7964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7964" class="Function">+</a>  <a id="7967" class="Symbol">=</a>  <a id="7970" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="7972" class="String">&quot;+&quot;</a>
  <a id="7978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7978" class="Function">m</a>  <a id="7981" class="Symbol">=</a>  <a id="7984" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="7986" class="String">&quot;m&quot;</a>
  <a id="7992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#7992" class="Function">n</a>  <a id="7995" class="Symbol">=</a>  <a id="7998" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="8000" class="String">&quot;n&quot;</a>
</pre>{% endraw %}Write out the definition of multiplication in the same style.


### Formal vs informal

In informal presentation of formal semantics, one uses choice of
variable name to disambiguate and writes `x` rather than `` ` x ``
for a term that is a variable. Agda requires we distinguish.

Similarly, informal presentation often use the same notation for
function types, lambda abstraction, and function application in both
the _object language_ (the language one is describing) and the
_meta-language_ (the language in which the description is written),
trusting readers can use context to distinguish the two.  Agda is
not quite so forgiving, so here we use `ƛ x ⇒ N` and `L · M` for the
object language, as compared to `λ x → N` and `L M` in our
meta-language, Agda.


### Bound and free variables

In an abstraction `ƛ x ⇒ N` we call `x` the _bound_ variable
and `N` the _body_ of the abstraction.  A central feature
of lambda calculus is that consistent renaming of bound variables
leaves the meaning of a term unchanged.  Thus the five terms

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
* `` ƛ "f" ⇒ ƛ "x" ⇒ ` "f" · (` "f" · ` "x") ``
* `` ƛ "sam" ⇒ ƛ "zelda" ⇒ ` "sam" · (` "sam" · ` "zelda") ``
* `` ƛ "z" ⇒ ƛ "s" ⇒ ` "z" · (` "z" · ` "s") ``
* `` ƛ "😇" ⇒ ƛ "😈" ⇒ ` "😇" · (` "😇" · ` "😈" ) ``

are all considered equivalent.  Following the convention introduced
by Haskell Curry, who used the Greek letter `α` (_alpha_) to label such rules,
this equivalence relation is called _alpha renaming_.

As we descend from a term into its subterms, variables
that are bound may become free.  Consider the following terms:

* `` ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as bound variables.

* `` ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ``
  has `z` bound and `s` free.

* `` ` "s" · (` "s" · ` "z") ``
  has both `s` and `z` as free variables.

We say that a term with no free variables is _closed_; otherwise it is
_open_.  Of the three terms above, the first is closed and the other
two are open.  We will focus on reduction of closed terms.

Different occurrences of a variable may be bound and free.
In the term

    (ƛ "x" ⇒ ` "x") · ` "x"

the inner occurrence of `x` is bound while the outer occurrence is free.
By alpha renaming, the term above is equivalent to

    (ƛ "y" ⇒ ` "y") · ` "x"

in which `y` is bound and `x` is free.  A common convention, called the
_Barendregt convention_, is to use alpha renaming to ensure that the bound
variables in a term are distinct from the free variables, which can
avoid confusions that may arise if bound and free variables have the
same names.

Case and recursion also introduce bound variables, which are also subject
to alpha renaming. In the term

    μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

notice that there are two binding occurrences of `m`, one in the first
line and one in the last line.  It is equivalent to the following term,

    μ "plus" ⇒ ƛ "x" ⇒ ƛ "y" ⇒
      case ` "x"
        [zero⇒ ` "y"
        |suc "x′" ⇒ `suc (` "plus" · ` "x′" · ` "y") ]

where the two binding occurrences corresponding to `m` now have distinct
names, `x` and `x′`.


## Values

A _value_ is a term that corresponds to an answer.
Thus, `` `suc `suc `suc `suc `zero `` is a value,
while `` plus · two · two `` is not.
Following convention, we treat all function abstractions
as values; thus, `` plus `` by itself is considered a value.

The predicate `Value M` holds if term `M` is a value:

{% raw %}<pre class="Agda"><a id="11531" class="Keyword">data</a> <a id="Value"></a><a id="11536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="11542" class="Symbol">:</a> <a id="11544" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="11549" class="Symbol">→</a> <a id="11551" class="PrimitiveType">Set</a> <a id="11555" class="Keyword">where</a>

  <a id="Value.V-ƛ"></a><a id="11564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11564" class="InductiveConstructor">V-ƛ</a> <a id="11568" class="Symbol">:</a> <a id="11570" class="Symbol">∀</a> <a id="11572" class="Symbol">{</a><a id="11573" href="plfa.Lambda.html#11573" class="Bound">x</a> <a id="11575" href="plfa.Lambda.html#11575" class="Bound">N</a><a id="11576" class="Symbol">}</a>
      <a id="11584" class="Comment">---------------</a>
    <a id="11604" class="Symbol">→</a> <a id="11606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="11612" class="Symbol">(</a><a id="11613" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="11615" href="plfa.Lambda.html#11573" class="Bound">x</a> <a id="11617" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="11619" href="plfa.Lambda.html#11575" class="Bound">N</a><a id="11620" class="Symbol">)</a>

  <a id="Value.V-zero"></a><a id="11625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11625" class="InductiveConstructor">V-zero</a> <a id="11632" class="Symbol">:</a>
      <a id="11640" class="Comment">-----------</a>
      <a id="11658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="11664" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>

  <a id="Value.V-suc"></a><a id="11673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11673" class="InductiveConstructor">V-suc</a> <a id="11679" class="Symbol">:</a> <a id="11681" class="Symbol">∀</a> <a id="11683" class="Symbol">{</a><a id="11684" href="plfa.Lambda.html#11684" class="Bound">V</a><a id="11685" class="Symbol">}</a>
    <a id="11691" class="Symbol">→</a> <a id="11693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="11699" href="plfa.Lambda.html#11684" class="Bound">V</a>
      <a id="11707" class="Comment">--------------</a>
    <a id="11726" class="Symbol">→</a> <a id="11728" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="11734" class="Symbol">(</a><a id="11735" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="11740" href="plfa.Lambda.html#11684" class="Bound">V</a><a id="11741" class="Symbol">)</a>
</pre>{% endraw %}
In what follows, we let `V` and `W` range over values.


### Formal vs informal

In informal presentations of formal semantics, using
`V` as the name of a metavariable is sufficient to
indicate that it is a value. In Agda, we must explicitly
invoke the `Value` predicate.

### Other approaches

An alternative is not to focus on closed terms,
to treat variables as values, and to treat
`ƛ x ⇒ N` as a value only if `N` is a value.
Indeed, this is how Agda normalises terms.
We consider this approach in
Chapter [Untyped]({{ site.baseurl }}/Untyped/).


## Substitution

The heart of lambda calculus is the operation of
substituting one term for a variable in another term.
Substitution plays a key role in defining the
operational semantics of function application.
For instance, we have

      (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · sucᶜ · `zero
    —→
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · "z")) · `zero
    —→
      sucᶜ · (sucᶜ · `zero)

where we substitute `sucᶜ` for `` ` "s" `` and `` `zero `` for `` ` "z" ``
in the body of the function abstraction.

We write substitution as `N [ x := V ]`, meaning
"substitute term `V` for free occurrences of variable `x` in term `N`",
or, more compactly, "substitute `V` for `x` in `N`",
or equivalently, "in `N` replace `x` by `V`".
Substitution works if `V` is any closed term;
it need not be a value, but we use `V` since in fact we
usually substitute values.

Here are some examples:

* `` (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] `` yields
  `` ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z") ``.
* `` (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] `` yields
  `` sucᶜ · (sucᶜ · `zero) ``.
* `` (ƛ "x" ⇒ ` "y") [ "y" := `zero ] `` yields `` ƛ "x" ⇒ `zero ``.
* `` (ƛ "x" ⇒ ` "x") [ "x" := `zero ] `` yields `` ƛ "x" ⇒ ` "x" ``.
* `` (ƛ "y" ⇒ ` "y") [ "x" := `zero ] `` yields `` ƛ "y" ⇒ ` "y" ``.

In the last but one example, substituting `` `zero `` for `x` in
`` ƛ "x" ⇒ ` "x" `` does _not_ yield `` ƛ "x" ⇒ `zero ``,
since `x` is bound in the lambda abstraction.
The choice of bound names is irrelevant: both
`` ƛ "x" ⇒ ` "x" `` and `` ƛ "y" ⇒ ` "y" `` stand for the
identity function.  One way to think of this is that `x` within
the body of the abstraction stands for a _different_ variable than
`x` outside the abstraction, they just happen to have the same name.

We will give a definition of substitution that is only valid
when term substituted for the variable is closed. This is because
substitution by terms that are _not_ closed may require renaming
of bound variables. For example:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] `` should not yield <br/>
  `` (ƛ "x" ⇒ ` "x" · (` "x" · `zero)) ``.

Instead, we should rename the bound variable to avoid capture:

* `` (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] `` should yield <br/>
  `` ƛ "x′" ⇒ ` "x′" · (` "x" · `zero) ``.

Here `x′` is a fresh variable distinct from `x`.
Formal definition of substitution with suitable renaming is considerably
more complex, so we avoid it by restricting to substitution by closed terms,
which will be adequate for our purposes.

Here is the formal definition of substitution by closed terms in Agda:

{% raw %}<pre class="Agda"><a id="14902" class="Keyword">infix</a> <a id="14908" class="Number">9</a> <a id="14910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#14919" class="Function Operator">_[_:=_]</a>

<a id="_[_:=_]"></a><a id="14919" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#14919" class="Function Operator">_[_:=_]</a> <a id="14927" class="Symbol">:</a> <a id="14929" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="14934" class="Symbol">→</a> <a id="14936" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="14939" class="Symbol">→</a> <a id="14941" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="14946" class="Symbol">→</a> <a id="14948" href="plfa.Lambda.html#3748" class="Datatype">Term</a>
<a id="14953" class="Symbol">(</a><a id="14954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="14956" href="plfa.Lambda.html#14956" class="Bound">x</a><a id="14957" class="Symbol">)</a> <a id="14959" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="14961" href="plfa.Lambda.html#14961" class="Bound">y</a> <a id="14963" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="14966" href="plfa.Lambda.html#14966" class="Bound">V</a> <a id="14968" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="14970" class="Keyword">with</a> <a id="14975" href="plfa.Lambda.html#14956" class="Bound">x</a> <a id="14977" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="14979" href="plfa.Lambda.html#14961" class="Bound">y</a>
<a id="14981" class="Symbol">...</a> <a id="14985" class="Symbol">|</a> <a id="14987" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="14991" class="Symbol">_</a>          <a id="15002" class="Symbol">=</a>  <a id="15005" class="Bound">V</a>
<a id="15007" class="Symbol">...</a> <a id="15011" class="Symbol">|</a> <a id="15013" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15017" class="Symbol">_</a>          <a id="15028" class="Symbol">=</a>  <a id="15031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3767" class="InductiveConstructor Operator">`</a> <a id="15033" class="Bound">x</a>
<a id="15035" class="Symbol">(</a><a id="15036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="15038" href="plfa.Lambda.html#15038" class="Bound">x</a> <a id="15040" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="15042" href="plfa.Lambda.html#15042" class="Bound">N</a><a id="15043" class="Symbol">)</a> <a id="15045" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15047" href="plfa.Lambda.html#15047" class="Bound">y</a> <a id="15049" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15052" href="plfa.Lambda.html#15052" class="Bound">V</a> <a id="15054" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15056" class="Keyword">with</a> <a id="15061" href="plfa.Lambda.html#15038" class="Bound">x</a> <a id="15063" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15065" href="plfa.Lambda.html#15047" class="Bound">y</a>
<a id="15067" class="Symbol">...</a> <a id="15071" class="Symbol">|</a> <a id="15073" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15077" class="Symbol">_</a>          <a id="15088" class="Symbol">=</a>  <a id="15091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="15093" class="Bound">x</a> <a id="15095" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="15097" class="Bound">N</a>
<a id="15099" class="Symbol">...</a> <a id="15103" class="Symbol">|</a> <a id="15105" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15109" class="Symbol">_</a>          <a id="15120" class="Symbol">=</a>  <a id="15123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="15125" class="Bound">x</a> <a id="15127" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="15129" class="Bound">N</a> <a id="15131" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15133" class="Bound">y</a> <a id="15135" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15138" class="Bound">V</a> <a id="15140" href="plfa.Lambda.html#14919" class="Function Operator">]</a>
<a id="15142" class="Symbol">(</a><a id="15143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#15143" class="Bound">L</a> <a id="15145" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="15147" href="plfa.Lambda.html#15147" class="Bound">M</a><a id="15148" class="Symbol">)</a> <a id="15150" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15152" href="plfa.Lambda.html#15152" class="Bound">y</a> <a id="15154" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15157" href="plfa.Lambda.html#15157" class="Bound">V</a> <a id="15159" href="plfa.Lambda.html#14919" class="Function Operator">]</a>   <a id="15163" class="Symbol">=</a>  <a id="15166" href="plfa.Lambda.html#15143" class="Bound">L</a> <a id="15168" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15170" href="plfa.Lambda.html#15152" class="Bound">y</a> <a id="15172" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15175" href="plfa.Lambda.html#15157" class="Bound">V</a> <a id="15177" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15179" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="15181" href="plfa.Lambda.html#15147" class="Bound">M</a> <a id="15183" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15185" href="plfa.Lambda.html#15152" class="Bound">y</a> <a id="15187" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15190" href="plfa.Lambda.html#15157" class="Bound">V</a> <a id="15192" href="plfa.Lambda.html#14919" class="Function Operator">]</a>
<a id="15194" class="Symbol">(</a><a id="15195" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3900" class="InductiveConstructor">`zero</a><a id="15200" class="Symbol">)</a> <a id="15202" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15204" href="plfa.Lambda.html#15204" class="Bound">y</a> <a id="15206" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15209" href="plfa.Lambda.html#15209" class="Bound">V</a> <a id="15211" href="plfa.Lambda.html#14919" class="Function Operator">]</a>   <a id="15215" class="Symbol">=</a>  <a id="15218" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
<a id="15224" class="Symbol">(</a><a id="15225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="15230" href="plfa.Lambda.html#15230" class="Bound">M</a><a id="15231" class="Symbol">)</a> <a id="15233" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15235" href="plfa.Lambda.html#15235" class="Bound">y</a> <a id="15237" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15240" href="plfa.Lambda.html#15240" class="Bound">V</a> <a id="15242" href="plfa.Lambda.html#14919" class="Function Operator">]</a>  <a id="15245" class="Symbol">=</a>  <a id="15248" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="15253" href="plfa.Lambda.html#15230" class="Bound">M</a> <a id="15255" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15257" href="plfa.Lambda.html#15235" class="Bound">y</a> <a id="15259" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15262" href="plfa.Lambda.html#15240" class="Bound">V</a> <a id="15264" href="plfa.Lambda.html#14919" class="Function Operator">]</a>
<a id="15266" class="Symbol">(</a><a id="15267" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="15272" href="plfa.Lambda.html#15272" class="Bound">L</a> <a id="15274" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="15281" href="plfa.Lambda.html#15281" class="Bound">M</a> <a id="15283" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="15288" href="plfa.Lambda.html#15288" class="Bound">x</a> <a id="15290" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="15292" href="plfa.Lambda.html#15292" class="Bound">N</a> <a id="15294" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="15295" class="Symbol">)</a> <a id="15297" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15299" href="plfa.Lambda.html#15299" class="Bound">y</a> <a id="15301" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15304" href="plfa.Lambda.html#15304" class="Bound">V</a> <a id="15306" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15308" class="Keyword">with</a> <a id="15313" href="plfa.Lambda.html#15288" class="Bound">x</a> <a id="15315" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15317" href="plfa.Lambda.html#15299" class="Bound">y</a>
<a id="15319" class="Symbol">...</a> <a id="15323" class="Symbol">|</a> <a id="15325" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15329" class="Symbol">_</a>          <a id="15340" class="Symbol">=</a>  <a id="15343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="15348" class="Bound">L</a> <a id="15350" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15352" class="Bound">y</a> <a id="15354" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15357" class="Bound">V</a> <a id="15359" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15361" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="15368" class="Bound">M</a> <a id="15370" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15372" class="Bound">y</a> <a id="15374" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15377" class="Bound">V</a> <a id="15379" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15381" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="15386" class="Bound">x</a> <a id="15388" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="15390" class="Bound">N</a> <a id="15392" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>
<a id="15394" class="Symbol">...</a> <a id="15398" class="Symbol">|</a> <a id="15400" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15404" class="Symbol">_</a>          <a id="15415" class="Symbol">=</a>  <a id="15418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="15423" class="Bound">L</a> <a id="15425" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15427" class="Bound">y</a> <a id="15429" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15432" class="Bound">V</a> <a id="15434" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15436" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="15443" class="Bound">M</a> <a id="15445" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15447" class="Bound">y</a> <a id="15449" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15452" class="Bound">V</a> <a id="15454" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15456" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="15461" class="Bound">x</a> <a id="15463" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="15465" class="Bound">N</a> <a id="15467" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15469" class="Bound">y</a> <a id="15471" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15474" class="Bound">V</a> <a id="15476" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15478" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>
<a id="15480" class="Symbol">(</a><a id="15481" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4035" class="InductiveConstructor Operator">μ</a> <a id="15483" href="plfa.Lambda.html#15483" class="Bound">x</a> <a id="15485" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="15487" href="plfa.Lambda.html#15487" class="Bound">N</a><a id="15488" class="Symbol">)</a> <a id="15490" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15492" href="plfa.Lambda.html#15492" class="Bound">y</a> <a id="15494" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15497" href="plfa.Lambda.html#15497" class="Bound">V</a> <a id="15499" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="15501" class="Keyword">with</a> <a id="15506" href="plfa.Lambda.html#15483" class="Bound">x</a> <a id="15508" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="15510" href="plfa.Lambda.html#15492" class="Bound">y</a>
<a id="15512" class="Symbol">...</a> <a id="15516" class="Symbol">|</a> <a id="15518" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="15522" class="Symbol">_</a>          <a id="15533" class="Symbol">=</a>  <a id="15536" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4035" class="InductiveConstructor Operator">μ</a> <a id="15538" class="Bound">x</a> <a id="15540" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="15542" class="Bound">N</a>
<a id="15544" class="Symbol">...</a> <a id="15548" class="Symbol">|</a> <a id="15550" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="15554" class="Symbol">_</a>          <a id="15565" class="Symbol">=</a>  <a id="15568" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4035" class="InductiveConstructor Operator">μ</a> <a id="15570" class="Bound">x</a> <a id="15572" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="15574" class="Bound">N</a> <a id="15576" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="15578" class="Bound">y</a> <a id="15580" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="15583" class="Bound">V</a> <a id="15585" href="plfa.Lambda.html#14919" class="Function Operator">]</a>
</pre>{% endraw %}
Let's unpack the first three cases:

* For variables, we compare `y`, the substituted variable,
with `x`, the variable in the term. If they are the same,
we yield `V`, otherwise we yield `x` unchanged.

* For abstractions, we compare `y`, the substituted variable,
with `x`, the variable bound in the abstraction. If they are the same,
we yield the abstraction unchanged, otherwise we substitute inside the body.

* For application, we recursively substitute in the function
and the argument.

Case expressions and recursion also have bound variables that are
treated similarly to those in lambda abstractions.  Otherwise we
simply push substitution recursively into the subterms.


### Examples

Here is confirmation that the examples above are correct:

{% raw %}<pre class="Agda"><a id="16352" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16352" class="Function">_</a> <a id="16354" class="Symbol">:</a> <a id="16356" class="Symbol">(</a><a id="16357" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16359" class="String">&quot;z&quot;</a> <a id="16363" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16365" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16367" class="String">&quot;s&quot;</a> <a id="16371" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16373" class="Symbol">(</a><a id="16374" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16376" class="String">&quot;s&quot;</a> <a id="16380" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16382" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16384" class="String">&quot;z&quot;</a><a id="16387" class="Symbol">))</a> <a id="16390" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="16392" class="String">&quot;s&quot;</a> <a id="16396" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="16399" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16404" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="16406" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16408" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16410" class="String">&quot;z&quot;</a> <a id="16414" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16416" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16421" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16423" class="Symbol">(</a><a id="16424" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16429" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16431" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16433" class="String">&quot;z&quot;</a><a id="16436" class="Symbol">)</a>
<a id="16438" class="Symbol">_</a> <a id="16440" class="Symbol">=</a> <a id="16442" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16448" class="Function">_</a> <a id="16450" class="Symbol">:</a> <a id="16452" class="Symbol">(</a><a id="16453" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16458" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16460" class="Symbol">(</a><a id="16461" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16466" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16468" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16470" class="String">&quot;z&quot;</a><a id="16473" class="Symbol">))</a> <a id="16476" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="16478" class="String">&quot;z&quot;</a> <a id="16482" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="16485" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="16491" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="16493" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16495" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16500" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16502" class="Symbol">(</a><a id="16503" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="16508" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="16510" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="16515" class="Symbol">)</a>
<a id="16517" class="Symbol">_</a> <a id="16519" class="Symbol">=</a> <a id="16521" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16527" class="Function">_</a> <a id="16529" class="Symbol">:</a> <a id="16531" class="Symbol">(</a><a id="16532" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16534" class="String">&quot;x&quot;</a> <a id="16538" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16540" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16542" class="String">&quot;y&quot;</a><a id="16545" class="Symbol">)</a> <a id="16547" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="16549" class="String">&quot;y&quot;</a> <a id="16553" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="16556" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="16562" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="16564" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16566" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16568" class="String">&quot;x&quot;</a> <a id="16572" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16574" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
<a id="16580" class="Symbol">_</a> <a id="16582" class="Symbol">=</a> <a id="16584" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16590" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16590" class="Function">_</a> <a id="16592" class="Symbol">:</a> <a id="16594" class="Symbol">(</a><a id="16595" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16597" class="String">&quot;x&quot;</a> <a id="16601" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16603" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16605" class="String">&quot;x&quot;</a><a id="16608" class="Symbol">)</a> <a id="16610" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="16612" class="String">&quot;x&quot;</a> <a id="16616" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="16619" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="16625" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="16627" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16629" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16631" class="String">&quot;x&quot;</a> <a id="16635" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16637" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16639" class="String">&quot;x&quot;</a>
<a id="16643" class="Symbol">_</a> <a id="16645" class="Symbol">=</a> <a id="16647" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>

<a id="16653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#16653" class="Function">_</a> <a id="16655" class="Symbol">:</a> <a id="16657" class="Symbol">(</a><a id="16658" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16660" class="String">&quot;y&quot;</a> <a id="16664" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16666" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16668" class="String">&quot;y&quot;</a><a id="16671" class="Symbol">)</a> <a id="16673" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="16675" class="String">&quot;x&quot;</a> <a id="16679" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="16682" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="16688" href="plfa.Lambda.html#14919" class="Function Operator">]</a> <a id="16690" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="16692" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="16694" class="String">&quot;y&quot;</a> <a id="16698" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="16700" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="16702" class="String">&quot;y&quot;</a>
<a id="16706" class="Symbol">_</a> <a id="16708" class="Symbol">=</a> <a id="16710" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}

#### Quiz

What is the result of the following substitution?

    (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]

1. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) ``
2. `` (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ `zero)) ``
3. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x")) ``
4. `` (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ `zero)) ``


#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a `with` clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

{% raw %}<pre class="Agda"><a id="17333" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Reduction

We give the reduction rules for call-by-value lambda calculus.  To
reduce an application, first we reduce the left-hand side until it
becomes a value (which must be an abstraction); then we reduce the
right-hand side until it becomes a value; and finally we substitute
the argument for the variable in the abstraction.

In an informal presentation of the operational semantics,
the rules for reduction of applications are written as follows:

    L —→ L′
    --------------- ξ-·₁
    L · M —→ L′ · M

    M —→ M′
    --------------- ξ-·₂
    V · M —→ V · M′

    ----------------------------- β-ƛ
    (ƛ x ⇒ N) · V —→ N [ x := V ]

The Agda version of the rules below will be similar, except that universal
quantifications are made explicit, and so are the predicates that indicate
which terms are values.

The rules break into two sorts. Compatibility rules direct us to
reduce some part of a term.  We give them names starting with the
Greek letter `ξ` (_xi_).  Once a term is sufficiently reduced, it will
consist of a constructor and a deconstructor, in our case `ƛ` and `·`,
which reduces directly.  We give them names starting with the Greek
letter `β` (_beta_) and such rules are traditionally called _beta rules_.

A bit of terminology: A term that matches the left-hand side of a
reduction rule is called a _redex_. In the redex `(ƛ x ⇒ N) · V`, we
may refer to `x` as the _formal parameter_ of the function, and `V`
as the _actual parameter_ of the function application.  Beta reduction
replaces the formal parameter by the actual parameter.

If a term is a value, then no reduction applies; conversely,
if a reduction applies to a term then it is not a value.
We will show in the next chapter that 
this exhausts the possibilities: every well-typed term
either reduces or is a value.

For numbers, zero does not reduce and successor reduces the subterm.
A case expression reduces its argument to a number, and then chooses
the zero or successor branch as appropriate.  A fixpoint replaces
the bound variable by the entire fixpoint term; this is the one
case where we substitute by a term that is not a value.

Here are the rules formalised in Agda:

{% raw %}<pre class="Agda"><a id="19541" class="Keyword">infix</a> <a id="19547" class="Number">4</a> <a id="19549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19560" class="Datatype Operator">_—→_</a>

<a id="19555" class="Keyword">data</a> <a id="_—→_"></a><a id="19560" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19560" class="Datatype Operator">_—→_</a> <a id="19565" class="Symbol">:</a> <a id="19567" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="19572" class="Symbol">→</a> <a id="19574" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="19579" class="Symbol">→</a> <a id="19581" class="PrimitiveType">Set</a> <a id="19585" class="Keyword">where</a>

  <a id="_—→_.ξ-·₁"></a><a id="19594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19594" class="InductiveConstructor">ξ-·₁</a> <a id="19599" class="Symbol">:</a> <a id="19601" class="Symbol">∀</a> <a id="19603" class="Symbol">{</a><a id="19604" href="plfa.Lambda.html#19604" class="Bound">L</a> <a id="19606" href="plfa.Lambda.html#19606" class="Bound">L′</a> <a id="19609" href="plfa.Lambda.html#19609" class="Bound">M</a><a id="19610" class="Symbol">}</a>
    <a id="19616" class="Symbol">→</a> <a id="19618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19604" class="Bound">L</a> <a id="19620" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19623" href="plfa.Lambda.html#19606" class="Bound">L′</a>
      <a id="19632" class="Comment">-----------------</a>
    <a id="19654" class="Symbol">→</a> <a id="19656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19604" class="Bound">L</a> <a id="19658" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="19660" href="plfa.Lambda.html#19609" class="Bound">M</a> <a id="19662" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19665" href="plfa.Lambda.html#19606" class="Bound">L′</a> <a id="19668" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="19670" href="plfa.Lambda.html#19609" class="Bound">M</a>

  <a id="_—→_.ξ-·₂"></a><a id="19675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19675" class="InductiveConstructor">ξ-·₂</a> <a id="19680" class="Symbol">:</a> <a id="19682" class="Symbol">∀</a> <a id="19684" class="Symbol">{</a><a id="19685" href="plfa.Lambda.html#19685" class="Bound">V</a> <a id="19687" href="plfa.Lambda.html#19687" class="Bound">M</a> <a id="19689" href="plfa.Lambda.html#19689" class="Bound">M′</a><a id="19691" class="Symbol">}</a>
    <a id="19697" class="Symbol">→</a> <a id="19699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="19705" href="plfa.Lambda.html#19685" class="Bound">V</a>
    <a id="19711" class="Symbol">→</a> <a id="19713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19687" class="Bound">M</a> <a id="19715" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19718" href="plfa.Lambda.html#19689" class="Bound">M′</a>
      <a id="19727" class="Comment">-----------------</a>
    <a id="19749" class="Symbol">→</a> <a id="19751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19685" class="Bound">V</a> <a id="19753" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="19755" href="plfa.Lambda.html#19687" class="Bound">M</a> <a id="19757" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19760" href="plfa.Lambda.html#19685" class="Bound">V</a> <a id="19762" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="19764" href="plfa.Lambda.html#19689" class="Bound">M′</a>

  <a id="_—→_.β-ƛ"></a><a id="19770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19770" class="InductiveConstructor">β-ƛ</a> <a id="19774" class="Symbol">:</a> <a id="19776" class="Symbol">∀</a> <a id="19778" class="Symbol">{</a><a id="19779" href="plfa.Lambda.html#19779" class="Bound">x</a> <a id="19781" href="plfa.Lambda.html#19781" class="Bound">N</a> <a id="19783" href="plfa.Lambda.html#19783" class="Bound">V</a><a id="19784" class="Symbol">}</a>
    <a id="19790" class="Symbol">→</a> <a id="19792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="19798" href="plfa.Lambda.html#19783" class="Bound">V</a>
      <a id="19806" class="Comment">------------------------------</a>
    <a id="19841" class="Symbol">→</a> <a id="19843" class="Symbol">(</a><a id="19844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="19846" href="plfa.Lambda.html#19779" class="Bound">x</a> <a id="19848" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="19850" href="plfa.Lambda.html#19781" class="Bound">N</a><a id="19851" class="Symbol">)</a> <a id="19853" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="19855" href="plfa.Lambda.html#19783" class="Bound">V</a> <a id="19857" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19860" href="plfa.Lambda.html#19781" class="Bound">N</a> <a id="19862" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="19864" href="plfa.Lambda.html#19779" class="Bound">x</a> <a id="19866" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="19869" href="plfa.Lambda.html#19783" class="Bound">V</a> <a id="19871" href="plfa.Lambda.html#14919" class="Function Operator">]</a>

  <a id="_—→_.ξ-suc"></a><a id="19876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19876" class="InductiveConstructor">ξ-suc</a> <a id="19882" class="Symbol">:</a> <a id="19884" class="Symbol">∀</a> <a id="19886" class="Symbol">{</a><a id="19887" href="plfa.Lambda.html#19887" class="Bound">M</a> <a id="19889" href="plfa.Lambda.html#19889" class="Bound">M′</a><a id="19891" class="Symbol">}</a>
    <a id="19897" class="Symbol">→</a> <a id="19899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19887" class="Bound">M</a> <a id="19901" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19904" href="plfa.Lambda.html#19889" class="Bound">M′</a>
      <a id="19913" class="Comment">------------------</a>
    <a id="19936" class="Symbol">→</a> <a id="19938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="19943" href="plfa.Lambda.html#19887" class="Bound">M</a> <a id="19945" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19948" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="19953" href="plfa.Lambda.html#19889" class="Bound">M′</a>

  <a id="_—→_.ξ-case"></a><a id="19959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19959" class="InductiveConstructor">ξ-case</a> <a id="19966" class="Symbol">:</a> <a id="19968" class="Symbol">∀</a> <a id="19970" class="Symbol">{</a><a id="19971" href="plfa.Lambda.html#19971" class="Bound">x</a> <a id="19973" href="plfa.Lambda.html#19973" class="Bound">L</a> <a id="19975" href="plfa.Lambda.html#19975" class="Bound">L′</a> <a id="19978" href="plfa.Lambda.html#19978" class="Bound">M</a> <a id="19980" href="plfa.Lambda.html#19980" class="Bound">N</a><a id="19981" class="Symbol">}</a>
    <a id="19987" class="Symbol">→</a> <a id="19989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#19973" class="Bound">L</a> <a id="19991" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="19994" href="plfa.Lambda.html#19975" class="Bound">L′</a>
      <a id="20003" class="Comment">-----------------------------------------------------------------</a>
    <a id="20073" class="Symbol">→</a> <a id="20075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="20080" href="plfa.Lambda.html#19973" class="Bound">L</a> <a id="20082" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="20089" href="plfa.Lambda.html#19978" class="Bound">M</a> <a id="20091" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="20096" href="plfa.Lambda.html#19971" class="Bound">x</a> <a id="20098" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="20100" href="plfa.Lambda.html#19980" class="Bound">N</a> <a id="20102" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a> <a id="20104" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="20107" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">case</a> <a id="20112" href="plfa.Lambda.html#19975" class="Bound">L′</a> <a id="20115" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="20122" href="plfa.Lambda.html#19978" class="Bound">M</a> <a id="20124" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="20129" href="plfa.Lambda.html#19971" class="Bound">x</a> <a id="20131" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="20133" href="plfa.Lambda.html#19980" class="Bound">N</a> <a id="20135" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>

  <a id="_—→_.β-zero"></a><a id="20140" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#20140" class="InductiveConstructor">β-zero</a> <a id="20147" class="Symbol">:</a> <a id="20149" class="Symbol">∀</a> <a id="20151" class="Symbol">{</a><a id="20152" href="plfa.Lambda.html#20152" class="Bound">x</a> <a id="20154" href="plfa.Lambda.html#20154" class="Bound">M</a> <a id="20156" href="plfa.Lambda.html#20156" class="Bound">N</a><a id="20157" class="Symbol">}</a>
      <a id="20165" class="Comment">----------------------------------------</a>
    <a id="20210" class="Symbol">→</a> <a id="20212" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="20217" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="20223" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="20230" href="plfa.Lambda.html#20154" class="Bound">M</a> <a id="20232" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="20237" href="plfa.Lambda.html#20152" class="Bound">x</a> <a id="20239" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="20241" href="plfa.Lambda.html#20156" class="Bound">N</a> <a id="20243" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a> <a id="20245" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="20248" href="plfa.Lambda.html#20154" class="Bound">M</a>

  <a id="_—→_.β-suc"></a><a id="20253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#20253" class="InductiveConstructor">β-suc</a> <a id="20259" class="Symbol">:</a> <a id="20261" class="Symbol">∀</a> <a id="20263" class="Symbol">{</a><a id="20264" href="plfa.Lambda.html#20264" class="Bound">x</a> <a id="20266" href="plfa.Lambda.html#20266" class="Bound">V</a> <a id="20268" href="plfa.Lambda.html#20268" class="Bound">M</a> <a id="20270" href="plfa.Lambda.html#20270" class="Bound">N</a><a id="20271" class="Symbol">}</a>
    <a id="20277" class="Symbol">→</a> <a id="20279" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#11536" class="Datatype">Value</a> <a id="20285" href="plfa.Lambda.html#20266" class="Bound">V</a>
      <a id="20293" class="Comment">---------------------------------------------------</a>
    <a id="20349" class="Symbol">→</a> <a id="20351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="20356" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="20361" href="plfa.Lambda.html#20266" class="Bound">V</a> <a id="20363" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="20370" href="plfa.Lambda.html#20268" class="Bound">M</a> <a id="20372" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="20377" href="plfa.Lambda.html#20264" class="Bound">x</a> <a id="20379" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="20381" href="plfa.Lambda.html#20270" class="Bound">N</a> <a id="20383" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a> <a id="20385" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="20388" href="plfa.Lambda.html#20270" class="Bound">N</a> <a id="20390" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="20392" href="plfa.Lambda.html#20264" class="Bound">x</a> <a id="20394" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="20397" href="plfa.Lambda.html#20266" class="Bound">V</a> <a id="20399" href="plfa.Lambda.html#14919" class="Function Operator">]</a>

  <a id="_—→_.β-μ"></a><a id="20404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#20404" class="InductiveConstructor">β-μ</a> <a id="20408" class="Symbol">:</a> <a id="20410" class="Symbol">∀</a> <a id="20412" class="Symbol">{</a><a id="20413" href="plfa.Lambda.html#20413" class="Bound">x</a> <a id="20415" href="plfa.Lambda.html#20415" class="Bound">M</a><a id="20416" class="Symbol">}</a>
      <a id="20424" class="Comment">------------------------------</a>
    <a id="20459" class="Symbol">→</a> <a id="20461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4035" class="InductiveConstructor Operator">μ</a> <a id="20463" href="plfa.Lambda.html#20413" class="Bound">x</a> <a id="20465" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="20467" href="plfa.Lambda.html#20415" class="Bound">M</a> <a id="20469" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="20472" href="plfa.Lambda.html#20415" class="Bound">M</a> <a id="20474" href="plfa.Lambda.html#14919" class="Function Operator">[</a> <a id="20476" href="plfa.Lambda.html#20413" class="Bound">x</a> <a id="20478" href="plfa.Lambda.html#14919" class="Function Operator">:=</a> <a id="20481" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">μ</a> <a id="20483" href="plfa.Lambda.html#20413" class="Bound">x</a> <a id="20485" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="20487" href="plfa.Lambda.html#20415" class="Bound">M</a> <a id="20489" href="plfa.Lambda.html#14919" class="Function Operator">]</a>
</pre>{% endraw %}
The reduction rules are carefully designed to ensure that subterms
of a term are reduced to values before the whole term is reduced.
This is referred to as _call-by-value_ reduction.

Further, we have arranged that subterms are reduced in a
left-to-right order.  This means that reduction is _deterministic_:
for any term, there is at most one other term to which it reduces.
Put another way, our reduction relation `—→` is in fact a function.

This style of explaining the meaning of terms is called
a _small-step operational semantics_.  If `M —→ N`, we say that
term `M` _reduces_ to term `N`, or equivalently,
term `M` _steps_ to term `N`.  Each compatibility rule has
another reduction rule in its premise; so a step always consists
of a beta rule, possibly adjusted by zero or more compatibility rules.


#### Quiz

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?

    (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→  ???

1.  `` (ƛ "x" ⇒ ` "x") ``
2.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``
3.  `` (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ``

What does the following term step to?  (Where `twoᶜ` and `sucᶜ` are as
defined above.)

    twoᶜ · sucᶜ · `zero  —→  ???

1.  `` sucᶜ · (sucᶜ · `zero) ``
2.  `` (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero ``
3.  `` `zero ``


## Reflexive and transitive closure

A single step is only part of the story. In general, we wish to repeatedly
step a closed term until it reduces to a value.  We do this by defining
the reflexive and transitive closure `—↠` of the step relation `—→`.

We define reflexive and transitive closure as a sequence of zero or
more steps of the underlying relation, along lines similar to that for
reasoning about chains of equalities in
Chapter [Equality]({{ site.baseurl }}/Equality/):
{% raw %}<pre class="Agda"><a id="22485" class="Keyword">infix</a>  <a id="22492" class="Number">2</a> <a id="22494" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22550" class="Datatype Operator">_—↠_</a>
<a id="22499" class="Keyword">infix</a>  <a id="22506" class="Number">1</a> <a id="22508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22700" class="Function Operator">begin_</a>
<a id="22515" class="Keyword">infixr</a> <a id="22522" class="Number">2</a> <a id="22524" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">_—→⟨_⟩_</a>
<a id="22532" class="Keyword">infix</a>  <a id="22539" class="Number">3</a> <a id="22541" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22583" class="InductiveConstructor Operator">_∎</a>

<a id="22545" class="Keyword">data</a> <a id="_—↠_"></a><a id="22550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22550" class="Datatype Operator">_—↠_</a> <a id="22555" class="Symbol">:</a> <a id="22557" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="22562" class="Symbol">→</a> <a id="22564" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="22569" class="Symbol">→</a> <a id="22571" class="PrimitiveType">Set</a> <a id="22575" class="Keyword">where</a>
  <a id="_—↠_._∎"></a><a id="22583" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22583" class="InductiveConstructor Operator">_∎</a> <a id="22586" class="Symbol">:</a> <a id="22588" class="Symbol">∀</a> <a id="22590" href="plfa.Lambda.html#22590" class="Bound">M</a>
      <a id="22598" class="Comment">---------</a>
    <a id="22612" class="Symbol">→</a> <a id="22614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22590" class="Bound">M</a> <a id="22616" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="22619" href="plfa.Lambda.html#22590" class="Bound">M</a>

  <a id="_—↠_._—→⟨_⟩_"></a><a id="22624" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">_—→⟨_⟩_</a> <a id="22632" class="Symbol">:</a> <a id="22634" class="Symbol">∀</a> <a id="22636" href="plfa.Lambda.html#22636" class="Bound">L</a> <a id="22638" class="Symbol">{</a><a id="22639" href="plfa.Lambda.html#22639" class="Bound">M</a> <a id="22641" href="plfa.Lambda.html#22641" class="Bound">N</a><a id="22642" class="Symbol">}</a>
    <a id="22648" class="Symbol">→</a> <a id="22650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22636" class="Bound">L</a> <a id="22652" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="22655" href="plfa.Lambda.html#22639" class="Bound">M</a>
    <a id="22661" class="Symbol">→</a> <a id="22663" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22639" class="Bound">M</a> <a id="22665" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="22668" href="plfa.Lambda.html#22641" class="Bound">N</a>
      <a id="22676" class="Comment">---------</a>
    <a id="22690" class="Symbol">→</a> <a id="22692" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22636" class="Bound">L</a> <a id="22694" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="22697" href="plfa.Lambda.html#22641" class="Bound">N</a>

<a id="begin_"></a><a id="22700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22700" class="Function Operator">begin_</a> <a id="22707" class="Symbol">:</a> <a id="22709" class="Symbol">∀</a> <a id="22711" class="Symbol">{</a><a id="22712" href="plfa.Lambda.html#22712" class="Bound">M</a> <a id="22714" href="plfa.Lambda.html#22714" class="Bound">N</a><a id="22715" class="Symbol">}</a>
  <a id="22719" class="Symbol">→</a> <a id="22721" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22712" class="Bound">M</a> <a id="22723" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="22726" href="plfa.Lambda.html#22714" class="Bound">N</a>
    <a id="22732" class="Comment">------</a>
  <a id="22741" class="Symbol">→</a> <a id="22743" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22712" class="Bound">M</a> <a id="22745" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="22748" href="plfa.Lambda.html#22714" class="Bound">N</a>
<a id="22750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22700" class="Function Operator">begin</a> <a id="22756" href="plfa.Lambda.html#22756" class="Bound">M—↠N</a> <a id="22761" class="Symbol">=</a> <a id="22763" href="plfa.Lambda.html#22756" class="Bound">M—↠N</a>
</pre>{% endraw %}We can read this as follows:

* From term `M`, we can take no steps, giving a step of type `M —↠ M`.
  It is written `M ∎`.

* From term `L` we can take a single step of type `L —→ M` followed by zero
  or more steps of type `M —↠ N`, giving a step of type `L —↠ N`. It is
  written `L —→⟨ L—→M ⟩ M—↠N`, where `L—→M` and `M—↠N` are steps of the
  appropriate type.

The notation is chosen to allow us to lay out example reductions in an
appealing way, as we will see in the next section.

An alternative is to define reflexive and transitive closure directly,
as the smallest relation that includes `—→` and is also reflexive
and transitive.  We could do so as follows:
{% raw %}<pre class="Agda"><a id="23446" class="Keyword">data</a> <a id="_—↠′_"></a><a id="23451" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23451" class="Datatype Operator">_—↠′_</a> <a id="23457" class="Symbol">:</a> <a id="23459" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="23464" class="Symbol">→</a> <a id="23466" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="23471" class="Symbol">→</a> <a id="23473" class="PrimitiveType">Set</a> <a id="23477" class="Keyword">where</a>

  <a id="_—↠′_.step′"></a><a id="23486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23486" class="InductiveConstructor">step′</a> <a id="23492" class="Symbol">:</a> <a id="23494" class="Symbol">∀</a> <a id="23496" class="Symbol">{</a><a id="23497" href="plfa.Lambda.html#23497" class="Bound">M</a> <a id="23499" href="plfa.Lambda.html#23499" class="Bound">N</a><a id="23500" class="Symbol">}</a>
    <a id="23506" class="Symbol">→</a> <a id="23508" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23497" class="Bound">M</a> <a id="23510" href="plfa.Lambda.html#19560" class="Datatype Operator">—→</a> <a id="23513" href="plfa.Lambda.html#23499" class="Bound">N</a>
      <a id="23521" class="Comment">-------</a>
    <a id="23533" class="Symbol">→</a> <a id="23535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23497" class="Bound">M</a> <a id="23537" href="plfa.Lambda.html#23451" class="Datatype Operator">—↠′</a> <a id="23541" href="plfa.Lambda.html#23499" class="Bound">N</a>

  <a id="_—↠′_.refl′"></a><a id="23546" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23546" class="InductiveConstructor">refl′</a> <a id="23552" class="Symbol">:</a> <a id="23554" class="Symbol">∀</a> <a id="23556" class="Symbol">{</a><a id="23557" href="plfa.Lambda.html#23557" class="Bound">M</a><a id="23558" class="Symbol">}</a>
      <a id="23566" class="Comment">-------</a>
    <a id="23578" class="Symbol">→</a> <a id="23580" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23557" class="Bound">M</a> <a id="23582" href="plfa.Lambda.html#23451" class="Datatype Operator">—↠′</a> <a id="23586" href="plfa.Lambda.html#23557" class="Bound">M</a>

  <a id="_—↠′_.trans′"></a><a id="23591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23591" class="InductiveConstructor">trans′</a> <a id="23598" class="Symbol">:</a> <a id="23600" class="Symbol">∀</a> <a id="23602" class="Symbol">{</a><a id="23603" href="plfa.Lambda.html#23603" class="Bound">L</a> <a id="23605" href="plfa.Lambda.html#23605" class="Bound">M</a> <a id="23607" href="plfa.Lambda.html#23607" class="Bound">N</a><a id="23608" class="Symbol">}</a>
    <a id="23614" class="Symbol">→</a> <a id="23616" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23603" class="Bound">L</a> <a id="23618" href="plfa.Lambda.html#23451" class="Datatype Operator">—↠′</a> <a id="23622" href="plfa.Lambda.html#23605" class="Bound">M</a>
    <a id="23628" class="Symbol">→</a> <a id="23630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23605" class="Bound">M</a> <a id="23632" href="plfa.Lambda.html#23451" class="Datatype Operator">—↠′</a> <a id="23636" href="plfa.Lambda.html#23607" class="Bound">N</a>
      <a id="23644" class="Comment">-------</a>
    <a id="23656" class="Symbol">→</a> <a id="23658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#23603" class="Bound">L</a> <a id="23660" href="plfa.Lambda.html#23451" class="Datatype Operator">—↠′</a> <a id="23664" href="plfa.Lambda.html#23607" class="Bound">N</a>
</pre>{% endraw %}The three constructors specify, respectively, that `—↠′` includes `—→`
and is reflexive and transitive.  A good exercise is to show that
the two definitions are equivalent (indeed, one embeds in the other).

#### Exercise `—↠≲—↠′`

Show that the first notion of reflexive and transitive closure
above embeds into the second. Why are they not isomorphic?

{% raw %}<pre class="Agda"><a id="24029" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
## Confluence

One important property a reduction relation might satisfy is
to be _confluent_.  If term `L` reduces to two other terms,
`M` and `N`, then both of these reduce to a common term `P`.
It can be illustrated as follows:

               L
              / \
             /   \
            /     \
           M       N
            \     /
             \   /
              \ /
               P

Here `L`, `M`, `N` are universally quantified while `P`
is existentially quantified.  If each line stands for zero
or more reduction steps, this is called confluence,
while if the top two lines stand for a single reduction
step and the bottom two stand for zero or more reduction
steps it is called the diamond property. In symbols:

    confluence : ∀ {L M N} → ∃[ P ]
      ( ((L —↠ M) × (L —↠ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

    diamond : ∀ {L M N} → ∃[ P ]
      ( ((L —→ M) × (L —→ N))
        --------------------
      → ((M —↠ P) × (N —↠ P)) )

The reduction system studied in this chapter is deterministic.
In symbols:

    deterministic : ∀ {L M N}
      → L —→ M
      → L —→ N
        ------
      → M ≡ N

It is easy to show that every deterministic relation satisfies
the diamond property, and that every relation that satisfies
the diamond property is confluent.  Hence, all the reduction
systems studied in this text are trivially confluent.


## Examples

We start with a simple example. The Church numeral two applied to the
successor function and zero yields the natural number two:
{% raw %}<pre class="Agda"><a id="25599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#25599" class="Function">_</a> <a id="25601" class="Symbol">:</a> <a id="25603" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="25608" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25610" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="25615" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25617" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="25623" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="25626" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="25631" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="25636" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
<a id="25642" class="Symbol">_</a> <a id="25644" class="Symbol">=</a>
  <a id="25648" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22700" class="Function Operator">begin</a>
    <a id="25658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5725" class="Function">twoᶜ</a> <a id="25663" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25665" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="25670" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25672" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="25680" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="25684" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="25689" class="Symbol">(</a><a id="25690" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="25694" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a><a id="25697" class="Symbol">)</a> <a id="25699" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="25705" class="Symbol">(</a><a id="25706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="25708" class="String">&quot;z&quot;</a> <a id="25712" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="25714" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="25719" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25721" class="Symbol">(</a><a id="25722" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="25727" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25729" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="25731" class="String">&quot;z&quot;</a><a id="25734" class="Symbol">))</a> <a id="25737" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25739" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="25747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="25751" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="25755" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a> <a id="25762" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="25768" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5890" class="Function">sucᶜ</a> <a id="25773" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25775" class="Symbol">(</a><a id="25776" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="25781" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25783" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="25788" class="Symbol">)</a>
  <a id="25792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="25796" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="25801" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="25805" class="Symbol">(</a><a id="25806" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="25810" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="25816" class="Symbol">)</a> <a id="25818" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="25824" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5890" class="Function">sucᶜ</a> <a id="25829" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25831" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="25836" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="25844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="25848" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="25852" class="Symbol">(</a><a id="25853" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="25859" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="25865" class="Symbol">)</a> <a id="25867" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="25873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="25878" class="Symbol">(</a><a id="25879" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="25884" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="25889" class="Symbol">)</a>
  <a id="25893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22583" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
Here is a sample reduction demonstrating that two plus two is four:
{% raw %}<pre class="Agda"><a id="25972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#25972" class="Function">_</a> <a id="25974" class="Symbol">:</a> <a id="25976" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="25981" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25983" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="25987" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="25989" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="25993" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="25996" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26001" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26006" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26011" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26016" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
<a id="26022" class="Symbol">_</a> <a id="26024" class="Symbol">=</a>
  <a id="26028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22700" class="Function Operator">begin</a>
    <a id="26038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#4510" class="Function">plus</a> <a id="26043" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26045" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="26049" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26051" href="plfa.Lambda.html#4476" class="Function">two</a>
  <a id="26057" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26061" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="26066" class="Symbol">(</a><a id="26067" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="26072" href="plfa.Lambda.html#20404" class="InductiveConstructor">β-μ</a><a id="26075" class="Symbol">)</a> <a id="26077" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26083" class="Symbol">(</a><a id="26084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="26086" class="String">&quot;m&quot;</a> <a id="26090" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="26092" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="26094" class="String">&quot;n&quot;</a> <a id="26098" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
      <a id="26106" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="26111" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26113" class="String">&quot;m&quot;</a> <a id="26117" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="26124" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26126" class="String">&quot;n&quot;</a> <a id="26130" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="26135" class="String">&quot;m&quot;</a> <a id="26139" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="26141" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26146" class="Symbol">(</a><a id="26147" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26152" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26154" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26156" class="String">&quot;m&quot;</a> <a id="26160" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26162" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26164" class="String">&quot;n&quot;</a><a id="26167" class="Symbol">)</a> <a id="26169" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="26170" class="Symbol">)</a>
        <a id="26180" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="26182" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="26186" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26188" href="plfa.Lambda.html#4476" class="Function">two</a>
  <a id="26194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26198" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="26203" class="Symbol">(</a><a id="26204" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="26208" class="Symbol">(</a><a id="26209" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26215" class="Symbol">(</a><a id="26216" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26222" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="26228" class="Symbol">)))</a> <a id="26232" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26238" class="Symbol">(</a><a id="26239" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="26241" class="String">&quot;n&quot;</a> <a id="26245" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
      <a id="26253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="26258" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="26262" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="26269" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26271" class="String">&quot;n&quot;</a> <a id="26275" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="26280" class="String">&quot;m&quot;</a> <a id="26284" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="26286" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26291" class="Symbol">(</a><a id="26292" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26297" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26299" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26301" class="String">&quot;m&quot;</a> <a id="26305" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26307" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26309" class="String">&quot;n&quot;</a><a id="26312" class="Symbol">)</a> <a id="26314" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="26315" class="Symbol">)</a>
         <a id="26326" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="26328" href="plfa.Lambda.html#4476" class="Function">two</a>
  <a id="26334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26338" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="26342" class="Symbol">(</a><a id="26343" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26349" class="Symbol">(</a><a id="26350" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26356" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="26362" class="Symbol">))</a> <a id="26365" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26371" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="26376" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="26380" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="26387" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="26391" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="26396" class="String">&quot;m&quot;</a> <a id="26400" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="26402" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26407" class="Symbol">(</a><a id="26408" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26413" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26415" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26417" class="String">&quot;m&quot;</a> <a id="26421" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26423" href="plfa.Lambda.html#4476" class="Function">two</a><a id="26426" class="Symbol">)</a> <a id="26428" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a>
  <a id="26432" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26436" href="plfa.Lambda.html#20253" class="InductiveConstructor">β-suc</a> <a id="26442" class="Symbol">(</a><a id="26443" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26449" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="26455" class="Symbol">)</a> <a id="26457" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26463" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="26468" class="Symbol">(</a><a id="26469" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26474" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26476" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26481" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="26487" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26489" href="plfa.Lambda.html#4476" class="Function">two</a><a id="26492" class="Symbol">)</a>
  <a id="26496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26500" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="26506" class="Symbol">(</a><a id="26507" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="26512" class="Symbol">(</a><a id="26513" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="26518" href="plfa.Lambda.html#20404" class="InductiveConstructor">β-μ</a><a id="26521" class="Symbol">))</a> <a id="26524" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="26535" class="Symbol">((</a><a id="26537" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="26539" class="String">&quot;m&quot;</a> <a id="26543" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="26545" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="26547" class="String">&quot;n&quot;</a> <a id="26551" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
      <a id="26559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="26564" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26566" class="String">&quot;m&quot;</a> <a id="26570" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="26577" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26579" class="String">&quot;n&quot;</a> <a id="26583" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="26588" class="String">&quot;m&quot;</a> <a id="26592" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="26594" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26599" class="Symbol">(</a><a id="26600" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26605" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26607" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26609" class="String">&quot;m&quot;</a> <a id="26613" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26615" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26617" class="String">&quot;n&quot;</a><a id="26620" class="Symbol">)</a> <a id="26622" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="26623" class="Symbol">)</a>
        <a id="26633" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="26635" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26640" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="26646" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26648" href="plfa.Lambda.html#4476" class="Function">two</a><a id="26651" class="Symbol">)</a>
  <a id="26655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26659" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="26665" class="Symbol">(</a><a id="26666" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="26671" class="Symbol">(</a><a id="26672" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="26676" class="Symbol">(</a><a id="26677" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26683" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="26689" class="Symbol">)))</a> <a id="26693" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="26704" class="Symbol">((</a><a id="26706" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="26708" class="String">&quot;n&quot;</a> <a id="26712" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
      <a id="26720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="26725" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26730" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="26736" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="26743" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26745" class="String">&quot;n&quot;</a> <a id="26749" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="26754" class="String">&quot;m&quot;</a> <a id="26758" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="26760" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26765" class="Symbol">(</a><a id="26766" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26771" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26773" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26775" class="String">&quot;m&quot;</a> <a id="26779" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26781" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26783" class="String">&quot;n&quot;</a><a id="26786" class="Symbol">)</a> <a id="26788" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="26789" class="Symbol">)</a>
        <a id="26799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="26801" href="plfa.Lambda.html#4476" class="Function">two</a><a id="26804" class="Symbol">)</a>
  <a id="26808" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26812" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="26818" class="Symbol">(</a><a id="26819" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="26823" class="Symbol">(</a><a id="26824" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26830" class="Symbol">(</a><a id="26831" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="26837" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="26843" class="Symbol">)))</a> <a id="26847" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="26858" class="Symbol">(</a><a id="26859" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">case</a> <a id="26864" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26869" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="26875" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="26882" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="26886" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="26891" class="String">&quot;m&quot;</a> <a id="26895" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="26897" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26902" class="Symbol">(</a><a id="26903" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26908" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26910" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="26912" class="String">&quot;m&quot;</a> <a id="26916" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26918" href="plfa.Lambda.html#4476" class="Function">two</a><a id="26921" class="Symbol">)</a> <a id="26923" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="26924" class="Symbol">)</a>
  <a id="26928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26932" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="26938" class="Symbol">(</a><a id="26939" href="plfa.Lambda.html#20253" class="InductiveConstructor">β-suc</a> <a id="26945" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="26951" class="Symbol">)</a> <a id="26953" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="26959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="26964" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="26969" class="Symbol">(</a><a id="26970" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="26975" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26977" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="26983" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="26985" href="plfa.Lambda.html#4476" class="Function">two</a><a id="26988" class="Symbol">)</a>
  <a id="26992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="26996" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27002" class="Symbol">(</a><a id="27003" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27009" class="Symbol">(</a><a id="27010" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27015" class="Symbol">(</a><a id="27016" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27021" href="plfa.Lambda.html#20404" class="InductiveConstructor">β-μ</a><a id="27024" class="Symbol">)))</a> <a id="27028" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="27034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="27039" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27044" class="Symbol">((</a><a id="27046" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27048" class="String">&quot;m&quot;</a> <a id="27052" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27054" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27056" class="String">&quot;n&quot;</a> <a id="27060" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
      <a id="27068" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="27073" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27075" class="String">&quot;m&quot;</a> <a id="27079" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="27086" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27088" class="String">&quot;n&quot;</a> <a id="27092" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="27097" class="String">&quot;m&quot;</a> <a id="27101" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="27103" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27108" class="Symbol">(</a><a id="27109" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="27114" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27116" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27118" class="String">&quot;m&quot;</a> <a id="27122" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27124" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27126" class="String">&quot;n&quot;</a><a id="27129" class="Symbol">)</a> <a id="27131" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="27132" class="Symbol">)</a>
        <a id="27142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="27144" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="27150" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27152" href="plfa.Lambda.html#4476" class="Function">two</a><a id="27155" class="Symbol">)</a>
  <a id="27159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="27163" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27169" class="Symbol">(</a><a id="27170" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27176" class="Symbol">(</a><a id="27177" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27182" class="Symbol">(</a><a id="27183" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="27187" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="27193" class="Symbol">)))</a> <a id="27197" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="27203" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="27208" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27213" class="Symbol">((</a><a id="27215" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27217" class="String">&quot;n&quot;</a> <a id="27221" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a>
      <a id="27229" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3975" class="InductiveConstructor Operator">case</a> <a id="27234" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="27240" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="27247" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27249" class="String">&quot;n&quot;</a> <a id="27253" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="27258" class="String">&quot;m&quot;</a> <a id="27262" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="27264" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27269" class="Symbol">(</a><a id="27270" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="27275" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27277" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27279" class="String">&quot;m&quot;</a> <a id="27283" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27285" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27287" class="String">&quot;n&quot;</a><a id="27290" class="Symbol">)</a> <a id="27292" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="27293" class="Symbol">)</a>
        <a id="27303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="27305" href="plfa.Lambda.html#4476" class="Function">two</a><a id="27308" class="Symbol">)</a>
  <a id="27312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="27316" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27322" class="Symbol">(</a><a id="27323" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27329" class="Symbol">(</a><a id="27330" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="27334" class="Symbol">(</a><a id="27335" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="27341" class="Symbol">(</a><a id="27342" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="27348" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="27354" class="Symbol">))))</a> <a id="27359" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="27365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="27370" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27375" class="Symbol">(</a><a id="27376" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">case</a> <a id="27381" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="27387" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="27394" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="27398" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="27403" class="String">&quot;m&quot;</a> <a id="27407" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="27409" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27414" class="Symbol">(</a><a id="27415" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="27420" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27422" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27424" class="String">&quot;m&quot;</a> <a id="27428" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27430" href="plfa.Lambda.html#4476" class="Function">two</a><a id="27433" class="Symbol">)</a> <a id="27435" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a><a id="27436" class="Symbol">)</a>
  <a id="27440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="27444" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27450" class="Symbol">(</a><a id="27451" href="plfa.Lambda.html#19876" class="InductiveConstructor">ξ-suc</a> <a id="27457" href="plfa.Lambda.html#20140" class="InductiveConstructor">β-zero</a><a id="27463" class="Symbol">)</a> <a id="27465" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="27471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="27476" class="Symbol">(</a><a id="27477" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27482" class="Symbol">(</a><a id="27483" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27488" class="Symbol">(</a><a id="27489" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27494" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="27499" class="Symbol">)))</a>
  <a id="27505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22583" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
And here is a similar sample reduction for Church numerals:
{% raw %}<pre class="Agda"><a id="27576" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#27576" class="Function">_</a> <a id="27578" class="Symbol">:</a> <a id="27580" href="plfa.Lambda.html#5786" class="Function">plusᶜ</a> <a id="27586" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27588" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27593" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27595" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27600" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27602" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="27607" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27609" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="27615" href="plfa.Lambda.html#22550" class="Datatype Operator">—↠</a> <a id="27618" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27623" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27628" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27633" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="27638" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
<a id="27644" class="Symbol">_</a> <a id="27646" class="Symbol">=</a>
  <a id="27650" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22700" class="Function Operator">begin</a>
    <a id="27660" class="Symbol">(</a><a id="27661" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27663" class="String">&quot;m&quot;</a> <a id="27667" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27669" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27671" class="String">&quot;n&quot;</a> <a id="27675" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27677" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27679" class="String">&quot;s&quot;</a> <a id="27683" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27685" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27687" class="String">&quot;z&quot;</a> <a id="27691" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27693" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27695" class="String">&quot;m&quot;</a> <a id="27699" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27701" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27703" class="String">&quot;s&quot;</a> <a id="27707" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27709" class="Symbol">(</a><a id="27710" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27712" class="String">&quot;n&quot;</a> <a id="27716" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27718" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27720" class="String">&quot;s&quot;</a> <a id="27724" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27726" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27728" class="String">&quot;z&quot;</a><a id="27731" class="Symbol">))</a>
      <a id="27740" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="27742" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27747" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27749" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27754" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27756" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="27761" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27763" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="27771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="27775" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27780" class="Symbol">(</a><a id="27781" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27786" class="Symbol">(</a><a id="27787" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27792" class="Symbol">(</a><a id="27793" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="27797" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a><a id="27800" class="Symbol">)))</a> <a id="27804" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="27810" class="Symbol">(</a><a id="27811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27813" class="String">&quot;n&quot;</a> <a id="27817" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27819" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27821" class="String">&quot;s&quot;</a> <a id="27825" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27827" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27829" class="String">&quot;z&quot;</a> <a id="27833" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27835" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27840" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27842" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27844" class="String">&quot;s&quot;</a> <a id="27848" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27850" class="Symbol">(</a><a id="27851" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27853" class="String">&quot;n&quot;</a> <a id="27857" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27859" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27861" class="String">&quot;s&quot;</a> <a id="27865" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27867" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27869" class="String">&quot;z&quot;</a><a id="27872" class="Symbol">))</a>
      <a id="27881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3852" class="InductiveConstructor Operator">·</a> <a id="27883" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27888" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27890" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="27895" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27897" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="27905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="27909" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27914" class="Symbol">(</a><a id="27915" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="27920" class="Symbol">(</a><a id="27921" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="27925" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a><a id="27928" class="Symbol">))</a> <a id="27931" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="27937" class="Symbol">(</a><a id="27938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27940" class="String">&quot;s&quot;</a> <a id="27944" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27946" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="27948" class="String">&quot;z&quot;</a> <a id="27952" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="27954" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27959" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27961" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27963" class="String">&quot;s&quot;</a> <a id="27967" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27969" class="Symbol">(</a><a id="27970" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="27975" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27977" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27979" class="String">&quot;s&quot;</a> <a id="27983" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27985" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="27987" class="String">&quot;z&quot;</a><a id="27990" class="Symbol">))</a> <a id="27993" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="27995" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28000" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28002" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="28010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28014" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="28019" class="Symbol">(</a><a id="28020" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28024" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a><a id="28027" class="Symbol">)</a> <a id="28029" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28035" class="Symbol">(</a><a id="28036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28038" class="String">&quot;z&quot;</a> <a id="28042" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28044" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="28049" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28051" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28056" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28058" class="Symbol">(</a><a id="28059" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="28064" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28066" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28071" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28073" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28075" class="String">&quot;z&quot;</a><a id="28078" class="Symbol">))</a> <a id="28081" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28083" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a>
  <a id="28091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28095" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28099" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a> <a id="28106" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28112" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5725" class="Function">twoᶜ</a> <a id="28117" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28119" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28124" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28126" class="Symbol">(</a><a id="28127" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="28132" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28134" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28139" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28141" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28146" class="Symbol">)</a>
  <a id="28150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28154" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="28159" class="Symbol">(</a><a id="28160" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28164" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a><a id="28167" class="Symbol">)</a> <a id="28169" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28175" class="Symbol">(</a><a id="28176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28178" class="String">&quot;z&quot;</a> <a id="28182" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28184" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28189" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28191" class="Symbol">(</a><a id="28192" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28197" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28199" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28201" class="String">&quot;z&quot;</a><a id="28204" class="Symbol">))</a> <a id="28207" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28209" class="Symbol">(</a><a id="28210" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="28215" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28217" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28222" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28224" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28229" class="Symbol">)</a>
  <a id="28233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28237" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="28242" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="28246" class="Symbol">(</a><a id="28247" href="plfa.Lambda.html#19594" class="InductiveConstructor">ξ-·₁</a> <a id="28252" class="Symbol">(</a><a id="28253" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28257" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a><a id="28260" class="Symbol">))</a> <a id="28263" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28269" class="Symbol">(</a><a id="28270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28272" class="String">&quot;z&quot;</a> <a id="28276" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28278" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28283" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28285" class="Symbol">(</a><a id="28286" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28291" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28293" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28295" class="String">&quot;z&quot;</a><a id="28298" class="Symbol">))</a> <a id="28301" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28303" class="Symbol">((</a><a id="28305" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28307" class="String">&quot;z&quot;</a> <a id="28311" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28313" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28318" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28320" class="Symbol">(</a><a id="28321" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28326" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28328" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28330" class="String">&quot;z&quot;</a><a id="28333" class="Symbol">))</a> <a id="28336" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28338" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28343" class="Symbol">)</a>
  <a id="28347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28351" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="28356" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="28360" class="Symbol">(</a><a id="28361" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28365" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="28371" class="Symbol">)</a> <a id="28373" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28379" class="Symbol">(</a><a id="28380" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28382" class="String">&quot;z&quot;</a> <a id="28386" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28388" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28393" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28395" class="Symbol">(</a><a id="28396" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28401" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28403" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28405" class="String">&quot;z&quot;</a><a id="28408" class="Symbol">))</a> <a id="28411" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28413" class="Symbol">(</a><a id="28414" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28419" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28421" class="Symbol">(</a><a id="28422" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28427" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28429" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28434" class="Symbol">))</a>
  <a id="28439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28443" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="28448" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="28452" class="Symbol">(</a><a id="28453" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="28458" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="28462" class="Symbol">(</a><a id="28463" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28467" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="28473" class="Symbol">))</a> <a id="28476" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28482" class="Symbol">(</a><a id="28483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28485" class="String">&quot;z&quot;</a> <a id="28489" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28491" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28496" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28498" class="Symbol">(</a><a id="28499" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28504" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28506" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28508" class="String">&quot;z&quot;</a><a id="28511" class="Symbol">))</a> <a id="28514" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28516" class="Symbol">(</a><a id="28517" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28522" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28524" class="Symbol">(</a><a id="28525" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28530" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28535" class="Symbol">))</a>
  <a id="28540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28544" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="28549" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="28553" class="Symbol">(</a><a id="28554" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28558" class="Symbol">(</a><a id="28559" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28565" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="28571" class="Symbol">))</a> <a id="28574" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28580" class="Symbol">(</a><a id="28581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3806" class="InductiveConstructor Operator">ƛ</a> <a id="28583" class="String">&quot;z&quot;</a> <a id="28587" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="28589" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28594" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28596" class="Symbol">(</a><a id="28597" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28602" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28604" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="28606" class="String">&quot;z&quot;</a><a id="28609" class="Symbol">))</a> <a id="28612" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28614" class="Symbol">(</a><a id="28615" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28620" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28625" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28630" class="Symbol">)</a>
  <a id="28634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28638" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28642" class="Symbol">(</a><a id="28643" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28649" class="Symbol">(</a><a id="28650" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28656" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="28662" class="Symbol">))</a> <a id="28665" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5890" class="Function">sucᶜ</a> <a id="28676" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28678" class="Symbol">(</a><a id="28679" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="28684" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28686" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28691" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28696" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28701" class="Symbol">)</a>
  <a id="28705" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28709" href="plfa.Lambda.html#19675" class="InductiveConstructor">ξ-·₂</a> <a id="28714" href="plfa.Lambda.html#11564" class="InductiveConstructor">V-ƛ</a> <a id="28718" class="Symbol">(</a><a id="28719" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28723" class="Symbol">(</a><a id="28724" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28730" class="Symbol">(</a><a id="28731" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28737" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="28743" class="Symbol">)))</a> <a id="28747" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
    <a id="28753" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#5890" class="Function">sucᶜ</a> <a id="28758" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="28760" class="Symbol">(</a><a id="28761" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28766" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28771" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28776" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28781" class="Symbol">)</a>
  <a id="28785" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22624" class="InductiveConstructor Operator">—→⟨</a> <a id="28789" href="plfa.Lambda.html#19770" class="InductiveConstructor">β-ƛ</a> <a id="28793" class="Symbol">(</a><a id="28794" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28800" class="Symbol">(</a><a id="28801" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28807" class="Symbol">(</a><a id="28808" href="plfa.Lambda.html#11673" class="InductiveConstructor">V-suc</a> <a id="28814" href="plfa.Lambda.html#11625" class="InductiveConstructor">V-zero</a><a id="28820" class="Symbol">)))</a> <a id="28824" href="plfa.Lambda.html#22624" class="InductiveConstructor Operator">⟩</a>
   <a id="28829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#3934" class="InductiveConstructor Operator">`suc</a> <a id="28834" class="Symbol">(</a><a id="28835" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28840" class="Symbol">(</a><a id="28841" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28846" class="Symbol">(</a><a id="28847" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="28852" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a><a id="28857" class="Symbol">)))</a>
  <a id="28863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#22583" class="InductiveConstructor Operator">∎</a>
</pre>{% endraw %}
In the next chapter, we will see how to compute such reduction sequences.


#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.

{% raw %}<pre class="Agda"><a id="29054" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Syntax of types

We have just two types:

  * Functions, `A ⇒ B`
  * Naturals, `` `ℕ ``

As before, to avoid overlap we use variants of the names used by Agda.

Here is the syntax of types in BNF:

    A, B, C  ::=  A ⇒ B | `ℕ

And here it is formalised in Agda:

{% raw %}<pre class="Agda"><a id="29354" class="Keyword">infixr</a> <a id="29361" class="Number">7</a> <a id="29363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29392" class="InductiveConstructor Operator">_⇒_</a>

<a id="29368" class="Keyword">data</a> <a id="Type"></a><a id="29373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29373" class="Datatype">Type</a> <a id="29378" class="Symbol">:</a> <a id="29380" class="PrimitiveType">Set</a> <a id="29384" class="Keyword">where</a>
  <a id="Type._⇒_"></a><a id="29392" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29392" class="InductiveConstructor Operator">_⇒_</a> <a id="29396" class="Symbol">:</a> <a id="29398" href="plfa.Lambda.html#29373" class="Datatype">Type</a> <a id="29403" class="Symbol">→</a> <a id="29405" href="plfa.Lambda.html#29373" class="Datatype">Type</a> <a id="29410" class="Symbol">→</a> <a id="29412" href="plfa.Lambda.html#29373" class="Datatype">Type</a>
  <a id="Type.`ℕ"></a><a id="29419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#29419" class="InductiveConstructor">`ℕ</a> <a id="29422" class="Symbol">:</a> <a id="29424" href="plfa.Lambda.html#29373" class="Datatype">Type</a>
</pre>{% endraw %}
### Precedence

As in Agda, functions of two or more arguments are represented via
currying. This is made more convenient by declaring `_⇒_` to
associate to the right and `_·_` to associate to the left.
Thus:

* ``(`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ`` stands for ``((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ))``.
* `plus · two · two` stands for `(plus · two) · two`.

### Quiz

* What is the type of the following term?

    `` ƛ "s" ⇒ ` "s" · (` "s"  · `zero) ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.

* What is the type of the following term?

    `` (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ ``

  1. `` (`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ) ``
  2. `` (`ℕ ⇒ `ℕ) ⇒ `ℕ ``
  3. `` `ℕ ⇒ (`ℕ ⇒ `ℕ) ``
  4. `` `ℕ ⇒ `ℕ ⇒ `ℕ ``
  5. `` `ℕ ⇒ `ℕ ``
  6. `` `ℕ ``

  Give more than one answer if appropriate.


## Typing

### Contexts

While reduction considers only closed terms, typing must
consider terms with free variables.  To type a term,
we must first type its subterms, and in particular in the
body of an abstraction its bound variable may appear free.

A _context_ associates variables with types.  We let `Γ` and `Δ` range
over contexts.  We write `∅` for the empty context, and `Γ , x ⦂ A`
for the context that extends `Γ` by mapping variable `x` to type `A`.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ``

is the context that associates variable `` "s" `` with type `` `ℕ ⇒ `ℕ ``,
and variable `` "z" `` with type `` `ℕ ``.

Contexts are formalised as follows:

{% raw %}<pre class="Agda"><a id="31009" class="Keyword">infixl</a> <a id="31016" class="Number">5</a>  <a id="31019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31071" class="InductiveConstructor Operator">_,_⦂_</a>

<a id="31026" class="Keyword">data</a> <a id="Context"></a><a id="31031" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31031" class="Datatype">Context</a> <a id="31039" class="Symbol">:</a> <a id="31041" class="PrimitiveType">Set</a> <a id="31045" class="Keyword">where</a>
  <a id="Context.∅"></a><a id="31053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31053" class="InductiveConstructor">∅</a>     <a id="31059" class="Symbol">:</a> <a id="31061" href="plfa.Lambda.html#31031" class="Datatype">Context</a>
  <a id="Context._,_⦂_"></a><a id="31071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#31071" class="InductiveConstructor Operator">_,_⦂_</a> <a id="31077" class="Symbol">:</a> <a id="31079" href="plfa.Lambda.html#31031" class="Datatype">Context</a> <a id="31087" class="Symbol">→</a> <a id="31089" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="31092" class="Symbol">→</a> <a id="31094" href="plfa.Lambda.html#29373" class="Datatype">Type</a> <a id="31099" class="Symbol">→</a> <a id="31101" href="plfa.Lambda.html#31031" class="Datatype">Context</a>
</pre>{% endraw %}

#### Exercise `Context-≃`

Show that `Context` is isomorphic to `List (Id × Type)`.
For instance, the isomorphism relates the context

    ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ

to the list

    [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

{% raw %}<pre class="Agda"><a id="31343" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}
### Lookup judgment

We have two forms of _judgment_.  The first is written

    Γ ∋ x ⦂ A

and indicates in context `Γ` that variable `x` has type `A`.
It is called _lookup_.
For example,

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ ``

give us the types associated with variables `` "z" `` and `` "s" ``,
respectively.  The symbol `∋` (pronounced "ni", for "in"
backwards) is chosen because checking that `Γ ∋ x ⦂ A` is analogous to
checking whether `x ⦂ A` appears in a list corresponding to `Γ`.

If two variables in a context have the same name, then lookup
should return the most recently bound variable, which _shadows_
the other variables.  For example,

* `` ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ ``.

Here `` "x" ⦂ `ℕ ⇒ `ℕ `` is shadowed by `` "x" ⦂ `ℕ ``.

Lookup is formalised as follows:
{% raw %}<pre class="Agda"><a id="32232" class="Keyword">infix</a>  <a id="32239" class="Number">4</a>  <a id="32242" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32254" class="Datatype Operator">_∋_⦂_</a>

<a id="32249" class="Keyword">data</a> <a id="_∋_⦂_"></a><a id="32254" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32254" class="Datatype Operator">_∋_⦂_</a> <a id="32260" class="Symbol">:</a> <a id="32262" href="plfa.Lambda.html#31031" class="Datatype">Context</a> <a id="32270" class="Symbol">→</a> <a id="32272" href="plfa.Lambda.html#3647" class="Function">Id</a> <a id="32275" class="Symbol">→</a> <a id="32277" href="plfa.Lambda.html#29373" class="Datatype">Type</a> <a id="32282" class="Symbol">→</a> <a id="32284" class="PrimitiveType">Set</a> <a id="32288" class="Keyword">where</a>

  <a id="_∋_⦂_.Z"></a><a id="32297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32297" class="InductiveConstructor">Z</a> <a id="32299" class="Symbol">:</a> <a id="32301" class="Symbol">∀</a> <a id="32303" class="Symbol">{</a><a id="32304" href="plfa.Lambda.html#32304" class="Bound">Γ</a> <a id="32306" href="plfa.Lambda.html#32306" class="Bound">x</a> <a id="32308" href="plfa.Lambda.html#32308" class="Bound">A</a><a id="32309" class="Symbol">}</a>
      <a id="32317" class="Comment">------------------</a>
    <a id="32340" class="Symbol">→</a> <a id="32342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32304" class="Bound">Γ</a> <a id="32344" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">,</a> <a id="32346" href="plfa.Lambda.html#32306" class="Bound">x</a> <a id="32348" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">⦂</a> <a id="32350" href="plfa.Lambda.html#32308" class="Bound">A</a> <a id="32352" href="plfa.Lambda.html#32254" class="Datatype Operator">∋</a> <a id="32354" href="plfa.Lambda.html#32306" class="Bound">x</a> <a id="32356" href="plfa.Lambda.html#32254" class="Datatype Operator">⦂</a> <a id="32358" href="plfa.Lambda.html#32308" class="Bound">A</a>

  <a id="_∋_⦂_.S"></a><a id="32363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32363" class="InductiveConstructor">S</a> <a id="32365" class="Symbol">:</a> <a id="32367" class="Symbol">∀</a> <a id="32369" class="Symbol">{</a><a id="32370" href="plfa.Lambda.html#32370" class="Bound">Γ</a> <a id="32372" href="plfa.Lambda.html#32372" class="Bound">x</a> <a id="32374" href="plfa.Lambda.html#32374" class="Bound">y</a> <a id="32376" href="plfa.Lambda.html#32376" class="Bound">A</a> <a id="32378" href="plfa.Lambda.html#32378" class="Bound">B</a><a id="32379" class="Symbol">}</a>
    <a id="32385" class="Symbol">→</a> <a id="32387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32372" class="Bound">x</a> <a id="32389" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="32391" href="plfa.Lambda.html#32374" class="Bound">y</a>
    <a id="32397" class="Symbol">→</a> <a id="32399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32370" class="Bound">Γ</a> <a id="32401" href="plfa.Lambda.html#32254" class="Datatype Operator">∋</a> <a id="32403" href="plfa.Lambda.html#32372" class="Bound">x</a> <a id="32405" href="plfa.Lambda.html#32254" class="Datatype Operator">⦂</a> <a id="32407" href="plfa.Lambda.html#32376" class="Bound">A</a>
      <a id="32415" class="Comment">------------------</a>
    <a id="32438" class="Symbol">→</a> <a id="32440" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#32370" class="Bound">Γ</a> <a id="32442" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">,</a> <a id="32444" href="plfa.Lambda.html#32374" class="Bound">y</a> <a id="32446" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">⦂</a> <a id="32448" href="plfa.Lambda.html#32378" class="Bound">B</a> <a id="32450" href="plfa.Lambda.html#32254" class="Datatype Operator">∋</a> <a id="32452" href="plfa.Lambda.html#32372" class="Bound">x</a> <a id="32454" href="plfa.Lambda.html#32254" class="Datatype Operator">⦂</a> <a id="32456" href="plfa.Lambda.html#32376" class="Bound">A</a>
</pre>{% endraw %}
The constructors `Z` and `S` correspond roughly to the constructors
`here` and `there` for the element-of relation `_∈_` on lists.
Constructor `S` takes an additional parameter, which ensures that
when we look up a variable that it is not _shadowed_ by another
variable with the same name to its left in the list.

### Typing judgment

The second judgment is written

    Γ ⊢ M ⦂ A

and indicates in context `Γ` that term `M` has type `A`.
Context `Γ` provides types for all the free variables in `M`.
For example:

* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ ``
* `` ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  `ℕ ⇒ `ℕ ``
* `` ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ ``

Typing is formalised as follows:
{% raw %}<pre class="Agda"><a id="33396" class="Keyword">infix</a>  <a id="33403" class="Number">4</a>  <a id="33406" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33418" class="Datatype Operator">_⊢_⦂_</a>

<a id="33413" class="Keyword">data</a> <a id="_⊢_⦂_"></a><a id="33418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33418" class="Datatype Operator">_⊢_⦂_</a> <a id="33424" class="Symbol">:</a> <a id="33426" href="plfa.Lambda.html#31031" class="Datatype">Context</a> <a id="33434" class="Symbol">→</a> <a id="33436" href="plfa.Lambda.html#3748" class="Datatype">Term</a> <a id="33441" class="Symbol">→</a> <a id="33443" href="plfa.Lambda.html#29373" class="Datatype">Type</a> <a id="33448" class="Symbol">→</a> <a id="33450" class="PrimitiveType">Set</a> <a id="33454" class="Keyword">where</a>

  <a id="33463" class="Comment">-- Axiom</a>
  <a id="_⊢_⦂_.⊢`"></a><a id="33474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33474" class="InductiveConstructor">⊢`</a> <a id="33477" class="Symbol">:</a> <a id="33479" class="Symbol">∀</a> <a id="33481" class="Symbol">{</a><a id="33482" href="plfa.Lambda.html#33482" class="Bound">Γ</a> <a id="33484" href="plfa.Lambda.html#33484" class="Bound">x</a> <a id="33486" href="plfa.Lambda.html#33486" class="Bound">A</a><a id="33487" class="Symbol">}</a>
    <a id="33493" class="Symbol">→</a> <a id="33495" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33482" class="Bound">Γ</a> <a id="33497" href="plfa.Lambda.html#32254" class="Datatype Operator">∋</a> <a id="33499" href="plfa.Lambda.html#33484" class="Bound">x</a> <a id="33501" href="plfa.Lambda.html#32254" class="Datatype Operator">⦂</a> <a id="33503" href="plfa.Lambda.html#33486" class="Bound">A</a>
      <a id="33511" class="Comment">-----------</a>
    <a id="33527" class="Symbol">→</a> <a id="33529" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33482" class="Bound">Γ</a> <a id="33531" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33533" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="33535" href="plfa.Lambda.html#33484" class="Bound">x</a> <a id="33537" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33539" href="plfa.Lambda.html#33486" class="Bound">A</a>

  <a id="33544" class="Comment">-- ⇒-I</a>
  <a id="_⊢_⦂_.⊢ƛ"></a><a id="33553" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33553" class="InductiveConstructor">⊢ƛ</a> <a id="33556" class="Symbol">:</a> <a id="33558" class="Symbol">∀</a> <a id="33560" class="Symbol">{</a><a id="33561" href="plfa.Lambda.html#33561" class="Bound">Γ</a> <a id="33563" href="plfa.Lambda.html#33563" class="Bound">x</a> <a id="33565" href="plfa.Lambda.html#33565" class="Bound">N</a> <a id="33567" href="plfa.Lambda.html#33567" class="Bound">A</a> <a id="33569" href="plfa.Lambda.html#33569" class="Bound">B</a><a id="33570" class="Symbol">}</a>
    <a id="33576" class="Symbol">→</a> <a id="33578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33561" class="Bound">Γ</a> <a id="33580" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">,</a> <a id="33582" href="plfa.Lambda.html#33563" class="Bound">x</a> <a id="33584" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">⦂</a> <a id="33586" href="plfa.Lambda.html#33567" class="Bound">A</a> <a id="33588" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33590" href="plfa.Lambda.html#33565" class="Bound">N</a> <a id="33592" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33594" href="plfa.Lambda.html#33569" class="Bound">B</a>
      <a id="33602" class="Comment">-------------------</a>
    <a id="33626" class="Symbol">→</a> <a id="33628" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33561" class="Bound">Γ</a> <a id="33630" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33632" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="33634" href="plfa.Lambda.html#33563" class="Bound">x</a> <a id="33636" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="33638" href="plfa.Lambda.html#33565" class="Bound">N</a> <a id="33640" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33642" href="plfa.Lambda.html#33567" class="Bound">A</a> <a id="33644" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="33646" href="plfa.Lambda.html#33569" class="Bound">B</a>

  <a id="33651" class="Comment">-- ⇒-E</a>
  <a id="_⊢_⦂_._·_"></a><a id="33660" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33660" class="InductiveConstructor Operator">_·_</a> <a id="33664" class="Symbol">:</a> <a id="33666" class="Symbol">∀</a> <a id="33668" class="Symbol">{</a><a id="33669" href="plfa.Lambda.html#33669" class="Bound">Γ</a> <a id="33671" href="plfa.Lambda.html#33671" class="Bound">L</a> <a id="33673" href="plfa.Lambda.html#33673" class="Bound">M</a> <a id="33675" href="plfa.Lambda.html#33675" class="Bound">A</a> <a id="33677" href="plfa.Lambda.html#33677" class="Bound">B</a><a id="33678" class="Symbol">}</a>
    <a id="33684" class="Symbol">→</a> <a id="33686" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33669" class="Bound">Γ</a> <a id="33688" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33690" href="plfa.Lambda.html#33671" class="Bound">L</a> <a id="33692" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33694" href="plfa.Lambda.html#33675" class="Bound">A</a> <a id="33696" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="33698" href="plfa.Lambda.html#33677" class="Bound">B</a>
    <a id="33704" class="Symbol">→</a> <a id="33706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33669" class="Bound">Γ</a> <a id="33708" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33710" href="plfa.Lambda.html#33673" class="Bound">M</a> <a id="33712" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33714" href="plfa.Lambda.html#33675" class="Bound">A</a>
      <a id="33722" class="Comment">-------------</a>
    <a id="33740" class="Symbol">→</a> <a id="33742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33669" class="Bound">Γ</a> <a id="33744" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33746" href="plfa.Lambda.html#33671" class="Bound">L</a> <a id="33748" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="33750" href="plfa.Lambda.html#33673" class="Bound">M</a> <a id="33752" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33754" href="plfa.Lambda.html#33677" class="Bound">B</a>

  <a id="33759" class="Comment">-- ℕ-I₁</a>
  <a id="_⊢_⦂_.⊢zero"></a><a id="33769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33769" class="InductiveConstructor">⊢zero</a> <a id="33775" class="Symbol">:</a> <a id="33777" class="Symbol">∀</a> <a id="33779" class="Symbol">{</a><a id="33780" href="plfa.Lambda.html#33780" class="Bound">Γ</a><a id="33781" class="Symbol">}</a>
      <a id="33789" class="Comment">--------------</a>
    <a id="33808" class="Symbol">→</a> <a id="33810" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33780" class="Bound">Γ</a> <a id="33812" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33814" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="33820" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33822" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>

  <a id="33828" class="Comment">-- ℕ-I₂</a>
  <a id="_⊢_⦂_.⊢suc"></a><a id="33838" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33838" class="InductiveConstructor">⊢suc</a> <a id="33843" class="Symbol">:</a> <a id="33845" class="Symbol">∀</a> <a id="33847" class="Symbol">{</a><a id="33848" href="plfa.Lambda.html#33848" class="Bound">Γ</a> <a id="33850" href="plfa.Lambda.html#33850" class="Bound">M</a><a id="33851" class="Symbol">}</a>
    <a id="33857" class="Symbol">→</a> <a id="33859" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33848" class="Bound">Γ</a> <a id="33861" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33863" href="plfa.Lambda.html#33850" class="Bound">M</a> <a id="33865" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33867" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
      <a id="33876" class="Comment">---------------</a>
    <a id="33896" class="Symbol">→</a> <a id="33898" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33848" class="Bound">Γ</a> <a id="33900" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33902" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="33907" href="plfa.Lambda.html#33850" class="Bound">M</a> <a id="33909" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33911" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>

  <a id="33917" class="Comment">-- ℕ-E</a>
  <a id="_⊢_⦂_.⊢case"></a><a id="33926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33926" class="InductiveConstructor">⊢case</a> <a id="33932" class="Symbol">:</a> <a id="33934" class="Symbol">∀</a> <a id="33936" class="Symbol">{</a><a id="33937" href="plfa.Lambda.html#33937" class="Bound">Γ</a> <a id="33939" href="plfa.Lambda.html#33939" class="Bound">L</a> <a id="33941" href="plfa.Lambda.html#33941" class="Bound">M</a> <a id="33943" href="plfa.Lambda.html#33943" class="Bound">x</a> <a id="33945" href="plfa.Lambda.html#33945" class="Bound">N</a> <a id="33947" href="plfa.Lambda.html#33947" class="Bound">A</a><a id="33948" class="Symbol">}</a>
    <a id="33954" class="Symbol">→</a> <a id="33956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33937" class="Bound">Γ</a> <a id="33958" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33960" href="plfa.Lambda.html#33939" class="Bound">L</a> <a id="33962" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33964" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
    <a id="33971" class="Symbol">→</a> <a id="33973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33937" class="Bound">Γ</a> <a id="33975" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="33977" href="plfa.Lambda.html#33941" class="Bound">M</a> <a id="33979" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="33981" href="plfa.Lambda.html#33947" class="Bound">A</a>
    <a id="33987" class="Symbol">→</a> <a id="33989" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33937" class="Bound">Γ</a> <a id="33991" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">,</a> <a id="33993" href="plfa.Lambda.html#33943" class="Bound">x</a> <a id="33995" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">⦂</a> <a id="33997" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a> <a id="34000" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="34002" href="plfa.Lambda.html#33945" class="Bound">N</a> <a id="34004" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="34006" href="plfa.Lambda.html#33947" class="Bound">A</a>
      <a id="34014" class="Comment">-------------------------------------</a>
    <a id="34056" class="Symbol">→</a> <a id="34058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33937" class="Bound">Γ</a> <a id="34060" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="34062" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">case</a> <a id="34067" href="plfa.Lambda.html#33939" class="Bound">L</a> <a id="34069" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">[zero⇒</a> <a id="34076" href="plfa.Lambda.html#33941" class="Bound">M</a> <a id="34078" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">|suc</a> <a id="34083" href="plfa.Lambda.html#33943" class="Bound">x</a> <a id="34085" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">⇒</a> <a id="34087" href="plfa.Lambda.html#33945" class="Bound">N</a> <a id="34089" href="plfa.Lambda.html#3975" class="InductiveConstructor Operator">]</a> <a id="34091" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="34093" href="plfa.Lambda.html#33947" class="Bound">A</a>

  <a id="_⊢_⦂_.⊢μ"></a><a id="34098" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#34098" class="InductiveConstructor">⊢μ</a> <a id="34101" class="Symbol">:</a> <a id="34103" class="Symbol">∀</a> <a id="34105" class="Symbol">{</a><a id="34106" href="plfa.Lambda.html#34106" class="Bound">Γ</a> <a id="34108" href="plfa.Lambda.html#34108" class="Bound">x</a> <a id="34110" href="plfa.Lambda.html#34110" class="Bound">M</a> <a id="34112" href="plfa.Lambda.html#34112" class="Bound">A</a><a id="34113" class="Symbol">}</a>
    <a id="34119" class="Symbol">→</a> <a id="34121" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#34106" class="Bound">Γ</a> <a id="34123" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">,</a> <a id="34125" href="plfa.Lambda.html#34108" class="Bound">x</a> <a id="34127" href="plfa.Lambda.html#31071" class="InductiveConstructor Operator">⦂</a> <a id="34129" href="plfa.Lambda.html#34112" class="Bound">A</a> <a id="34131" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="34133" href="plfa.Lambda.html#34110" class="Bound">M</a> <a id="34135" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="34137" href="plfa.Lambda.html#34112" class="Bound">A</a>
      <a id="34145" class="Comment">-----------------</a>
    <a id="34167" class="Symbol">→</a> <a id="34169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#34106" class="Bound">Γ</a> <a id="34171" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="34173" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">μ</a> <a id="34175" href="plfa.Lambda.html#34108" class="Bound">x</a> <a id="34177" href="plfa.Lambda.html#4035" class="InductiveConstructor Operator">⇒</a> <a id="34179" href="plfa.Lambda.html#34110" class="Bound">M</a> <a id="34181" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="34183" href="plfa.Lambda.html#34112" class="Bound">A</a>
</pre>{% endraw %}
Each type rule is named after the constructor for the
corresponding term.

Most of the rules have a second name, derived from a convention in
logic, whereby the rule is named after the type connective that it
concerns; rules to introduce and to eliminate each connective are
labeled `-I` and `-E`, respectively. As we read the rules from top to
bottom, introduction and elimination rules do what they say on the
tin: the first _introduces_ a formula for the connective, which
appears in the conclusion but not in the premises; while the second
_eliminates_ a formula for the connective, which appears in a premise
but not in the conclusion. An introduction rule describes how to
construct a value of the type (abstractions yield functions, successor
and zero yield naturals), while an elimination rule describes how to
deconstruct a value of the given type (applications use functions,
case expressions use naturals).

Note also the three places (in `⊢ƛ`, `⊢case`, and `⊢μ`) where the
context is extended with `x` and an appropriate type, corresponding to
the three places where a bound variable is introduced.

The rules are deterministic, in that at most one rule applies to every term.


### Checking inequality and postulating the impossible {#impossible}

The following function makes it convenient to assert an inequality:
{% raw %}<pre class="Agda"><a id="_≠_"></a><a id="35523" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35523" class="Function Operator">_≠_</a> <a id="35527" class="Symbol">:</a> <a id="35529" class="Symbol">∀</a> <a id="35531" class="Symbol">(</a><a id="35532" href="plfa.Lambda.html#35532" class="Bound">x</a> <a id="35534" href="plfa.Lambda.html#35534" class="Bound">y</a> <a id="35536" class="Symbol">:</a> <a id="35538" href="plfa.Lambda.html#3647" class="Function">Id</a><a id="35540" class="Symbol">)</a> <a id="35542" class="Symbol">→</a> <a id="35544" href="plfa.Lambda.html#35532" class="Bound">x</a> <a id="35546" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#799" class="Function Operator">≢</a> <a id="35548" href="plfa.Lambda.html#35534" class="Bound">y</a>
<a id="35550" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35550" class="Bound">x</a> <a id="35552" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="35554" href="plfa.Lambda.html#35554" class="Bound">y</a>  <a id="35557" class="Keyword">with</a> <a id="35562" href="plfa.Lambda.html#35550" class="Bound">x</a> <a id="35564" href="https://agda.github.io/agda-stdlib/v1.1/Data.String.Properties.html#2569" class="Function Operator">≟</a> <a id="35566" href="plfa.Lambda.html#35554" class="Bound">y</a>
<a id="35568" class="Symbol">...</a>       <a id="35578" class="Symbol">|</a> <a id="35580" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#668" class="InductiveConstructor">no</a>  <a id="35584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35584" class="Bound">x≢y</a>  <a id="35589" class="Symbol">=</a>  <a id="35592" href="plfa.Lambda.html#35584" class="Bound">x≢y</a>
<a id="35596" class="Symbol">...</a>       <a id="35606" class="Symbol">|</a> <a id="35608" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#641" class="InductiveConstructor">yes</a> <a id="35612" class="Symbol">_</a>    <a id="35617" class="Symbol">=</a>  <a id="35620" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="35627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35656" class="Postulate">impossible</a>
  <a id="35640" class="Keyword">where</a> <a id="35646" class="Keyword">postulate</a> <a id="35656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#35656" class="Postulate">impossible</a> <a id="35667" class="Symbol">:</a> <a id="35669" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#279" class="Datatype">⊥</a>
</pre>{% endraw %}Here `_≟_` is the function that tests two identifiers for equality.
We intend to apply the function only when the
two arguments are indeed unequal, and indicate that the second
case should never arise by postulating a term `impossible` of
the empty type `⊥`.  If we use C-c C-n to normalise the term

    "a" ≠ "a"

Agda will return an answer warning us that the impossible has occurred:

    ⊥-elim (.plfa.Lambda.impossible "a" "a" refl)

While postulating the impossible is a useful technique, it must be
used with care, since such postulation could allow us to provide
evidence of _any_ proposition whatsoever, regardless of its truth.


### Example type derivations {#derivation}

Type derivations correspond to trees. In informal notation, here
is a type derivation for the Church numeral two,

                            ∋s                     ∋z
                            ------------------ ⊢`  -------------- ⊢`
    ∋s                      Γ₂ ⊢ ` "s" ⦂ A ⇒ A     Γ₂ ⊢ ` "z" ⦂ A
    ------------------ ⊢`   ------------------------------------- _·_
    Γ₂ ⊢ ` "s" ⦂ A ⇒ A      Γ₂ ⊢ ` "s" · ` "z" ⦂ A
    ---------------------------------------------- _·_
    Γ₂ ⊢ ` "s" · (` "s" · ` "z") ⦂ A
    -------------------------------------------- ⊢ƛ
    Γ₁ ⊢ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ A ⇒ A
    ------------------------------------------------------------- ⊢ƛ
    Γ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") ⦂ (A ⇒ A) ⇒ A ⇒ A

where `∋s` and `∋z` abbreviate the two derivations,

                 ---------------- Z
    "s" ≢ "z"    Γ₁ ∋ "s" ⦂ A ⇒ A
    ----------------------------- S       ------------- Z
    Γ₂ ∋ "s" ⦂ A ⇒ A                       Γ₂ ∋ "z" ⦂ A

and where `Γ₁ = Γ , "s" ⦂ A ⇒ A` and `Γ₂ = Γ , "s" ⦂ A ⇒ A , "z" ⦂ A`.
The typing derivation is valid for any `Γ` and `A`, for instance,
we might take `Γ` to be `∅` and `A` to be `` `ℕ ``.

Here is the above typing derivation formalised in Agda:
{% raw %}<pre class="Agda"><a id="Ch"></a><a id="37602" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37602" class="Function">Ch</a> <a id="37605" class="Symbol">:</a> <a id="37607" href="plfa.Lambda.html#29373" class="Datatype">Type</a> <a id="37612" class="Symbol">→</a> <a id="37614" href="plfa.Lambda.html#29373" class="Datatype">Type</a>
<a id="37619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37602" class="Function">Ch</a> <a id="37622" href="plfa.Lambda.html#37622" class="Bound">A</a> <a id="37624" class="Symbol">=</a> <a id="37626" class="Symbol">(</a><a id="37627" href="plfa.Lambda.html#37622" class="Bound">A</a> <a id="37629" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="37631" href="plfa.Lambda.html#37622" class="Bound">A</a><a id="37632" class="Symbol">)</a> <a id="37634" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="37636" href="plfa.Lambda.html#37622" class="Bound">A</a> <a id="37638" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="37640" href="plfa.Lambda.html#37622" class="Bound">A</a>

<a id="⊢twoᶜ"></a><a id="37643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37643" class="Function">⊢twoᶜ</a> <a id="37649" class="Symbol">:</a> <a id="37651" class="Symbol">∀</a> <a id="37653" class="Symbol">{</a><a id="37654" href="plfa.Lambda.html#37654" class="Bound">Γ</a> <a id="37656" href="plfa.Lambda.html#37656" class="Bound">A</a><a id="37657" class="Symbol">}</a> <a id="37659" class="Symbol">→</a> <a id="37661" href="plfa.Lambda.html#37654" class="Bound">Γ</a> <a id="37663" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="37665" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="37670" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="37672" href="plfa.Lambda.html#37602" class="Function">Ch</a> <a id="37675" href="plfa.Lambda.html#37656" class="Bound">A</a>
<a id="37677" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37643" class="Function">⊢twoᶜ</a> <a id="37683" class="Symbol">=</a> <a id="37685" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="37688" class="Symbol">(</a><a id="37689" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="37692" class="Symbol">(</a><a id="37693" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37696" href="plfa.Lambda.html#37729" class="Function">∋s</a> <a id="37699" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="37701" class="Symbol">(</a><a id="37702" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37705" href="plfa.Lambda.html#37729" class="Function">∋s</a> <a id="37708" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="37710" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37713" href="plfa.Lambda.html#37752" class="Function">∋z</a><a id="37715" class="Symbol">)))</a>
  <a id="37721" class="Keyword">where</a>
  <a id="37729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37729" class="Function">∋s</a> <a id="37732" class="Symbol">=</a> <a id="37734" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="37736" class="Symbol">(</a><a id="37737" class="String">&quot;s&quot;</a> <a id="37741" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="37743" class="String">&quot;z&quot;</a><a id="37746" class="Symbol">)</a> <a id="37748" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>
  <a id="37752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37752" class="Function">∋z</a> <a id="37755" class="Symbol">=</a> <a id="37757" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>
</pre>{% endraw %}
Here are the typings corresponding to computing two plus two:
{% raw %}<pre class="Agda"><a id="⊢two"></a><a id="37830" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37830" class="Function">⊢two</a> <a id="37835" class="Symbol">:</a> <a id="37837" class="Symbol">∀</a> <a id="37839" class="Symbol">{</a><a id="37840" href="plfa.Lambda.html#37840" class="Bound">Γ</a><a id="37841" class="Symbol">}</a> <a id="37843" class="Symbol">→</a> <a id="37845" href="plfa.Lambda.html#37840" class="Bound">Γ</a> <a id="37847" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="37849" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="37853" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="37855" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
<a id="37858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37830" class="Function">⊢two</a> <a id="37863" class="Symbol">=</a> <a id="37865" href="plfa.Lambda.html#33838" class="InductiveConstructor">⊢suc</a> <a id="37870" class="Symbol">(</a><a id="37871" href="plfa.Lambda.html#33838" class="InductiveConstructor">⊢suc</a> <a id="37876" href="plfa.Lambda.html#33769" class="InductiveConstructor">⊢zero</a><a id="37881" class="Symbol">)</a>

<a id="⊢plus"></a><a id="37884" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37884" class="Function">⊢plus</a> <a id="37890" class="Symbol">:</a> <a id="37892" class="Symbol">∀</a> <a id="37894" class="Symbol">{</a><a id="37895" href="plfa.Lambda.html#37895" class="Bound">Γ</a><a id="37896" class="Symbol">}</a> <a id="37898" class="Symbol">→</a> <a id="37900" href="plfa.Lambda.html#37895" class="Bound">Γ</a> <a id="37902" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="37904" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="37909" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="37911" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a> <a id="37914" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="37916" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a> <a id="37919" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="37921" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
<a id="37924" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#37884" class="Function">⊢plus</a> <a id="37930" class="Symbol">=</a> <a id="37932" href="plfa.Lambda.html#34098" class="InductiveConstructor">⊢μ</a> <a id="37935" class="Symbol">(</a><a id="37936" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="37939" class="Symbol">(</a><a id="37940" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="37943" class="Symbol">(</a><a id="37944" href="plfa.Lambda.html#33926" class="InductiveConstructor">⊢case</a> <a id="37950" class="Symbol">(</a><a id="37951" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37954" href="plfa.Lambda.html#38079" class="Function">∋m</a><a id="37956" class="Symbol">)</a> <a id="37958" class="Symbol">(</a><a id="37959" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37962" href="plfa.Lambda.html#38105" class="Function">∋n</a><a id="37964" class="Symbol">)</a>
         <a id="37975" class="Symbol">(</a><a id="37976" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#33838" class="InductiveConstructor">⊢suc</a> <a id="37981" class="Symbol">(</a><a id="37982" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37985" href="plfa.Lambda.html#38021" class="Function">∋+</a> <a id="37988" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="37990" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="37993" href="plfa.Lambda.html#38115" class="Function">∋m′</a> <a id="37997" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="37999" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="38002" href="plfa.Lambda.html#38125" class="Function">∋n′</a><a id="38005" class="Symbol">)))))</a>
  <a id="38013" class="Keyword">where</a>
  <a id="38021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38021" class="Function">∋+</a>  <a id="38025" class="Symbol">=</a> <a id="38027" class="Symbol">(</a><a id="38028" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="38030" class="Symbol">(</a><a id="38031" class="String">&quot;+&quot;</a> <a id="38035" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="38037" class="String">&quot;m&quot;</a><a id="38040" class="Symbol">)</a> <a id="38042" class="Symbol">(</a><a id="38043" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="38045" class="Symbol">(</a><a id="38046" class="String">&quot;+&quot;</a> <a id="38050" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="38052" class="String">&quot;n&quot;</a><a id="38055" class="Symbol">)</a> <a id="38057" class="Symbol">(</a><a id="38058" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="38060" class="Symbol">(</a><a id="38061" class="String">&quot;+&quot;</a> <a id="38065" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="38067" class="String">&quot;m&quot;</a><a id="38070" class="Symbol">)</a> <a id="38072" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a><a id="38073" class="Symbol">)))</a>
  <a id="38079" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38079" class="Function">∋m</a>  <a id="38083" class="Symbol">=</a> <a id="38085" class="Symbol">(</a><a id="38086" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="38088" class="Symbol">(</a><a id="38089" class="String">&quot;m&quot;</a> <a id="38093" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="38095" class="String">&quot;n&quot;</a><a id="38098" class="Symbol">)</a> <a id="38100" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a><a id="38101" class="Symbol">)</a>
  <a id="38105" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38105" class="Function">∋n</a>  <a id="38109" class="Symbol">=</a> <a id="38111" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>
  <a id="38115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38115" class="Function">∋m′</a> <a id="38119" class="Symbol">=</a> <a id="38121" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>
  <a id="38125" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38125" class="Function">∋n′</a> <a id="38129" class="Symbol">=</a> <a id="38131" class="Symbol">(</a><a id="38132" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="38134" class="Symbol">(</a><a id="38135" class="String">&quot;n&quot;</a> <a id="38139" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="38141" class="String">&quot;m&quot;</a><a id="38144" class="Symbol">)</a> <a id="38146" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a><a id="38147" class="Symbol">)</a>

<a id="⊢2+2"></a><a id="38150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38150" class="Function">⊢2+2</a> <a id="38155" class="Symbol">:</a> <a id="38157" href="plfa.Lambda.html#31053" class="InductiveConstructor">∅</a> <a id="38159" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="38161" href="plfa.Lambda.html#4510" class="Function">plus</a> <a id="38166" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="38168" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="38172" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="38174" href="plfa.Lambda.html#4476" class="Function">two</a> <a id="38178" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="38180" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
<a id="38183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38150" class="Function">⊢2+2</a> <a id="38188" class="Symbol">=</a> <a id="38190" href="plfa.Lambda.html#37884" class="Function">⊢plus</a> <a id="38196" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="38198" href="plfa.Lambda.html#37830" class="Function">⊢two</a> <a id="38203" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="38205" href="plfa.Lambda.html#37830" class="Function">⊢two</a>
</pre>{% endraw %}In contrast to our earlier examples, here we have typed `two` and `plus`
in an arbitrary context rather than the empty context; this makes it easy
to use them inside other binding contexts as well as at the top level.
Here the two lookup judgments `∋m` and `∋m′` refer to two different
bindings of variables named `"m"`.  In contrast, the two judgments `∋n` and
`∋n′` both refer to the same binding of `"n"` but accessed in different
contexts, the first where "n" is the last binding in the context, and
the second after "m" is bound in the successor branch of the case.

And here are typings for the remainder of the Church example:
{% raw %}<pre class="Agda"><a id="⊢plusᶜ"></a><a id="38852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38852" class="Function">⊢plusᶜ</a> <a id="38859" class="Symbol">:</a> <a id="38861" class="Symbol">∀</a> <a id="38863" class="Symbol">{</a><a id="38864" href="plfa.Lambda.html#38864" class="Bound">Γ</a> <a id="38866" href="plfa.Lambda.html#38866" class="Bound">A</a><a id="38867" class="Symbol">}</a> <a id="38869" class="Symbol">→</a> <a id="38871" href="plfa.Lambda.html#38864" class="Bound">Γ</a>  <a id="38874" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="38876" href="plfa.Lambda.html#5786" class="Function">plusᶜ</a> <a id="38882" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="38884" href="plfa.Lambda.html#37602" class="Function">Ch</a> <a id="38887" href="plfa.Lambda.html#38866" class="Bound">A</a> <a id="38889" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="38891" href="plfa.Lambda.html#37602" class="Function">Ch</a> <a id="38894" href="plfa.Lambda.html#38866" class="Bound">A</a> <a id="38896" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="38898" href="plfa.Lambda.html#37602" class="Function">Ch</a> <a id="38901" href="plfa.Lambda.html#38866" class="Bound">A</a>
<a id="38903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38852" class="Function">⊢plusᶜ</a> <a id="38910" class="Symbol">=</a> <a id="38912" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="38915" class="Symbol">(</a><a id="38916" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="38919" class="Symbol">(</a><a id="38920" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="38923" class="Symbol">(</a><a id="38924" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="38927" class="Symbol">(</a><a id="38928" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="38931" href="plfa.Lambda.html#38982" class="Function">∋m</a> <a id="38934" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="38936" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="38939" href="plfa.Lambda.html#39076" class="Function">∋s</a> <a id="38942" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="38944" class="Symbol">(</a><a id="38945" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="38948" href="plfa.Lambda.html#39037" class="Function">∋n</a> <a id="38951" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="38953" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="38956" href="plfa.Lambda.html#39076" class="Function">∋s</a> <a id="38959" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="38961" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="38964" href="plfa.Lambda.html#39099" class="Function">∋z</a><a id="38966" class="Symbol">)))))</a>
  <a id="38974" class="Keyword">where</a>
  <a id="38982" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#38982" class="Function">∋m</a> <a id="38985" class="Symbol">=</a> <a id="38987" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="38989" class="Symbol">(</a><a id="38990" class="String">&quot;m&quot;</a> <a id="38994" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="38996" class="String">&quot;z&quot;</a><a id="38999" class="Symbol">)</a> <a id="39001" class="Symbol">(</a><a id="39002" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="39004" class="Symbol">(</a><a id="39005" class="String">&quot;m&quot;</a> <a id="39009" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="39011" class="String">&quot;s&quot;</a><a id="39014" class="Symbol">)</a> <a id="39016" class="Symbol">(</a><a id="39017" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="39019" class="Symbol">(</a><a id="39020" class="String">&quot;m&quot;</a> <a id="39024" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="39026" class="String">&quot;n&quot;</a><a id="39029" class="Symbol">)</a> <a id="39031" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a><a id="39032" class="Symbol">))</a>
  <a id="39037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39037" class="Function">∋n</a> <a id="39040" class="Symbol">=</a> <a id="39042" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="39044" class="Symbol">(</a><a id="39045" class="String">&quot;n&quot;</a> <a id="39049" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="39051" class="String">&quot;z&quot;</a><a id="39054" class="Symbol">)</a> <a id="39056" class="Symbol">(</a><a id="39057" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="39059" class="Symbol">(</a><a id="39060" class="String">&quot;n&quot;</a> <a id="39064" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="39066" class="String">&quot;s&quot;</a><a id="39069" class="Symbol">)</a> <a id="39071" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a><a id="39072" class="Symbol">)</a>
  <a id="39076" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39076" class="Function">∋s</a> <a id="39079" class="Symbol">=</a> <a id="39081" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="39083" class="Symbol">(</a><a id="39084" class="String">&quot;s&quot;</a> <a id="39088" href="plfa.Lambda.html#35523" class="Function Operator">≠</a> <a id="39090" class="String">&quot;z&quot;</a><a id="39093" class="Symbol">)</a> <a id="39095" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>
  <a id="39099" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39099" class="Function">∋z</a> <a id="39102" class="Symbol">=</a> <a id="39104" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>

<a id="⊢sucᶜ"></a><a id="39107" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39107" class="Function">⊢sucᶜ</a> <a id="39113" class="Symbol">:</a> <a id="39115" class="Symbol">∀</a> <a id="39117" class="Symbol">{</a><a id="39118" href="plfa.Lambda.html#39118" class="Bound">Γ</a><a id="39119" class="Symbol">}</a> <a id="39121" class="Symbol">→</a> <a id="39123" href="plfa.Lambda.html#39118" class="Bound">Γ</a> <a id="39125" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="39127" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="39132" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="39134" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a> <a id="39137" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="39139" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
<a id="39142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39107" class="Function">⊢sucᶜ</a> <a id="39148" class="Symbol">=</a> <a id="39150" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="39153" class="Symbol">(</a><a id="39154" href="plfa.Lambda.html#33838" class="InductiveConstructor">⊢suc</a> <a id="39159" class="Symbol">(</a><a id="39160" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="39163" href="plfa.Lambda.html#39178" class="Function">∋n</a><a id="39165" class="Symbol">))</a>
  <a id="39170" class="Keyword">where</a>
  <a id="39178" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39178" class="Function">∋n</a> <a id="39181" class="Symbol">=</a> <a id="39183" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>

<a id="⊢2+2ᶜ"></a><a id="39186" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39186" class="Function">⊢2+2ᶜ</a> <a id="39192" class="Symbol">:</a> <a id="39194" href="plfa.Lambda.html#31053" class="InductiveConstructor">∅</a> <a id="39196" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="39198" href="plfa.Lambda.html#5786" class="Function">plusᶜ</a> <a id="39204" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="39206" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="39211" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="39213" href="plfa.Lambda.html#5725" class="Function">twoᶜ</a> <a id="39218" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="39220" href="plfa.Lambda.html#5890" class="Function">sucᶜ</a> <a id="39225" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="39227" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="39233" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="39235" href="plfa.Lambda.html#29419" class="InductiveConstructor">`ℕ</a>
<a id="39238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#39186" class="Function">⊢2+2ᶜ</a> <a id="39244" class="Symbol">=</a> <a id="39246" href="plfa.Lambda.html#38852" class="Function">⊢plusᶜ</a> <a id="39253" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="39255" href="plfa.Lambda.html#37643" class="Function">⊢twoᶜ</a> <a id="39261" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="39263" href="plfa.Lambda.html#37643" class="Function">⊢twoᶜ</a> <a id="39269" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="39271" href="plfa.Lambda.html#39107" class="Function">⊢sucᶜ</a> <a id="39277" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="39279" href="plfa.Lambda.html#33769" class="InductiveConstructor">⊢zero</a>
</pre>{% endraw %}
### Interaction with Agda

Construction of a type derivation may be done interactively.
Start with the declaration:

    ⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
    ⊢sucᶜ = ?

Typing C-c C-l causes Agda to create a hole and tell us its expected type:

    ⊢sucᶜ = { }0
    ?0 : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ

Now we fill in the hole by typing C-c C-r. Agda observes that
the outermost term in `sucᶜ` is `ƛ`, which is typed using `⊢ƛ`. The
`⊢ƛ` rule in turn takes one argument, which Agda leaves as a hole:

    ⊢sucᶜ = ⊢ƛ { }1
    ?1 : ∅ , "n" ⦂ `ℕ ⊢ `suc ` "n" ⦂ `ℕ

We can fill in the hole by typing C-c C-r again:

    ⊢sucᶜ = ⊢ƛ (⊢suc { }2)
    ?2 : ∅ , "n" ⦂ `ℕ ⊢ ` "n" ⦂ `ℕ

And again:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` { }3))
    ?3 : ∅ , "n" ⦂ `ℕ ∋ "n" ⦂ `ℕ

A further attempt with C-c C-r yields the message:

    Don't know which constructor to introduce of Z or S

We can fill in `Z` by hand. If we type C-c C-space, Agda will confirm we are done:

    ⊢suc′ = ⊢ƛ (⊢suc (⊢` Z))

The entire process can be automated using Agsy, invoked with C-c C-a.

Chapter [Inference]({{ site.baseurl }}/Inference/)
will show how to use Agda to compute type derivations directly.


### Lookup is injective

The lookup relation `Γ ∋ x ⦂ A` is injective, in that for each `Γ` and `x`
there is at most one `A` such that the judgment holds:
{% raw %}<pre class="Agda"><a id="∋-injective"></a><a id="40595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40595" class="Function">∋-injective</a> <a id="40607" class="Symbol">:</a> <a id="40609" class="Symbol">∀</a> <a id="40611" class="Symbol">{</a><a id="40612" href="plfa.Lambda.html#40612" class="Bound">Γ</a> <a id="40614" href="plfa.Lambda.html#40614" class="Bound">x</a> <a id="40616" href="plfa.Lambda.html#40616" class="Bound">A</a> <a id="40618" href="plfa.Lambda.html#40618" class="Bound">B</a><a id="40619" class="Symbol">}</a> <a id="40621" class="Symbol">→</a> <a id="40623" href="plfa.Lambda.html#40612" class="Bound">Γ</a> <a id="40625" href="plfa.Lambda.html#32254" class="Datatype Operator">∋</a> <a id="40627" href="plfa.Lambda.html#40614" class="Bound">x</a> <a id="40629" href="plfa.Lambda.html#32254" class="Datatype Operator">⦂</a> <a id="40631" href="plfa.Lambda.html#40616" class="Bound">A</a> <a id="40633" class="Symbol">→</a> <a id="40635" href="plfa.Lambda.html#40612" class="Bound">Γ</a> <a id="40637" href="plfa.Lambda.html#32254" class="Datatype Operator">∋</a> <a id="40639" href="plfa.Lambda.html#40614" class="Bound">x</a> <a id="40641" href="plfa.Lambda.html#32254" class="Datatype Operator">⦂</a> <a id="40643" href="plfa.Lambda.html#40618" class="Bound">B</a> <a id="40645" class="Symbol">→</a> <a id="40647" href="plfa.Lambda.html#40616" class="Bound">A</a> <a id="40649" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="40651" href="plfa.Lambda.html#40618" class="Bound">B</a>
<a id="40653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40595" class="Function">∋-injective</a> <a id="40665" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>        <a id="40674" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>          <a id="40685" class="Symbol">=</a>  <a id="40688" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="40693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40595" class="Function">∋-injective</a> <a id="40705" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>        <a id="40714" class="Symbol">(</a><a id="40715" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="40717" href="plfa.Lambda.html#40717" class="Bound">x≢</a> <a id="40720" class="Symbol">_)</a>   <a id="40725" class="Symbol">=</a>  <a id="40728" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40735" class="Symbol">(</a><a id="40736" href="plfa.Lambda.html#40717" class="Bound">x≢</a> <a id="40739" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40743" class="Symbol">)</a>
<a id="40745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40595" class="Function">∋-injective</a> <a id="40757" class="Symbol">(</a><a id="40758" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="40760" href="plfa.Lambda.html#40760" class="Bound">x≢</a> <a id="40763" class="Symbol">_)</a> <a id="40766" href="plfa.Lambda.html#32297" class="InductiveConstructor">Z</a>          <a id="40777" class="Symbol">=</a>  <a id="40780" href="https://agda.github.io/agda-stdlib/v1.1/Data.Empty.html#294" class="Function">⊥-elim</a> <a id="40787" class="Symbol">(</a><a id="40788" href="plfa.Lambda.html#40760" class="Bound">x≢</a> <a id="40791" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="40795" class="Symbol">)</a>
<a id="40797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#40595" class="Function">∋-injective</a> <a id="40809" class="Symbol">(</a><a id="40810" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="40812" class="Symbol">_</a> <a id="40814" href="plfa.Lambda.html#40814" class="Bound">∋x</a><a id="40816" class="Symbol">)</a> <a id="40818" class="Symbol">(</a><a id="40819" href="plfa.Lambda.html#32363" class="InductiveConstructor">S</a> <a id="40821" class="Symbol">_</a> <a id="40823" href="plfa.Lambda.html#40823" class="Bound">∋x′</a><a id="40826" class="Symbol">)</a>  <a id="40829" class="Symbol">=</a>  <a id="40832" href="plfa.Lambda.html#40595" class="Function">∋-injective</a> <a id="40844" href="plfa.Lambda.html#40814" class="Bound">∋x</a> <a id="40847" href="plfa.Lambda.html#40823" class="Bound">∋x′</a>
</pre>{% endraw %}
The typing relation `Γ ⊢ M ⦂ A` is not injective. For example, in any `Γ`
the term `ƛ "x" ⇒ "x"` has type `A ⇒ A` for any type `A`.

### Non-examples

We can also show that terms are _not_ typeable.  For example, here is
a formal proof that it is not possible to type the term
`` `zero · `suc `zero ``.  It cannot be typed, because doing so
requires that the first term in the application is both a natural and
a function:

{% raw %}<pre class="Agda"><a id="nope₁"></a><a id="41284" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41284" class="Function">nope₁</a> <a id="41290" class="Symbol">:</a> <a id="41292" class="Symbol">∀</a> <a id="41294" class="Symbol">{</a><a id="41295" href="plfa.Lambda.html#41295" class="Bound">A</a><a id="41296" class="Symbol">}</a> <a id="41298" class="Symbol">→</a> <a id="41300" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41302" class="Symbol">(</a><a id="41303" href="plfa.Lambda.html#31053" class="InductiveConstructor">∅</a> <a id="41305" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="41307" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="41313" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="41315" href="plfa.Lambda.html#3934" class="InductiveConstructor Operator">`suc</a> <a id="41320" href="plfa.Lambda.html#3900" class="InductiveConstructor">`zero</a> <a id="41326" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="41328" href="plfa.Lambda.html#41295" class="Bound">A</a><a id="41329" class="Symbol">)</a>
<a id="41331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41284" class="Function">nope₁</a> <a id="41337" class="Symbol">(()</a> <a id="41341" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="41343" class="Symbol">_)</a>
</pre>{% endraw %}
As a second example, here is a formal proof that it is not possible to
type `` ƛ "x" ⇒ ` "x" · ` "x" ``. It cannot be typed, because
doing so requires types `A` and `B` such that `A ⇒ B ≡ A`:

{% raw %}<pre class="Agda"><a id="nope₂"></a><a id="41548" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41548" class="Function">nope₂</a> <a id="41554" class="Symbol">:</a> <a id="41556" class="Symbol">∀</a> <a id="41558" class="Symbol">{</a><a id="41559" href="plfa.Lambda.html#41559" class="Bound">A</a><a id="41560" class="Symbol">}</a> <a id="41562" class="Symbol">→</a> <a id="41564" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41566" class="Symbol">(</a><a id="41567" href="plfa.Lambda.html#31053" class="InductiveConstructor">∅</a> <a id="41569" href="plfa.Lambda.html#33418" class="Datatype Operator">⊢</a> <a id="41571" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">ƛ</a> <a id="41573" class="String">&quot;x&quot;</a> <a id="41577" href="plfa.Lambda.html#3806" class="InductiveConstructor Operator">⇒</a> <a id="41579" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="41581" class="String">&quot;x&quot;</a> <a id="41585" href="plfa.Lambda.html#3852" class="InductiveConstructor Operator">·</a> <a id="41587" href="plfa.Lambda.html#3767" class="InductiveConstructor Operator">`</a> <a id="41589" class="String">&quot;x&quot;</a> <a id="41593" href="plfa.Lambda.html#33418" class="Datatype Operator">⦂</a> <a id="41595" href="plfa.Lambda.html#41559" class="Bound">A</a><a id="41596" class="Symbol">)</a>
<a id="41598" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41548" class="Function">nope₂</a> <a id="41604" class="Symbol">(</a><a id="41605" href="plfa.Lambda.html#33553" class="InductiveConstructor">⊢ƛ</a> <a id="41608" class="Symbol">(</a><a id="41609" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="41612" href="plfa.Lambda.html#41612" class="Bound">∋x</a> <a id="41615" href="plfa.Lambda.html#33660" class="InductiveConstructor Operator">·</a> <a id="41617" href="plfa.Lambda.html#33474" class="InductiveConstructor">⊢`</a> <a id="41620" href="plfa.Lambda.html#41620" class="Bound">∋x′</a><a id="41623" class="Symbol">))</a>  <a id="41627" class="Symbol">=</a>  <a id="41630" href="plfa.Lambda.html#41675" class="Function">contradiction</a> <a id="41644" class="Symbol">(</a><a id="41645" href="plfa.Lambda.html#40595" class="Function">∋-injective</a> <a id="41657" href="plfa.Lambda.html#41612" class="Bound">∋x</a> <a id="41660" href="plfa.Lambda.html#41620" class="Bound">∋x′</a><a id="41663" class="Symbol">)</a>
  <a id="41667" class="Keyword">where</a>
  <a id="41675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41675" class="Function">contradiction</a> <a id="41689" class="Symbol">:</a> <a id="41691" class="Symbol">∀</a> <a id="41693" class="Symbol">{</a><a id="41694" href="plfa.Lambda.html#41694" class="Bound">A</a> <a id="41696" href="plfa.Lambda.html#41696" class="Bound">B</a><a id="41697" class="Symbol">}</a> <a id="41699" class="Symbol">→</a> <a id="41701" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Nullary.html#535" class="Function Operator">¬</a> <a id="41703" class="Symbol">(</a><a id="41704" href="plfa.Lambda.html#41694" class="Bound">A</a> <a id="41706" href="plfa.Lambda.html#29392" class="InductiveConstructor Operator">⇒</a> <a id="41708" href="plfa.Lambda.html#41696" class="Bound">B</a> <a id="41710" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="41712" href="plfa.Lambda.html#41694" class="Bound">A</a><a id="41713" class="Symbol">)</a>
  <a id="41717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Lambda.md %}{% raw %}#41675" class="Function">contradiction</a> <a id="41731" class="Symbol">()</a>
</pre>{% endraw %}

#### Quiz

For each of the following, give a type `A` for which it is derivable,
or explain why there is no such `A`.

1. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A ``
2. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A ``
3. `` ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A ``

For each of the following, give types `A`, `B`, and `C` for which it is derivable,
or explain why there are no such types.

1. `` ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B ``
2. `` ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C ``


#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42410" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

#### Exercise `mulᶜ-type`

Using the term `mulᶜ` you defined earlier, write out the derivation
showing that it is well typed.

{% raw %}<pre class="Agda"><a id="42570" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}

## Unicode

This chapter uses the following unicode:

    ⇒  U+21D2  RIGHTWARDS DOUBLE ARROW (\=>)
    ƛ  U+019B  LATIN SMALL LETTER LAMBDA WITH STROKE (\Gl-)
    ·  U+00B7  MIDDLE DOT (\cdot)
    —  U+2014  EM DASH (\em)
    ↠  U+21A0  RIGHTWARDS TWO HEADED ARROW (\rr-)
    ξ  U+03BE  GREEK SMALL LETTER XI (\Gx or \xi)
    β  U+03B2  GREEK SMALL LETTER BETA (\Gb or \beta)
    Γ  U+0393  GREEK CAPITAL LETTER GAMMA (\GG or \Gamma)
    ≠  U+2260  NOT EQUAL TO (\=n or \ne)
    ∋  U+220B  CONTAINS AS MEMBER (\ni)
    ∅  U+2205  EMPTY SET (\0)
    ⊢  U+22A2  RIGHT TACK (\vdash or \|-)
    ⦂  U+2982  Z NOTATION TYPE COLON (\:)
    😇  U+1F607  SMILING FACE WITH HALO
    😈  U+1F608  SMILING FACE WITH HORNS

We compose reduction `—→` from an em dash `—` and an arrow `→`.
Similarly for reflexive and transitive closure `—↠`.
