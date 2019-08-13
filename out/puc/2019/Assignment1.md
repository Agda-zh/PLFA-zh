---
src       : "courses/puc/2019/Assignment1.lagda.md"
title     : "Assignment1: PUC Assignment 1"
layout    : page
permalink : /PUC/2019/Assignment1/
---

{% raw %}<pre class="Agda"><a id="110" class="Keyword">module</a> <a id="117" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment1.md %}{% raw %}" class="Module">Assignment1</a> <a id="129" class="Keyword">where</a>
</pre>{% endraw %}
## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

{% raw %}<pre class="Agda"><a id="555" class="Keyword">import</a> <a id="562" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="600" class="Symbol">as</a> <a id="603" class="Module">Eq</a>
<a id="606" class="Keyword">open</a> <a id="611" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="614" class="Keyword">using</a> <a id="620" class="Symbol">(</a><a id="621" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="624" class="Symbol">;</a> <a id="626" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="630" class="Symbol">;</a> <a id="632" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="636" class="Symbol">;</a> <a id="638" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#939" class="Function">sym</a><a id="641" class="Symbol">)</a>
<a id="643" class="Keyword">open</a> <a id="648" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2499" class="Module">Eq.≡-Reasoning</a> <a id="663" class="Keyword">using</a> <a id="669" class="Symbol">(</a><a id="670" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2597" class="Function Operator">begin_</a><a id="676" class="Symbol">;</a> <a id="678" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2655" class="Function Operator">_≡⟨⟩_</a><a id="683" class="Symbol">;</a> <a id="685" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2714" class="Function Operator">_≡⟨_⟩_</a><a id="691" class="Symbol">;</a> <a id="693" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#2892" class="Function Operator">_∎</a><a id="695" class="Symbol">)</a>
<a id="697" class="Keyword">open</a> <a id="702" class="Keyword">import</a> <a id="709" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="718" class="Keyword">using</a> <a id="724" class="Symbol">(</a><a id="725" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="726" class="Symbol">;</a> <a id="728" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="732" class="Symbol">;</a> <a id="734" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="737" class="Symbol">;</a> <a id="739" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="742" class="Symbol">;</a> <a id="744" href="Agda.Builtin.Nat.html#501" class="Primitive Operator">_*_</a><a id="747" class="Symbol">;</a> <a id="749" href="Agda.Builtin.Nat.html#388" class="Primitive Operator">_∸_</a><a id="752" class="Symbol">;</a> <a id="754" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="757" class="Symbol">;</a> <a id="759" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="762" class="Symbol">;</a> <a id="764" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="767" class="Symbol">)</a>
<a id="769" class="Keyword">open</a> <a id="774" class="Keyword">import</a> <a id="781" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="801" class="Keyword">using</a> <a id="807" class="Symbol">(</a><a id="808" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11578" class="Function">+-assoc</a><a id="815" class="Symbol">;</a> <a id="817" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11734" class="Function">+-identityʳ</a><a id="828" class="Symbol">;</a> <a id="830" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11370" class="Function">+-suc</a><a id="835" class="Symbol">;</a> <a id="837" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="843" class="Symbol">;</a>
  <a id="847" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="853" class="Symbol">;</a> <a id="855" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="862" class="Symbol">;</a> <a id="864" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="873" class="Symbol">;</a> <a id="875" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="882" class="Symbol">;</a> <a id="884" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="893" class="Symbol">;</a> <a id="895" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="904" class="Symbol">;</a> <a id="906" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="914" class="Symbol">)</a>
<a id="916" class="Keyword">open</a> <a id="921" class="Keyword">import</a> <a id="928" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="943" class="Keyword">using</a> <a id="949" class="Symbol">(</a><a id="950" href="plfa.Relations.html#26522" class="Datatype Operator">_&lt;_</a><a id="953" class="Symbol">;</a> <a id="955" href="plfa.Relations.html#26549" class="InductiveConstructor">z&lt;s</a><a id="958" class="Symbol">;</a> <a id="960" href="plfa.Relations.html#26606" class="InductiveConstructor">s&lt;s</a><a id="963" class="Symbol">;</a> <a id="965" href="plfa.Relations.html#30834" class="InductiveConstructor">zero</a><a id="969" class="Symbol">;</a> <a id="971" href="plfa.Relations.html#30876" class="InductiveConstructor">suc</a><a id="974" class="Symbol">;</a> <a id="976" href="plfa.Relations.html#30779" class="Datatype">even</a><a id="980" class="Symbol">;</a> <a id="982" href="plfa.Relations.html#30799" class="Datatype">odd</a><a id="985" class="Symbol">)</a>
</pre>{% endraw %}
## Naturals

#### Exercise `seven` {#seven}

Write out `7` in longhand.


#### Exercise `+-example` {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.


#### Exercise `*-example` {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.


#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.


#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
{% raw %}<pre class="Agda"><a id="1808" class="Keyword">data</a> <a id="Bin"></a><a id="1813" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment1.md %}{% raw %}#1813" class="Datatype">Bin</a> <a id="1817" class="Symbol">:</a> <a id="1819" class="PrimitiveType">Set</a> <a id="1823" class="Keyword">where</a>
  <a id="Bin.nil"></a><a id="1831" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment1.md %}{% raw %}#1831" class="InductiveConstructor">nil</a> <a id="1835" class="Symbol">:</a> <a id="1837" href="Assignment1.html#1813" class="Datatype">Bin</a>
  <a id="Bin.x0_"></a><a id="1843" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment1.md %}{% raw %}#1843" class="InductiveConstructor Operator">x0_</a> <a id="1847" class="Symbol">:</a> <a id="1849" href="Assignment1.html#1813" class="Datatype">Bin</a> <a id="1853" class="Symbol">→</a> <a id="1855" href="Assignment1.html#1813" class="Datatype">Bin</a>
  <a id="Bin.x1_"></a><a id="1861" href="{% endraw %}{{ site.baseurl }}{% link out/puc/2019/Assignment1.md %}{% raw %}#1861" class="InductiveConstructor Operator">x1_</a> <a id="1865" class="Symbol">:</a> <a id="1867" href="Assignment1.html#1813" class="Datatype">Bin</a> <a id="1871" class="Symbol">→</a> <a id="1873" href="Assignment1.html#1813" class="Datatype">Bin</a>
</pre>{% endraw %}For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

## Induction

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-|-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap}

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-|-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


## Relations


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` {#leq-antisym-cases}

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)
