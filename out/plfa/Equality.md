---
src       : "src/plfa/Equality.lagda.md"
title     : "Equality: 相等性与等式推理"
layout    : page
prev      : /Relations/
permalink : /Equality/
next      : /Isomorphism/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="183" class="Keyword">module</a> <a id="190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}" class="Module">plfa.Equality</a> <a id="204" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
Much of our reasoning has involved equality.  Given two terms `M`
and `N`, both of type `A`, we write `M ≡ N` to assert that `M` and `N`
are interchangeable.  So far we have treated equality as a primitive,
here we show how to define it as an inductive datatype.
{:/}

我们在论证的过程中经常会使用相等性。给定两个都为 `A` 类型的项 `M` 和 `N`，
我们用 `M ≡ N` 来表示 `M` 和 `N` 可以相互替换。在此之前，
我们将相等性作为一个基础运算，而现在我们来说明如果将其定义为一个归纳的数据类型。


{::comment}
## Imports
{:/}

## 导入

{::comment}
This chapter has no imports.  Every chapter in this book, and nearly
every module in the Agda standard library, imports equality.
Since we define equality here, any import would create a conflict.
{:/}

本章节没有导入的内容。本书的每一章节，以及 Agda 标准库的每个模块都导入了相等性。
我们在此定义相等性，导入其他内容将会产生冲突。


{::comment}
## Equality
{:/}

## 相等性

{::comment}
We declare equality as follows:
{:/}

我们如下定义相等性：

{% raw %}<pre class="Agda"><a id="1048" class="Keyword">data</a> <a id="_≡_"></a><a id="1053" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1053" class="Datatype Operator">_≡_</a> <a id="1057" class="Symbol">{</a><a id="1058" href="plfa.Equality.html#1058" class="Bound">A</a> <a id="1060" class="Symbol">:</a> <a id="1062" class="PrimitiveType">Set</a><a id="1065" class="Symbol">}</a> <a id="1067" class="Symbol">(</a><a id="1068" href="plfa.Equality.html#1068" class="Bound">x</a> <a id="1070" class="Symbol">:</a> <a id="1072" href="plfa.Equality.html#1058" class="Bound">A</a><a id="1073" class="Symbol">)</a> <a id="1075" class="Symbol">:</a> <a id="1077" href="plfa.Equality.html#1058" class="Bound">A</a> <a id="1079" class="Symbol">→</a> <a id="1081" class="PrimitiveType">Set</a> <a id="1085" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="1093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1093" class="InductiveConstructor">refl</a> <a id="1098" class="Symbol">:</a> <a id="1100" href="plfa.Equality.html#1068" class="Bound">x</a> <a id="1102" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="1104" href="plfa.Equality.html#1068" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
In other words, for any type `A` and for any `x` of type `A`, the
constructor `refl` provides evidence that `x ≡ x`. Hence, every value
is equal to itself, and we have no other way of showing values
equal.  The definition features an asymmetry, in that the
first argument to `_≡_` is given by the parameter `x : A`, while the
second is given by an index in `A → Set`.  This follows our policy
of using parameters wherever possible.  The first argument to `_≡_`
can be a parameter because it doesn't vary, while the second must be
an index, so it can be required to be equal to the first.
{:/}

用其他的话来说，对于任意类型 `A` 和任意 `A` 类型的 `x`，构造子 `refl` 提供了
`x ≡ x` 的证明。所以，每个值等同于它本身，我们并没有其他办法来证明值的相等性。
这个定义里有不对称的地方，`_≡_` 的第一个参数（Argument）由 `x : A` 给出，
而第二个参数（Argument）则是由 `A → Set` 的索引给出。
这和我们尽可能多的使用参数（Parameter）的理念相符。`_≡_` 的第一个参数（Argument）
可以作为一个参数（Parameter），因为它不会变，而第二个参数（Argument）则必须是一个索引，
这样它才可以等用于第一个。

{::comment}
We declare the precedence of equality as follows:
{:/}

我们如下定义相等性的优先级：

{% raw %}<pre class="Agda"><a id="2106" class="Keyword">infix</a> <a id="2112" class="Number">4</a> <a id="2114" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1053" class="Datatype Operator">_≡_</a>
</pre>{% endraw %}
{::comment}
We set the precedence of `_≡_` at level 4, the same as `_≤_`,
which means it binds less tightly than any arithmetic operator.
It associates neither to left nor right; writing `x ≡ y ≡ z`
is illegal.
{:/}

我们将 `_≡_` 的优先级设置为 4，与 `_≤_` 相同，所以其它算术运算符的结合都比它紧密。
由于它既不是左结合，也不是右结合的，因此 `x ≡ y ≡ z` 是不合法的。


{::comment}
## Equality is an equivalence relation
{:/}

## 相等性是一个等价关系（Equivalence Relation）

{::comment}
An equivalence relation is one which is reflexive, symmetric, and transitive.
Reflexivity is built-in to the definition of equality, via the
constructor `refl`.  It is straightforward to show symmetry:
{:/}

一个等价关系是自反、对称和传递的。其中自反性可以通过构造子 `refl` 直接从相等性的定义中得来。
我们可以直接地证明其对称性：

{% raw %}<pre class="Agda"><a id="sym"></a><a id="2817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2817" class="Function">sym</a> <a id="2821" class="Symbol">:</a> <a id="2823" class="Symbol">∀</a> <a id="2825" class="Symbol">{</a><a id="2826" href="plfa.Equality.html#2826" class="Bound">A</a> <a id="2828" class="Symbol">:</a> <a id="2830" class="PrimitiveType">Set</a><a id="2833" class="Symbol">}</a> <a id="2835" class="Symbol">{</a><a id="2836" href="plfa.Equality.html#2836" class="Bound">x</a> <a id="2838" href="plfa.Equality.html#2838" class="Bound">y</a> <a id="2840" class="Symbol">:</a> <a id="2842" href="plfa.Equality.html#2826" class="Bound">A</a><a id="2843" class="Symbol">}</a>
  <a id="2847" class="Symbol">→</a> <a id="2849" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2836" class="Bound">x</a> <a id="2851" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="2853" href="plfa.Equality.html#2838" class="Bound">y</a>
    <a id="2859" class="Comment">-----</a>
  <a id="2867" class="Symbol">→</a> <a id="2869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2838" class="Bound">y</a> <a id="2871" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="2873" href="plfa.Equality.html#2836" class="Bound">x</a>
<a id="2875" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#2817" class="Function">sym</a> <a id="2879" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="2884" class="Symbol">=</a> <a id="2886" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
How does this proof work? The argument to `sym` has type `x ≡ y`, but
on the left-hand side of the equation the argument has been
instantiated to the pattern `refl`, which requires that `x` and `y`
are the same.  Hence, for the right-hand side of the equation we need
a term of type `x ≡ x`, and `refl` will do.
{:/}

这个证明是怎么运作的呢？`sym` 参数的类型是 `x ≡ y`，但是等式的左手边被 `refl` 模式实例化了，
这要求 `x` 和 `y` 相等。因此，等式的右手边需要一个类型为 `x ≡ x` 的项，用 `refl` 即可。

{::comment}
It is instructive to develop `sym` interactively.  To start, we supply
a variable for the argument on the left, and a hole for the body on
the right:
{:/}

交互式地证明 `sym` 很有教育意义。首先，我们在左手边使用一个变量来表示参数，在右手边使用一个洞：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym e = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入这个洞，使用 `C-c C-,`，Agda 会告诉我们：

    Goal: .y ≡ .x
    ————————————————————————————————————————————————————————————
    e  : .x ≡ .y
    .y : .A
    .x : .A
    .A : Set

{::comment}
If in the hole we type `C-c C-c e` then Agda will instantiate `e` to
all possible constructors, with one equation for each. There is only
one possible constructor:
{:/}

在这个洞里，我们使用 `C-c C-c e`，Agda 会将 `e` 逐一展开为所有可能的构造子。
此处只有一个构造子：

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入这个洞，重新使用 `C-c C-,`，然后 Agda 现在会告诉我们：

     Goal: .x ≡ .x
     ————————————————————————————————————————————————————————————
     .x : .A
     .A : Set

{::comment}
This is the key step---Agda has worked out that `x` and `y` must be
the same to match the pattern `refl`!
{:/}

这是一个重要的步骤—— Agda 发现了 `x` 和 `y` 必须相等，才能与模式 `refl` 相匹配。

{::comment}
Finally, if we go back into the hole and type `C-c C-r` it will
instantiate the hole with the one constructor that yields a value of
the expected type:
{:/}

最后，我们回到洞里，使用 `C-c C-r`，Agda 将会把洞变成一个可以满足给定类型的构造子实例。

    sym : ∀ {A : Set} {x y : A}
      → x ≡ y
        -----
      → y ≡ x
    sym refl = refl

{::comment}
This completes the definition as given above.
{:/}

我们至此完成了与之前给出证明相同的证明。

{::comment}
Transitivity is equally straightforward:
{:/}

传递性亦是很直接：

{% raw %}<pre class="Agda"><a id="trans"></a><a id="5154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5154" class="Function">trans</a> <a id="5160" class="Symbol">:</a> <a id="5162" class="Symbol">∀</a> <a id="5164" class="Symbol">{</a><a id="5165" href="plfa.Equality.html#5165" class="Bound">A</a> <a id="5167" class="Symbol">:</a> <a id="5169" class="PrimitiveType">Set</a><a id="5172" class="Symbol">}</a> <a id="5174" class="Symbol">{</a><a id="5175" href="plfa.Equality.html#5175" class="Bound">x</a> <a id="5177" href="plfa.Equality.html#5177" class="Bound">y</a> <a id="5179" href="plfa.Equality.html#5179" class="Bound">z</a> <a id="5181" class="Symbol">:</a> <a id="5183" href="plfa.Equality.html#5165" class="Bound">A</a><a id="5184" class="Symbol">}</a>
  <a id="5188" class="Symbol">→</a> <a id="5190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5175" class="Bound">x</a> <a id="5192" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5194" href="plfa.Equality.html#5177" class="Bound">y</a>
  <a id="5198" class="Symbol">→</a> <a id="5200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5177" class="Bound">y</a> <a id="5202" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5204" href="plfa.Equality.html#5179" class="Bound">z</a>
    <a id="5210" class="Comment">-----</a>
  <a id="5218" class="Symbol">→</a> <a id="5220" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5175" class="Bound">x</a> <a id="5222" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5224" href="plfa.Equality.html#5179" class="Bound">z</a>
<a id="5226" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5154" class="Function">trans</a> <a id="5232" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="5237" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>  <a id="5243" class="Symbol">=</a>  <a id="5246" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Again, a useful exercise is to carry out an interactive development,
checking how Agda's knowledge changes as each of the two arguments is
instantiated.
{:/}

同样，交互式地证明这个特性是一个很好的练习，尤其是观察 Agda 的已知内容根据参数的实例而变化的过程。


{::comment}
## Congruence and substitution {#cong}
{:/}

## 合同性和替换性 {#cong}

{::comment}
Equality satisfies _congruence_.  If two terms are equal,
they remain so after the same function is applied to both:
{:/}

相等性满足 *合同性*（Congurence）。如果两个项相等，那么对它们使用相同的函数，
其结果仍然相等：

{% raw %}<pre class="Agda"><a id="cong"></a><a id="5754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5754" class="Function">cong</a> <a id="5759" class="Symbol">:</a> <a id="5761" class="Symbol">∀</a> <a id="5763" class="Symbol">{</a><a id="5764" href="plfa.Equality.html#5764" class="Bound">A</a> <a id="5766" href="plfa.Equality.html#5766" class="Bound">B</a> <a id="5768" class="Symbol">:</a> <a id="5770" class="PrimitiveType">Set</a><a id="5773" class="Symbol">}</a> <a id="5775" class="Symbol">(</a><a id="5776" href="plfa.Equality.html#5776" class="Bound">f</a> <a id="5778" class="Symbol">:</a> <a id="5780" href="plfa.Equality.html#5764" class="Bound">A</a> <a id="5782" class="Symbol">→</a> <a id="5784" href="plfa.Equality.html#5766" class="Bound">B</a><a id="5785" class="Symbol">)</a> <a id="5787" class="Symbol">{</a><a id="5788" href="plfa.Equality.html#5788" class="Bound">x</a> <a id="5790" href="plfa.Equality.html#5790" class="Bound">y</a> <a id="5792" class="Symbol">:</a> <a id="5794" href="plfa.Equality.html#5764" class="Bound">A</a><a id="5795" class="Symbol">}</a>
  <a id="5799" class="Symbol">→</a> <a id="5801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5788" class="Bound">x</a> <a id="5803" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5805" href="plfa.Equality.html#5790" class="Bound">y</a>
    <a id="5811" class="Comment">---------</a>
  <a id="5823" class="Symbol">→</a> <a id="5825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5776" class="Bound">f</a> <a id="5827" href="plfa.Equality.html#5788" class="Bound">x</a> <a id="5829" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="5831" href="plfa.Equality.html#5776" class="Bound">f</a> <a id="5833" href="plfa.Equality.html#5790" class="Bound">y</a>
<a id="5835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5754" class="Function">cong</a> <a id="5840" href="plfa.Equality.html#5840" class="Bound">f</a> <a id="5842" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>  <a id="5848" class="Symbol">=</a>  <a id="5851" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Congruence of functions with two arguments is similar:
{:/}

两个参数的函数也满足合同性：

{% raw %}<pre class="Agda"><a id="cong₂"></a><a id="5954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5954" class="Function">cong₂</a> <a id="5960" class="Symbol">:</a> <a id="5962" class="Symbol">∀</a> <a id="5964" class="Symbol">{</a><a id="5965" href="plfa.Equality.html#5965" class="Bound">A</a> <a id="5967" href="plfa.Equality.html#5967" class="Bound">B</a> <a id="5969" href="plfa.Equality.html#5969" class="Bound">C</a> <a id="5971" class="Symbol">:</a> <a id="5973" class="PrimitiveType">Set</a><a id="5976" class="Symbol">}</a> <a id="5978" class="Symbol">(</a><a id="5979" href="plfa.Equality.html#5979" class="Bound">f</a> <a id="5981" class="Symbol">:</a> <a id="5983" href="plfa.Equality.html#5965" class="Bound">A</a> <a id="5985" class="Symbol">→</a> <a id="5987" href="plfa.Equality.html#5967" class="Bound">B</a> <a id="5989" class="Symbol">→</a> <a id="5991" href="plfa.Equality.html#5969" class="Bound">C</a><a id="5992" class="Symbol">)</a> <a id="5994" class="Symbol">{</a><a id="5995" href="plfa.Equality.html#5995" class="Bound">u</a> <a id="5997" href="plfa.Equality.html#5997" class="Bound">x</a> <a id="5999" class="Symbol">:</a> <a id="6001" href="plfa.Equality.html#5965" class="Bound">A</a><a id="6002" class="Symbol">}</a> <a id="6004" class="Symbol">{</a><a id="6005" href="plfa.Equality.html#6005" class="Bound">v</a> <a id="6007" href="plfa.Equality.html#6007" class="Bound">y</a> <a id="6009" class="Symbol">:</a> <a id="6011" href="plfa.Equality.html#5967" class="Bound">B</a><a id="6012" class="Symbol">}</a>
  <a id="6016" class="Symbol">→</a> <a id="6018" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5995" class="Bound">u</a> <a id="6020" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6022" href="plfa.Equality.html#5997" class="Bound">x</a>
  <a id="6026" class="Symbol">→</a> <a id="6028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6005" class="Bound">v</a> <a id="6030" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6032" href="plfa.Equality.html#6007" class="Bound">y</a>
    <a id="6038" class="Comment">-------------</a>
  <a id="6054" class="Symbol">→</a> <a id="6056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5979" class="Bound">f</a> <a id="6058" href="plfa.Equality.html#5995" class="Bound">u</a> <a id="6060" href="plfa.Equality.html#6005" class="Bound">v</a> <a id="6062" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6064" href="plfa.Equality.html#5979" class="Bound">f</a> <a id="6066" href="plfa.Equality.html#5997" class="Bound">x</a> <a id="6068" href="plfa.Equality.html#6007" class="Bound">y</a>
<a id="6070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#5954" class="Function">cong₂</a> <a id="6076" href="plfa.Equality.html#6076" class="Bound">f</a> <a id="6078" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="6083" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>  <a id="6089" class="Symbol">=</a>  <a id="6092" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Equality is also a congruence in the function position of an application.
If two functions are equal, then applying them to the same term
yields equal terms:
{:/}

在函数上的等价性也满足合同性。如果两个函数是相等的，那么它们作用在同一项上的结果是相等的：

{% raw %}<pre class="Agda"><a id="cong-app"></a><a id="6329" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6329" class="Function">cong-app</a> <a id="6338" class="Symbol">:</a> <a id="6340" class="Symbol">∀</a> <a id="6342" class="Symbol">{</a><a id="6343" href="plfa.Equality.html#6343" class="Bound">A</a> <a id="6345" href="plfa.Equality.html#6345" class="Bound">B</a> <a id="6347" class="Symbol">:</a> <a id="6349" class="PrimitiveType">Set</a><a id="6352" class="Symbol">}</a> <a id="6354" class="Symbol">{</a><a id="6355" href="plfa.Equality.html#6355" class="Bound">f</a> <a id="6357" href="plfa.Equality.html#6357" class="Bound">g</a> <a id="6359" class="Symbol">:</a> <a id="6361" href="plfa.Equality.html#6343" class="Bound">A</a> <a id="6363" class="Symbol">→</a> <a id="6365" href="plfa.Equality.html#6345" class="Bound">B</a><a id="6366" class="Symbol">}</a>
  <a id="6370" class="Symbol">→</a> <a id="6372" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6355" class="Bound">f</a> <a id="6374" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6376" href="plfa.Equality.html#6357" class="Bound">g</a>
    <a id="6382" class="Comment">---------------------</a>
  <a id="6406" class="Symbol">→</a> <a id="6408" class="Symbol">∀</a> <a id="6410" class="Symbol">(</a><a id="6411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6411" class="Bound">x</a> <a id="6413" class="Symbol">:</a> <a id="6415" href="plfa.Equality.html#6343" class="Bound">A</a><a id="6416" class="Symbol">)</a> <a id="6418" class="Symbol">→</a> <a id="6420" href="plfa.Equality.html#6355" class="Bound">f</a> <a id="6422" href="plfa.Equality.html#6411" class="Bound">x</a> <a id="6424" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6426" href="plfa.Equality.html#6357" class="Bound">g</a> <a id="6428" href="plfa.Equality.html#6411" class="Bound">x</a>
<a id="6430" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6329" class="Function">cong-app</a> <a id="6439" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="6444" href="plfa.Equality.html#6444" class="Bound">x</a> <a id="6446" class="Symbol">=</a> <a id="6448" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
Equality also satisfies *substitution*.
If two values are equal and a predicate holds of the first then it also holds of the second:
{:/}

相等性也满足*替换性*（Substitution）。
如果两个值相等，其中一个满足某谓词，那么另一个也满足此谓词。

{% raw %}<pre class="Agda"><a id="subst"></a><a id="6672" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6672" class="Function">subst</a> <a id="6678" class="Symbol">:</a> <a id="6680" class="Symbol">∀</a> <a id="6682" class="Symbol">{</a><a id="6683" href="plfa.Equality.html#6683" class="Bound">A</a> <a id="6685" class="Symbol">:</a> <a id="6687" class="PrimitiveType">Set</a><a id="6690" class="Symbol">}</a> <a id="6692" class="Symbol">{</a><a id="6693" href="plfa.Equality.html#6693" class="Bound">x</a> <a id="6695" href="plfa.Equality.html#6695" class="Bound">y</a> <a id="6697" class="Symbol">:</a> <a id="6699" href="plfa.Equality.html#6683" class="Bound">A</a><a id="6700" class="Symbol">}</a> <a id="6702" class="Symbol">(</a><a id="6703" href="plfa.Equality.html#6703" class="Bound">P</a> <a id="6705" class="Symbol">:</a> <a id="6707" href="plfa.Equality.html#6683" class="Bound">A</a> <a id="6709" class="Symbol">→</a> <a id="6711" class="PrimitiveType">Set</a><a id="6714" class="Symbol">)</a>
  <a id="6718" class="Symbol">→</a> <a id="6720" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6693" class="Bound">x</a> <a id="6722" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="6724" href="plfa.Equality.html#6695" class="Bound">y</a>
    <a id="6730" class="Comment">---------</a>
  <a id="6742" class="Symbol">→</a> <a id="6744" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6703" class="Bound">P</a> <a id="6746" href="plfa.Equality.html#6693" class="Bound">x</a> <a id="6748" class="Symbol">→</a> <a id="6750" href="plfa.Equality.html#6703" class="Bound">P</a> <a id="6752" href="plfa.Equality.html#6695" class="Bound">y</a>
<a id="6754" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#6672" class="Function">subst</a> <a id="6760" href="plfa.Equality.html#6760" class="Bound">P</a> <a id="6762" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a> <a id="6767" href="plfa.Equality.html#6767" class="Bound">px</a> <a id="6770" class="Symbol">=</a> <a id="6772" href="plfa.Equality.html#6767" class="Bound">px</a>
</pre>{% endraw %}

{::comment}
## Chains of equations
{:/}

## 等式串

{::comment}
Here we show how to support reasoning with chains of equations, as
used throughout the book.  We package the declarations into a module,
named `≡-Reasoning`, to match the format used in Agda's standard
library:
{:/}

我们在此演示如何使用等式串来论证，正如本书中使用证明形式。我们讲声明放在一个叫做
`≡-Reasoning` 的模块里，与 Agda 标准库中的格式相对应。

{% raw %}<pre class="Agda"><a id="7143" class="Keyword">module</a> <a id="≡-Reasoning"></a><a id="7150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7150" class="Module">≡-Reasoning</a> <a id="7162" class="Symbol">{</a><a id="7163" href="plfa.Equality.html#7163" class="Bound">A</a> <a id="7165" class="Symbol">:</a> <a id="7167" class="PrimitiveType">Set</a><a id="7170" class="Symbol">}</a> <a id="7172" class="Keyword">where</a>

  <a id="7181" class="Keyword">infix</a>  <a id="7188" class="Number">1</a> <a id="7190" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7238" class="Function Operator">begin_</a>
  <a id="7199" class="Keyword">infixr</a> <a id="7206" class="Number">2</a> <a id="7208" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7318" class="Function Operator">_≡⟨⟩_</a> <a id="7214" href="plfa.Equality.html#7403" class="Function Operator">_≡⟨_⟩_</a>
  <a id="7223" class="Keyword">infix</a>  <a id="7230" class="Number">3</a> <a id="7232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7518" class="Function Operator">_∎</a>

  <a id="≡-Reasoning.begin_"></a><a id="7238" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7238" class="Function Operator">begin_</a> <a id="7245" class="Symbol">:</a> <a id="7247" class="Symbol">∀</a> <a id="7249" class="Symbol">{</a><a id="7250" href="plfa.Equality.html#7250" class="Bound">x</a> <a id="7252" href="plfa.Equality.html#7252" class="Bound">y</a> <a id="7254" class="Symbol">:</a> <a id="7256" href="plfa.Equality.html#7163" class="Bound">A</a><a id="7257" class="Symbol">}</a>
    <a id="7263" class="Symbol">→</a> <a id="7265" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7250" class="Bound">x</a> <a id="7267" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7269" href="plfa.Equality.html#7252" class="Bound">y</a>
      <a id="7277" class="Comment">-----</a>
    <a id="7287" class="Symbol">→</a> <a id="7289" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7250" class="Bound">x</a> <a id="7291" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7293" href="plfa.Equality.html#7252" class="Bound">y</a>
  <a id="7297" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7238" class="Function Operator">begin</a> <a id="7303" href="plfa.Equality.html#7303" class="Bound">x≡y</a>  <a id="7308" class="Symbol">=</a>  <a id="7311" href="plfa.Equality.html#7303" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨⟩_"></a><a id="7318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7318" class="Function Operator">_≡⟨⟩_</a> <a id="7324" class="Symbol">:</a> <a id="7326" class="Symbol">∀</a> <a id="7328" class="Symbol">(</a><a id="7329" href="plfa.Equality.html#7329" class="Bound">x</a> <a id="7331" class="Symbol">:</a> <a id="7333" href="plfa.Equality.html#7163" class="Bound">A</a><a id="7334" class="Symbol">)</a> <a id="7336" class="Symbol">{</a><a id="7337" href="plfa.Equality.html#7337" class="Bound">y</a> <a id="7339" class="Symbol">:</a> <a id="7341" href="plfa.Equality.html#7163" class="Bound">A</a><a id="7342" class="Symbol">}</a>
    <a id="7348" class="Symbol">→</a> <a id="7350" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7329" class="Bound">x</a> <a id="7352" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7354" href="plfa.Equality.html#7337" class="Bound">y</a>
      <a id="7362" class="Comment">-----</a>
    <a id="7372" class="Symbol">→</a> <a id="7374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7329" class="Bound">x</a> <a id="7376" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7378" href="plfa.Equality.html#7337" class="Bound">y</a>
  <a id="7382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7382" class="Bound">x</a> <a id="7384" href="plfa.Equality.html#7318" class="Function Operator">≡⟨⟩</a> <a id="7388" href="plfa.Equality.html#7388" class="Bound">x≡y</a>  <a id="7393" class="Symbol">=</a>  <a id="7396" href="plfa.Equality.html#7388" class="Bound">x≡y</a>

  <a id="≡-Reasoning._≡⟨_⟩_"></a><a id="7403" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7403" class="Function Operator">_≡⟨_⟩_</a> <a id="7410" class="Symbol">:</a> <a id="7412" class="Symbol">∀</a> <a id="7414" class="Symbol">(</a><a id="7415" href="plfa.Equality.html#7415" class="Bound">x</a> <a id="7417" class="Symbol">:</a> <a id="7419" href="plfa.Equality.html#7163" class="Bound">A</a><a id="7420" class="Symbol">)</a> <a id="7422" class="Symbol">{</a><a id="7423" href="plfa.Equality.html#7423" class="Bound">y</a> <a id="7425" href="plfa.Equality.html#7425" class="Bound">z</a> <a id="7427" class="Symbol">:</a> <a id="7429" href="plfa.Equality.html#7163" class="Bound">A</a><a id="7430" class="Symbol">}</a>
    <a id="7436" class="Symbol">→</a> <a id="7438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7415" class="Bound">x</a> <a id="7440" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7442" href="plfa.Equality.html#7423" class="Bound">y</a>
    <a id="7448" class="Symbol">→</a> <a id="7450" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7423" class="Bound">y</a> <a id="7452" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7454" href="plfa.Equality.html#7425" class="Bound">z</a>
      <a id="7462" class="Comment">-----</a>
    <a id="7472" class="Symbol">→</a> <a id="7474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7415" class="Bound">x</a> <a id="7476" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7478" href="plfa.Equality.html#7425" class="Bound">z</a>
  <a id="7482" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7482" class="Bound">x</a> <a id="7484" href="plfa.Equality.html#7403" class="Function Operator">≡⟨</a> <a id="7487" href="plfa.Equality.html#7487" class="Bound">x≡y</a> <a id="7491" href="plfa.Equality.html#7403" class="Function Operator">⟩</a> <a id="7493" href="plfa.Equality.html#7493" class="Bound">y≡z</a>  <a id="7498" class="Symbol">=</a>  <a id="7501" href="plfa.Equality.html#5154" class="Function">trans</a> <a id="7507" href="plfa.Equality.html#7487" class="Bound">x≡y</a> <a id="7511" href="plfa.Equality.html#7493" class="Bound">y≡z</a>

  <a id="≡-Reasoning._∎"></a><a id="7518" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7518" class="Function Operator">_∎</a> <a id="7521" class="Symbol">:</a> <a id="7523" class="Symbol">∀</a> <a id="7525" class="Symbol">(</a><a id="7526" href="plfa.Equality.html#7526" class="Bound">x</a> <a id="7528" class="Symbol">:</a> <a id="7530" href="plfa.Equality.html#7163" class="Bound">A</a><a id="7531" class="Symbol">)</a>
      <a id="7539" class="Comment">-----</a>
    <a id="7549" class="Symbol">→</a> <a id="7551" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7526" class="Bound">x</a> <a id="7553" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="7555" href="plfa.Equality.html#7526" class="Bound">x</a>
  <a id="7559" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7559" class="Bound">x</a> <a id="7561" href="plfa.Equality.html#7518" class="Function Operator">∎</a>  <a id="7564" class="Symbol">=</a>  <a id="7567" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>

<a id="7573" class="Keyword">open</a> <a id="7578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7150" class="Module">≡-Reasoning</a>
</pre>{% endraw %}
{::comment}
This is our first use of a nested module. It consists of the keyword
`module` followed by the module name and any parameters, explicit or
implicit, the keyword `where`, and the contents of the module indented.
Modules may contain any sort of declaration, including other nested modules.
Nested modules are similar to the top-level modules that constitute
each chapter of this book, save that the body of a top-level module
need not be indented.  Opening the module makes all of the definitions
available in the current environment.
{:/}

这是我们第一次使用嵌套的模块。它包括了关键字 `module` 和后续的模块名、隐式或显式参数，
关键字 `where`，和模块中的内容（在缩进内）。模块里可以包括任何形式的声明，也可以包括其他模块。
嵌套的模块和本书每章节所定义的顶层模块相似，只是顶层模块不需要缩进。
打开（Open）一个模块会把模块内的所有定义导入进当前的环境中。

{::comment}
As an example, let's look at a proof of transitivity
as a chain of equations:
{:/}

举个例子，我们来看看如何用等式串证明传递性：

{% raw %}<pre class="Agda"><a id="trans′"></a><a id="8439" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8439" class="Function">trans′</a> <a id="8446" class="Symbol">:</a> <a id="8448" class="Symbol">∀</a> <a id="8450" class="Symbol">{</a><a id="8451" href="plfa.Equality.html#8451" class="Bound">A</a> <a id="8453" class="Symbol">:</a> <a id="8455" class="PrimitiveType">Set</a><a id="8458" class="Symbol">}</a> <a id="8460" class="Symbol">{</a><a id="8461" href="plfa.Equality.html#8461" class="Bound">x</a> <a id="8463" href="plfa.Equality.html#8463" class="Bound">y</a> <a id="8465" href="plfa.Equality.html#8465" class="Bound">z</a> <a id="8467" class="Symbol">:</a> <a id="8469" href="plfa.Equality.html#8451" class="Bound">A</a><a id="8470" class="Symbol">}</a>
  <a id="8474" class="Symbol">→</a> <a id="8476" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8461" class="Bound">x</a> <a id="8478" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="8480" href="plfa.Equality.html#8463" class="Bound">y</a>
  <a id="8484" class="Symbol">→</a> <a id="8486" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8463" class="Bound">y</a> <a id="8488" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="8490" href="plfa.Equality.html#8465" class="Bound">z</a>
    <a id="8496" class="Comment">-----</a>
  <a id="8504" class="Symbol">→</a> <a id="8506" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8461" class="Bound">x</a> <a id="8508" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="8510" href="plfa.Equality.html#8465" class="Bound">z</a>
<a id="8512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8439" class="Function">trans′</a> <a id="8519" class="Symbol">{</a><a id="8520" href="plfa.Equality.html#8520" class="Bound">A</a><a id="8521" class="Symbol">}</a> <a id="8523" class="Symbol">{</a><a id="8524" href="plfa.Equality.html#8524" class="Bound">x</a><a id="8525" class="Symbol">}</a> <a id="8527" class="Symbol">{</a><a id="8528" href="plfa.Equality.html#8528" class="Bound">y</a><a id="8529" class="Symbol">}</a> <a id="8531" class="Symbol">{</a><a id="8532" href="plfa.Equality.html#8532" class="Bound">z</a><a id="8533" class="Symbol">}</a> <a id="8535" href="plfa.Equality.html#8535" class="Bound">x≡y</a> <a id="8539" href="plfa.Equality.html#8539" class="Bound">y≡z</a> <a id="8543" class="Symbol">=</a>
  <a id="8547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7238" class="Function Operator">begin</a>
    <a id="8557" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8524" class="Bound">x</a>
  <a id="8561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7403" class="Function Operator">≡⟨</a> <a id="8564" href="plfa.Equality.html#8535" class="Bound">x≡y</a> <a id="8568" href="plfa.Equality.html#7403" class="Function Operator">⟩</a>
    <a id="8574" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8528" class="Bound">y</a>
  <a id="8578" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7403" class="Function Operator">≡⟨</a> <a id="8581" href="plfa.Equality.html#8539" class="Bound">y≡z</a> <a id="8585" href="plfa.Equality.html#7403" class="Function Operator">⟩</a>
    <a id="8591" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#8532" class="Bound">z</a>
  <a id="8595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7518" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
According to the fixity declarations, the body parses as follows:
{:/}

根据其定义，等式右边会被解析成如下：

    begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))

{::comment}
The application of `begin` is purely cosmetic, as it simply returns
its argument.  That argument consists of `_≡⟨_⟩_` applied to `x`,
`x≡y`, and `y ≡⟨ y≡z ⟩ (z ∎)`.  The first argument is a term, `x`,
while the second and third arguments are both proofs of equations, in
particular proofs of `x ≡ y` and `y ≡ z` respectively, which are
combined by `trans` in the body of `_≡⟨_⟩_` to yield a proof of `x ≡
z`.  The proof of `y ≡ z` consists of `_≡⟨_⟩_` applied to `y`, `y≡z`,
and `z ∎`.  The first argument is a term, `y`, while the second and
third arguments are both proofs of equations, in particular proofs of
`y ≡ z` and `z ≡ z` respectively, which are combined by `trans` in the
body of `_≡⟨_⟩_` to yield a proof of `y ≡ z`.  Finally, the proof of
`z ≡ z` consists of `_∎` applied to the term `z`, which yields `refl`.
After simplification, the body is equivalent to the term:
{:/}

这里 `begin` 的使用纯粹是装饰性的，因为它直接返回了其参数。其参数包括了
`_≡⟨_⟩_` 作用于 `x`、`x≡y` 和 `y ≡⟨ y≡z ⟩ (z ∎)`。第一个参数是一个项 `x`，
而第二、第三个参数分别是等式 `x ≡ y`、`y ≡ z` 的证明，它们在 `_≡⟨_⟩_` 的定义中用
`trans` 连接起来，形成 `x ≡ z` 的证明。`y ≡ z` 的证明包括了 `_≡⟨_⟩_` 作用于 `y`、
`y≡z` 和 `z ∎`。第一个参数是一个项 `y`，而第二、第三个参数分别是等式 `y ≡ z`、`z ≡ z` 的证明，
它们在 `_≡⟨_⟩_` 的定义中用 `trans` 连接起来，形成 `y ≡ z` 的证明。最后，`z ≡ z`
的证明包括了 `_∎` 作用于 `z` 之上，使用了 `refl`。经过化简，上述定义等同于：

    trans x≡y (trans y≡z refl)

{::comment}
We could replace any use of a chain of equations by a chain of
applications of `trans`; the result would be more compact but harder
to read.  The trick behind `∎` means that a chain of equalities
simplifies to a chain of applications of `trans` that ends in `trans e
refl`, where `e` is a term that proves some equality, even though `e`
alone would do.
{:/}

我们可以把任意等式串转化成一系列的 `trans` 的使用。这样的证明更加精简，但是更难以阅读。
`∎` 的小窍门意味着等式串化简成为的一系列 `trans` 会以 `trans e refl` 结尾，尽管只需要 `e`
就足够了，这里的 `e` 是等式的证明。


{::comment}
## Chains of equations, another example
{:/}

## 等式串的另外一个例子

{::comment}
As a second example of chains of equations, we repeat the proof that addition
is commutative.  We first repeat the definitions of naturals and addition.
We cannot import them because (as noted at the beginning of this chapter)
it would cause a conflict:
{:/}

我们重新证明加法的交换律来作为等式串的第二个例子。我们首先重复自然数和加法的定义。
我们不能导入它们（正如本章节开头中所解释的那样），因为那样会产生一个冲突：

{% raw %}<pre class="Agda"><a id="11002" class="Keyword">data</a> <a id="ℕ"></a><a id="11007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11007" class="Datatype">ℕ</a> <a id="11009" class="Symbol">:</a> <a id="11011" class="PrimitiveType">Set</a> <a id="11015" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="11023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11023" class="InductiveConstructor">zero</a> <a id="11028" class="Symbol">:</a> <a id="11030" href="plfa.Equality.html#11007" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="11034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11034" class="InductiveConstructor">suc</a>  <a id="11039" class="Symbol">:</a> <a id="11041" href="plfa.Equality.html#11007" class="Datatype">ℕ</a> <a id="11043" class="Symbol">→</a> <a id="11045" href="plfa.Equality.html#11007" class="Datatype">ℕ</a>

<a id="_+_"></a><a id="11048" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11048" class="Function Operator">_+_</a> <a id="11052" class="Symbol">:</a> <a id="11054" href="plfa.Equality.html#11007" class="Datatype">ℕ</a> <a id="11056" class="Symbol">→</a> <a id="11058" href="plfa.Equality.html#11007" class="Datatype">ℕ</a> <a id="11060" class="Symbol">→</a> <a id="11062" href="plfa.Equality.html#11007" class="Datatype">ℕ</a>
<a id="11064" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11023" class="InductiveConstructor">zero</a>    <a id="11072" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11074" href="plfa.Equality.html#11074" class="Bound">n</a>  <a id="11077" class="Symbol">=</a>  <a id="11080" href="plfa.Equality.html#11074" class="Bound">n</a>
<a id="11082" class="Symbol">(</a><a id="11083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11034" class="InductiveConstructor">suc</a> <a id="11087" href="plfa.Equality.html#11087" class="Bound">m</a><a id="11088" class="Symbol">)</a> <a id="11090" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11092" href="plfa.Equality.html#11092" class="Bound">n</a>  <a id="11095" class="Symbol">=</a>  <a id="11098" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="11102" class="Symbol">(</a><a id="11103" href="plfa.Equality.html#11087" class="Bound">m</a> <a id="11105" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11107" href="plfa.Equality.html#11092" class="Bound">n</a><a id="11108" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
To save space we postulate (rather than prove in full) two lemmas:
{:/}

为了节约空间，我们假设两条引理（而不是证明它们）：

{% raw %}<pre class="Agda"><a id="11231" class="Keyword">postulate</a>
  <a id="+-identity"></a><a id="11243" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11243" class="Postulate">+-identity</a> <a id="11254" class="Symbol">:</a> <a id="11256" class="Symbol">∀</a> <a id="11258" class="Symbol">(</a><a id="11259" href="plfa.Equality.html#11259" class="Bound">m</a> <a id="11261" class="Symbol">:</a> <a id="11263" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="11264" class="Symbol">)</a> <a id="11266" class="Symbol">→</a> <a id="11268" href="plfa.Equality.html#11259" class="Bound">m</a> <a id="11270" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11272" href="plfa.Equality.html#11023" class="InductiveConstructor">zero</a> <a id="11277" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="11279" href="plfa.Equality.html#11259" class="Bound">m</a>
  <a id="+-suc"></a><a id="11283" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11283" class="Postulate">+-suc</a> <a id="11289" class="Symbol">:</a> <a id="11291" class="Symbol">∀</a> <a id="11293" class="Symbol">(</a><a id="11294" href="plfa.Equality.html#11294" class="Bound">m</a> <a id="11296" href="plfa.Equality.html#11296" class="Bound">n</a> <a id="11298" class="Symbol">:</a> <a id="11300" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="11301" class="Symbol">)</a> <a id="11303" class="Symbol">→</a> <a id="11305" href="plfa.Equality.html#11294" class="Bound">m</a> <a id="11307" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11309" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="11313" href="plfa.Equality.html#11296" class="Bound">n</a> <a id="11315" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="11317" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="11321" class="Symbol">(</a><a id="11322" href="plfa.Equality.html#11294" class="Bound">m</a> <a id="11324" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11326" href="plfa.Equality.html#11296" class="Bound">n</a><a id="11327" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is our first use of a _postulate_.  A postulate specifies a
signature for an identifier but no definition.  Here we postulate
something proved earlier to save space.  Postulates must be used with
caution.  If we postulate something false then we could use Agda to
prove anything whatsoever.
{:/}

这是我们第一次使用*假设*（Postulate）。假设为一个标识符指定一个签名，但是不提供定义。
我们在这里假设之前证明过的东西，来节约空间。假设在使用时必须加以注意。如果假设的内容为假，
那么我们可以证明出任何东西。

{::comment}
We then repeat the proof of commutativity:
{:/}

我们接下来重复交换律的证明：

{% raw %}<pre class="Agda"><a id="+-comm"></a><a id="11840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11840" class="Function">+-comm</a> <a id="11847" class="Symbol">:</a> <a id="11849" class="Symbol">∀</a> <a id="11851" class="Symbol">(</a><a id="11852" href="plfa.Equality.html#11852" class="Bound">m</a> <a id="11854" href="plfa.Equality.html#11854" class="Bound">n</a> <a id="11856" class="Symbol">:</a> <a id="11858" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="11859" class="Symbol">)</a> <a id="11861" class="Symbol">→</a> <a id="11863" href="plfa.Equality.html#11852" class="Bound">m</a> <a id="11865" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11867" href="plfa.Equality.html#11854" class="Bound">n</a> <a id="11869" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="11871" href="plfa.Equality.html#11854" class="Bound">n</a> <a id="11873" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11875" href="plfa.Equality.html#11852" class="Bound">m</a>
<a id="11877" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11840" class="Function">+-comm</a> <a id="11884" href="plfa.Equality.html#11884" class="Bound">m</a> <a id="11886" href="plfa.Equality.html#11023" class="InductiveConstructor">zero</a> <a id="11891" class="Symbol">=</a>
  <a id="11895" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7238" class="Function Operator">begin</a>
    <a id="11905" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11884" class="Bound">m</a> <a id="11907" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11909" href="plfa.Equality.html#11023" class="InductiveConstructor">zero</a>
  <a id="11916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7403" class="Function Operator">≡⟨</a> <a id="11919" href="plfa.Equality.html#11243" class="Postulate">+-identity</a> <a id="11930" href="plfa.Equality.html#11884" class="Bound">m</a> <a id="11932" href="plfa.Equality.html#7403" class="Function Operator">⟩</a>
    <a id="11938" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11884" class="Bound">m</a>
  <a id="11942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7318" class="Function Operator">≡⟨⟩</a>
    <a id="11950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11023" class="InductiveConstructor">zero</a> <a id="11955" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11957" href="plfa.Equality.html#11884" class="Bound">m</a>
  <a id="11961" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7518" class="Function Operator">∎</a>
<a id="11963" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11840" class="Function">+-comm</a> <a id="11970" href="plfa.Equality.html#11970" class="Bound">m</a> <a id="11972" class="Symbol">(</a><a id="11973" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="11977" href="plfa.Equality.html#11977" class="Bound">n</a><a id="11978" class="Symbol">)</a> <a id="11980" class="Symbol">=</a>
  <a id="11984" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7238" class="Function Operator">begin</a>
    <a id="11994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11970" class="Bound">m</a> <a id="11996" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="11998" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="12002" href="plfa.Equality.html#11977" class="Bound">n</a>
  <a id="12006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7403" class="Function Operator">≡⟨</a> <a id="12009" href="plfa.Equality.html#11283" class="Postulate">+-suc</a> <a id="12015" href="plfa.Equality.html#11970" class="Bound">m</a> <a id="12017" href="plfa.Equality.html#11977" class="Bound">n</a> <a id="12019" href="plfa.Equality.html#7403" class="Function Operator">⟩</a>
    <a id="12025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11034" class="InductiveConstructor">suc</a> <a id="12029" class="Symbol">(</a><a id="12030" href="plfa.Equality.html#11970" class="Bound">m</a> <a id="12032" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="12034" href="plfa.Equality.html#11977" class="Bound">n</a><a id="12035" class="Symbol">)</a>
  <a id="12039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7403" class="Function Operator">≡⟨</a> <a id="12042" href="plfa.Equality.html#5754" class="Function">cong</a> <a id="12047" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="12051" class="Symbol">(</a><a id="12052" href="plfa.Equality.html#11840" class="Function">+-comm</a> <a id="12059" href="plfa.Equality.html#11970" class="Bound">m</a> <a id="12061" href="plfa.Equality.html#11977" class="Bound">n</a><a id="12062" class="Symbol">)</a> <a id="12064" href="plfa.Equality.html#7403" class="Function Operator">⟩</a>
    <a id="12070" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11034" class="InductiveConstructor">suc</a> <a id="12074" class="Symbol">(</a><a id="12075" href="plfa.Equality.html#11977" class="Bound">n</a> <a id="12077" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="12079" href="plfa.Equality.html#11970" class="Bound">m</a><a id="12080" class="Symbol">)</a>
  <a id="12084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7318" class="Function Operator">≡⟨⟩</a>
    <a id="12092" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11034" class="InductiveConstructor">suc</a> <a id="12096" href="plfa.Equality.html#11977" class="Bound">n</a> <a id="12098" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="12100" href="plfa.Equality.html#11970" class="Bound">m</a>
  <a id="12104" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#7518" class="Function Operator">∎</a>
</pre>{% endraw %}
{::comment}
The reasoning here is similar to that in the
preceding section.  We use
`_≡⟨⟩_` when no justification is required.
One can think of `_≡⟨⟩_` as equivalent to `_≡⟨ refl ⟩_`.
{:/}

论证的过程和之前的相似。我们在不需要解释的地方使用 `_≡⟨⟩_`，我们可以认为
`_≡⟨⟩_` 和 `_≡⟨ refl ⟩_` 是等价的。

{::comment}
Agda always treats a term as equivalent to its
simplified term.  The reason that one can write
{:/}

Agda 总是认为一个项与其化简的项是等价的。我们之所以可以写出

      suc (n + m)
    ≡⟨⟩
      suc n + m

{::comment}
is because Agda treats both terms as the same.
This also means that one could instead interchange
the lines and write
{:/}

是因为 Agda 认为它们是一样的。这也意味着我们可以交换两行的顺序，写出

      suc n + m
    ≡⟨⟩
      suc (n + m)

{::comment}
and Agda would not object. Agda only checks that the terms separated
by `≡⟨⟩` have the same simplified form; it's up to us to write them in
an order that will make sense to the reader.
{:/}

而 Agda 并不会反对。Agda 只会检查由 `≡⟨⟩` 隔开的项是否化简后相同。
而书写的顺序合不合理则是由我们自行决定。


{::comment}
#### Exercise `≤-Reasoning` (stretch)
{:/}

#### 练习 `≤-Reasoning` (延伸)

{::comment}
The proof of monotonicity from
Chapter [Relations]({{ site.baseurl }}/Relations/)
can be written in a more readable form by using an analogue of our
notation for `≡-Reasoning`.  Define `≤-Reasoning` analogously, and use
it to write out an alternative proof that addition is monotonic with
regard to inequality.  Rewrite all of `+-monoˡ-≤`, `+-monoʳ-≤`, and `+-mono-≤`.
{:/}

[Relations]({{ site.baseurl }}/Relations/) 章节中的单调性证明亦可以用相似于 `≡-Reasoning` 的，更易于理解的形式给出。
相似地来定义 `≤-Reasoning`，并用其重新给出加法对于不等式是单调的证明。重写 `+-monoˡ-≤`、`+-monoʳ-≤`
和 `+-mono-≤`。

{::comment}
{% raw %}<pre class="Agda"><a id="13709" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="13746" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Rewriting
{:/}

## 重写

{::comment}
Consider a property of natural numbers, such as being even.
We repeat the earlier definition:
{:/}

考虑一个自然数的性质，比如说一个数是偶数。我们重复之前给出的定义：

{% raw %}<pre class="Agda"><a id="13954" class="Keyword">data</a> <a id="even"></a><a id="13959" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="13964" class="Symbol">:</a> <a id="13966" href="plfa.Equality.html#11007" class="Datatype">ℕ</a> <a id="13968" class="Symbol">→</a> <a id="13970" class="PrimitiveType">Set</a>
<a id="13974" class="Keyword">data</a> <a id="odd"></a><a id="13979" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13979" class="Datatype">odd</a>  <a id="13984" class="Symbol">:</a> <a id="13986" href="plfa.Equality.html#11007" class="Datatype">ℕ</a> <a id="13988" class="Symbol">→</a> <a id="13990" class="PrimitiveType">Set</a>

<a id="13995" class="Keyword">data</a> <a id="14000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="14005" class="Keyword">where</a>

  <a id="even.even-zero"></a><a id="14014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14014" class="InductiveConstructor">even-zero</a> <a id="14024" class="Symbol">:</a> <a id="14026" href="plfa.Equality.html#13959" class="Datatype">even</a> <a id="14031" href="plfa.Equality.html#11023" class="InductiveConstructor">zero</a>

  <a id="even.even-suc"></a><a id="14039" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14039" class="InductiveConstructor">even-suc</a> <a id="14048" class="Symbol">:</a> <a id="14050" class="Symbol">∀</a> <a id="14052" class="Symbol">{</a><a id="14053" href="plfa.Equality.html#14053" class="Bound">n</a> <a id="14055" class="Symbol">:</a> <a id="14057" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="14058" class="Symbol">}</a>
    <a id="14064" class="Symbol">→</a> <a id="14066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13979" class="Datatype">odd</a> <a id="14070" href="plfa.Equality.html#14053" class="Bound">n</a>
      <a id="14078" class="Comment">------------</a>
    <a id="14095" class="Symbol">→</a> <a id="14097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="14102" class="Symbol">(</a><a id="14103" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="14107" href="plfa.Equality.html#14053" class="Bound">n</a><a id="14108" class="Symbol">)</a>

<a id="14111" class="Keyword">data</a> <a id="14116" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13979" class="Datatype">odd</a> <a id="14120" class="Keyword">where</a>
  <a id="odd.odd-suc"></a><a id="14128" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14128" class="InductiveConstructor">odd-suc</a> <a id="14136" class="Symbol">:</a> <a id="14138" class="Symbol">∀</a> <a id="14140" class="Symbol">{</a><a id="14141" href="plfa.Equality.html#14141" class="Bound">n</a> <a id="14143" class="Symbol">:</a> <a id="14145" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="14146" class="Symbol">}</a>
    <a id="14152" class="Symbol">→</a> <a id="14154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="14159" href="plfa.Equality.html#14141" class="Bound">n</a>
      <a id="14167" class="Comment">-----------</a>
    <a id="14183" class="Symbol">→</a> <a id="14185" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13979" class="Datatype">odd</a> <a id="14189" class="Symbol">(</a><a id="14190" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="14194" href="plfa.Equality.html#14141" class="Bound">n</a><a id="14195" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the previous section, we proved addition is commutative.  Given
evidence that `even (m + n)` holds, we ought also to be able to take
that as evidence that `even (n + m)` holds.
{:/}

在前面的部分中，我们证明了加法满足交换律。给定 `even (m + n)` 成立的证据，我们应当可以用它来做
`even (n + m)` 成立的证据。

{::comment}
Agda includes special notation to support just this kind of reasoning,
the `rewrite` notation we encountered earlier.
To enable this notation, we use pragmas to tell Agda which type
corresponds to equality:
{:/}

Agda 对这种论证有特殊记法的支持——我们之前提到过的 `rewrite` 记法。来启用这种记法，
我们只用编译程序指令来告诉 Agda 什么类型对应相等性：

{% raw %}<pre class="Agda"><a id="14790" class="Symbol">{-#</a> <a id="14794" class="Keyword">BUILTIN</a> <a id="14802" class="Pragma">EQUALITY</a> <a id="14811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#1053" class="Datatype Operator">_≡_</a> <a id="14815" class="Symbol">#-}</a>
</pre>{% endraw %}
{::comment}
We can then prove the desired property as follows:
{:/}

我们然后就可以如下证明求证的性质：

{% raw %}<pre class="Agda"><a id="even-comm"></a><a id="14916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14916" class="Function">even-comm</a> <a id="14926" class="Symbol">:</a> <a id="14928" class="Symbol">∀</a> <a id="14930" class="Symbol">(</a><a id="14931" href="plfa.Equality.html#14931" class="Bound">m</a> <a id="14933" href="plfa.Equality.html#14933" class="Bound">n</a> <a id="14935" class="Symbol">:</a> <a id="14937" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="14938" class="Symbol">)</a>
  <a id="14942" class="Symbol">→</a> <a id="14944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="14949" class="Symbol">(</a><a id="14950" href="plfa.Equality.html#14931" class="Bound">m</a> <a id="14952" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="14954" href="plfa.Equality.html#14933" class="Bound">n</a><a id="14955" class="Symbol">)</a>
    <a id="14961" class="Comment">------------</a>
  <a id="14976" class="Symbol">→</a> <a id="14978" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="14983" class="Symbol">(</a><a id="14984" href="plfa.Equality.html#14933" class="Bound">n</a> <a id="14986" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="14988" href="plfa.Equality.html#14931" class="Bound">m</a><a id="14989" class="Symbol">)</a>
<a id="14991" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#14916" class="Function">even-comm</a> <a id="15001" href="plfa.Equality.html#15001" class="Bound">m</a> <a id="15003" href="plfa.Equality.html#15003" class="Bound">n</a> <a id="15005" href="plfa.Equality.html#15005" class="Bound">ev</a>  <a id="15009" class="Keyword">rewrite</a> <a id="15017" href="plfa.Equality.html#11840" class="Function">+-comm</a> <a id="15024" href="plfa.Equality.html#15003" class="Bound">n</a> <a id="15026" href="plfa.Equality.html#15001" class="Bound">m</a>  <a id="15029" class="Symbol">=</a>  <a id="15032" href="plfa.Equality.html#15005" class="Bound">ev</a>
</pre>{% endraw %}
{::comment}
Here `ev` ranges over evidence that `even (m + n)` holds, and we show
that it also provides evidence that `even (n + m)` holds.  In
general, the keyword `rewrite` is followed by evidence of an
equality, and that equality is used to rewrite the type of the
goal and of any variable in scope.
{:/}

在这里，`ev` 包括了所有 `even (m + n)` 成立的证据，我们证明它亦可作为 `even (n + m)`
成立的证据。一般来说，关键字 `rewrite` 之后跟着一个等式的证明，这个等式被用于重写目标和任意作用域内变量的类型。

{::comment}
It is instructive to develop `even-comm` interactively.  To start, we
supply variables for the arguments on the left, and a hole for the
body on the right:
{:/}

交互性地证明 `even-comm` 是很有帮助的。一开始，我们先给左边的参数赋予变量，给右手边放上一个洞：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev = {! !}

{::comment}
If we go into the hole and type `C-c C-,` then Agda reports:
{:/}

如果我们进入洞里，输入 `C-c C-,`，Agda 会报告：

    Goal: even (n + m)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
Now we add the rewrite:
{:/}

现在我们加入重写：

    even-comm : ∀ (m n : ℕ)
      → even (m + n)
        ------------
      → even (n + m)
    even-comm m n ev rewrite +-comm n m = {! !}

{::comment}
If we go into the hole again and type `C-c C-,` then Agda now reports:
{:/}

如果我们再次进入洞里，并输入 `C-c C-,`，Agda 现在会报告：

    Goal: even (m + n)
    ————————————————————————————————————————————————————————————
    ev : even (m + n)
    n  : ℕ
    m  : ℕ

{::comment}
The arguments have been swapped in the goal.  Now it is trivial to see
that `ev` satisfies the goal, and typing `C-c C-a` in the hole causes
it to be filled with `ev`.  The command `C-c C-a` performs an
automated search, including checking whether a variable in scope has
the same type as the goal.
{:/}

目标里的参数被交换了。现在 `ev` 显然满足目标条件，输入 `C-c C-a` 会用 `ev` 来填充这个洞。
命令 `C-c C-a` 可以进行自动搜索，检查作用域内的变量是否和目标有相同的类型。


{::comment}
## Multiple rewrites
{:/}

## 多重重写

{::comment}
One may perform multiple rewrites, each separated by a vertical bar.  For instance,
here is a second proof that addition is commutative, relying on rewrites rather
than chains of equalities:
{:/}

我们可以多次使用重写，以竖线隔开。举个例子，这里是加法交换律的第二个证明，使用重写而不是等式串：

{% raw %}<pre class="Agda"><a id="+-comm′"></a><a id="17253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17253" class="Function">+-comm′</a> <a id="17261" class="Symbol">:</a> <a id="17263" class="Symbol">∀</a> <a id="17265" class="Symbol">(</a><a id="17266" href="plfa.Equality.html#17266" class="Bound">m</a> <a id="17268" href="plfa.Equality.html#17268" class="Bound">n</a> <a id="17270" class="Symbol">:</a> <a id="17272" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="17273" class="Symbol">)</a> <a id="17275" class="Symbol">→</a> <a id="17277" href="plfa.Equality.html#17266" class="Bound">m</a> <a id="17279" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="17281" href="plfa.Equality.html#17268" class="Bound">n</a> <a id="17283" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="17285" href="plfa.Equality.html#17268" class="Bound">n</a> <a id="17287" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="17289" href="plfa.Equality.html#17266" class="Bound">m</a>
<a id="17291" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17253" class="Function">+-comm′</a> <a id="17299" href="plfa.Equality.html#11023" class="InductiveConstructor">zero</a>    <a id="17307" href="plfa.Equality.html#17307" class="Bound">n</a>  <a id="17310" class="Keyword">rewrite</a> <a id="17318" href="plfa.Equality.html#11243" class="Postulate">+-identity</a> <a id="17329" href="plfa.Equality.html#17307" class="Bound">n</a>             <a id="17343" class="Symbol">=</a>  <a id="17346" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
<a id="17351" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#17253" class="Function">+-comm′</a> <a id="17359" class="Symbol">(</a><a id="17360" href="plfa.Equality.html#11034" class="InductiveConstructor">suc</a> <a id="17364" href="plfa.Equality.html#17364" class="Bound">m</a><a id="17365" class="Symbol">)</a> <a id="17367" href="plfa.Equality.html#17367" class="Bound">n</a>  <a id="17370" class="Keyword">rewrite</a> <a id="17378" href="plfa.Equality.html#11283" class="Postulate">+-suc</a> <a id="17384" href="plfa.Equality.html#17367" class="Bound">n</a> <a id="17386" href="plfa.Equality.html#17364" class="Bound">m</a> <a id="17388" class="Symbol">|</a> <a id="17390" href="plfa.Equality.html#17253" class="Function">+-comm′</a> <a id="17398" href="plfa.Equality.html#17364" class="Bound">m</a> <a id="17400" href="plfa.Equality.html#17367" class="Bound">n</a>  <a id="17403" class="Symbol">=</a>  <a id="17406" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
This is far more compact.  Among other things, whereas the previous
proof required `cong suc (+-comm m n)` as the justification to invoke
the inductive hypothesis, here it is sufficient to rewrite with
`+-comm m n`, as rewriting automatically takes congruence into
account.  Although proofs with rewriting are shorter, proofs as chains
of equalities are easier to follow, and we will stick with the latter
when feasible.
{:/}

这个证明更加的简短。之前的证明用 `cong suc (+-comm m n)` 作为使用归纳假设的说明，
而这里我们使用 `+-comm m n` 来重写就足够了，因为重写可以将合同性考虑在其中。尽管使用重写的证明更加的简短，
使用等式串的证明能容易理解，我们将尽可能的使用后者。


{::comment}
## Rewriting expanded
{:/}

## 深入重写

{::comment}
The `rewrite` notation is in fact shorthand for an appropriate use of `with`
abstraction:
{:/}

`rewrite` 记法实际上是 `with` 抽象的一种应用：

{% raw %}<pre class="Agda"><a id="even-comm′"></a><a id="18194" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18194" class="Function">even-comm′</a> <a id="18205" class="Symbol">:</a> <a id="18207" class="Symbol">∀</a> <a id="18209" class="Symbol">(</a><a id="18210" href="plfa.Equality.html#18210" class="Bound">m</a> <a id="18212" href="plfa.Equality.html#18212" class="Bound">n</a> <a id="18214" class="Symbol">:</a> <a id="18216" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="18217" class="Symbol">)</a>
  <a id="18221" class="Symbol">→</a> <a id="18223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="18228" class="Symbol">(</a><a id="18229" href="plfa.Equality.html#18210" class="Bound">m</a> <a id="18231" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="18233" href="plfa.Equality.html#18212" class="Bound">n</a><a id="18234" class="Symbol">)</a>
    <a id="18240" class="Comment">------------</a>
  <a id="18255" class="Symbol">→</a> <a id="18257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="18262" class="Symbol">(</a><a id="18263" href="plfa.Equality.html#18212" class="Bound">n</a> <a id="18265" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="18267" href="plfa.Equality.html#18210" class="Bound">m</a><a id="18268" class="Symbol">)</a>
<a id="18270" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#18194" class="Function">even-comm′</a> <a id="18281" href="plfa.Equality.html#18281" class="Bound">m</a> <a id="18283" href="plfa.Equality.html#18283" class="Bound">n</a> <a id="18285" href="plfa.Equality.html#18285" class="Bound">ev</a> <a id="18288" class="Keyword">with</a>   <a id="18295" href="plfa.Equality.html#18281" class="Bound">m</a> <a id="18297" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="18299" href="plfa.Equality.html#18283" class="Bound">n</a>  <a id="18302" class="Symbol">|</a> <a id="18304" href="plfa.Equality.html#11840" class="Function">+-comm</a> <a id="18311" href="plfa.Equality.html#18281" class="Bound">m</a> <a id="18313" href="plfa.Equality.html#18283" class="Bound">n</a>
<a id="18315" class="Symbol">...</a>                  <a id="18336" class="Symbol">|</a> <a id="18338" class="DottedPattern Symbol">.(</a><a id="18340" class="DottedPattern Bound">n</a> <a id="18342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#11048" class="DottedPattern Function Operator">+</a> <a id="18344" class="DottedPattern Bound">m</a><a id="18345" class="DottedPattern Symbol">)</a> <a id="18347" class="Symbol">|</a> <a id="18349" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>       <a id="18360" class="Symbol">=</a> <a id="18362" class="Bound">ev</a>
</pre>{% endraw %}
{::comment}
In general, one can follow `with` by any number of expressions,
separated by bars, where each following equation has the same number
of patterns.  We often write expressions and the corresponding
patterns so they line up in columns, as above. Here the first column
asserts that `m + n` and `n + m` are identical, and the second column
justifies that assertion with evidence of the appropriate equality.
Note also the use of the _dot pattern_, `.(n + m)`.  A dot pattern
consists of a dot followed by an expression, and is used when other
information forces the value matched to be equal to the value of the
expression in the dot pattern.  In this case, the identification of
`m + n` and `n + m` is justified by the subsequent matching of
`+-comm m n` against `refl`.  One might think that the first clause is
redundant as the information is inherent in the second clause, but in
fact Agda is rather picky on this point: omitting the first clause or
reversing the order of the clauses will cause Agda to report an error.
(Try it and see!)
{:/}

总的来着，我们可以在 `with` 后面跟上任何数量的表达式，用竖线分隔开，并且在每个等式中使用相同个数的模式。
我们经常将表达式和模式如上对齐。这个第一列表明了 `m + n` 和 `n + m` 是相同的，第二列使用相应等式来证明的前述的断言。
注意在这里使用的*点模式*（Dot Pattern），`.(n + m)`。点模式由一个点和一个表达式组成，
在其他信息迫使这个值和点模式中的值相等时使用。在这里，`m + n` 和 `n + m` 由后续的
`+-comm m n` 与 `refl` 的匹配来识别。我们可能会认为第一种情况是多余的，因为第二种情况中才蕴涵了需要的信息。
但实际上 Agda 在这件事上很挑剔——省略第一条或者更换顺序会让 Agda 报告一个错误。（试一试你就知道！）

{::comment}
In this case, we can avoid rewrite by simply applying the substitution
function defined earlier:
{:/}

在这种情况中，我们也可以使用之前定义的替换函数来避免使用重写：

{% raw %}<pre class="Agda"><a id="even-comm″"></a><a id="19931" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#19931" class="Function">even-comm″</a> <a id="19942" class="Symbol">:</a> <a id="19944" class="Symbol">∀</a> <a id="19946" class="Symbol">(</a><a id="19947" href="plfa.Equality.html#19947" class="Bound">m</a> <a id="19949" href="plfa.Equality.html#19949" class="Bound">n</a> <a id="19951" class="Symbol">:</a> <a id="19953" href="plfa.Equality.html#11007" class="Datatype">ℕ</a><a id="19954" class="Symbol">)</a>
  <a id="19958" class="Symbol">→</a> <a id="19960" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="19965" class="Symbol">(</a><a id="19966" href="plfa.Equality.html#19947" class="Bound">m</a> <a id="19968" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="19970" href="plfa.Equality.html#19949" class="Bound">n</a><a id="19971" class="Symbol">)</a>
    <a id="19977" class="Comment">------------</a>
  <a id="19992" class="Symbol">→</a> <a id="19994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#13959" class="Datatype">even</a> <a id="19999" class="Symbol">(</a><a id="20000" href="plfa.Equality.html#19949" class="Bound">n</a> <a id="20002" href="plfa.Equality.html#11048" class="Function Operator">+</a> <a id="20004" href="plfa.Equality.html#19947" class="Bound">m</a><a id="20005" class="Symbol">)</a>
<a id="20007" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#19931" class="Function">even-comm″</a> <a id="20018" href="plfa.Equality.html#20018" class="Bound">m</a> <a id="20020" href="plfa.Equality.html#20020" class="Bound">n</a>  <a id="20023" class="Symbol">=</a>  <a id="20026" href="plfa.Equality.html#6672" class="Function">subst</a> <a id="20032" href="plfa.Equality.html#13959" class="Datatype">even</a> <a id="20037" class="Symbol">(</a><a id="20038" href="plfa.Equality.html#11840" class="Function">+-comm</a> <a id="20045" href="plfa.Equality.html#20018" class="Bound">m</a> <a id="20047" href="plfa.Equality.html#20020" class="Bound">n</a><a id="20048" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Nonetheless, rewrite is a vital part of the Agda toolkit.  We will use
it sparingly, but it is occasionally essential.
{:/}

尽管如此，重写是 Agda 工具箱中很重要的一部分。我们会偶尔使用它，但是它有的时候是必要的。


{::comment}
## Leibniz equality
{:/}

## 莱布尼兹（Leibniz）相等性

{::comment}
The form of asserting equality that we have used is due to Martin
Löf, and was published in 1975.  An older form is due to Leibniz, and
was published in 1686.  Leibniz asserted the _identity of
indiscernibles_: two objects are equal if and only if they satisfy the
same properties. This principle sometimes goes by the name Leibniz'
Law, and is closely related to Spock's Law, "A difference that makes
no difference is no difference".  Here we define Leibniz equality,
and show that two terms satisfy Leibniz equality if and only if they
satisfy Martin Löf equality.
{:/}

我们使用的相等性断言的形式源于 Martin Löf，于 1975 年发表。一个更早的形式源于莱布尼兹，
于 1686 年发表。莱布尼兹断言的相等性表示*不可分辨的实体*（Identity of Indiscernibles）：
两个对象相等当且仅当它们满足完全相同的性质。这条原理有时被称作莱布尼兹定律（Leibniz' Law），
与史波克定律紧密相关：“一个不造成区别的区别不是区别”。我们在这里定义莱布尼兹相等性，
并证明两个项满足莱布尼兹相等性当且仅当其满足 Martin Löf 相等性。

{::comment}
Leibniz equality is usually formalised to state that `x ≐ y` holds if
every property `P` that holds of `x` also holds of `y`.  Perhaps
surprisingly, this definition is sufficient to also ensure the
converse, that every property `P` that holds of `y` also holds of `x`.
{:/}

莱布尼兹不等式一般如下来定义：`x ≐ y` 当每个对于 `x` 成立的性质 `P` 对于 `y` 也成立时成立。
可能这有些出乎意料，但是这个定义亦足够保证其相反的命题：每个对于 `y` 成立的性质 `P` 对于 `x` 也成立。

{::comment}
Let `x` and `y` be objects of type `A`. We say that `x ≐ y` holds if
for every predicate `P` over type `A` we have that `P x` implies `P y`:
{:/}

令 `x` 和 `y` 为类型 `A` 的对象。我们定义 `x ≐ y` 成立，当每个对于类型 `A` 成立的谓词 `P`，
我们有 `P x` 蕴涵了 `P y`：

{% raw %}<pre class="Agda"><a id="_≐_"></a><a id="21791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21791" class="Function Operator">_≐_</a> <a id="21795" class="Symbol">:</a> <a id="21797" class="Symbol">∀</a> <a id="21799" class="Symbol">{</a><a id="21800" href="plfa.Equality.html#21800" class="Bound">A</a> <a id="21802" class="Symbol">:</a> <a id="21804" class="PrimitiveType">Set</a><a id="21807" class="Symbol">}</a> <a id="21809" class="Symbol">(</a><a id="21810" href="plfa.Equality.html#21810" class="Bound">x</a> <a id="21812" href="plfa.Equality.html#21812" class="Bound">y</a> <a id="21814" class="Symbol">:</a> <a id="21816" href="plfa.Equality.html#21800" class="Bound">A</a><a id="21817" class="Symbol">)</a> <a id="21819" class="Symbol">→</a> <a id="21821" class="PrimitiveType">Set₁</a>
<a id="21826" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#21791" class="Function Operator">_≐_</a> <a id="21830" class="Symbol">{</a><a id="21831" href="plfa.Equality.html#21831" class="Bound">A</a><a id="21832" class="Symbol">}</a> <a id="21834" href="plfa.Equality.html#21834" class="Bound">x</a> <a id="21836" href="plfa.Equality.html#21836" class="Bound">y</a> <a id="21838" class="Symbol">=</a> <a id="21840" class="Symbol">∀</a> <a id="21842" class="Symbol">(</a><a id="21843" href="plfa.Equality.html#21843" class="Bound">P</a> <a id="21845" class="Symbol">:</a> <a id="21847" href="plfa.Equality.html#21831" class="Bound">A</a> <a id="21849" class="Symbol">→</a> <a id="21851" class="PrimitiveType">Set</a><a id="21854" class="Symbol">)</a> <a id="21856" class="Symbol">→</a> <a id="21858" href="plfa.Equality.html#21843" class="Bound">P</a> <a id="21860" href="plfa.Equality.html#21834" class="Bound">x</a> <a id="21862" class="Symbol">→</a> <a id="21864" href="plfa.Equality.html#21843" class="Bound">P</a> <a id="21866" href="plfa.Equality.html#21836" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
We cannot write the left-hand side of the equation as `x ≐ y`,
and instead we write `_≐_ {A} x y` to provide access to the implicit
parameter `A` which appears on the right-hand side.
{:/}

我们不能在左手边使用 `x ≐ y`，取而代之我们使用 `_≐_ {A} x y` 来提供隐式参数 `A`，这样 `A`
可以出现在右手边。

{::comment}
This is our first use of _levels_.  We cannot assign `Set` the type
`Set`, since this would lead to contradictions such as Russell's
Paradox and Girard's Paradox.  Instead, there is a hierarchy of types,
where `Set : Set₁`, `Set₁ : Set₂`, and so on.  In fact, `Set` itself
is just an abbreviation for `Set₀`.  Since the equation defining `_≐_`
mentions `Set` on the right-hand side, the corresponding signature
must use `Set₁`.  We say a bit more about levels below.
{:/}

这是我们第一次使用*等级*（Levels）。我们不能将 `Set` 赋予类型 `Set`，因为这会导致自相矛盾，
比如罗素悖论（Russell's Paradox）或者 Girard 悖论。不同的是，我们有一个阶级的类型：其中
`Set : Set₁`，`Set₁ : Set₂`，以此类推。实际上，`Set` 本身就是 `Set₀` 的缩写。定义
`_≐_` 的等式在右手边提到了 `Set`，因此签名中必须使用 `Set₁`。我们稍后将进一步介绍等级。

{::comment}
Leibniz equality is reflexive and transitive,
where the first follows by a variant of the identity function
and the second by a variant of function composition:
{:/}

莱布尼兹相等性是自反和传递的。自反性由恒等函数的变种得来，传递性由函数组合的变种得来：

{% raw %}<pre class="Agda"><a id="refl-≐"></a><a id="23090" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23090" class="Function">refl-≐</a> <a id="23097" class="Symbol">:</a> <a id="23099" class="Symbol">∀</a> <a id="23101" class="Symbol">{</a><a id="23102" href="plfa.Equality.html#23102" class="Bound">A</a> <a id="23104" class="Symbol">:</a> <a id="23106" class="PrimitiveType">Set</a><a id="23109" class="Symbol">}</a> <a id="23111" class="Symbol">{</a><a id="23112" href="plfa.Equality.html#23112" class="Bound">x</a> <a id="23114" class="Symbol">:</a> <a id="23116" href="plfa.Equality.html#23102" class="Bound">A</a><a id="23117" class="Symbol">}</a>
  <a id="23121" class="Symbol">→</a> <a id="23123" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23112" class="Bound">x</a> <a id="23125" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="23127" href="plfa.Equality.html#23112" class="Bound">x</a>
<a id="23129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23090" class="Function">refl-≐</a> <a id="23136" href="plfa.Equality.html#23136" class="Bound">P</a> <a id="23138" href="plfa.Equality.html#23138" class="Bound">Px</a>  <a id="23142" class="Symbol">=</a>  <a id="23145" href="plfa.Equality.html#23138" class="Bound">Px</a>

<a id="trans-≐"></a><a id="23149" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23149" class="Function">trans-≐</a> <a id="23157" class="Symbol">:</a> <a id="23159" class="Symbol">∀</a> <a id="23161" class="Symbol">{</a><a id="23162" href="plfa.Equality.html#23162" class="Bound">A</a> <a id="23164" class="Symbol">:</a> <a id="23166" class="PrimitiveType">Set</a><a id="23169" class="Symbol">}</a> <a id="23171" class="Symbol">{</a><a id="23172" href="plfa.Equality.html#23172" class="Bound">x</a> <a id="23174" href="plfa.Equality.html#23174" class="Bound">y</a> <a id="23176" href="plfa.Equality.html#23176" class="Bound">z</a> <a id="23178" class="Symbol">:</a> <a id="23180" href="plfa.Equality.html#23162" class="Bound">A</a><a id="23181" class="Symbol">}</a>
  <a id="23185" class="Symbol">→</a> <a id="23187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23172" class="Bound">x</a> <a id="23189" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="23191" href="plfa.Equality.html#23174" class="Bound">y</a>
  <a id="23195" class="Symbol">→</a> <a id="23197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23174" class="Bound">y</a> <a id="23199" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="23201" href="plfa.Equality.html#23176" class="Bound">z</a>
    <a id="23207" class="Comment">-----</a>
  <a id="23215" class="Symbol">→</a> <a id="23217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23172" class="Bound">x</a> <a id="23219" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="23221" href="plfa.Equality.html#23176" class="Bound">z</a>
<a id="23223" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23149" class="Function">trans-≐</a> <a id="23231" href="plfa.Equality.html#23231" class="Bound">x≐y</a> <a id="23235" href="plfa.Equality.html#23235" class="Bound">y≐z</a> <a id="23239" href="plfa.Equality.html#23239" class="Bound">P</a> <a id="23241" href="plfa.Equality.html#23241" class="Bound">Px</a>  <a id="23245" class="Symbol">=</a>  <a id="23248" href="plfa.Equality.html#23235" class="Bound">y≐z</a> <a id="23252" href="plfa.Equality.html#23239" class="Bound">P</a> <a id="23254" class="Symbol">(</a><a id="23255" href="plfa.Equality.html#23231" class="Bound">x≐y</a> <a id="23259" href="plfa.Equality.html#23239" class="Bound">P</a> <a id="23261" href="plfa.Equality.html#23241" class="Bound">Px</a><a id="23263" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Symmetry is less obvious.  We have to show that if `P x` implies `P y`
for all predicates `P`, then the implication holds the other way round
as well:
{:/}

对称性就没有那么显然了。我们需要证明如果对于所有谓词 `P`，`P x` 蕴涵 `P y`，
那么反方向的蕴涵也成立。

{% raw %}<pre class="Agda"><a id="sym-≐"></a><a id="23504" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23504" class="Function">sym-≐</a> <a id="23510" class="Symbol">:</a> <a id="23512" class="Symbol">∀</a> <a id="23514" class="Symbol">{</a><a id="23515" href="plfa.Equality.html#23515" class="Bound">A</a> <a id="23517" class="Symbol">:</a> <a id="23519" class="PrimitiveType">Set</a><a id="23522" class="Symbol">}</a> <a id="23524" class="Symbol">{</a><a id="23525" href="plfa.Equality.html#23525" class="Bound">x</a> <a id="23527" href="plfa.Equality.html#23527" class="Bound">y</a> <a id="23529" class="Symbol">:</a> <a id="23531" href="plfa.Equality.html#23515" class="Bound">A</a><a id="23532" class="Symbol">}</a>
  <a id="23536" class="Symbol">→</a> <a id="23538" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23525" class="Bound">x</a> <a id="23540" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="23542" href="plfa.Equality.html#23527" class="Bound">y</a>
    <a id="23548" class="Comment">-----</a>
  <a id="23556" class="Symbol">→</a> <a id="23558" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23527" class="Bound">y</a> <a id="23560" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="23562" href="plfa.Equality.html#23525" class="Bound">x</a>
<a id="23564" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23504" class="Function">sym-≐</a> <a id="23570" class="Symbol">{</a><a id="23571" href="plfa.Equality.html#23571" class="Bound">A</a><a id="23572" class="Symbol">}</a> <a id="23574" class="Symbol">{</a><a id="23575" href="plfa.Equality.html#23575" class="Bound">x</a><a id="23576" class="Symbol">}</a> <a id="23578" class="Symbol">{</a><a id="23579" href="plfa.Equality.html#23579" class="Bound">y</a><a id="23580" class="Symbol">}</a> <a id="23582" href="plfa.Equality.html#23582" class="Bound">x≐y</a> <a id="23586" href="plfa.Equality.html#23586" class="Bound">P</a>  <a id="23589" class="Symbol">=</a>  <a id="23592" href="plfa.Equality.html#23674" class="Function">Qy</a>
  <a id="23597" class="Keyword">where</a>
    <a id="23607" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23607" class="Function">Q</a> <a id="23609" class="Symbol">:</a> <a id="23611" href="plfa.Equality.html#23571" class="Bound">A</a> <a id="23613" class="Symbol">→</a> <a id="23615" class="PrimitiveType">Set</a>
    <a id="23623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23607" class="Function">Q</a> <a id="23625" href="plfa.Equality.html#23625" class="Bound">z</a> <a id="23627" class="Symbol">=</a> <a id="23629" href="plfa.Equality.html#23586" class="Bound">P</a> <a id="23631" href="plfa.Equality.html#23625" class="Bound">z</a> <a id="23633" class="Symbol">→</a> <a id="23635" href="plfa.Equality.html#23586" class="Bound">P</a> <a id="23637" href="plfa.Equality.html#23575" class="Bound">x</a>
    <a id="23643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23643" class="Function">Qx</a> <a id="23646" class="Symbol">:</a> <a id="23648" href="plfa.Equality.html#23607" class="Function">Q</a> <a id="23650" href="plfa.Equality.html#23575" class="Bound">x</a>
    <a id="23656" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23643" class="Function">Qx</a> <a id="23659" class="Symbol">=</a> <a id="23661" href="plfa.Equality.html#23090" class="Function">refl-≐</a> <a id="23668" href="plfa.Equality.html#23586" class="Bound">P</a>
    <a id="23674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23674" class="Function">Qy</a> <a id="23677" class="Symbol">:</a> <a id="23679" href="plfa.Equality.html#23607" class="Function">Q</a> <a id="23681" href="plfa.Equality.html#23579" class="Bound">y</a>
    <a id="23687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#23674" class="Function">Qy</a> <a id="23690" class="Symbol">=</a> <a id="23692" href="plfa.Equality.html#23582" class="Bound">x≐y</a> <a id="23696" href="plfa.Equality.html#23607" class="Function">Q</a> <a id="23698" href="plfa.Equality.html#23643" class="Function">Qx</a>
</pre>{% endraw %}
{::comment}
Given `x ≐ y`, a specific `P`, we have to construct a proof that `P y`
implies `P x`.  To do so, we instantiate the equality with a predicate
`Q` such that `Q z` holds if `P z` implies `P x`.  The property `Q x`
is trivial by reflexivity, and hence `Q y` follows from `x ≐ y`.  But
`Q y` is exactly a proof of what we require, that `P y` implies `P x`.
{:/}

给定 `x ≐ y` 和一个特定的 `P`，我们需要构造一个 `P y` 蕴涵 `P x` 的证明。
我们首先用一个谓词 `Q` 将相等性实例化，使得 `Q z` 在 `P z` 蕴涵 `P x` 时成立。
`Q x` 这个性质是显然的，由自反性可以得出，由此通过 `x ≐ y` 就能推出 `Q y` 成立。而 `Q y`
正是我们需要的证明，即 `P y` 蕴涵 `P x`。

{::comment}
We now show that Martin Löf equality implies
Leibniz equality, and vice versa.  In the forward direction, if we know
`x ≡ y` we need for any `P` to take evidence of `P x` to evidence of `P y`,
which is easy since equality of `x` and `y` implies that any proof
of `P x` is also a proof of `P y`:
{:/}

我们现在来证明 Martin Löf 相等性蕴涵了莱布尼兹相等性，以及其逆命题。在正方向上，
如果我们已知 `x ≡ y`，我们需要对于任意的 `P`，将 `P x` 的证明转换为 `P y` 的证明。
我们很容易就可以做到这一点，因为 `x` 与 `y` 相等意味着任何 `P x` 的证明即是 `P y` 的证明。

{% raw %}<pre class="Agda"><a id="≡-implies-≐"></a><a id="24747" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24747" class="Function">≡-implies-≐</a> <a id="24759" class="Symbol">:</a> <a id="24761" class="Symbol">∀</a> <a id="24763" class="Symbol">{</a><a id="24764" href="plfa.Equality.html#24764" class="Bound">A</a> <a id="24766" class="Symbol">:</a> <a id="24768" class="PrimitiveType">Set</a><a id="24771" class="Symbol">}</a> <a id="24773" class="Symbol">{</a><a id="24774" href="plfa.Equality.html#24774" class="Bound">x</a> <a id="24776" href="plfa.Equality.html#24776" class="Bound">y</a> <a id="24778" class="Symbol">:</a> <a id="24780" href="plfa.Equality.html#24764" class="Bound">A</a><a id="24781" class="Symbol">}</a>
  <a id="24785" class="Symbol">→</a> <a id="24787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24774" class="Bound">x</a> <a id="24789" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="24791" href="plfa.Equality.html#24776" class="Bound">y</a>
    <a id="24797" class="Comment">-----</a>
  <a id="24805" class="Symbol">→</a> <a id="24807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24774" class="Bound">x</a> <a id="24809" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="24811" href="plfa.Equality.html#24776" class="Bound">y</a>
<a id="24813" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#24747" class="Function">≡-implies-≐</a> <a id="24825" href="plfa.Equality.html#24825" class="Bound">x≡y</a> <a id="24829" href="plfa.Equality.html#24829" class="Bound">P</a>  <a id="24832" class="Symbol">=</a>  <a id="24835" href="plfa.Equality.html#6672" class="Function">subst</a> <a id="24841" href="plfa.Equality.html#24829" class="Bound">P</a> <a id="24843" href="plfa.Equality.html#24825" class="Bound">x≡y</a>
</pre>{% endraw %}
{::comment}
This direction follows from substitution, which we showed earlier.
{:/}

因为这个方向由替换性可以得来，如之前证明的那样。

{::comment}
In the reverse direction, given that for any `P` we can take a proof of `P x`
to a proof of `P y` we need to show `x ≡ y`:
{:/}

在反方向上，我们已知对于任何 `P`，我们可以将 `P x` 的证明转换成 `P y` 的证明，
我们需要证明 `x ≡ y`：

{% raw %}<pre class="Agda"><a id="≐-implies-≡"></a><a id="25174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25174" class="Function">≐-implies-≡</a> <a id="25186" class="Symbol">:</a> <a id="25188" class="Symbol">∀</a> <a id="25190" class="Symbol">{</a><a id="25191" href="plfa.Equality.html#25191" class="Bound">A</a> <a id="25193" class="Symbol">:</a> <a id="25195" class="PrimitiveType">Set</a><a id="25198" class="Symbol">}</a> <a id="25200" class="Symbol">{</a><a id="25201" href="plfa.Equality.html#25201" class="Bound">x</a> <a id="25203" href="plfa.Equality.html#25203" class="Bound">y</a> <a id="25205" class="Symbol">:</a> <a id="25207" href="plfa.Equality.html#25191" class="Bound">A</a><a id="25208" class="Symbol">}</a>
  <a id="25212" class="Symbol">→</a> <a id="25214" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25201" class="Bound">x</a> <a id="25216" href="plfa.Equality.html#21791" class="Function Operator">≐</a> <a id="25218" href="plfa.Equality.html#25203" class="Bound">y</a>
    <a id="25224" class="Comment">-----</a>
  <a id="25232" class="Symbol">→</a> <a id="25234" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25201" class="Bound">x</a> <a id="25236" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="25238" href="plfa.Equality.html#25203" class="Bound">y</a>
<a id="25240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25174" class="Function">≐-implies-≡</a> <a id="25252" class="Symbol">{</a><a id="25253" href="plfa.Equality.html#25253" class="Bound">A</a><a id="25254" class="Symbol">}</a> <a id="25256" class="Symbol">{</a><a id="25257" href="plfa.Equality.html#25257" class="Bound">x</a><a id="25258" class="Symbol">}</a> <a id="25260" class="Symbol">{</a><a id="25261" href="plfa.Equality.html#25261" class="Bound">y</a><a id="25262" class="Symbol">}</a> <a id="25264" href="plfa.Equality.html#25264" class="Bound">x≐y</a>  <a id="25269" class="Symbol">=</a>  <a id="25272" href="plfa.Equality.html#25346" class="Function">Qy</a>
  <a id="25277" class="Keyword">where</a>
    <a id="25287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25287" class="Function">Q</a> <a id="25289" class="Symbol">:</a> <a id="25291" href="plfa.Equality.html#25253" class="Bound">A</a> <a id="25293" class="Symbol">→</a> <a id="25295" class="PrimitiveType">Set</a>
    <a id="25303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25287" class="Function">Q</a> <a id="25305" href="plfa.Equality.html#25305" class="Bound">z</a> <a id="25307" class="Symbol">=</a> <a id="25309" href="plfa.Equality.html#25257" class="Bound">x</a> <a id="25311" href="plfa.Equality.html#1053" class="Datatype Operator">≡</a> <a id="25313" href="plfa.Equality.html#25305" class="Bound">z</a>
    <a id="25319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25319" class="Function">Qx</a> <a id="25322" class="Symbol">:</a> <a id="25324" href="plfa.Equality.html#25287" class="Function">Q</a> <a id="25326" href="plfa.Equality.html#25257" class="Bound">x</a>
    <a id="25332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25319" class="Function">Qx</a> <a id="25335" class="Symbol">=</a> <a id="25337" href="plfa.Equality.html#1093" class="InductiveConstructor">refl</a>
    <a id="25346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25346" class="Function">Qy</a> <a id="25349" class="Symbol">:</a> <a id="25351" href="plfa.Equality.html#25287" class="Function">Q</a> <a id="25353" href="plfa.Equality.html#25261" class="Bound">y</a>
    <a id="25359" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#25346" class="Function">Qy</a> <a id="25362" class="Symbol">=</a> <a id="25364" href="plfa.Equality.html#25264" class="Bound">x≐y</a> <a id="25368" href="plfa.Equality.html#25287" class="Function">Q</a> <a id="25370" href="plfa.Equality.html#25319" class="Function">Qx</a>
</pre>{% endraw %}
{::comment}
The proof is similar to that for symmetry of Leibniz equality. We take
`Q` to be the predicate that holds of `z` if `x ≡ z`. Then `Q x` is
trivial by reflexivity of Martin Löf equality, and hence `Q y`
follows from `x ≐ y`.  But `Q y` is exactly a proof of what we
require, that `x ≡ y`.
{:/}

此证明与莱布尼兹相等性的对称性证明相似。我们取谓词 `Q`，使得 `Q z` 在 `x ≡ z` 成立时成立。
那么 `Q x` 是显然的，由 Martin Löf 相等性的自反性得来。从而 `Q y` 由 `x ≐ y` 可得，
而 `Q y` 即是我们所需要的 `x ≡ y` 的证明。

{::comment}
(Parts of this section are adapted from *≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*, by Andreas Abel,
Jesper Cockx, Dominique Devries, Andreas Nuyts, and Philip Wadler,
draft, 2017.)
{:/}

（本部分的内容由此处改编得来：
*≐≃≡: Leibniz Equality is
Isomorphic to Martin-Löf Identity, Parametrically*
作者：Andreas Abel、Jesper Cockx、Dominique Devries、Andreas Nuyts 与 Philip Wadler，
草稿，2017）


{::comment}
## Universe polymorphism {#unipoly}
{:/}

## 全体多态 {#unipoly}

{::comment}
As we have seen, not every type belongs to `Set`, but instead every
type belongs somewhere in the hierarchy `Set₀`, `Set₁`, `Set₂`, and so on,
where `Set` abbreviates `Set₀`, and `Set₀ : Set₁`, `Set₁ : Set₂`, and so on.
The definition of equality given above is fine if we want to compare two
values of a type that belongs to `Set`, but what if we want to compare
two values of a type that belongs to `Set ℓ` for some arbitrary level `ℓ`?
{:/}

正如我们之前看到的那样，不是每个类型都属于 `Set`，但是每个类型都属于类型阶级的某处，
`Set₀`、`Set₁`、`Set₂`等等。其中 `Set` 是 `Set₀` 的缩写，此外 `Set₀ : Set₁`，`Set₁ : Set₂`，以此类推。
当我们需要比较两个属于 `Set` 的类型的值时，我们之前给出的定义是足够的，
但如果我们需要比较对于任何等级 `ℓ`，两个属于 `Set ℓ` 的类型的值该怎么办呢？

{::comment}
The answer is _universe polymorphism_, where a definition is made
with respect to an arbitrary level `ℓ`. To make use of levels, we
first import the following:
{:/}

答案是*全体多态*（Universe Polymorphism），一个定义可以根据任何等级 `ℓ` 来做出。
为了使用等级，我们首先导入下列内容：

{% raw %}<pre class="Agda"><a id="27249" class="Keyword">open</a> <a id="27254" class="Keyword">import</a> <a id="27261" href="https://agda.github.io/agda-stdlib/v1.1/Level.html" class="Module">Level</a> <a id="27267" class="Keyword">using</a> <a id="27273" class="Symbol">(</a><a id="27274" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="27279" class="Symbol">;</a> <a id="27281" href="Agda.Primitive.html#657" class="Primitive Operator">_⊔_</a><a id="27284" class="Symbol">)</a> <a id="27286" class="Keyword">renaming</a> <a id="27295" class="Symbol">(</a><a id="27296" href="Agda.Primitive.html#611" class="Primitive">zero</a> <a id="27301" class="Symbol">to</a> <a id="27304" href="Agda.Primitive.html#611" class="Primitive">lzero</a><a id="27309" class="Symbol">;</a> <a id="27311" href="Agda.Primitive.html#627" class="Primitive">suc</a> <a id="27315" class="Symbol">to</a> <a id="27318" href="Agda.Primitive.html#627" class="Primitive">lsuc</a><a id="27322" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
We rename constructors `zero` and `suc` to `lzero` and `lsuc` to avoid confusion
between levels and naturals.
{:/}

我们将构造子 `zero` 和 `suc` 重命名至 `lzero` 和 `lsuc`，为了防止自然数和等级之间的混淆。

{::comment}
Levels are isomorphic to natural numbers, and have similar constructors:
{:/}

等级与自然数是同构的，有相似的构造子：

    lzero : Level
    lsuc  : Level → Level

{::comment}
The names `Set₀`, `Set₁`, `Set₂`, and so on, are abbreviations for
{:/}

`Set₀`、`Set₁`、`Set₂` 等名称，是下列的简写：

    Set lzero
    Set (lsuc lzero)
    Set (lsuc (lsuc lzero))

{::comment}
and so on. There is also an operator
{:/}

以此类推。我们还有一个运算符：

    _⊔_ : Level → Level → Level

{::comment}
that given two levels returns the larger of the two.
{:/}

给定两个等级，返回两者中较大的那个。

{::comment}
Here is the definition of equality, generalised to an arbitrary level:
{:/}

下面是相等性的定义，推广到任意等级：

{% raw %}<pre class="Agda"><a id="28168" class="Keyword">data</a> <a id="_≡′_"></a><a id="28173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28173" class="Datatype Operator">_≡′_</a> <a id="28178" class="Symbol">{</a><a id="28179" href="plfa.Equality.html#28179" class="Bound">ℓ</a> <a id="28181" class="Symbol">:</a> <a id="28183" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="28188" class="Symbol">}</a> <a id="28190" class="Symbol">{</a><a id="28191" href="plfa.Equality.html#28191" class="Bound">A</a> <a id="28193" class="Symbol">:</a> <a id="28195" class="PrimitiveType">Set</a> <a id="28199" href="plfa.Equality.html#28179" class="Bound">ℓ</a><a id="28200" class="Symbol">}</a> <a id="28202" class="Symbol">(</a><a id="28203" href="plfa.Equality.html#28203" class="Bound">x</a> <a id="28205" class="Symbol">:</a> <a id="28207" href="plfa.Equality.html#28191" class="Bound">A</a><a id="28208" class="Symbol">)</a> <a id="28210" class="Symbol">:</a> <a id="28212" href="plfa.Equality.html#28191" class="Bound">A</a> <a id="28214" class="Symbol">→</a> <a id="28216" class="PrimitiveType">Set</a> <a id="28220" href="plfa.Equality.html#28179" class="Bound">ℓ</a> <a id="28222" class="Keyword">where</a>
  <a id="_≡′_.refl′"></a><a id="28230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28230" class="InductiveConstructor">refl′</a> <a id="28236" class="Symbol">:</a> <a id="28238" href="plfa.Equality.html#28203" class="Bound">x</a> <a id="28240" href="plfa.Equality.html#28173" class="Datatype Operator">≡′</a> <a id="28243" href="plfa.Equality.html#28203" class="Bound">x</a>
</pre>{% endraw %}
{::comment}
Similarly, here is the generalised definition of symmetry:
{:/}

相似的，下面是对称性的推广定义：

{% raw %}<pre class="Agda"><a id="sym′"></a><a id="28349" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28349" class="Function">sym′</a> <a id="28354" class="Symbol">:</a> <a id="28356" class="Symbol">∀</a> <a id="28358" class="Symbol">{</a><a id="28359" href="plfa.Equality.html#28359" class="Bound">ℓ</a> <a id="28361" class="Symbol">:</a> <a id="28363" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="28368" class="Symbol">}</a> <a id="28370" class="Symbol">{</a><a id="28371" href="plfa.Equality.html#28371" class="Bound">A</a> <a id="28373" class="Symbol">:</a> <a id="28375" class="PrimitiveType">Set</a> <a id="28379" href="plfa.Equality.html#28359" class="Bound">ℓ</a><a id="28380" class="Symbol">}</a> <a id="28382" class="Symbol">{</a><a id="28383" href="plfa.Equality.html#28383" class="Bound">x</a> <a id="28385" href="plfa.Equality.html#28385" class="Bound">y</a> <a id="28387" class="Symbol">:</a> <a id="28389" href="plfa.Equality.html#28371" class="Bound">A</a><a id="28390" class="Symbol">}</a>
  <a id="28394" class="Symbol">→</a> <a id="28396" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28383" class="Bound">x</a> <a id="28398" href="plfa.Equality.html#28173" class="Datatype Operator">≡′</a> <a id="28401" href="plfa.Equality.html#28385" class="Bound">y</a>
    <a id="28407" class="Comment">------</a>
  <a id="28416" class="Symbol">→</a> <a id="28418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28385" class="Bound">y</a> <a id="28420" href="plfa.Equality.html#28173" class="Datatype Operator">≡′</a> <a id="28423" href="plfa.Equality.html#28383" class="Bound">x</a>
<a id="28425" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28349" class="Function">sym′</a> <a id="28430" href="plfa.Equality.html#28230" class="InductiveConstructor">refl′</a> <a id="28436" class="Symbol">=</a> <a id="28438" href="plfa.Equality.html#28230" class="InductiveConstructor">refl′</a>
</pre>{% endraw %}
{::comment}
For simplicity, we avoid universe polymorphism in the definitions given in
the text, but most definitions in the standard library, including those for
equality, are generalised to arbitrary levels as above.
{:/}

为了简介，我们在本书中给出的定义将避免使用全体多态，但是大多数标准库中的定义，
包括相等性的定义，都推广到了任意等级，如上所示。

{::comment}
Here is the generalised definition of Leibniz equality:
{:/}

下面是莱布尼兹相等性的推广定义：

{% raw %}<pre class="Agda"><a id="_≐′_"></a><a id="28836" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28836" class="Function Operator">_≐′_</a> <a id="28841" class="Symbol">:</a> <a id="28843" class="Symbol">∀</a> <a id="28845" class="Symbol">{</a><a id="28846" href="plfa.Equality.html#28846" class="Bound">ℓ</a> <a id="28848" class="Symbol">:</a> <a id="28850" href="Agda.Primitive.html#408" class="Postulate">Level</a><a id="28855" class="Symbol">}</a> <a id="28857" class="Symbol">{</a><a id="28858" href="plfa.Equality.html#28858" class="Bound">A</a> <a id="28860" class="Symbol">:</a> <a id="28862" class="PrimitiveType">Set</a> <a id="28866" href="plfa.Equality.html#28846" class="Bound">ℓ</a><a id="28867" class="Symbol">}</a> <a id="28869" class="Symbol">(</a><a id="28870" href="plfa.Equality.html#28870" class="Bound">x</a> <a id="28872" href="plfa.Equality.html#28872" class="Bound">y</a> <a id="28874" class="Symbol">:</a> <a id="28876" href="plfa.Equality.html#28858" class="Bound">A</a><a id="28877" class="Symbol">)</a> <a id="28879" class="Symbol">→</a> <a id="28881" class="PrimitiveType">Set</a> <a id="28885" class="Symbol">(</a><a id="28886" href="Agda.Primitive.html#627" class="Primitive">lsuc</a> <a id="28891" href="plfa.Equality.html#28846" class="Bound">ℓ</a><a id="28892" class="Symbol">)</a>
<a id="28894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Equality.md %}{% raw %}#28836" class="Function Operator">_≐′_</a> <a id="28899" class="Symbol">{</a><a id="28900" href="plfa.Equality.html#28900" class="Bound">ℓ</a><a id="28901" class="Symbol">}</a> <a id="28903" class="Symbol">{</a><a id="28904" href="plfa.Equality.html#28904" class="Bound">A</a><a id="28905" class="Symbol">}</a> <a id="28907" href="plfa.Equality.html#28907" class="Bound">x</a> <a id="28909" href="plfa.Equality.html#28909" class="Bound">y</a> <a id="28911" class="Symbol">=</a> <a id="28913" class="Symbol">∀</a> <a id="28915" class="Symbol">(</a><a id="28916" href="plfa.Equality.html#28916" class="Bound">P</a> <a id="28918" class="Symbol">:</a> <a id="28920" href="plfa.Equality.html#28904" class="Bound">A</a> <a id="28922" class="Symbol">→</a> <a id="28924" class="PrimitiveType">Set</a> <a id="28928" href="plfa.Equality.html#28900" class="Bound">ℓ</a><a id="28929" class="Symbol">)</a> <a id="28931" class="Symbol">→</a> <a id="28933" href="plfa.Equality.html#28916" class="Bound">P</a> <a id="28935" href="plfa.Equality.html#28907" class="Bound">x</a> <a id="28937" class="Symbol">→</a> <a id="28939" href="plfa.Equality.html#28916" class="Bound">P</a> <a id="28941" href="plfa.Equality.html#28909" class="Bound">y</a>
</pre>{% endraw %}
{::comment}
Before the signature used `Set₁` as the type of a term that includes
`Set`, whereas here the signature uses `Set (lsuc ℓ)` as the type of a
term that includes `Set ℓ`.
{:/}

之前，签名中使用了 `Set₁` 来作为一个值包括了 `Set` 的类型；而此处，我们使用
`Set (lsuc ℓ)` 来作为一个值包括了 `Set ℓ` 的类型。

{::comment}
Further information on levels can be found in the [Agda Wiki][wiki].
{:/}

更多的关于等级的信息可以从[Agda 维基（英文）][wiki]中查询。

[wiki]: http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.UniversePolymorphism


{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the
standard library:
{:/}

标准库中可以找到与本章节中相似的定义：

{% raw %}<pre class="Agda"><a id="29612" class="Comment">-- import Relation.Binary.PropositionalEquality as Eq</a>
<a id="29666" class="Comment">-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)</a>
<a id="29730" class="Comment">-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)</a>
</pre>{% endraw %}
{::comment}
Here the imports are shown as comments rather than code to avoid
collisions, as mentioned in the introduction.
{:/}

这里的导入以注释的形式给出，以防止冲突，如引言中解释的那样。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≡  U+2261  IDENTICAL TO (\==, \equiv)
    ⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
    ⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
    ∎  U+220E  END OF PROOF (\qed)
    ≐  U+2250  APPROACHES THE LIMIT (\.=)
    ℓ  U+2113  SCRIPT SMALL L (\ell)
    ⊔  U+2294  SQUARE CUP (\lub)
    ₀  U+2080  SUBSCRIPT ZERO (\_0)
    ₁  U+2081  SUBSCRIPT ONE (\_1)
    ₂  U+2082  SUBSCRIPT TWO (\_2)
{:/}

本章节使用下列 Unicode：

    ≡  U+2261  等同于 (\==, \equiv)
    ⟨  U+27E8  数学左尖括号 (\<)
    ⟩  U+27E9  数学右尖括号 (\>)
    ∎  U+220E  证毕 (\qed)
    ≐  U+2250  接近于极限 (\.=)
    ℓ  U+2113  手写小写 L (\ell)
    ⊔  U+2294  正方形向上开口 (\lub)
    ₀  U+2080  下标 0 (\_0)
    ₁  U+2081  下标 1 (\_1)
    ₂  U+2082  下标 2 (\_2)
