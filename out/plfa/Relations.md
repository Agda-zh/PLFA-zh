---
src       : "src/plfa/Relations.lagda.md"
title     : "Relations: 关系的归纳定义"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
translators : ["Fangyi Zhou"]
progress  : 100
---

{% raw %}<pre class="Agda"><a id="181" class="Keyword">module</a> <a id="188" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="203" class="Keyword">where</a>
</pre>{% endraw %}
{::comment}
After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.
{:/}

在定义了加法和乘法等运算以后，下一步我们来定义**关系（Relation）**，比如说**小于等于**。


{::comment}
## Imports
{:/}

## 导入

{% raw %}<pre class="Agda"><a id="464" class="Keyword">import</a> <a id="471" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="509" class="Symbol">as</a> <a id="512" class="Module">Eq</a>
<a id="515" class="Keyword">open</a> <a id="520" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="523" class="Keyword">using</a> <a id="529" class="Symbol">(</a><a id="530" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">_≡_</a><a id="533" class="Symbol">;</a> <a id="535" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a><a id="539" class="Symbol">;</a> <a id="541" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a><a id="545" class="Symbol">)</a>
<a id="547" class="Keyword">open</a> <a id="552" class="Keyword">import</a> <a id="559" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="568" class="Keyword">using</a> <a id="574" class="Symbol">(</a><a id="575" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="576" class="Symbol">;</a> <a id="578" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="582" class="Symbol">;</a> <a id="584" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a><a id="587" class="Symbol">;</a> <a id="589" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">_+_</a><a id="592" class="Symbol">)</a>
<a id="594" class="Keyword">open</a> <a id="599" class="Keyword">import</a> <a id="606" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="626" class="Keyword">using</a> <a id="632" class="Symbol">(</a><a id="633" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a><a id="639" class="Symbol">)</a>
</pre>{% endraw %}

{::comment}
## Defining relations
{:/}

## 定义关系

{::comment}
The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:
{:/}

小于等于这个关系有无穷个实例，如下所示：


    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

{::comment}
And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:
{:/}

但是，我们仍然可以用几行有限的定义来表示所有的实例，如下文所示的一对推理规则：

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

{::comment}
And here is the definition in Agda:
{:/}

以及其 Agda 定义：

{% raw %}<pre class="Agda"><a id="1456" class="Keyword">data</a> <a id="_≤_"></a><a id="1461" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1461" class="Datatype Operator">_≤_</a> <a id="1465" class="Symbol">:</a> <a id="1467" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1469" class="Symbol">→</a> <a id="1471" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="1473" class="Symbol">→</a> <a id="1475" class="PrimitiveType">Set</a> <a id="1479" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1488" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1488" class="InductiveConstructor">z≤n</a> <a id="1492" class="Symbol">:</a> <a id="1494" class="Symbol">∀</a> <a id="1496" class="Symbol">{</a><a id="1497" href="plfa.Relations.html#1497" class="Bound">n</a> <a id="1499" class="Symbol">:</a> <a id="1501" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1502" class="Symbol">}</a>
      <a id="1510" class="Comment">--------</a>
    <a id="1523" class="Symbol">→</a> <a id="1525" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="1530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1461" class="Datatype Operator">≤</a> <a id="1532" href="plfa.Relations.html#1497" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1537" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="1541" class="Symbol">:</a> <a id="1543" class="Symbol">∀</a> <a id="1545" class="Symbol">{</a><a id="1546" href="plfa.Relations.html#1546" class="Bound">m</a> <a id="1548" href="plfa.Relations.html#1548" class="Bound">n</a> <a id="1550" class="Symbol">:</a> <a id="1552" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="1553" class="Symbol">}</a>
    <a id="1559" class="Symbol">→</a> <a id="1561" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1546" class="Bound">m</a> <a id="1563" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="1565" href="plfa.Relations.html#1548" class="Bound">n</a>
      <a id="1573" class="Comment">-------------</a>
    <a id="1591" class="Symbol">→</a> <a id="1593" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1546" class="Bound">m</a> <a id="1599" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="1601" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="1605" href="plfa.Relations.html#1548" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.
{:/}

在这里，`z≤n` 和 `s≤s`（无空格）是构造子的名称，`zero ≤ n`、`m ≤ n` 和
`suc m ≤ suc n` （带空格）是类型。在这里我们第一次用到了
**索引数据类型（Indexed datatype）**。我们使用 `m` 和 `n` 这两个自然数来索引
`m ≤ n` 这个类型。在 Agda 里，由两个及以上短横线开始的行是注释行，
我们巧妙利用这一语法特性，用上述形式来表示相应的推理规则。
在后文中，我们还会继续使用这一形式。

{::comment}
Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.
{:/}

这两条定义告诉我们相同的两件事：

* **起始步骤**: 对于所有的自然数 `n`，命题 `zero ≤ n` 成立。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，如果命题 `m ≤ n` 成立，
  那么命题 `suc m ≤ suc n` 成立。

{::comment}
In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.
{:/}

实际上，他们分别给我们更多的信息：

* **起始步骤**: 对于所有的自然数 `n`，构造子 `z≤n` 提供了 `zero ≤ n` 成立的证明。
* **归纳步骤**：对于所有的自然数 `m` 和 `n`，构造子 `s≤s` 将 `m ≤ n` 成立的证明
  转化为 `suc m ≤ suc n` 成立的证明。

{::comment}
For example, here in inference rule notation is the proof that
`2 ≤ 4`:
{:/}

例如，我们在这里以推理规则的形式写出 `2 ≤ 4` 的证明：

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

{::comment}
And here is the corresponding Agda proof:
{:/}

下面是对应的 Agda 证明：

{% raw %}<pre class="Agda"><a id="3535" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3535" class="Function">_</a> <a id="3537" class="Symbol">:</a> <a id="3539" class="Number">2</a> <a id="3541" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="3543" class="Number">4</a>
<a id="3545" class="Symbol">_</a> <a id="3547" class="Symbol">=</a> <a id="3549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="3553" class="Symbol">(</a><a id="3554" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="3558" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a><a id="3561" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
## Implicit arguments
{:/}

## 隐式参数

{::comment}
This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:
{:/}

这是我们第一次使用隐式参数。定义不等式时，构造子的定义中使用了 `∀`，
就像我们在下面的命题中使用 `∀` 一样：

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

{::comment}
However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.
{:/}

但是我们这里的定义使用了花括号 `{ }`，而不是小括号 `( )`。
这意味着参数是**隐式的（Implicit）**，不需要额外声明。实际上，Agda 的类型检查器
会**推导（Infer）**出它们。因此，我们在 `m + n ≡ n + m` 的证明中需要写出 `+-comm m n`，
在 `zero ≤ n` 的证明中可以省略 `n`。同理，如果 `m≤n` 是 `m ≤ n`的证明，
那么我们写出 `s≤s m≤n` 作为 `suc m ≤ suc n` 的证明，无需声明 `m` 和 `n`。

{::comment}
If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
{:/}

如果有希望的话，我们也可以在大括号里显式声明隐式参数。例如，下面是 `2 ≤ 4` 的 Agda
证明，包括了显式声明了的隐式参数：

{% raw %}<pre class="Agda"><a id="5001" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5001" class="Function">_</a> <a id="5003" class="Symbol">:</a> <a id="5005" class="Number">2</a> <a id="5007" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="5009" class="Number">4</a>
<a id="5011" class="Symbol">_</a> <a id="5013" class="Symbol">=</a> <a id="5015" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="5019" class="Symbol">{</a><a id="5020" class="Number">1</a><a id="5021" class="Symbol">}</a> <a id="5023" class="Symbol">{</a><a id="5024" class="Number">3</a><a id="5025" class="Symbol">}</a> <a id="5027" class="Symbol">(</a><a id="5028" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="5032" class="Symbol">{</a><a id="5033" class="Number">0</a><a id="5034" class="Symbol">}</a> <a id="5036" class="Symbol">{</a><a id="5037" class="Number">2</a><a id="5038" class="Symbol">}</a> <a id="5040" class="Symbol">(</a><a id="5041" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a> <a id="5045" class="Symbol">{</a><a id="5046" class="Number">2</a><a id="5047" class="Symbol">}))</a>
</pre>{% endraw %}
{::comment}
One may also identify implicit arguments by name:
{:/}

也可以额外加上参数的名字：

{% raw %}<pre class="Agda"><a id="5143" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5143" class="Function">_</a> <a id="5145" class="Symbol">:</a> <a id="5147" class="Number">2</a> <a id="5149" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="5151" class="Number">4</a>
<a id="5153" class="Symbol">_</a> <a id="5155" class="Symbol">=</a> <a id="5157" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="5161" class="Symbol">{</a><a id="5162" class="Argument">m</a> <a id="5164" class="Symbol">=</a> <a id="5166" class="Number">1</a><a id="5167" class="Symbol">}</a> <a id="5169" class="Symbol">{</a><a id="5170" class="Argument">n</a> <a id="5172" class="Symbol">=</a> <a id="5174" class="Number">3</a><a id="5175" class="Symbol">}</a> <a id="5177" class="Symbol">(</a><a id="5178" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="5182" class="Symbol">{</a><a id="5183" class="Argument">m</a> <a id="5185" class="Symbol">=</a> <a id="5187" class="Number">0</a><a id="5188" class="Symbol">}</a> <a id="5190" class="Symbol">{</a><a id="5191" class="Argument">n</a> <a id="5193" class="Symbol">=</a> <a id="5195" class="Number">2</a><a id="5196" class="Symbol">}</a> <a id="5198" class="Symbol">(</a><a id="5199" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a> <a id="5203" class="Symbol">{</a><a id="5204" class="Argument">n</a> <a id="5206" class="Symbol">=</a> <a id="5208" class="Number">2</a><a id="5209" class="Symbol">}))</a>
</pre>{% endraw %}
{::comment}
In the latter format, you may only supply some implicit arguments:
{:/}

在后者的形式中，也可以只声明一部分隐式参数：

{% raw %}<pre class="Agda"><a id="5331" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5331" class="Function">_</a> <a id="5333" class="Symbol">:</a> <a id="5335" class="Number">2</a> <a id="5337" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="5339" class="Number">4</a>
<a id="5341" class="Symbol">_</a> <a id="5343" class="Symbol">=</a> <a id="5345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1537" class="InductiveConstructor">s≤s</a> <a id="5349" class="Symbol">{</a><a id="5350" class="Argument">n</a> <a id="5352" class="Symbol">=</a> <a id="5354" class="Number">3</a><a id="5355" class="Symbol">}</a> <a id="5357" class="Symbol">(</a><a id="5358" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="5362" class="Symbol">{</a><a id="5363" class="Argument">n</a> <a id="5365" class="Symbol">=</a> <a id="5367" class="Number">2</a><a id="5368" class="Symbol">}</a> <a id="5370" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a><a id="5373" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
It is not permitted to swap implicit arguments, even when named.
{:/}

但是不可以改变隐式参数的顺序，即便加上了名字。


{::comment}
## Precedence
{:/}

## 优先级

{::comment}
We declare the precedence for comparison as follows:
{:/}

我们如下定义比较的优先级：

{% raw %}<pre class="Agda"><a id="5619" class="Keyword">infix</a> <a id="5625" class="Number">4</a> <a id="5627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1461" class="Datatype Operator">_≤_</a>
</pre>{% endraw %}
{::comment}
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.
{:/}

我们将 `_≤_` 的优先级设置为 4，所以它比优先级为 6 的 `_+_` 结合的更紧，此外，
`1 + 2 ≤ 3` 将被解析为 `(1 + 2) ≤ 3`。我们用 `infix` 来表示运算符既不是左结合的，
也不是右结合的。因为 `1 ≤ 2 ≤ 3` 解析为 `(1 ≤ 2) ≤ 3` 或者 `1 ≤ (2 ≤ 3)` 都没有意义。


{::comment}
## Decidability
{:/}

## 可决定性

{::comment}
Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}/Decidable/).
{:/}

给定两个数，我们可以很直接地决定第一个数是不是小于等于第二个数。我们在此处不给出说明的代码，
但我们会在 [Decidable]({{ site.baseurl }}/Decidable/) 章节重新讨论这个问题。


{::comment}
## Inversion
{:/}

## 反演

{::comment}
In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.
{:/}

在我们的定义中，我们从更小的东西得到更大的东西。例如，我们可以从
`m ≤ n` 得出 `suc m ≤ suc n` 的结论，这里的 `suc m` 比 `m` 更大
（也就是说，前者包含后者），`suc n` 也比 `n` 更大。但有时我们也
需要从更大的东西得到更小的东西。

{::comment}
There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
{:/}

只有一种方式能够证明对于任意 `m` 和 `n` 有 `suc m ≤ suc n`。
这让我们能够反演（invert）之前的规则。

{% raw %}<pre class="Agda"><a id="inv-s≤s"></a><a id="7257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7257" class="Function">inv-s≤s</a> <a id="7265" class="Symbol">:</a> <a id="7267" class="Symbol">∀</a> <a id="7269" class="Symbol">{</a><a id="7270" href="plfa.Relations.html#7270" class="Bound">m</a> <a id="7272" href="plfa.Relations.html#7272" class="Bound">n</a> <a id="7274" class="Symbol">:</a> <a id="7276" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="7277" class="Symbol">}</a>
  <a id="7281" class="Symbol">→</a> <a id="7283" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7270" class="Bound">m</a> <a id="7289" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="7291" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="7295" href="plfa.Relations.html#7272" class="Bound">n</a>
    <a id="7301" class="Comment">-------------</a>
  <a id="7317" class="Symbol">→</a> <a id="7319" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7270" class="Bound">m</a> <a id="7321" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="7323" href="plfa.Relations.html#7272" class="Bound">n</a>
<a id="7325" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7257" class="Function">inv-s≤s</a> <a id="7333" class="Symbol">(</a><a id="7334" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="7338" href="plfa.Relations.html#7338" class="Bound">m≤n</a><a id="7341" class="Symbol">)</a> <a id="7343" class="Symbol">=</a> <a id="7345" href="plfa.Relations.html#7338" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
Here `m≤n` (with no spaces) is a variable name while
`m ≤ n` (with spaces) is a type, and the latter
is the type of the former.  It is a common convention
in Agda to choose derive a variable name by removing
spaces from its type.
{:/}

这里的 `m≤n`（不带空格）是一个变量名，而 `m ≤ n`（带空格）是一个类型，
且后者是前者的类型。在 Agda 中，将类型中的空格去掉来作为变量名是一种常见的约定。

{::comment}
Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.
{:/}

并不是所有规则都可以反演。实际上，`z≤n` 的规则没有非隐式的假设，
因此它没有可以被反演的规则。但这种反演通常是成立的。

{::comment}
Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
{:/}

反演的另一个例子是证明只存在一种情况使得一个数字能够小于或等于零。

{% raw %}<pre class="Agda"><a id="inv-z≤n"></a><a id="8100" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8100" class="Function">inv-z≤n</a> <a id="8108" class="Symbol">:</a> <a id="8110" class="Symbol">∀</a> <a id="8112" class="Symbol">{</a><a id="8113" href="plfa.Relations.html#8113" class="Bound">m</a> <a id="8115" class="Symbol">:</a> <a id="8117" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="8118" class="Symbol">}</a>
  <a id="8122" class="Symbol">→</a> <a id="8124" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8113" class="Bound">m</a> <a id="8126" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="8128" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
    <a id="8137" class="Comment">--------</a>
  <a id="8148" class="Symbol">→</a> <a id="8150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8113" class="Bound">m</a> <a id="8152" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="8154" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>
<a id="8159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8100" class="Function">inv-z≤n</a> <a id="8167" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a> <a id="8171" class="Symbol">=</a> <a id="8173" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
</pre>{% endraw %}
{::comment}
## Properties of ordering relations
{:/}

## 序关系的性质

{::comment}
Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.
{:/}

数学家对于关系的常见性质给出了约定的名称。

* **自反（Reflexive）**：对于所有的 `n`，关系 `n ≤ n` 成立。
* **传递（Transitive）**：对于所有的 `m`、 `n` 和 `p`，如果 `m ≤ n` 和 `n ≤ p`
  成立，那么 `m ≤ p` 也成立。
* **反对称（Anti-symmetric）**：对于所有的 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
  同时成立，那么 `m ≡ n` 成立。
* **完全（Total）**：对于所有的 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。

{::comment}
The relation `_≤_` satisfies all four of these properties.
{:/}

`_≤_` 关系满足上述四条性质。

{::comment}
There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.
{:/}

对于上述性质的组合也有约定的名称。

* **预序（Preorder）**：满足自反和传递的关系。
* **偏序（Partial Order）**：满足反对称的预序。
* **全序（Total Order）**：满足完全的偏序。

{::comment}
If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.
{:/}

如果你进入了关于关系的聚会，你现在知道怎么样和人讨论了，可以讨论关于自反、传递、反对称和完全，
或者问一问这是不是预序、偏序或者全序。

{::comment}
Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.
{:/}

更认真的来说，如果你在阅读论文时碰到了一个关系，本文的介绍让你可以对关系有基本的了解和判断，
来判断这个关系是不是预序、偏序或者全序。一个认真的作者一般会在文章指出这个关系具有（或者缺少）
上述性质，比如说指出新定义的关系是一个偏序而不是全序。

{::comment}
#### Exercise `orderings` {#orderings}
{:/}

#### 练习 `orderings` {#orderings}

{::comment}
Give an example of a preorder that is not a partial order.
{:/}

给出一个不是偏序的预序的例子。

{::comment}
{% raw %}<pre class="Agda"><a id="10494" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10531" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}
{::comment}
Give an example of a partial order that is not a total order.
{:/}

给出一个不是全序的偏序的例子。

{::comment}
{% raw %}<pre class="Agda"><a id="10662" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="10699" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Reflexivity
{:/}

## 自反性

{::comment}
The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
{:/}

我们第一个来证明的性质是自反性：对于任意自然数 `n`，关系 `n ≤ n` 成立。我们使用标准库
的惯例来隐式申明参数，在使用自反性的证明时这样可以更加方便。

{% raw %}<pre class="Agda"><a id="≤-refl"></a><a id="11115" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11115" class="Function">≤-refl</a> <a id="11122" class="Symbol">:</a> <a id="11124" class="Symbol">∀</a> <a id="11126" class="Symbol">{</a><a id="11127" href="plfa.Relations.html#11127" class="Bound">n</a> <a id="11129" class="Symbol">:</a> <a id="11131" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="11132" class="Symbol">}</a>
    <a id="11138" class="Comment">-----</a>
  <a id="11146" class="Symbol">→</a> <a id="11148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11127" class="Bound">n</a> <a id="11150" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="11152" href="plfa.Relations.html#11127" class="Bound">n</a>
<a id="11154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11115" class="Function">≤-refl</a> <a id="11161" class="Symbol">{</a><a id="11162" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a><a id="11166" class="Symbol">}</a> <a id="11168" class="Symbol">=</a> <a id="11170" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="11174" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11115" class="Function">≤-refl</a> <a id="11181" class="Symbol">{</a><a id="11182" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="11186" href="plfa.Relations.html#11186" class="Bound">n</a><a id="11187" class="Symbol">}</a> <a id="11189" class="Symbol">=</a> <a id="11191" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="11195" href="plfa.Relations.html#11115" class="Function">≤-refl</a>
</pre>{% endraw %}
{::comment}
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.
{:/}

这个证明直接在 `n` 上进行归纳。在起始步骤中，`zero ≤ zero` 由 `z≤n` 证明；在归纳步骤中，
归纳假设 `≤-refl {n}` 给我们带来了 `n ≤ n` 的证明，我们只需要使用 `s≤s`，就可以获得
`suc n ≤ suc n` 的证明。

{::comment}
It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

在 Emacs 中来交互式地证明自反性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


{::comment}
## Transitivity
{:/}

## 传递性

{::comment}
The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
{:/}

我们第二个证明的性质是传递性：对于任意自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ p`
成立，那么 `m ≤ p` 成立。同样，`m`、`n` 和 `p` 是隐式参数：

{% raw %}<pre class="Agda"><a id="≤-trans"></a><a id="12218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12218" class="Function">≤-trans</a> <a id="12226" class="Symbol">:</a> <a id="12228" class="Symbol">∀</a> <a id="12230" class="Symbol">{</a><a id="12231" href="plfa.Relations.html#12231" class="Bound">m</a> <a id="12233" href="plfa.Relations.html#12233" class="Bound">n</a> <a id="12235" href="plfa.Relations.html#12235" class="Bound">p</a> <a id="12237" class="Symbol">:</a> <a id="12239" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="12240" class="Symbol">}</a>
  <a id="12244" class="Symbol">→</a> <a id="12246" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12231" class="Bound">m</a> <a id="12248" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="12250" href="plfa.Relations.html#12233" class="Bound">n</a>
  <a id="12254" class="Symbol">→</a> <a id="12256" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12233" class="Bound">n</a> <a id="12258" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="12260" href="plfa.Relations.html#12235" class="Bound">p</a>
    <a id="12266" class="Comment">-----</a>
  <a id="12274" class="Symbol">→</a> <a id="12276" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12231" class="Bound">m</a> <a id="12278" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="12280" href="plfa.Relations.html#12235" class="Bound">p</a>
<a id="12282" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12218" class="Function">≤-trans</a> <a id="12290" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>       <a id="12300" class="Symbol">_</a>          <a id="12311" class="Symbol">=</a>  <a id="12314" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="12318" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12218" class="Function">≤-trans</a> <a id="12326" class="Symbol">(</a><a id="12327" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="12331" href="plfa.Relations.html#12331" class="Bound">m≤n</a><a id="12334" class="Symbol">)</a> <a id="12336" class="Symbol">(</a><a id="12337" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="12341" href="plfa.Relations.html#12341" class="Bound">n≤p</a><a id="12344" class="Symbol">)</a>  <a id="12347" class="Symbol">=</a>  <a id="12350" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="12354" class="Symbol">(</a><a id="12355" href="plfa.Relations.html#12218" class="Function">≤-trans</a> <a id="12363" href="plfa.Relations.html#12331" class="Bound">m≤n</a> <a id="12367" href="plfa.Relations.html#12341" class="Bound">n≤p</a><a id="12370" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.
{:/}

这里我们在 `m ≤ n` 的**证据（Evidence）**上进行归纳。在起始步骤里，第一个不等式因为 `z≤n` 而成立，
那么结论亦可由 `z≤n` 而得出。在这里，`n ≤ p` 的证明是不需要的，我们用 `_` 来表示这个
证明没有被使用。

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.
{:/}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个不等式因为 `s≤s n≤p` 而成立，
所以我们已知 `suc m ≤ suc n` 和 `suc n ≤ suc p`，求证 `suc m ≤ suc p`。
通过归纳假设 `≤-trans m≤n n≤p`，我们得知 `m ≤ p`，在此之上使用 `s≤s` 即可证。

{::comment}
The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.
{:/}

`≤-trans (s≤s m≤n) z≤n` 不可能发生，因为第一个不等式告诉我们中间的数是一个 `suc n`，
而第二个不等式告诉我们中间的书是 `zero`。Agda 可以推断这样的情况不可能发现，所以我们不需要
（也不可以）列出这种情况。

{::comment}
Alternatively, we could make the implicit parameters explicit:
{:/}

我们也可以将隐式参数显式地声明。

{% raw %}<pre class="Agda"><a id="≤-trans′"></a><a id="13844" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13844" class="Function">≤-trans′</a> <a id="13853" class="Symbol">:</a> <a id="13855" class="Symbol">∀</a> <a id="13857" class="Symbol">(</a><a id="13858" href="plfa.Relations.html#13858" class="Bound">m</a> <a id="13860" href="plfa.Relations.html#13860" class="Bound">n</a> <a id="13862" href="plfa.Relations.html#13862" class="Bound">p</a> <a id="13864" class="Symbol">:</a> <a id="13866" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="13867" class="Symbol">)</a>
  <a id="13871" class="Symbol">→</a> <a id="13873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13858" class="Bound">m</a> <a id="13875" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="13877" href="plfa.Relations.html#13860" class="Bound">n</a>
  <a id="13881" class="Symbol">→</a> <a id="13883" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13860" class="Bound">n</a> <a id="13885" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="13887" href="plfa.Relations.html#13862" class="Bound">p</a>
    <a id="13893" class="Comment">-----</a>
  <a id="13901" class="Symbol">→</a> <a id="13903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13858" class="Bound">m</a> <a id="13905" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="13907" href="plfa.Relations.html#13862" class="Bound">p</a>
<a id="13909" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13844" class="Function">≤-trans′</a> <a id="13918" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="13926" class="Symbol">_</a>       <a id="13934" class="Symbol">_</a>       <a id="13942" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>       <a id="13952" class="Symbol">_</a>          <a id="13963" class="Symbol">=</a>  <a id="13966" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="13970" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13844" class="Function">≤-trans′</a> <a id="13979" class="Symbol">(</a><a id="13980" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13984" href="plfa.Relations.html#13984" class="Bound">m</a><a id="13985" class="Symbol">)</a> <a id="13987" class="Symbol">(</a><a id="13988" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="13992" href="plfa.Relations.html#13992" class="Bound">n</a><a id="13993" class="Symbol">)</a> <a id="13995" class="Symbol">(</a><a id="13996" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="14000" href="plfa.Relations.html#14000" class="Bound">p</a><a id="14001" class="Symbol">)</a> <a id="14003" class="Symbol">(</a><a id="14004" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="14008" href="plfa.Relations.html#14008" class="Bound">m≤n</a><a id="14011" class="Symbol">)</a> <a id="14013" class="Symbol">(</a><a id="14014" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="14018" href="plfa.Relations.html#14018" class="Bound">n≤p</a><a id="14021" class="Symbol">)</a>  <a id="14024" class="Symbol">=</a>  <a id="14027" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="14031" class="Symbol">(</a><a id="14032" href="plfa.Relations.html#13844" class="Function">≤-trans′</a> <a id="14041" href="plfa.Relations.html#13984" class="Bound">m</a> <a id="14043" href="plfa.Relations.html#13992" class="Bound">n</a> <a id="14045" href="plfa.Relations.html#14000" class="Bound">p</a> <a id="14047" href="plfa.Relations.html#14008" class="Bound">m≤n</a> <a id="14051" href="plfa.Relations.html#14018" class="Bound">n≤p</a><a id="14054" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.
{:/}

有人说这样的证明更加的清晰，也有人说这个更长的证明让人难以抓住证明的重点。
我们一般选择使用简短的证明。

{::comment}
The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.
{:/}

对于性质成立证明进行的归纳（如上文中对于 `m ≤ n` 的证明进行归纳），相比于对于性质成立的值进行的归纳
（如对于 `m` 进行归纳），有非常大的价值。我们会经常使用这样的方法。

{::comment}
Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.
{:/}

同样，在 Emacs 中来交互式地证明传递性是一个很好的练习，可以使用洞，以及 `C-c C-c`、
`C-c C-,` 和 `C-c C-r` 命令。


{::comment}
## Anti-symmetry
{:/}

## 反对称性

{::comment}
The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
{:/}

我们证明的第三个性质是反对称性：对于所有的自然数 `m` 和 `n`，如果 `m ≤ n` 和 `n ≤ m`
同时成立，那么 `m ≡ n` 成立：

{% raw %}<pre class="Agda"><a id="≤-antisym"></a><a id="15197" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15197" class="Function">≤-antisym</a> <a id="15207" class="Symbol">:</a> <a id="15209" class="Symbol">∀</a> <a id="15211" class="Symbol">{</a><a id="15212" href="plfa.Relations.html#15212" class="Bound">m</a> <a id="15214" href="plfa.Relations.html#15214" class="Bound">n</a> <a id="15216" class="Symbol">:</a> <a id="15218" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="15219" class="Symbol">}</a>
  <a id="15223" class="Symbol">→</a> <a id="15225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15212" class="Bound">m</a> <a id="15227" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="15229" href="plfa.Relations.html#15214" class="Bound">n</a>
  <a id="15233" class="Symbol">→</a> <a id="15235" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15214" class="Bound">n</a> <a id="15237" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="15239" href="plfa.Relations.html#15212" class="Bound">m</a>
    <a id="15245" class="Comment">-----</a>
  <a id="15253" class="Symbol">→</a> <a id="15255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15212" class="Bound">m</a> <a id="15257" href="Agda.Builtin.Equality.html#125" class="Datatype Operator">≡</a> <a id="15259" href="plfa.Relations.html#15214" class="Bound">n</a>
<a id="15261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15197" class="Function">≤-antisym</a> <a id="15271" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>       <a id="15281" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>        <a id="15292" class="Symbol">=</a>  <a id="15295" href="Agda.Builtin.Equality.html#182" class="InductiveConstructor">refl</a>
<a id="15300" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15197" class="Function">≤-antisym</a> <a id="15310" class="Symbol">(</a><a id="15311" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="15315" href="plfa.Relations.html#15315" class="Bound">m≤n</a><a id="15318" class="Symbol">)</a> <a id="15320" class="Symbol">(</a><a id="15321" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="15325" href="plfa.Relations.html#15325" class="Bound">n≤m</a><a id="15328" class="Symbol">)</a>  <a id="15331" class="Symbol">=</a>  <a id="15334" href="https://agda.github.io/agda-stdlib/v1.1/Relation.Binary.PropositionalEquality.Core.html#1090" class="Function">cong</a> <a id="15339" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="15343" class="Symbol">(</a><a id="15344" href="plfa.Relations.html#15197" class="Function">≤-antisym</a> <a id="15354" href="plfa.Relations.html#15315" class="Bound">m≤n</a> <a id="15358" href="plfa.Relations.html#15325" class="Bound">n≤m</a><a id="15361" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.
{:/}

同样，我们对于 `m ≤ n` 和 `n ≤ m` 的证明进行归纳。

{::comment}
In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)
{:/}

在起始步骤中，两个不等式都因为 `z≤n` 而成立。因此我们已知 `zero ≤ zero` 和 `zero ≤ zero`，
求证 `zero ≡ zero`，由自反性可证。（注：由等式的自反性可证，而不是不等式的自反性）

{::comment}
In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

{::comment}

在归纳步骤中，第一个不等式因为 `s≤s m≤n` 而成立，第二个等式因为 `s≤s n≤m` 而成立。因此我们已知
`suc m ≤ suc n` 和 `suc n ≤ suc m`，求证 `suc m ≡ suc n`。归纳假设 `≤-antisym m≤n n≤m`
可以证明 `m ≡ n`，因此我们可以使用同余性完成证明。


{::comment}
#### Exercise `≤-antisym-cases` {#leq-antisym-cases}
{:/}

#### 练习 `≤-antisym-cases` {#leq-antisym-cases}

{::comment}
The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?
{:/}

上面的证明中省略了一个参数是 `z≤n`，另一个参数是 `s≤s` 的情况。为什么可以省略这种情况？

{::comment}
{% raw %}<pre class="Agda"><a id="16681" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="16718" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Total
{:/}

## 完全性

{::comment}
The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.
{:/}

我们证明的第四个性质是完全性：对于任何自然数 `m` 和 `n`，`m ≤ n` 或者 `n ≤ m` 成立。
在 `m` 和 `n` 相等时，两者同时成立。

{::comment}
We specify what it means for inequality to be total:
{:/}

我们首先来说明怎么样不等式才是完全的：

{% raw %}<pre class="Agda"><a id="17124" class="Keyword">data</a> <a id="Total"></a><a id="17129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17129" class="Datatype">Total</a> <a id="17135" class="Symbol">(</a><a id="17136" href="plfa.Relations.html#17136" class="Bound">m</a> <a id="17138" href="plfa.Relations.html#17138" class="Bound">n</a> <a id="17140" class="Symbol">:</a> <a id="17142" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="17143" class="Symbol">)</a> <a id="17145" class="Symbol">:</a> <a id="17147" class="PrimitiveType">Set</a> <a id="17151" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="17160" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17160" class="InductiveConstructor">forward</a> <a id="17168" class="Symbol">:</a>
      <a id="17176" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17136" class="Bound">m</a> <a id="17178" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="17180" href="plfa.Relations.html#17138" class="Bound">n</a>
      <a id="17188" class="Comment">---------</a>
    <a id="17202" class="Symbol">→</a> <a id="17204" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17129" class="Datatype">Total</a> <a id="17210" href="plfa.Relations.html#17136" class="Bound">m</a> <a id="17212" href="plfa.Relations.html#17138" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="17217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17217" class="InductiveConstructor">flipped</a> <a id="17225" class="Symbol">:</a>
      <a id="17233" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17138" class="Bound">n</a> <a id="17235" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="17237" href="plfa.Relations.html#17136" class="Bound">m</a>
      <a id="17245" class="Comment">---------</a>
    <a id="17259" class="Symbol">→</a> <a id="17261" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17129" class="Datatype">Total</a> <a id="17267" href="plfa.Relations.html#17136" class="Bound">m</a> <a id="17269" href="plfa.Relations.html#17138" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.
{:/}

`Total m n` 成立的证明有两种形式：`forward m≤n` 或者 `flipped n≤m`，其中
`m≤n` 和 `n≤m` 分别是 `m ≤ n` 和 `n ≤ m` 的证明。

{::comment}
(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}/Connectives/).)
{:/}

（如果你对于逻辑学有所了解，上面的定义可以由析取（Disjunction）表示。
我们会在 [Connectives]({{ site.baseurl }}/Connectives/) 章节介绍析取。）

{::comment}
This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
{:/}

这是我们第一次使用带*参数*的数据类型，这里 `m` 和 `n` 是参数。这等同于下面的索引数据类型：

{% raw %}<pre class="Agda"><a id="18066" class="Keyword">data</a> <a id="Total′"></a><a id="18071" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18071" class="Datatype">Total′</a> <a id="18078" class="Symbol">:</a> <a id="18080" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18082" class="Symbol">→</a> <a id="18084" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="18086" class="Symbol">→</a> <a id="18088" class="PrimitiveType">Set</a> <a id="18092" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="18101" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18101" class="InductiveConstructor">forward′</a> <a id="18110" class="Symbol">:</a> <a id="18112" class="Symbol">∀</a> <a id="18114" class="Symbol">{</a><a id="18115" href="plfa.Relations.html#18115" class="Bound">m</a> <a id="18117" href="plfa.Relations.html#18117" class="Bound">n</a> <a id="18119" class="Symbol">:</a> <a id="18121" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18122" class="Symbol">}</a>
    <a id="18128" class="Symbol">→</a> <a id="18130" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18115" class="Bound">m</a> <a id="18132" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="18134" href="plfa.Relations.html#18117" class="Bound">n</a>
      <a id="18142" class="Comment">----------</a>
    <a id="18157" class="Symbol">→</a> <a id="18159" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18071" class="Datatype">Total′</a> <a id="18166" href="plfa.Relations.html#18115" class="Bound">m</a> <a id="18168" href="plfa.Relations.html#18117" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="18173" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18173" class="InductiveConstructor">flipped′</a> <a id="18182" class="Symbol">:</a> <a id="18184" class="Symbol">∀</a> <a id="18186" class="Symbol">{</a><a id="18187" href="plfa.Relations.html#18187" class="Bound">m</a> <a id="18189" href="plfa.Relations.html#18189" class="Bound">n</a> <a id="18191" class="Symbol">:</a> <a id="18193" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="18194" class="Symbol">}</a>
    <a id="18200" class="Symbol">→</a> <a id="18202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18189" class="Bound">n</a> <a id="18204" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="18206" href="plfa.Relations.html#18187" class="Bound">m</a>
      <a id="18214" class="Comment">----------</a>
    <a id="18229" class="Symbol">→</a> <a id="18231" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18071" class="Datatype">Total′</a> <a id="18238" href="plfa.Relations.html#18187" class="Bound">m</a> <a id="18240" href="plfa.Relations.html#18189" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.
{:/}

类型里的每个参数都转换成构造子的一个隐式参数。索引数据类型中的索引可以变化，正如在
`zero ≤ n` 和 `suc m ≤ suc n` 中那样，而参数化数据类型不一样，其参数必须保持相同，
正如在 `Total m n` 中那样。参数化的声明更短，更易于阅读，而且有时可以帮助到 Agda 的
终结检查器，所以我们尽可能地使用它们，而不是索引数据类型。

{::comment}
With that preliminary out of the way, we specify and prove totality:
{:/}

在上述准备工作完成后，我们定义并证明完全性。

{% raw %}<pre class="Agda"><a id="≤-total"></a><a id="19000" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19000" class="Function">≤-total</a> <a id="19008" class="Symbol">:</a> <a id="19010" class="Symbol">∀</a> <a id="19012" class="Symbol">(</a><a id="19013" href="plfa.Relations.html#19013" class="Bound">m</a> <a id="19015" href="plfa.Relations.html#19015" class="Bound">n</a> <a id="19017" class="Symbol">:</a> <a id="19019" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="19020" class="Symbol">)</a> <a id="19022" class="Symbol">→</a> <a id="19024" href="plfa.Relations.html#17129" class="Datatype">Total</a> <a id="19030" href="plfa.Relations.html#19013" class="Bound">m</a> <a id="19032" href="plfa.Relations.html#19015" class="Bound">n</a>
<a id="19034" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19000" class="Function">≤-total</a> <a id="19042" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="19050" href="plfa.Relations.html#19050" class="Bound">n</a>                         <a id="19076" class="Symbol">=</a>  <a id="19079" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="19087" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="19091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19000" class="Function">≤-total</a> <a id="19099" class="Symbol">(</a><a id="19100" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="19104" href="plfa.Relations.html#19104" class="Bound">m</a><a id="19105" class="Symbol">)</a> <a id="19107" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="19133" class="Symbol">=</a>  <a id="19136" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="19144" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="19148" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#19000" class="Function">≤-total</a> <a id="19156" class="Symbol">(</a><a id="19157" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="19161" href="plfa.Relations.html#19161" class="Bound">m</a><a id="19162" class="Symbol">)</a> <a id="19164" class="Symbol">(</a><a id="19165" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="19169" href="plfa.Relations.html#19169" class="Bound">n</a><a id="19170" class="Symbol">)</a> <a id="19172" class="Keyword">with</a> <a id="19177" href="plfa.Relations.html#19000" class="Function">≤-total</a> <a id="19185" href="plfa.Relations.html#19161" class="Bound">m</a> <a id="19187" href="plfa.Relations.html#19169" class="Bound">n</a>
<a id="19189" class="Symbol">...</a>                        <a id="19216" class="Symbol">|</a> <a id="19218" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17160" class="InductiveConstructor">forward</a> <a id="19226" href="plfa.Relations.html#19226" class="Bound">m≤n</a>  <a id="19231" class="Symbol">=</a>  <a id="19234" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="19242" class="Symbol">(</a><a id="19243" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="19247" href="plfa.Relations.html#19226" class="Bound">m≤n</a><a id="19250" class="Symbol">)</a>
<a id="19252" class="Symbol">...</a>                        <a id="19279" class="Symbol">|</a> <a id="19281" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17217" class="InductiveConstructor">flipped</a> <a id="19289" href="plfa.Relations.html#19289" class="Bound">n≤m</a>  <a id="19294" class="Symbol">=</a>  <a id="19297" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="19305" class="Symbol">(</a><a id="19306" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="19310" href="plfa.Relations.html#19289" class="Bound">n≤m</a><a id="19313" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.
{:/}

这里，我们的证明在两个参数上进行归纳，并按照情况分析：

* **第一起始步骤**：如果第一个参数是 `zero`，第二个参数是 `n`，那么 forward
  条件成立，我们使用 `z≤n` 作为 `zero ≤ n` 的证明。

* **第二起始步骤**：如果第一个参数是 `suc m`，第二个参数是 `zero`，那么 flipped
  条件成立，我们使用 `z≤n` 作为 `zero ≤ suc m` 的证明。

* **归纳步骤**：如果第一个参数是 `suc m`，第二个参数是 `suc n`，那么归纳假设
  `≤-total m n` 可以给出如下推断：

  + 归纳假设的 forward 条件成立，以 `m≤n` 作为 `m ≤ n` 的证明。以此我们可以使用
    `s≤s m≤n` 作为 `suc m ≤ suc n` 来证明 forward 条件成立。

  + 归纳假设的 flipped 条件成立，以 `n≤m` 作为 `n ≤ m` 的证明。以此我们可以使用
    `s≤s n≤m` 作为 `suc n ≤ suc m` 来证明 flipped 条件成立。

{::comment}
This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.
{:/}

这是我们第一次在 Agda 中使用 `with` 语句。`with` 关键字后面有一个表达式和一或多行。
每行以省略号（`...`）和一个竖线（`|`）开头，后面跟着用来匹配表达式的模式，和等式的右手边。

{::comment}
Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
{:/}

使用 `with` 语句等同于定义一个辅助函数。比如说，上面的定义和下面的等价：

{% raw %}<pre class="Agda"><a id="≤-total′"></a><a id="21510" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21510" class="Function">≤-total′</a> <a id="21519" class="Symbol">:</a> <a id="21521" class="Symbol">∀</a> <a id="21523" class="Symbol">(</a><a id="21524" href="plfa.Relations.html#21524" class="Bound">m</a> <a id="21526" href="plfa.Relations.html#21526" class="Bound">n</a> <a id="21528" class="Symbol">:</a> <a id="21530" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="21531" class="Symbol">)</a> <a id="21533" class="Symbol">→</a> <a id="21535" href="plfa.Relations.html#17129" class="Datatype">Total</a> <a id="21541" href="plfa.Relations.html#21524" class="Bound">m</a> <a id="21543" href="plfa.Relations.html#21526" class="Bound">n</a>
<a id="21545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21510" class="Function">≤-total′</a> <a id="21554" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="21562" href="plfa.Relations.html#21562" class="Bound">n</a>        <a id="21571" class="Symbol">=</a>  <a id="21574" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="21582" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="21586" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21510" class="Function">≤-total′</a> <a id="21595" class="Symbol">(</a><a id="21596" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21600" href="plfa.Relations.html#21600" class="Bound">m</a><a id="21601" class="Symbol">)</a> <a id="21603" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>     <a id="21612" class="Symbol">=</a>  <a id="21615" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="21623" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="21627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21510" class="Function">≤-total′</a> <a id="21636" class="Symbol">(</a><a id="21637" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21641" href="plfa.Relations.html#21641" class="Bound">m</a><a id="21642" class="Symbol">)</a> <a id="21644" class="Symbol">(</a><a id="21645" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21649" href="plfa.Relations.html#21649" class="Bound">n</a><a id="21650" class="Symbol">)</a>  <a id="21653" class="Symbol">=</a>  <a id="21656" href="plfa.Relations.html#21688" class="Function">helper</a> <a id="21663" class="Symbol">(</a><a id="21664" href="plfa.Relations.html#21510" class="Function">≤-total′</a> <a id="21673" href="plfa.Relations.html#21641" class="Bound">m</a> <a id="21675" href="plfa.Relations.html#21649" class="Bound">n</a><a id="21676" class="Symbol">)</a>
  <a id="21680" class="Keyword">where</a>
  <a id="21688" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21688" class="Function">helper</a> <a id="21695" class="Symbol">:</a> <a id="21697" href="plfa.Relations.html#17129" class="Datatype">Total</a> <a id="21703" href="plfa.Relations.html#21641" class="Bound">m</a> <a id="21705" href="plfa.Relations.html#21649" class="Bound">n</a> <a id="21707" class="Symbol">→</a> <a id="21709" href="plfa.Relations.html#17129" class="Datatype">Total</a> <a id="21715" class="Symbol">(</a><a id="21716" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21720" href="plfa.Relations.html#21641" class="Bound">m</a><a id="21721" class="Symbol">)</a> <a id="21723" class="Symbol">(</a><a id="21724" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="21728" href="plfa.Relations.html#21649" class="Bound">n</a><a id="21729" class="Symbol">)</a>
  <a id="21733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21688" class="Function">helper</a> <a id="21740" class="Symbol">(</a><a id="21741" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="21749" href="plfa.Relations.html#21749" class="Bound">m≤n</a><a id="21752" class="Symbol">)</a>  <a id="21755" class="Symbol">=</a>  <a id="21758" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="21766" class="Symbol">(</a><a id="21767" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="21771" href="plfa.Relations.html#21749" class="Bound">m≤n</a><a id="21774" class="Symbol">)</a>
  <a id="21778" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21688" class="Function">helper</a> <a id="21785" class="Symbol">(</a><a id="21786" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="21794" href="plfa.Relations.html#21794" class="Bound">n≤m</a><a id="21797" class="Symbol">)</a>  <a id="21800" class="Symbol">=</a>  <a id="21803" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="21811" class="Symbol">(</a><a id="21812" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="21816" href="plfa.Relations.html#21794" class="Bound">n≤m</a><a id="21819" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.
{:/}

这也是我们第一次在 Agda 中使用 `where` 语句。`where` 关键字后面有一或多条定义，其必须被缩进。
之前等式左手边的约束变量（此例中的 `m` 和 `n`）在嵌套的定义中仍然在作用域内。
在嵌套定义中的约束标识符（此例中的 `helper` ）在等式的右手边的作用域内。

{::comment}
If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
{:/}

如果两个参数相同，那么两个情况同时成立，我们可以返回任一证明。上面的代码中我们返回 forward 条件，
但是我们也可以返回 flipped 条件，如下：

{% raw %}<pre class="Agda"><a id="≤-total″"></a><a id="22703" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22703" class="Function">≤-total″</a> <a id="22712" class="Symbol">:</a> <a id="22714" class="Symbol">∀</a> <a id="22716" class="Symbol">(</a><a id="22717" href="plfa.Relations.html#22717" class="Bound">m</a> <a id="22719" href="plfa.Relations.html#22719" class="Bound">n</a> <a id="22721" class="Symbol">:</a> <a id="22723" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="22724" class="Symbol">)</a> <a id="22726" class="Symbol">→</a> <a id="22728" href="plfa.Relations.html#17129" class="Datatype">Total</a> <a id="22734" href="plfa.Relations.html#22717" class="Bound">m</a> <a id="22736" href="plfa.Relations.html#22719" class="Bound">n</a>
<a id="22738" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22703" class="Function">≤-total″</a> <a id="22747" href="plfa.Relations.html#22747" class="Bound">m</a>       <a id="22755" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>                      <a id="22781" class="Symbol">=</a>  <a id="22784" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="22792" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="22796" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22703" class="Function">≤-total″</a> <a id="22805" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="22813" class="Symbol">(</a><a id="22814" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22818" href="plfa.Relations.html#22818" class="Bound">n</a><a id="22819" class="Symbol">)</a>                   <a id="22839" class="Symbol">=</a>  <a id="22842" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="22850" href="plfa.Relations.html#1488" class="InductiveConstructor">z≤n</a>
<a id="22854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22703" class="Function">≤-total″</a> <a id="22863" class="Symbol">(</a><a id="22864" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22868" href="plfa.Relations.html#22868" class="Bound">m</a><a id="22869" class="Symbol">)</a> <a id="22871" class="Symbol">(</a><a id="22872" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="22876" href="plfa.Relations.html#22876" class="Bound">n</a><a id="22877" class="Symbol">)</a> <a id="22879" class="Keyword">with</a> <a id="22884" href="plfa.Relations.html#22703" class="Function">≤-total″</a> <a id="22893" href="plfa.Relations.html#22868" class="Bound">m</a> <a id="22895" href="plfa.Relations.html#22876" class="Bound">n</a>
<a id="22897" class="Symbol">...</a>                        <a id="22924" class="Symbol">|</a> <a id="22926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17160" class="InductiveConstructor">forward</a> <a id="22934" href="plfa.Relations.html#22934" class="Bound">m≤n</a>   <a id="22940" class="Symbol">=</a>  <a id="22943" href="plfa.Relations.html#17160" class="InductiveConstructor">forward</a> <a id="22951" class="Symbol">(</a><a id="22952" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="22956" href="plfa.Relations.html#22934" class="Bound">m≤n</a><a id="22959" class="Symbol">)</a>
<a id="22961" class="Symbol">...</a>                        <a id="22988" class="Symbol">|</a> <a id="22990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17217" class="InductiveConstructor">flipped</a> <a id="22998" href="plfa.Relations.html#22998" class="Bound">n≤m</a>   <a id="23004" class="Symbol">=</a>  <a id="23007" href="plfa.Relations.html#17217" class="InductiveConstructor">flipped</a> <a id="23015" class="Symbol">(</a><a id="23016" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="23020" href="plfa.Relations.html#22998" class="Bound">n≤m</a><a id="23023" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
It differs from the original code in that it pattern
matches on the second argument before the first argument.
{:/}

两者的区别在于上述代码在对于第一个参数进行模式匹配之前先对于第二个参数先进行模式匹配。


{::comment}
## Monotonicity
{:/}

## 单调性

{::comment}
If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:
{:/}

如果在聚会中碰到了一个运算符和一个序，那么有人可能会问这个运算符对于这个序是不是
**单调的（Monotonic）**。比如说，加法对于小于等于是单调的，这意味着：

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

{::comment}
The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
{:/}

这个证明可以用我们学会的方法，很直接的来完成。我们最好把它分成三个部分，首先我们证明加法对于
小于等于在右手边是单调的：

{% raw %}<pre class="Agda"><a id="+-monoʳ-≤"></a><a id="23881" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23881" class="Function">+-monoʳ-≤</a> <a id="23891" class="Symbol">:</a> <a id="23893" class="Symbol">∀</a> <a id="23895" class="Symbol">(</a><a id="23896" href="plfa.Relations.html#23896" class="Bound">n</a> <a id="23898" href="plfa.Relations.html#23898" class="Bound">p</a> <a id="23900" href="plfa.Relations.html#23900" class="Bound">q</a> <a id="23902" class="Symbol">:</a> <a id="23904" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="23905" class="Symbol">)</a>
  <a id="23909" class="Symbol">→</a> <a id="23911" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23898" class="Bound">p</a> <a id="23913" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="23915" href="plfa.Relations.html#23900" class="Bound">q</a>
    <a id="23921" class="Comment">-------------</a>
  <a id="23937" class="Symbol">→</a> <a id="23939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23896" class="Bound">n</a> <a id="23941" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23943" href="plfa.Relations.html#23898" class="Bound">p</a> <a id="23945" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="23947" href="plfa.Relations.html#23896" class="Bound">n</a> <a id="23949" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="23951" href="plfa.Relations.html#23900" class="Bound">q</a>
<a id="23953" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23881" class="Function">+-monoʳ-≤</a> <a id="23963" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>    <a id="23971" href="plfa.Relations.html#23971" class="Bound">p</a> <a id="23973" href="plfa.Relations.html#23973" class="Bound">q</a> <a id="23975" href="plfa.Relations.html#23975" class="Bound">p≤q</a>  <a id="23980" class="Symbol">=</a>  <a id="23983" href="plfa.Relations.html#23975" class="Bound">p≤q</a>
<a id="23987" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#23881" class="Function">+-monoʳ-≤</a> <a id="23997" class="Symbol">(</a><a id="23998" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="24002" href="plfa.Relations.html#24002" class="Bound">n</a><a id="24003" class="Symbol">)</a> <a id="24005" href="plfa.Relations.html#24005" class="Bound">p</a> <a id="24007" href="plfa.Relations.html#24007" class="Bound">q</a> <a id="24009" href="plfa.Relations.html#24009" class="Bound">p≤q</a>  <a id="24014" class="Symbol">=</a>  <a id="24017" href="plfa.Relations.html#1537" class="InductiveConstructor">s≤s</a> <a id="24021" class="Symbol">(</a><a id="24022" href="plfa.Relations.html#23881" class="Function">+-monoʳ-≤</a> <a id="24032" href="plfa.Relations.html#24002" class="Bound">n</a> <a id="24034" href="plfa.Relations.html#24005" class="Bound">p</a> <a id="24036" href="plfa.Relations.html#24007" class="Bound">q</a> <a id="24038" href="plfa.Relations.html#24009" class="Bound">p≤q</a><a id="24041" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.
{:/}

我们对于第一个参数进行归纳。

* **起始步骤**：第一个参数是 `zero`，那么 `zero + p ≤ zero + q` 可以化简为 `p ≤ q`，
  其证明由 `p≤q` 给出。

* **归纳步骤**：第一个参数是 `suc n`，那么 `suc n + p ≤ suc n + q` 可以化简为
  `suc (n + p) ≤ suc (n + q)`。归纳假设 `+-monoʳ-≤ n p q p≤q` 可以证明
  `n + p ≤ n + q`，我们在此之上使用 `s≤s` 即可得证。

{::comment}
Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
{:/}

接下来，我们证明加法对于小于等于在左手边是单调的。我们可以用之前的结论和加法的交换律来证明：

{% raw %}<pre class="Agda"><a id="+-monoˡ-≤"></a><a id="25025" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25025" class="Function">+-monoˡ-≤</a> <a id="25035" class="Symbol">:</a> <a id="25037" class="Symbol">∀</a> <a id="25039" class="Symbol">(</a><a id="25040" href="plfa.Relations.html#25040" class="Bound">m</a> <a id="25042" href="plfa.Relations.html#25042" class="Bound">n</a> <a id="25044" href="plfa.Relations.html#25044" class="Bound">p</a> <a id="25046" class="Symbol">:</a> <a id="25048" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="25049" class="Symbol">)</a>
  <a id="25053" class="Symbol">→</a> <a id="25055" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25040" class="Bound">m</a> <a id="25057" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25059" href="plfa.Relations.html#25042" class="Bound">n</a>
    <a id="25065" class="Comment">-------------</a>
  <a id="25081" class="Symbol">→</a> <a id="25083" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25040" class="Bound">m</a> <a id="25085" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25087" href="plfa.Relations.html#25044" class="Bound">p</a> <a id="25089" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25091" href="plfa.Relations.html#25042" class="Bound">n</a> <a id="25093" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25095" href="plfa.Relations.html#25044" class="Bound">p</a>
<a id="25097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25025" class="Function">+-monoˡ-≤</a> <a id="25107" href="plfa.Relations.html#25107" class="Bound">m</a> <a id="25109" href="plfa.Relations.html#25109" class="Bound">n</a> <a id="25111" href="plfa.Relations.html#25111" class="Bound">p</a> <a id="25113" href="plfa.Relations.html#25113" class="Bound">m≤n</a>  <a id="25118" class="Keyword">rewrite</a> <a id="25126" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="25133" href="plfa.Relations.html#25107" class="Bound">m</a> <a id="25135" href="plfa.Relations.html#25111" class="Bound">p</a> <a id="25137" class="Symbol">|</a> <a id="25139" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#11911" class="Function">+-comm</a> <a id="25146" href="plfa.Relations.html#25109" class="Bound">n</a> <a id="25148" href="plfa.Relations.html#25111" class="Bound">p</a>  <a id="25151" class="Symbol">=</a> <a id="25153" href="plfa.Relations.html#23881" class="Function">+-monoʳ-≤</a> <a id="25163" href="plfa.Relations.html#25111" class="Bound">p</a> <a id="25165" href="plfa.Relations.html#25107" class="Bound">m</a> <a id="25167" href="plfa.Relations.html#25109" class="Bound">n</a> <a id="25169" href="plfa.Relations.html#25113" class="Bound">m≤n</a>
</pre>{% endraw %}
{::comment}
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.
{:/}

用 `+-comm m p` 和 `+-comm n p` 来重写，可以让 `m + p ≤ n + p` 转换成 `p + n ≤ p + m`，
而我们可以用 `+-moroʳ-≤ p m n m≤n` 来证明。

{::comment}
Third, we combine the two previous results:
{:/}

最后，我们把前两步的结论结合起来：

{% raw %}<pre class="Agda"><a id="+-mono-≤"></a><a id="25532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25532" class="Function">+-mono-≤</a> <a id="25541" class="Symbol">:</a> <a id="25543" class="Symbol">∀</a> <a id="25545" class="Symbol">(</a><a id="25546" href="plfa.Relations.html#25546" class="Bound">m</a> <a id="25548" href="plfa.Relations.html#25548" class="Bound">n</a> <a id="25550" href="plfa.Relations.html#25550" class="Bound">p</a> <a id="25552" href="plfa.Relations.html#25552" class="Bound">q</a> <a id="25554" class="Symbol">:</a> <a id="25556" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="25557" class="Symbol">)</a>
  <a id="25561" class="Symbol">→</a> <a id="25563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25546" class="Bound">m</a> <a id="25565" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25567" href="plfa.Relations.html#25548" class="Bound">n</a>
  <a id="25571" class="Symbol">→</a> <a id="25573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25550" class="Bound">p</a> <a id="25575" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25577" href="plfa.Relations.html#25552" class="Bound">q</a>
    <a id="25583" class="Comment">-------------</a>
  <a id="25599" class="Symbol">→</a> <a id="25601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25546" class="Bound">m</a> <a id="25603" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25605" href="plfa.Relations.html#25550" class="Bound">p</a> <a id="25607" href="plfa.Relations.html#1461" class="Datatype Operator">≤</a> <a id="25609" href="plfa.Relations.html#25548" class="Bound">n</a> <a id="25611" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="25613" href="plfa.Relations.html#25552" class="Bound">q</a>
<a id="25615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#25532" class="Function">+-mono-≤</a> <a id="25624" href="plfa.Relations.html#25624" class="Bound">m</a> <a id="25626" href="plfa.Relations.html#25626" class="Bound">n</a> <a id="25628" href="plfa.Relations.html#25628" class="Bound">p</a> <a id="25630" href="plfa.Relations.html#25630" class="Bound">q</a> <a id="25632" href="plfa.Relations.html#25632" class="Bound">m≤n</a> <a id="25636" href="plfa.Relations.html#25636" class="Bound">p≤q</a>  <a id="25641" class="Symbol">=</a>  <a id="25644" href="plfa.Relations.html#12218" class="Function">≤-trans</a> <a id="25652" class="Symbol">(</a><a id="25653" href="plfa.Relations.html#25025" class="Function">+-monoˡ-≤</a> <a id="25663" href="plfa.Relations.html#25624" class="Bound">m</a> <a id="25665" href="plfa.Relations.html#25626" class="Bound">n</a> <a id="25667" href="plfa.Relations.html#25628" class="Bound">p</a> <a id="25669" href="plfa.Relations.html#25632" class="Bound">m≤n</a><a id="25672" class="Symbol">)</a> <a id="25674" class="Symbol">(</a><a id="25675" href="plfa.Relations.html#23881" class="Function">+-monoʳ-≤</a> <a id="25685" href="plfa.Relations.html#25626" class="Bound">n</a> <a id="25687" href="plfa.Relations.html#25628" class="Bound">p</a> <a id="25689" href="plfa.Relations.html#25630" class="Bound">q</a> <a id="25691" href="plfa.Relations.html#25636" class="Bound">p≤q</a><a id="25694" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.
{:/}

使用 `+-monoˡ-≤ m n p m≤n` 可以证明 `m + p ≤ n + p`，
使用 `+-monoʳ-≤ n p q p≤q` 可以证明 `n + p ≤ n + q`，用传递性把两者连接起来，
我们可以获得 `m + p ≤ n + q` 的证明，如上所示。

{::comment}
#### Exercise `*-mono-≤` (stretch)
{:/}

#### 练习 `*-mono-≤` （延伸）

{::comment}
Show that multiplication is monotonic with regard to inequality.
{:/}

证明乘法对于小于等于是单调的。

{::comment}
{% raw %}<pre class="Agda"><a id="26248" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="26285" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Strict inequality {#strict-inequality}
{:/}

## 严格不等关系 {#strict-inequality}

{::comment}
We can define strict inequality similarly to inequality:
{:/}

我们可以用类似于定义不等关系的方法来定义严格不等关系。

{% raw %}<pre class="Agda"><a id="26504" class="Keyword">infix</a> <a id="26510" class="Number">4</a> <a id="26512" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26522" class="Datatype Operator">_&lt;_</a>

<a id="26517" class="Keyword">data</a> <a id="_&lt;_"></a><a id="26522" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26522" class="Datatype Operator">_&lt;_</a> <a id="26526" class="Symbol">:</a> <a id="26528" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="26530" class="Symbol">→</a> <a id="26532" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="26534" class="Symbol">→</a> <a id="26536" class="PrimitiveType">Set</a> <a id="26540" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="26549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26549" class="InductiveConstructor">z&lt;s</a> <a id="26553" class="Symbol">:</a> <a id="26555" class="Symbol">∀</a> <a id="26557" class="Symbol">{</a><a id="26558" href="plfa.Relations.html#26558" class="Bound">n</a> <a id="26560" class="Symbol">:</a> <a id="26562" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="26563" class="Symbol">}</a>
      <a id="26571" class="Comment">------------</a>
    <a id="26588" class="Symbol">→</a> <a id="26590" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a> <a id="26595" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26522" class="Datatype Operator">&lt;</a> <a id="26597" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="26601" href="plfa.Relations.html#26558" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="26606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26606" class="InductiveConstructor">s&lt;s</a> <a id="26610" class="Symbol">:</a> <a id="26612" class="Symbol">∀</a> <a id="26614" class="Symbol">{</a><a id="26615" href="plfa.Relations.html#26615" class="Bound">m</a> <a id="26617" href="plfa.Relations.html#26617" class="Bound">n</a> <a id="26619" class="Symbol">:</a> <a id="26621" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="26622" class="Symbol">}</a>
    <a id="26628" class="Symbol">→</a> <a id="26630" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26615" class="Bound">m</a> <a id="26632" href="plfa.Relations.html#26522" class="Datatype Operator">&lt;</a> <a id="26634" href="plfa.Relations.html#26617" class="Bound">n</a>
      <a id="26642" class="Comment">-------------</a>
    <a id="26660" class="Symbol">→</a> <a id="26662" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="26666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#26615" class="Bound">m</a> <a id="26668" href="plfa.Relations.html#26522" class="Datatype Operator">&lt;</a> <a id="26670" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="26674" href="plfa.Relations.html#26617" class="Bound">n</a>
</pre>{% endraw %}
{::comment}
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.
{:/}

严格不等关系与不等关系最重要的区别在于，0 小于任何数的后继，而不小于 0。

{::comment}
Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.
{:/}

显然，严格不等关系不是自反的，而是**非自反的（Irreflexive）**，表示 `n < n` 对于
任何值 `n` 都不成立。和不等关系一样，严格不等关系是传递的。严格不等关系不是完全的，但是满足
一个相似的性质：*三分律*（Trichotomy）：对于任意的 `m` 和 `n`，`m < n`、`m ≡ n` 或者
`m > n` 三者有且仅有一者成立。（我们定义 `m > n` 当且仅当 `n < m` 成立时成立）
严格不等关系对于加法和乘法也是单调的。

{::comment}
Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}/Negation/).
{:/}

我们把一部分上述性质作为习题。非自反性需要逻辑非，三分律需要证明三者是互斥的，因此这两个性质
暂不做为习题。我们会在 [Negation]({{ site.baseurl }}/Negation/) 章节来重新讨论。

{::comment}
It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.
{:/}

我们可以直接地来证明 `suc m ≤ n` 蕴涵了 `m < n`，及其逆命题。
因此我们亦可从不等关系的性质中，使用此性质来证明严格不等关系的性质。


{::comment}
#### Exercise `<-trans` (recommended) {#less-trans}
{:/}

#### 练习 `<-trans` （推荐） {#less-trans}

{::comment}
Show that strict inequality is transitive.
{:/}

证明严格不等是传递的。

{::comment}
{% raw %}<pre class="Agda"><a id="28475" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="28512" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `trichotomy` {#trichotomy}
{:/}

#### 练习 `trichotomy` {#trichotomy}

{::comment}
Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.
{:/}

证明严格不等关系满足弱化的三元律，证明对于任意 `m` 和 `n`，下列命题有一条成立：

  * `m < n`，
  * `m ≡ n`，或者
  * `m > n`。

{::comment}
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}/Negation/).)
{:/}

定义 `m > n` 为 `n < m`。你需要一个合适的数据类型声明，如同我们在证明完全性中使用的那样。
（我们会在介绍完[否定]({{ site.baseurl }}/Negation/)之后证明三者是互斥的。）

{::comment}
{% raw %}<pre class="Agda"><a id="29288" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="29325" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `+-mono-<` {#plus-mono-less}
{:/}

#### 练习 `+-mono-<` {#plus-mono-less}

{::comment}
Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.
{:/}

证明加法对于严格不等关系是单调的。正如不等关系中那样，你可以需要额外的定义。

{::comment}
{% raw %}<pre class="Agda"><a id="29649" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="29686" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}
{:/}

#### 练习 `≤-iff-<` (推荐) {#leq-iff-less}

{::comment}
Show that `suc m ≤ n` implies `m < n`, and conversely.
{:/}

证明 `suc m ≤ n` 蕴涵了 `m < n`，及其逆命题。

{::comment}
{% raw %}<pre class="Agda"><a id="29941" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="29978" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `<-trans-revisited` {#less-trans-revisited}
{:/}

#### 练习 `<-trans-revisited` {#less-trans-revisited}

{::comment}
Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.
{:/}

用另外一种方法证明严格不等是传递的，使用之前证明的不等关系和严格不等关系的联系，
以及不等关系的传递性。

{::comment}
{% raw %}<pre class="Agda"><a id="30382" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="30419" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Even and odd
{:/}

## 奇和偶

{::comment}
As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
{:/}

作为一个额外的例子，我们来定义奇数和偶数。不等关系和严格不等关系是**二元关系**，而奇偶性
是**一元关系**，有时也被叫做**谓词（Predicate）**：

{% raw %}<pre class="Agda"><a id="30774" class="Keyword">data</a> <a id="even"></a><a id="30779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="30784" class="Symbol">:</a> <a id="30786" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="30788" class="Symbol">→</a> <a id="30790" class="PrimitiveType">Set</a>
<a id="30794" class="Keyword">data</a> <a id="odd"></a><a id="30799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30799" class="Datatype">odd</a>  <a id="30804" class="Symbol">:</a> <a id="30806" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a> <a id="30808" class="Symbol">→</a> <a id="30810" class="PrimitiveType">Set</a>

<a id="30815" class="Keyword">data</a> <a id="30820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="30825" class="Keyword">where</a>

  <a id="even.zero"></a><a id="30834" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30834" class="InductiveConstructor">zero</a> <a id="30839" class="Symbol">:</a>
      <a id="30847" class="Comment">---------</a>
      <a id="30863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="30868" href="Agda.Builtin.Nat.html#183" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="30876" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30876" class="InductiveConstructor">suc</a>  <a id="30881" class="Symbol">:</a> <a id="30883" class="Symbol">∀</a> <a id="30885" class="Symbol">{</a><a id="30886" href="plfa.Relations.html#30886" class="Bound">n</a> <a id="30888" class="Symbol">:</a> <a id="30890" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="30891" class="Symbol">}</a>
    <a id="30897" class="Symbol">→</a> <a id="30899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30799" class="Datatype">odd</a> <a id="30903" href="plfa.Relations.html#30886" class="Bound">n</a>
      <a id="30911" class="Comment">------------</a>
    <a id="30928" class="Symbol">→</a> <a id="30930" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="30935" class="Symbol">(</a><a id="30936" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="30940" href="plfa.Relations.html#30886" class="Bound">n</a><a id="30941" class="Symbol">)</a>

<a id="30944" class="Keyword">data</a> <a id="30949" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30799" class="Datatype">odd</a> <a id="30953" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="30962" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30962" class="InductiveConstructor">suc</a>   <a id="30968" class="Symbol">:</a> <a id="30970" class="Symbol">∀</a> <a id="30972" class="Symbol">{</a><a id="30973" href="plfa.Relations.html#30973" class="Bound">n</a> <a id="30975" class="Symbol">:</a> <a id="30977" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="30978" class="Symbol">}</a>
    <a id="30984" class="Symbol">→</a> <a id="30986" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="30991" href="plfa.Relations.html#30973" class="Bound">n</a>
      <a id="30999" class="Comment">-----------</a>
    <a id="31015" class="Symbol">→</a> <a id="31017" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30799" class="Datatype">odd</a> <a id="31021" class="Symbol">(</a><a id="31022" href="Agda.Builtin.Nat.html#196" class="InductiveConstructor">suc</a> <a id="31026" href="plfa.Relations.html#30973" class="Bound">n</a><a id="31027" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.
{:/}

一个数是偶数，如果它是 0，或者是奇数的后继。一个数是奇数，如果它是偶数的后继。

{::comment}
This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).
{:/}

这是我们第一次定义一个相互递归的数据类型。因为每个标识符必须在使用前声明，所以
我们首先声明索引数据类型 `even` 和 `odd` （省略 `where` 关键字和其构造子的定义），
然后声明其构造子（省略其签名 `ℕ → Set`，因为在之前已经给出）。

{::comment}
This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:
{:/}

这也是我们第一次使用 **重载（Overloaded）**的构造子。这意味着不同类型的构造子
拥有相同的名字。在这里 `suc` 表示下面三种构造子其中之一：

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

{::comment}
Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.
{:/}

同理，`zero` 表示两种构造子的一种。因为类型推导的限制，Agda 不允许重载已定义的名字，
但是允许重载构造子。我们推荐将重载限制在有关联的定义中，如我们所做的这样，但这不是必须的。

{::comment}
We show that the sum of two even numbers is even:
{:/}

我们证明两个偶数之和是偶数：

{% raw %}<pre class="Agda"><a id="e+e≡e"></a><a id="32641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32641" class="Function">e+e≡e</a> <a id="32647" class="Symbol">:</a> <a id="32649" class="Symbol">∀</a> <a id="32651" class="Symbol">{</a><a id="32652" href="plfa.Relations.html#32652" class="Bound">m</a> <a id="32654" href="plfa.Relations.html#32654" class="Bound">n</a> <a id="32656" class="Symbol">:</a> <a id="32658" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="32659" class="Symbol">}</a>
  <a id="32663" class="Symbol">→</a> <a id="32665" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="32670" href="plfa.Relations.html#32652" class="Bound">m</a>
  <a id="32674" class="Symbol">→</a> <a id="32676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="32681" href="plfa.Relations.html#32654" class="Bound">n</a>
    <a id="32687" class="Comment">------------</a>
  <a id="32702" class="Symbol">→</a> <a id="32704" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="32709" class="Symbol">(</a><a id="32710" href="plfa.Relations.html#32652" class="Bound">m</a> <a id="32712" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32714" href="plfa.Relations.html#32654" class="Bound">n</a><a id="32715" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="32718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32718" class="Function">o+e≡o</a> <a id="32724" class="Symbol">:</a> <a id="32726" class="Symbol">∀</a> <a id="32728" class="Symbol">{</a><a id="32729" href="plfa.Relations.html#32729" class="Bound">m</a> <a id="32731" href="plfa.Relations.html#32731" class="Bound">n</a> <a id="32733" class="Symbol">:</a> <a id="32735" href="Agda.Builtin.Nat.html#165" class="Datatype">ℕ</a><a id="32736" class="Symbol">}</a>
  <a id="32740" class="Symbol">→</a> <a id="32742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30799" class="Datatype">odd</a> <a id="32746" href="plfa.Relations.html#32729" class="Bound">m</a>
  <a id="32750" class="Symbol">→</a> <a id="32752" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30779" class="Datatype">even</a> <a id="32757" href="plfa.Relations.html#32731" class="Bound">n</a>
    <a id="32763" class="Comment">-----------</a>
  <a id="32777" class="Symbol">→</a> <a id="32779" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#30799" class="Datatype">odd</a> <a id="32783" class="Symbol">(</a><a id="32784" href="plfa.Relations.html#32729" class="Bound">m</a> <a id="32786" href="Agda.Builtin.Nat.html#298" class="Primitive Operator">+</a> <a id="32788" href="plfa.Relations.html#32731" class="Bound">n</a><a id="32789" class="Symbol">)</a>

<a id="32792" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32641" class="Function">e+e≡e</a> <a id="32798" href="plfa.Relations.html#30834" class="InductiveConstructor">zero</a>     <a id="32807" href="plfa.Relations.html#32807" class="Bound">en</a>  <a id="32811" class="Symbol">=</a>  <a id="32814" href="plfa.Relations.html#32807" class="Bound">en</a>
<a id="32817" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32641" class="Function">e+e≡e</a> <a id="32823" class="Symbol">(</a><a id="32824" href="plfa.Relations.html#30876" class="InductiveConstructor">suc</a> <a id="32828" href="plfa.Relations.html#32828" class="Bound">om</a><a id="32830" class="Symbol">)</a> <a id="32832" href="plfa.Relations.html#32832" class="Bound">en</a>  <a id="32836" class="Symbol">=</a>  <a id="32839" href="plfa.Relations.html#30876" class="InductiveConstructor">suc</a> <a id="32843" class="Symbol">(</a><a id="32844" href="plfa.Relations.html#32718" class="Function">o+e≡o</a> <a id="32850" href="plfa.Relations.html#32828" class="Bound">om</a> <a id="32853" href="plfa.Relations.html#32832" class="Bound">en</a><a id="32855" class="Symbol">)</a>

<a id="32858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#32718" class="Function">o+e≡o</a> <a id="32864" class="Symbol">(</a><a id="32865" href="plfa.Relations.html#30962" class="InductiveConstructor">suc</a> <a id="32869" href="plfa.Relations.html#32869" class="Bound">em</a><a id="32871" class="Symbol">)</a> <a id="32873" href="plfa.Relations.html#32873" class="Bound">en</a>  <a id="32877" class="Symbol">=</a>  <a id="32880" href="plfa.Relations.html#30962" class="InductiveConstructor">suc</a> <a id="32884" class="Symbol">(</a><a id="32885" href="plfa.Relations.html#32641" class="Function">e+e≡e</a> <a id="32891" href="plfa.Relations.html#32869" class="Bound">em</a> <a id="32894" href="plfa.Relations.html#32873" class="Bound">en</a><a id="32896" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.
{:/}

与相互递归的定义对应，我们用两个相互递归的函数，一个证明两个偶数之和是偶数，另一个证明
一个奇数与一个偶数之和是奇数。

{::comment}
This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.
{:/}

这是我们第一次使用相互递归的函数。因为每个标识符必须在使用前声明，我们先给出两个函数的签名，
然后再给出其定义。

{::comment}
To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.
{:/}

要证明两个偶数之和为偶，我们考虑第一个数为偶数的证明。如果是因为第一个数为 0，
那么第二个数为偶数的证明即为和为偶数的证明。如果是因为第一个数为奇数的后继，
那么和为偶数是因为他是一个奇数和一个偶数的和的后续，而这个和是一个奇数。


{::comment}
To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.
{:/}

要证明一个奇数和一个偶数的和是奇数，我们考虑第一个数是奇数的证明。
如果是因为它是一个偶数的后继，那么和为奇数，因为它是两个偶数之和的后继，
而这个和是一个偶数。


{::comment}
#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}
{:/}

#### 练习 `o+o≡e` (延伸) {#odd-plus-odd}

{::comment}
Show that the sum of two odd numbers is even.
{:/}

证明两个奇数之和为偶数。

{::comment}
{% raw %}<pre class="Agda"><a id="34523" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="34560" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}
{:/}

#### 练习 `Bin-predicates` (延伸) {#Bin-predicates}

{::comment}
Recall that
Exercise [Bin]({{ site.baseurl }}/Naturals/#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:
{:/}

回忆我们在练习 [Bin][plfa.Naturals#Bin] 中定义了一个数据类型 `Bin` 来用二进制字符串表示自然数。
这个表达方法不是唯一的，因为我们在开头加任意个 0。因此，11 可以由以下方法表示：

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

{::comment}
Define a predicate
{:/}

定义一个谓词

    Can : Bin → Set

{::comment}
over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate
{:/}

其在一个二进制字符串的表示是标准的（Canonical）时成立，表示它没有开头的 0。在两个 11 的表达方式中，
第一个是标准的，而第二个不是。在定义这个谓词时，你需要一个辅助谓词：

    One : Bin → Set

{::comment}
that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).
{:/}

其仅在一个二进制字符串开头为 1 时成立。一个二进制字符串是标准的，如果它开头是 1 （表示一个正数），
或者它仅是一个 0 （表示 0）。

{::comment}
Show that increment preserves canonical bitstrings:
{:/}

证明递增可以保持标准性。

    Can x
    ------------
    Can (inc x)

{::comment}
Show that converting a natural to a bitstring always yields a
canonical bitstring:
{:/}

证明从自然数转换成的二进制字符串是标准的。

    ----------
    Can (to n)

{::comment}
Show that converting a canonical bitstring to a natural
and back is the identity:
{:/}

证明将一个标准的二进制字符串转换成自然数之后，再转换回二进制字符串与原二进制字符串相同。

    Can x
    ---------------
    to (from x) ≡ x

{::comment}
(Hint: For each of these, you may first need to prove related
properties of `One`.)
{:/}

（提示：对于每一条习题，先从 `One` 的性质开始）

{::comment}
{% raw %}<pre class="Agda"><a id="36452" class="Comment">-- Your code goes here</a>
</pre>{% endraw %}{:/}

{% raw %}<pre class="Agda"><a id="36489" class="Comment">-- 请将代码写在此处。</a>
</pre>{% endraw %}

{::comment}
## Standard library
{:/}

## 标准库

{::comment}
Definitions similar to those in this chapter can be found in the standard library:
{:/}

标准库中有类似于本章介绍的定义：

{% raw %}<pre class="Agda"><a id="36677" class="Keyword">import</a> <a id="36684" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.html" class="Module">Data.Nat</a> <a id="36693" class="Keyword">using</a> <a id="36699" class="Symbol">(</a><a id="36700" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#895" class="Datatype Operator">_≤_</a><a id="36703" class="Symbol">;</a> <a id="36705" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#918" class="InductiveConstructor">z≤n</a><a id="36708" class="Symbol">;</a> <a id="36710" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Base.html#960" class="InductiveConstructor">s≤s</a><a id="36713" class="Symbol">)</a>
<a id="36715" class="Keyword">import</a> <a id="36722" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="36742" class="Keyword">using</a> <a id="36748" class="Symbol">(</a><a id="36749" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3632" class="Function">≤-refl</a><a id="36755" class="Symbol">;</a> <a id="36757" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3815" class="Function">≤-trans</a><a id="36764" class="Symbol">;</a> <a id="36766" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3682" class="Function">≤-antisym</a><a id="36775" class="Symbol">;</a> <a id="36777" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#3927" class="Function">≤-total</a><a id="36784" class="Symbol">;</a>
                                  <a id="36820" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15619" class="Function">+-monoʳ-≤</a><a id="36829" class="Symbol">;</a> <a id="36831" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15529" class="Function">+-monoˡ-≤</a><a id="36840" class="Symbol">;</a> <a id="36842" href="https://agda.github.io/agda-stdlib/v1.1/Data.Nat.Properties.html#15373" class="Function">+-mono-≤</a><a id="36850" class="Symbol">)</a>
</pre>{% endraw %}
{::comment}
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}/Connectives/)),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.
{:/}

在标准库中，`≤-total` 是使用析取定义的（我们将在 [Connectives][plfa.Connectives] 章节定义）。
`+-monoʳ-≤`、`+-monoˡ-≤` 和 `+-mono-≤` 的证明方法和本书不同。
更多的参数是隐式申明的。


## Unicode

{::comment}
This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)
{:/}

本章使用了如下 Unicode 符号：

    ≤  U+2264  小于等于 (\<=, \le)
    ≥  U+2265  大于等于 (\>=, \ge)
    ˡ  U+02E1  小写字母 L 标识符 (\^l)
    ʳ  U+02B3  小写字母 R 标识符 (\^r)

{::comment}
The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
{:/}

`\^l` 和 `\^r` 命令给出了左右箭头，以及上标字母 `l` 和 `r`。
