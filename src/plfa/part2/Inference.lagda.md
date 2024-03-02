---
title      : "Inference: 双向类型推理"
permalink  : /Inference/
translators: ["Fangyi Zhou"]
progress   : 100
---

```agda
module plfa.part2.Inference where
```

<!--
So far in our development, type derivations for the corresponding
term have been provided by fiat.
In Chapter [Lambda](/Lambda/)
type derivations are extrinsic to the term, while
in Chapter [DeBruijn](/DeBruijn/)
type derivations are intrinsic to the term,
but in both we have written out the type derivations in full.
-->

在本书至此的进展中，项的类型推导是如法令一般直接给出的。
在 [Lambda](/Lambda/) 章节，类型推导以外在于项的形式给出，
而在 [DeBruijn](/DeBruijn/) 章节，类型推导以内在于项的形式给出，
但在两者均要求我们将类型推导完全写出。

<!--
In practice, one often writes down a term with a few decorations and
applies an algorithm to _infer_ the corresponding type derivation.
Indeed, this is exactly what happens in Agda: we specify the types for
top-level function declarations, and type information for everything
else is inferred from what has been given.  The style of inference
Agda uses is based on a technique called _bidirectional_ type
inference, which will be presented in this chapter.
-->

在实践中，我们一般可以给项加上一些装饰，然后运用算法来**推理**（Infer）出类型推导。
的确，Agda 中也是这样：我们给顶层的函数声明指定类型，而其余可由给出的信息推理而来。
Agda 使用的这种推理被称为**双向**（Bidirectional）类型推理，我们将在本章中进行展示。

<!--
This chapter ties our previous developments together. We begin with
a term with some type annotations, close to the raw terms of
Chapter [Lambda](/Lambda/),
and from it we compute an intrinsically-typed term, in the style of
Chapter [DeBruijn](/DeBruijn/).
-->

本章中，我们讲之前的进展结合在一起。
我们首先由带有类型注释的项开始，其与 [Lambda](/Lambda/) 章节中的源项相似，
从此我们计算出内在类型的项，如同 [DeBruijn](/DeBruijn) 章节中那样。

<!--
## Introduction: Inference rules as algorithms {#algorithms}
-->

## 绪论：推理规则作为算法 {#algorithms}

<!--
In the calculus we have considered so far, a term may have more than
one type.  For example,
-->

在我们至此使用的演算中，一个项可以有多于一个类型。例如，

    (ƛ x ⇒ x) ⦂ (A ⇒ A)

<!--
holds for _every_ type `A`.  We start by considering a small language for
lambda terms where every term has a unique type.  All we need do
is decorate each abstraction term with the type of its argument.
This gives us the grammar:
-->

对于**任意**类型 `A` 成立。
我们首先考虑一个带有 λ 项的小语言，其每一项有其唯一的类型。
我们只需要给抽象加上参数的类型。
这样我们可以得到如下的语法：

<!--
    L, M, N ::=                         decorated terms
      x                                   variable
      ƛ x ⦂ A ⇒ N                         abstraction (decorated)
      L · M                               application
-->

    L, M, N ::=                         带装饰的项
      x                                   变量
      ƛ x ⦂ A ⇒ N                         抽象（装饰后）
      L · M                               应用

<!--
Each of the associated type rules can be read as an algorithm for
type checking.  For each typing judgment, we label each position
as either an _input_ or an _output_.
-->

每一条相关的赋型规则可以被读作类型检查的算法。
对于每一条赋型规则，我们将每个位置标记如**输入**（Input）或者**输出**（Output）。

<!--
For the judgment
-->

对于下面的判断

    Γ ∋ x ⦂ A

<!--
we take the context `Γ` and the variable `x` as inputs, and the
type `A` as output.  Consider the rules:
-->

我们将语境 `Γ` 和变量 `x` 作为输入，类型 `A` 作为输出。
考虑下面的规则：

    ----------------- Z
    Γ , x ⦂ A ∋ x ⦂ A

    Γ ∋ x ⦂ A
    ----------------- S
    Γ , y ⦂ B ∋ x ⦂ A

<!--
From the inputs we can determine which rule applies: if the last
variable in the context matches the given variable then the first
rule applies, else the second.  (For de Bruijn indices, it is even
easier: zero matches the first rule and successor the second.)
For the first rule, the output type can be read off as the last
type in the input context. For the second rule, the inputs of the
conclusion determine the inputs of the hypothesis, and the output
of the hypothesis determines the output of the conclusion.
-->

从输入中，我们可以决定应用哪一条规则：
如果语境中最后一个变量与给定的变量一致，那么应用第一条规则，否则应用第二条。
（对于 de Bruijn 因子来说，这更加简单：零对应第一条，后继对应第二条。）
对于第一条，输出类型可以直接从语境中得到。
对于第二条，结论中的输入可以作为假设的输入，而假设的输出决定了结论的输出。

<!--
For the judgment
-->

对于下面的判断：

    Γ ⊢ M ⦂ A

<!--
we take the context `Γ` and term `M` as inputs, and the type `A`
as output. Consider the rules:
-->

我们将语境 `Γ` 和项 `M` 作为输入，类型 `A` 作为输出。
考虑下面的规则：

    Γ ∋ x ⦂ A
    -----------
    Γ ⊢ ` x ⦂ A

    Γ , x ⦂ A ⊢ N ⦂ B
    ---------------------------
    Γ ⊢ (ƛ x ⦂ A ⇒ N) ⦂ (A ⇒ B)

    Γ ⊢ L ⦂ A ⇒ B
    Γ ⊢ M ⦂ A′
    A ≡ A′
    -------------
    Γ ⊢ L · M ⦂ B

<!--
The input term determines which rule applies: variables use the first
rule, abstractions the second, and applications the third.  We say
such rules are _syntax directed_.  For the variable rule, the inputs
of the conclusion determine the inputs of the hypothesis, and the
output of the hypothesis determines the output of the conclusion.
Same for the abstraction rule — the bound variable and argument are
carried from the term of the conclusion into the context of the
hypothesis; this works because we added the argument type to the
abstraction.  For the application rule, we add a third hypothesis to
check whether the domain of the function matches the type of the
argument; this judgment is decidable when both types are given as
inputs. The inputs of the conclusion determine the inputs of the first
two hypotheses, the outputs of the first two hypotheses determine the
inputs of the third hypothesis, and the output of the first hypothesis
determines the output of the conclusion.
-->

输入项决定了应用哪一条规则：
变量使用第一条，抽象使用第二条，应用使用第三条。
我们把这样的规则叫做**语法导向的**（Syntax directed）规则。
对于变量的规则，结论的输入决定了结论的输出。
抽象的规则也是一样——约束变量和参数从结论的输入流向假设中的语境；
这得以实现，因为我们在抽象中加入了参数的类型。
对于应用的规则，我们加入第三条假设来检查函数类型中的作用域是否与参数的类型一致；
这条判断是在两个类型已知时是可判定的。
结论的输入决定了前两个假设的输入，而前两个假设的输出决定了第三个假设的输入，而第一个假设的输出决定了结论的输出。

<!--
Converting the above to an algorithm is straightforward, as is adding
naturals and fixpoint.  We omit the details.  Instead, we consider a
detailed description of an approach that requires less obtrusive
decoration.  The idea is to break the normal typing judgment into two
judgments, one that produces the type as an output (as above), and
another that takes it as an input.
-->

我们可以直接地把上述内容转换成一个算法，加入自然数和不动点也很直接。我们省略其明细。
取而代之的是，我们考虑一种需要更少装饰的表示方法。
其核心思想是将普通的赋型判断拆分成两个判断，一个生成类型作为输出，另一个取类型作为输入。


<!--
## Synthesising and inheriting types
-->

## 生成和继承类型

<!--
In addition to the lookup judgment for variables, which will remain
as before, we now have two judgments for the type of the term:
-->

我们保留之前的变量的查询判断。除此之外，我们有两种联系类型和项的判断：

    Γ ⊢ M ↑ A
    Γ ⊢ M ↓ A

<!--
The first of these _synthesises_ the type of a term, as before,
while the second _inherits_ the type.  In the first, the context
and term are inputs and the type is an output; while in the
second, all three of the context, term, and type are inputs.
-->

第一类判断**生成**（Synthesise）项的类型，如上，而第二类**继承**（Inherit）类型。
在第一类中，语境和项作为输入，类型作为输出；
而在第二类中，语境、项和类型三者都作为输入。

<!--
Which terms use synthesis and which inheritance?  Our approach will be
that the main term in a _deconstructor_ is typed via synthesis while
_constructors_ are typed via inheritance.  For instance, the function in
an application is typed via synthesis, but an abstraction is typed via
inheritance.  The inherited type in an abstraction term serves the
same purpose as the argument type decoration of the previous section.
-->

什么项生成类型，什么项继承类型的？
我们的宗旨是**解构子**中的主项使用生成来赋型，而**构造子**使用继承。
比如，函数应用中的函数由生成来赋型，而抽象是由继承来赋型。
抽象中继承的类型和之前我们为参数额外增加的注解起到一样的作用。

<!--
Terms that deconstruct a value of a type always have a main term
(supplying an argument of the required type) and often have
side-terms.  For application, the main term supplies the function and
the side term supplies the argument.  For case terms, the main term
supplies a natural and the side terms are the two branches.  In a
deconstructor, the main term will be typed using synthesis but the
side terms will be typed using inheritance.  As we will see, this
leads naturally to an application as a whole being typed by synthesis,
while a case term as a whole will be typed by inheritance.
Variables are naturally typed by synthesis, since we can look up
the type in the input context.  Fixed points will be naturally
typed by inheritance.
-->

解构某一类型的值的项总有一个主项（提供一个所需类型的参数），且经常有副项。
对于函数应用来说，主项提供了函数，副项提供了参数。
对于分情况讨论来说，主项提供了自然数，副项则是两种情况不同的情况。
在解构子中，主项使用生成进行赋型，而副项使用继承进行赋型。
我们将看到，这自然地导致函数应用作为整体由生成进行赋型，而分情况讨论作为整体则使用继承进行赋型。
变量一般使用生成进行赋型，因为我们可以直接从语境中查询其类型。
不动点自然是用继承来赋型。

<!--
In order to get a syntax-directed type system we break terms into two
kinds, `Term⁺` and `Term⁻`, which are typed by synthesis and
inheritance, respectively.  A subterm that is typed
by synthesis may appear in a context where it is typed by inheritance,
or vice-versa, and this gives rise to two new term forms.
-->

为了达成赋型系统的语法导向性，我们将项分为两类：
`Term⁺` 和 `Term⁻`，分别用生成和继承来赋型。
由生成赋型的子项可能出现在由继承赋型的子项中，反之亦然，这给我们带来两种新形式。

<!--
For instance, we said above that the argument of an application is
typed by inheritance and that variables are typed by synthesis, giving
a mismatch if the argument of an application is a variable.  Hence, we
need a way to treat a synthesized term as if it is inherited.  We
introduce a new term form, `M ↑` for this purpose.  The typing judgment
checks that the inherited and synthesised types match.
-->

例如，我们之前提到函数应用的参数由继承赋型，而变量由生成赋型。
在参数是变量时会出现不匹配的情况。
因此，我们需要一种把生成的项当作继承的项的方法。
我们引入 `M ↑` 这种新的形式来达成此目的。
它的赋型判断即为检查其生成和继承的类型是否一致。

<!--
Similarly, we said above that the function of an application is typed
by synthesis and that abstractions are typed by inheritance, giving a
mismatch if the function of an application is an abstraction.  Hence, we
need a way to treat an inherited term as if it is synthesised.  We
introduce a new term form `M ↓ A` for this purpose.  The typing
judgment returns `A` as the synthesized type of the term as a whole,
as well as using it as the inherited type for `M`.
-->

同样，函数应用的函数部分由生成来赋型，而抽象是由继承来赋型。
在函数是抽象时会出现不匹配的情况。
因此，我们需要一种把继承的项当作生成的项的方法。
我们引入 `M ↓ A` 这种新的形式来达成此目的。
它的赋型判断返回 `A` 作为生成的类型，并把它作为 `M` 继承的类型。

<!--
The term form `M ↓ A` represents the only place terms need to be
decorated with types.  It only appears when switching from synthesis
to inheritance, that is, when a term that _deconstructs_ a value of a
type contains as its main term a term that _constructs_ a value of a
type, in other words, a place where a `β`-reduction will occur.
Typically, we will find that decorations are only required on top
level declarations.
-->

`M ↓ A` 这种形式表示了我们唯一需要用类型来装饰的项。
它只在从生成切换成继承时出现，
即当一个**解构**某一类型的值的项的主项中包含了一个**构造**某一类型的值的时候，
也就是说，这是在 `β` 规约发生的地方出现。
一般来说，我们只需要在顶层声明中需要这样的装饰。

<!--
We can extract the grammar for terms from the above:
-->

我们可以从上文中提取出项的语法：

<!--
    L⁺, M⁺, N⁺ ::=                      terms with synthesized type
      x                                   variable
      L⁺ · M⁻                             application
      M⁻ ↓ A                              switch to inherited

    L⁻, M⁻, N⁻ ::=                      terms with inherited type
      ƛ x ⇒ N⁻                            abstraction
      `zero                               zero
      `suc M⁻                             successor
      case L⁺ [zero⇒ M⁻ |suc x ⇒ N⁻ ]     case
      μ x ⇒ N⁻                            fixpoint
      M⁺ ↑                                switch to synthesized
-->

    L⁺, M⁺, N⁺ ::=                      带有生成类型的项
      x                                   变量
      L⁺ · M⁻                             应用
      M⁻ ↓ A                              切换至继承

    L⁻, M⁻, N⁻ ::=                      带有继承类型的项
      ƛ x ⇒ N⁻                            抽象
      `zero                               零
      `suc M⁻                             后继
      case L⁺ [zero⇒ M⁻ |suc x ⇒ N⁻ ]     分情况讨论
      μ x ⇒ N⁻                            不动点
      M⁺ ↑                                切换至生成

<!--
We will formalise the above shortly.
-->

我们将在下文中形式化上述定义。


<!--
## Soundness and completeness
-->

## 可靠性和完备性

<!--
What we intend to show is that the typing judgments are
_decidable_:
-->

我们试图证明赋型判断是**可判定**的：

    synthesize : ∀ (Γ : Context) (M : Term⁺)
        ------------------------------------
      → Dec (∃[ A ] Γ ⊢ M ↑ A)

    inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
              --------------------------------------
            → Dec (Γ ⊢ M ↓ A)

<!--
Given context `Γ` and synthesised term `M`, we must decide whether
there exists a type `A` such that `Γ ⊢ M ↑ A` holds, or its negation.
Similarly, given context `Γ`, inherited term `M`, and type `A`, we
must decide whether `Γ ⊢ M ↓ A` holds, or its negation.
-->

给定语境 `Γ` 和生成项 `M`，我们必须判定是否存在一个类型 `A` 使得 `Γ ⊢ M ↑ A` 成立，
或者其否定。
同样，给定语境 `Γ` 、继承项 `M` 和类型 `A`，我们必须判定 `Γ ⊢ M ↓ A` 成立，或者其否定。

<!--
Our proof is constructive. In the synthesised case, it will either
deliver a pair of a type `A` and evidence that `Γ ⊢ M ↓ A`, or a function
that given such a pair produces evidence of a contradiction. In the inherited
case, it will either deliver evidence that `Γ ⊢ M ↑ A`, or a function
that given such evidence produces evidence of a contradiction.
The positive case is referred to as _soundness_ - synthesis and inheritance
succeed only if the corresponding relation holds.  The negative case is
referred to as _completeness_ - synthesis and inheritance fail only when
they cannot possibly succeed.
-->

我们的证明是构造性的。
在生成的情况中，它要么给出一个包括类型 `A` 和 `Γ ⊢ M ↓ A` 成立的证明的有序对，或是一个将上述有序对转换成矛盾的函数。
在继承的情况中，它要么给出 `Γ ⊢ M ↑ A` 成立的证明，或是一个将上述证明转换成矛盾的函数。
成立的情况被称为**可靠性**（Soundness）——生成和继承只在对应关系成立时成功。
不成立的情况被称为**完备性**（Completeness）——生成和继承只在对应关系无法成立时失败。

<!--
Another approach might be to return a derivation if synthesis or
inheritance succeeds, and an error message otherwise - for instance,
see the section of the Agda user manual discussing
[syntactic sugar](https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html#example).
Such an approach demonstrates soundness, but not completeness.  If it
returns a derivation, we know it is correct; but there is nothing to
prevent us from writing a function that _always_ returns an error,
even when there exists a correct derivation.  Demonstrating both
soundness and completeness is significantly stronger than
demonstrating soundness alone.  The negative proof can be thought of
as a semantically verified error message, although in practice it
may be less readable than a well-crafted error message.
-->

另一种实现方法可能在生成或继承成功时返回其推导，并在失败时返回一条错误信息——例如，
参见 Agda
用户手册中讨论[语法糖](https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html#example)的章节。
这样的方法可以实现可靠性，而不是完备性。
如果其返回一个推导，那么我们知道它是正确的；
但没有人阻挡我们来给出一个**总是**返回错误的函数，即使正确的推导存在。
证明可靠性和完备性两者比起单独证明可靠性一者更加有力。
其反向的证明可以被看作是一个语义上验证过的错误信息，即便它本身比仔细撰写的错误信息更让人难懂。

<!--
We are now ready to begin the formal development.
-->

我们现在可以开始正式的形式化了：

<!--
## Imports
-->

## 导入

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
```

<!--
Once we have a type derivation, it will be easy to construct
from it the intrinsically-typed representation.  In order that we
can compare with our previous development, we import
module `plfa.part2.More`:
-->

当我们有一个赋型推导时，从它构造出内在类型的表示方法更加方便。
为了与我们之前的结果进行比较，我们导入模块 `plfa.part2.More`：

```agda
import plfa.part2.More as DB
```

<!--
The phrase `as DB` allows us to refer to definitions
from that module as, for instance, `DB._⊢_`, which is
invoked as `Γ DB.⊢ A`, where `Γ` has type
`DB.Context` and `A` has type `DB.Type`.
-->

`as DB` 这个词组让我们可以用例如 `DB._⊢_` 的方法来指代其中的定义，
我们用 `Γ DB.⊢ A` 来使用它，其中 `Γ` 的类型是 `DB.Context`，
`A` 的类型是 `DB.Type`。

<!--
## Syntax
-->

## 语法

<!--
First, we get all our infix declarations out of the way.
We list separately operators for judgments and terms:
-->

首先，我们来定义中缀声明。
我们将判断和项的运算符分别列出：

```agda
infix   4  _∋_⦂_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_⦂_

infixr  7  _⇒_

infix   5  ƛ_⇒_
infix   5  μ_⇒_
infix   6  _↑
infix   6  _↓_
infixl  7  _·_
infix   8  `suc_
infix   9  `_
```

<!--
Identifiers, types, and contexts are as before:
-->

标识符、类型和语境与之前一样：

```agda
Id : Set
Id = String

data Type : Set where
  `ℕ    : Type
  _⇒_   : Type → Type → Type

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context
```

<!--
The syntax of terms is defined by mutual recursion.
We use `Term⁺` and `Term⁻`
for terms with synthesized and inherited types, respectively.
Note the inclusion of the switching forms,
`M ↓ A` and `M ↑`:
-->

项的语法由共同递归来定义。
我们用 `Term⁺` 和 `Term⁻` 来分别表示生成和继承的项。
注意我们包括了变向的形式
`M ↓ A` 和 `M ↑`：

```agda
data Term⁺ : Set
data Term⁻ : Set

data Term⁺ where
  `_                       : Id → Term⁺
  _·_                      : Term⁺ → Term⁻ → Term⁺
  _↓_                      : Term⁻ → Type → Term⁺

data Term⁻ where
  ƛ_⇒_                     : Id → Term⁻ → Term⁻
  `zero                    : Term⁻
  `suc_                    : Term⁻ → Term⁻
  `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
  μ_⇒_                     : Id → Term⁻ → Term⁻
  _↑                       : Term⁺ → Term⁻
```

<!--
The choice as to whether each term is synthesized or
inherited follows the discussion above, and can be read
off from the informal grammar presented earlier.  Main terms in
deconstructors synthesise, constructors and side terms
in deconstructors inherit.
-->

至于每个项是由继承或者生成来赋型，我们在上文中已经讨论过，并且可以直接上文的非形式化语法中直接得来。
解构子中的主项由生成赋型，解构子中的构造子和副项由继承赋型。

<!--
## Example terms
-->

## 项的例子

<!--
We can recreate the examples from preceding chapters.
First, computing two plus two on naturals:
-->

我们重新给出前几章中的例子。
首先，计算自然数二加二：

```agda
two : Term⁻
two = `suc (`suc `zero)

plus : Term⁺
plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ ` "n" ↑
                        |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

2+2 : Term⁺
2+2 = plus · two · two
```

<!--
The only change is to decorate with down and up arrows as required.
The only type decoration required is for `plus`.
-->

唯一的变化是我们需要在需要时加入上下箭头。唯一的类型注释出现在 `plus`。

<!--
Next, computing two plus two with Church numerals:
-->

接下来，计算 Church 数的二加二：

```agda
Ch : Type
Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

twoᶜ : Term⁻
twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

plusᶜ : Term⁺
plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
           ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
             ↓ (Ch ⇒ Ch ⇒ Ch)

sucᶜ : Term⁻
sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

2+2ᶜ : Term⁺
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
```

<!--
The only type decoration required is for `plusᶜ`.  One is not even
required for `sucᶜ`, which inherits its type as an argument of `plusᶜ`.
-->

唯一的类型注释出现在 `plusᶜ`。
`sucᶜ` 甚至不需要类型注释，因为它从 `plusᶜ` 的参数中继承了类型。

<!--
## Bidirectional type checking
-->

## 双向类型检查

<!--
The typing rules for variables are as in
[Lambda](/Lambda/):
-->

变量的赋型规则与 [Lambda](/Lambda/) 章节中一致：

```agda
data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      -----------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A
```

<!--
As with syntax, the judgments for synthesizing
and inheriting types are mutually recursive:
-->

与语法一样，生成和继承的赋型判断也是共同递归的：

```agda
data _⊢_↑_ : Context → Term⁺ → Type → Set
data _⊢_↓_ : Context → Term⁻ → Type → Set

data _⊢_↑_ where

  ⊢` : ∀ {Γ A x}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A ⇒ B
    → Γ ⊢ M ↓ A
      -------------
    → Γ ⊢ L · M ↑ B

  ⊢↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ---------------
    → Γ ⊢ (M ↓ A) ↑ A

data _⊢_↓_ where

  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ↓ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ---------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x ⦂ `ℕ ⊢ N ↓ A
      -------------------------------------
    → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x ⦂ A ⊢ N ↓ A
      -----------------
    → Γ ⊢ μ x ⇒ N ↓ A

  ⊢↑ : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≡ B
      -------------
    → Γ ⊢ (M ↑) ↓ B
```

<!--
We follow the same convention as
Chapter [Lambda](/Lambda/),
prefacing the constructor with `⊢` to derive the name of the
corresponding type rule.
-->

我们用和 [Lambda](/Lambda/) 中一样的命名规则，
把 `⊢` 加在构造子之前，来当作对应赋型规则的名称。

<!--
The rules are similar to those in
Chapter [Lambda](/Lambda/),
modified to support synthesised and inherited types.
The two new rules are those for `⊢↓` and `⊢↑`.
The former both passes the type decoration as the inherited type and returns
it as the synthesised type.  The latter takes the synthesised type and the
inherited type and confirms they are identical - it should remind you of
the equality test in the application rule in the first
[section](/Inference/#algorithms).
-->

这些规则和 [Lambda](/Lambda/) 章节中相似，修改成支持生成和继承类型的样式。
其中有两条新规则 `⊢↓` 和 `⊢↑`。
前者把类型装饰当作继承的类型，并将其返回作为生成的类型。
后者取其生成的类型，并检查是否与继承的类型一致——这应该让你回忆起第一[部分](/Inference/#algorithms)中函数应用规则的相等性测试。


<!--
#### Exercise `bidirectional-mul` (recommended) {#bidirectional-mul}
-->

#### 练习 `bidirectional-mul` （推荐） {#bidirectional-mul}

<!--
Rewrite your definition of multiplication from
Chapter [Lambda](/Lambda/), decorated to support inference.
-->

将你在 [Lambda](/Lambda/) 章节中乘法的定义重写，将其装饰至支持类型推理的形式。

```agda
-- 请将代码写在此处。
```


<!--
#### Exercise `bidirectional-products` (recommended) {#bidirectional-products}
-->

#### 练习 `bidirectional-products` （推荐） {#bidirectional-products}

<!--
Extend the bidirectional type rules to include products from
Chapter [More](/More/).
-->

扩充你的双向赋型规则，来包括 [More](/More/) 章节中的积。


```agda
-- 请将代码写在此处。
```


<!--
#### Exercise `bidirectional-rest` (stretch) {#bidirectional-rest}
-->

#### 练习 `bidirectional-rest` （延伸）{#bidirectional-rest}

<!--
Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).
-->

扩充你的双向赋型规则，来包括 [More](/More/) 章节中的其余构造。

```agda
-- 请将代码写在此处。
```


<!--
## Prerequisites
-->

## 前置需求

<!--
The rule for `M ↑` requires the ability to decide whether two types
are equal.  It is straightforward to code:
-->

`M ↑` 规则需要我们有能力来判定两个类型是否相等。
我们可以直接地给出代码：

```agda
_≟Tp_ : (A B : Type) → Dec (A ≡ B)
`ℕ      ≟Tp `ℕ              =  yes refl
`ℕ      ≟Tp (A ⇒ B)         =  no λ()
(A ⇒ B) ≟Tp `ℕ              =  no λ()
(A ⇒ B) ≟Tp (A′ ⇒ B′)
  with A ≟Tp A′ | B ≟Tp B′
...  | no A≢    | _         =  no λ{refl → A≢ refl}
...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
...  | yes refl | yes refl  =  yes refl
```

<!--
We will also need a couple of obvious lemmas; the domain
and range of equal function types are equal:
-->

我们也会需要一些显然的引理；
作用域和值域相等的函数类型相等：

```agda
dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
dom≡ refl = refl

rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
rng≡ refl = refl
```

<!--
We will also need to know that the types `` `ℕ ``
and `A ⇒ B` are not equal:
-->

我们也需要知道 `` `ℕ `` 和 `A ⇒ B` 这两个类型不相等：

```agda
ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
ℕ≢⇒ ()
```


<!--
## Unique types
-->

## 唯一的类型

<!--
Looking up a type in the context is unique.  Given two derivations,
one showing `Γ ∋ x ⦂ A` and one showing `Γ ∋ x ⦂ B`, it follows that
`A` and `B` must be identical:
-->

从语境查询一个类型是唯一的。
给定两个推导，其一证明 `Γ ∋ x ⦂ A`，另一个证明 `Γ ∋ x ⦂ B`，那么
`A` 和 `B` 一定是一样的：

```agda
uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
uniq-∋ Z Z                 =  refl
uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′
```

<!--
If both derivations are by rule `Z` then uniqueness
follows immediately, while if both derivations are
by rule `S` then uniqueness follows by induction.
It is a contradiction if one derivation is by
rule `Z` and one by rule `S`, since rule `Z`
requires the variable we are looking for is the
final one in the context, while rule `S` requires
it is not.
-->

如果两个推导都使用 `Z` 规则，那么唯一性即可直接得出；
如果两个推导都使用 `S` 规则，那么唯一性可以由归纳得出。
如果一个使用了 `Z` 规则，另一个使用了 `S` 规则，这则是一个矛盾，
因为 `Z` 要求我们查询的变量是语境中的最后一个，而 `S` 要求不是这样。

<!--
Synthesizing a type is also unique.  Given two derivations,
one showing `Γ ⊢ M ↑ A` and one showing `Γ ⊢ M ↑ B`, it follows
that `A` and `B` must be identical:
-->

生成的类型也是唯一的。
给定两个推导，其一证明 `Γ ⊢ M ↑ A`，另一个证明 `Γ ⊢ M ↑ B`，那么
`A` 和 `B` 一定是一样的：

```agda
uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl
```

<!--
There are three possibilities for the term. If it is a variable,
uniqueness of synthesis follows from uniqueness of lookup.
If it is an application, uniqueness follows by induction on
the function in the application, since the range of equal
types are equal.  If it is a switch expression, uniqueness
follows since both terms are decorated with the same type.
-->

有三种项的形式。
如果项是变量，那么生成的唯一性从查询的唯一性中直接得出。
如果项是函数应用，那么唯一性由应用中的函数之上的归纳得出，因为值域相等的类型相等。
如果项是变向，两者装饰的类型相等，从此可得唯一性。

<!--
## Lookup type of a variable in the context
-->

## 查询语境中变量的类型

<!--
Given `Γ` and two distinct variables `x` and `y`, if there is no type `A`
such that `Γ ∋ x ⦂ A` holds, then there is also no type `A` such that
`Γ , y ⦂ B ∋ x ⦂ A` holds:
-->

给定 `Γ` 和两个不同的变量 `x` 和 `y`，
如果不存在类型 `A` 使得 `Γ ∋ x ⦂ A` 成立，
那么也不存在类型 `A` 使得 `Γ , y ⦂ B ∋ x ⦂ A` 成立：

```agda
ext∋ : ∀ {Γ B x y}
  → x ≢ y
  → ¬ (∃[ A ] Γ ∋ x ⦂ A)
    ----------------------------
  → ¬ (∃[ A ] Γ , y ⦂ B ∋ x ⦂ A)
ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
ext∋ _   ¬∃ ⟨ A , S _ ∋x ⟩  =  ¬∃ ⟨ A , ∋x ⟩
```

<!--
Given a type `A` and evidence that `Γ , y ⦂ B ∋ x ⦂ A` holds, we must
demonstrate a contradiction.  If the judgment holds by `Z`, then we
must have that `x` and `y` are the same, which contradicts the first
assumption. If the judgment holds by `S _ ∋x` then `∋x` provides
evidence that `Γ ∋ x ⦂ A`, which contradicts the second assumption.
-->

给定类型 `A` 和 `Γ , y ⦂ B ∋ x ⦂ A` 成立的证明，我们必须构造一个矛盾。
如果判断由 `Z` 成立，那么 `x` 和 `y` 一定是一样的，与第一个假设矛盾。
如果判断由 `S _ ∋x` 成立，那么 `∋x` 提供了 `Γ ∋ x ⦂ A` 成立的证明，与第二个假设矛盾。

<!--
Given a context `Γ` and a variable `x`, we decide whether
there exists a type `A` such that `Γ ∋ x ⦂ A` holds, or its
negation:
-->

给定语境 `Γ` 和变量 `x`，我们可判断是否存在一个类型 `A` 使得
`Γ ∋ x ⦂ A` 成立，或者其反命题：

```agda
lookup : ∀ (Γ : Context) (x : Id)
         ------------------------
       → Dec (∃[ A ] Γ ∋ x ⦂ A)
lookup ∅ x                        =  no  (λ ())
lookup (Γ , y ⦂ B) x with x ≟ y
... | yes refl                    =  yes ⟨ B , Z ⟩
... | no x≢y with lookup Γ x
...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
...             | yes ⟨ A , ∋x ⟩  =  yes ⟨ A , S x≢y ∋x ⟩
```

<!--
Consider the context:
-->

考虑语境的情况：

<!--
* If it is empty, then trivially there is no possible derivation.
-->

* 如果语境为空，那么平凡地，我们没有任何可能的推导。

<!--
* If it is non-empty, compare the given variable to the most
  recent binding:
-->

* 如果语境非空，比较给定的变量和最新的绑定：

  <!--
  + If they are identical, we have succeeded, with `Z` as
    the appropriate derivation.
  -->

  + 如果它们一致，我们完成了判定，使用 `Z` 作为对应的推导。

  <!--
  + If they differ, we recurse:
  -->

  + 如果它们不一致，我们递归：

    <!--
    - If lookup fails, we apply `ext∋` to convert the proof
      there is no derivation from the contained context
      to the extended context.
    -->

    - 如果查询失败了，我们使用 `ext∋` 将变量不存在于内部的语境中的证明扩充至扩充后的语境。

    <!--
    - If lookup succeeds, we extend the derivation with `S`.
    -->

    - 如果查询成功了，我们对返回的推导使用 `S`。


<!--
## Promoting negations
-->

## 提升否定

<!--
For each possible term form, we need to show that if one of its
components fails to type, then the whole fails to type.  Most of
these results are easy to demonstrate inline, but we provide
auxiliary functions for a couple of the trickier cases.
-->

对于每一个可能的项的形式，我们需要证明：如果其内部的子项无法被赋型，那么整个项无法被赋型。
大多数情况下，我们可以直接在行中直接完成所需的证明，但有一些困难的情况，
我们提供一些帮助函数。

<!--
If `Γ ⊢ L ↑ A ⇒ B` holds but `Γ ⊢ M ↓ A` does not hold, then
there is no type `B′` such that `Γ ⊢ L · M ↑ B′` holds:
-->

如果 `Γ ⊢ L ↑ A ⇒ B` 成立而  `Γ ⊢ M ↓ A` 不成立，那么不存在使得
`Γ ⊢ L · M ↑ B′` 成立的类型 `B′`：

```agda
¬arg : ∀ {Γ A B L M}
  → Γ ⊢ L ↑ A ⇒ B
  → ¬ Γ ⊢ M ↓ A
    --------------------------
  → ¬ (∃[ B′ ] Γ ⊢ L · M ↑ B′)
¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′
```

<!--
Let `⊢L` be evidence that `Γ ⊢ L ↑ A ⇒ B` holds and `¬⊢M` be evidence
that `Γ ⊢ M ↓ A` does not hold.  Given a type `B′` and evidence that
`Γ ⊢ L · M ↑ B′` holds, we must demonstrate a contradiction.  The
evidence must take the form `⊢L′ · ⊢M′`, where `⊢L′` is evidence that
`Γ ⊢ L ↑ A′ ⇒ B′` and `⊢M′` is evidence that `Γ ⊢ M ↓ A′`.  By
`uniq-↑` applied to `⊢L` and `⊢L′`, we know that `A ⇒ B ≡ A′ ⇒ B′`,
and hence that `A ≡ A′`, which means that `¬⊢M` and `⊢M′` yield a
contradiction.  Without the `rewrite` clause, Agda would not allow us
to derive a contradiction between `¬⊢M` and `⊢M′`, since one concerns
type `A` and the other type `A′`.
-->

让 `⊢L` 作为 `Γ ⊢ L ↑ A ⇒ B` 成立的证明、 `¬⊢M` 作为 `Γ ⊢ M ↓ A` 不成立的证明。
给定类型 `B′` 和 `Γ ⊢ L · M ↑ B′` 成立的证明，我们必须构造一个矛盾。
这样的证明一定是 `⊢L′ · ⊢M′` 的形式，其中 `⊢L′`
是 `Γ ⊢ L ↑ A′ ⇒ B′` 成立的证明、`⊢M′` 是 `Γ ⊢ M ↓ A′` 成立的证明。
将 `uniq-↑` 应用于 `⊢L` 和 `⊢L′`，我们知道 `A ⇒ B ≡ A′ ⇒ B′`，
所以可得 `A ≡ A′`，这意味着 `¬⊢M` 和 `⊢M′` 可以构造出一个矛盾。
不使用 `rewrite` 语句的话，Agda 不会让我们从 `¬⊢M` 和 `⊢M′` 中构造出一个矛盾，
因为其中的类型分别是 `A` 和 `A′`。

<!--
If `Γ ⊢ M ↑ A` holds and `A ≢ B`, then `Γ ⊢ (M ↑) ↓ B` does not hold:
-->

如果 `Γ ⊢ M ↑ A` 成立且 `A ≢ B`，那么 `Γ ⊢ (M ↑) ↓ B` 不成立：

```agda
¬switch : ∀ {Γ M A B}
  → Γ ⊢ M ↑ A
  → A ≢ B
    ---------------
  → ¬ Γ ⊢ (M ↑) ↓ B
¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B
```

<!--
Let `⊢M` be evidence that `Γ ⊢ M ↑ A` holds, and `A≢B` be evidence
that `A ≢ B`.  Given evidence that `Γ ⊢ (M ↑) ↓ B` holds, we must
demonstrate a contradiction.  The evidence must take the form `⊢↑ ⊢M′
A′≡B`, where `⊢M′` is evidence that `Γ ⊢ M ↑ A′` and `A′≡B` is
evidence that `A′ ≡ B`.  By `uniq-↑` applied to `⊢M` and `⊢M′` we know
that `A ≡ A′`, which means that `A≢B` and `A′≡B` yield a
contradiction.  Without the `rewrite` clause, Agda would not allow us
to derive a contradiction between `A≢B` and `A′≡B`, since one concerns
type `A` and the other type `A′`.
-->

让 `⊢M` 作为 `Γ ⊢ M ↑ A` 成立的证明、`A≢B` 作为 `A ≢ B` 成立的证明。
给定 `Γ ⊢ (M ↑) ↓ B` 成立的证明，我们必须构造一个矛盾。
这样的证明一定是 `⊢↑ ⊢M′ A′≡B` 的形式，其中
`⊢M′` 是 `Γ ⊢ M ↑ A′` 成立的证明、`A′≡B` 是 `A′ ≡ B` 成立的证明。
将 `uniq-↑` 应用于 `⊢M` 和 `⊢M′`，我们知道 `A ≡ A′`，这意味着 `A≢B` 和 `A′≡B`
可以构造出一个矛盾。
不使用 `rewrite` 语句的话，Agda 不会让我们从 `A≢B` 和 `A′≡B` 中构造出一个矛盾，
因为其中的类型分别是 `A` 和 `A′`。

<!--
## Synthesize and inherit types
-->

## 生成和继承类型

<!--
The table has been set and we are ready for the main course.
We define two mutually recursive functions,
one for synthesis and one for inheritance.  Synthesis is given
a context `Γ` and a synthesis term `M` and either
returns a type `A` and evidence that `Γ ⊢ M ↑ A`, or its negation.
Inheritance is given a context `Γ`, an inheritance term `M`,
and a type `A` and either returns evidence that `Γ ⊢ M ↓ A`,
or its negation:
-->

餐桌已经布置好了，我们已经准备好享用今天的主菜了。
我们定义两个共同递归的函数，一个用于生成，一个用于继承。
生成在给定语境 `Γ` 和生成项 `M` 时，要么返回一个类型 `A` 和 `Γ ⊢ M ↑ A` 成立的证明，或者其/否定。
继承在给定语境 `Γ` 、继承项 `M` 和类型 `A` 时要么返回 `Γ ⊢ M ↓ A` 成立的证明，或者其否定：

```agda
synthesize : ∀ (Γ : Context) (M : Term⁺)
             ---------------------------
           → Dec (∃[ A ] Γ ⊢ M ↑ A )

inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
    ---------------
  → Dec (Γ ⊢ M ↓ A)
```

<!--
We first consider the code for synthesis:
-->

我们首先考虑生成的代码：

```agda
synthesize Γ (` x) with lookup Γ x
... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
synthesize Γ (L · M) with synthesize Γ L
... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩
synthesize Γ (M ↓ A) with inherit Γ M A
... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩
```

<!--
There are three cases:
-->

有三种情况来考虑：

<!--
* If the term is a variable `` ` x ``, we use lookup as defined above:
-->

* 如果项是变量 `` ` x ``，我们使用之前定义的查询：

  <!--
  + If it fails, then `¬∃` is evidence that there is no `A` such
    that `Γ ∋ x ⦂ A` holds.  Evidence that `` Γ ⊢ ` x ↑ A `` holds must
    have the form `` ⊢` ∋x ``, where `∋x` is evidence that `Γ ∋ x ⦂ A`,
    which yields a contradiction.
  -->

  + 如果失败了，那么 `¬∃` 是不存在使得 `Γ ∋ x ⦂ A` 成立的类型 `A` 的证明。
    `` Γ ⊢ ` x ↑ A `` 成立的证明一定是 `` ⊢` ∋x `` 的形式，其中 `∋x`
    是 `Γ ∋ x ⦂ A` 成立的证明，这构成了一个矛盾。

  <!--
  + If it succeeds, then `∋x` is evidence that `Γ ∋ x ⦂ A`, and
    hence `` ⊢` ∋x `` is evidence that `` Γ ⊢ ` x ↑ A ``.
  -->

  + 如果成功了，那么 `∋x` 是 `Γ ∋ x ⦂ A` 成立的证明，所以 `` ⊢` ∋x `` 是
    `` Γ ⊢ ` x ↑ A `` 成立的证明。

<!--
* If the term is an application `L · M`, we recurse on the function `L`:
-->

* 如果项是函数应用 `L · M`，我们递归于函数项 `L`：

  <!--
  + If it fails, then `¬∃` is evidence that there is no type such
    that `Γ ⊢ L ↑ _` holds.  Evidence that `Γ ⊢ L · M ↑ _` holds
    must have the form `⊢L · _`, where `⊢L` is evidence that
    `Γ ⊢ L ↑ _`, which yields a contradiction.
  -->

  + 如果失败了，那么 `¬∃` 是不存在任何类型 `Γ ⊢ L ↑ _` 成立的证明。
    `Γ ⊢ L · M ↑ _` 成立的证明一定是 `⊢L · _` 的形式，其中 `⊢L`
    是 `Γ ⊢ L ↑ _` 成立的证明，这构成了一个矛盾。

  <!--
  + If it succeeds, there are two possibilities:
  -->

  + 如果成功了，那么有两种情况：

    <!--
    - One is that `⊢L` is evidence that `` Γ ⊢ L ⦂ `ℕ ``.  Evidence
      that `Γ ⊢ L · M ↑ _` holds must have the form `⊢L′ · _` where
      `⊢L′` is evidence that `Γ ⊢ L ↑ A ⇒ B` for some types `A` and
      `B`.  Applying `uniq-↑` to `⊢L` and `⊢L′` yields a
      contradiction, since `` `ℕ `` cannot equal `A ⇒ B`.
    -->

    - 其一是 `⊢L` 是 `` Γ ⊢ L ⦂ `ℕ `` 成立的证明。
      `Γ ⊢ L · M ↑ _` 成立的证明一定是 `⊢L′ · _` 的形式，其中
      `⊢L′` 是 `Γ ⊢ L ↑ A ⇒ B` 对于一些类型 `A` 和 `B` 成立的证明。
      将 `uniq-↑` 应用于 `⊢L` 和 `⊢L′` 构成了一个矛盾，
      因为 `` `ℕ `` 无法与 `A ⇒ B` 相等。

    <!--
    - The other is that `⊢L` is evidence that `Γ ⊢ L ↑ A ⇒ B`, in
      which case we recurse on the argument `M`:
    -->

    - 另一是 `⊢L` 是 `Γ ⊢ L ↑ A ⇒ B` 成立的证明，那么我们在参数项 `M` 上递归：

      <!--
      * If it fails, then `¬⊢M` is evidence that `Γ ⊢ M ↓ A` does
        not hold.  By `¬arg` applied to `⊢L` and `¬⊢M`, it follows
        that `Γ ⊢ L · M ↑ B` cannot hold.
      -->

      * 如果失败了，那么 `¬⊢M` 是 `Γ ⊢ M ↓ A` 不成立的证明。
        将 `¬arg` 应用于 `⊢L` 和 `¬⊢M`，我们可得
        `Γ ⊢ L · M ↑ B` 不成立。

      <!--
      * If it succeeds, then `⊢M` is evidence that `Γ ⊢ M ↓ A`,
        and `⊢L · ⊢M` provides evidence that `Γ ⊢ L · M ↑ B`.
      -->

      * 如果成功了，那么 `⊢M` 是 `Γ ⊢ M ↓ A` 成立的证明，
        且 `⊢L · ⊢M` 提供了 `Γ ⊢ L · M ↑ B` 成立的证明。

<!--
* If the term is a switch `M ↓ A` from synthesised to inherited,
  we recurse on the subterm `M`, supplying type `A` by inheritance:
-->

* 如果项是从生成到继承的变向项 `M ↓ A`，我们在子项 `M` 上递归，并向继承提供类型 `A`：

  <!--
  + If it fails, then `¬⊢M` is evidence that `Γ ⊢ M ↓ A` does not
    hold.  Evidence that `Γ ⊢ (M ↓ A) ↑ A` holds must have the
    form `⊢↓ ⊢M` where `⊢M` is evidence that `Γ ⊢ M ↓ A` holds,
    which yields a contradiction.
  -->

  + 如果失败了，那么 `¬⊢M` 是 `Γ ⊢ M ↓ A` 不成立的证明。
    `Γ ⊢ (M ↓ A) ↑ A` 成立的证明一定是 `⊢↓ ⊢M` 的形式，其中 `⊢M`
    是 `Γ ⊢ M ↓ A` 成立的证明，这构成了一个矛盾。

  <!--
  + If it succeeds, then `⊢M` is evidence that `Γ ⊢ M ↓ A`,
    and `⊢↓ ⊢M` provides evidence that `Γ ⊢ (M ↓ A) ↑ A`.
  -->

  + 如果成功了，那么 `⊢M` 是 `Γ ⊢ M ↓ A` 成立的证明，且
    `⊢↓ ⊢M` 提供了 `Γ ⊢ (M ↓ A) ↑ A` 成立的证明。

<!--
We next consider the code for inheritance:
-->

我们接下来考虑继承的代码：

```agda
inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢ƛ ⊢N)
inherit Γ `zero `ℕ          =  yes ⊢zero
inherit Γ `zero (A ⇒ B)     =  no  (λ())
inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
... | yes ⊢M                =  yes (⊢suc ⊢M)
inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })
... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
... | yes ⊢N                =  yes (⊢μ ⊢N)
inherit Γ (M ↑) B with synthesize Γ M
... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)
```

<!--
We consider only the cases for abstraction and
and for switching from inherited to synthesized:
-->

我们在此只考虑抽象和从继承变向至生成的情况：

<!--
* If the term is an abstraction `ƛ x ⇒ N` and the inherited type
  is `` `ℕ ``, then it is trivial that `` Γ ⊢ (ƛ x ⇒ N) ↓ `ℕ ``
  cannot hold.
-->

* 如果项是 `ƛ x ⇒ N`，而继承的类型是 `` `ℕ ``，那么平凡地， `` Γ ⊢ (ƛ x ⇒ N) ↓ `ℕ `` 无法成立。

<!--
* If the term is an abstraction `ƛ x ⇒ N` and the inherited type
  is `A ⇒ B`, then we recurse with context `Γ , x ⦂ A` on subterm
  `N` inheriting type `B`:
-->

* 如果项是 `ƛ x ⇒ N`，而继承的类型是 `A ⇒ B`，我们用语境 `Γ , x ⦂ A` 递归至
  子项 `N` 继承类型 `B`：

  <!--
  + If it fails, then `¬⊢N` is evidence that `Γ , x ⦂ A ⊢ N ↓ B`
    does not hold.  Evidence that `Γ ⊢ (ƛ x ⇒ N) ↓ A ⇒ B` holds
    must have the form `⊢ƛ ⊢N` where `⊢N` is evidence that
    `Γ , x ⦂ A ⊢ N ↓ B`, which yields a contradiction.
  -->

  + 如果失败了，那么 `¬⊢N` 是 `Γ , x ⦂ A ⊢ N ↓ B` 不成立的证明。
    `Γ ⊢ (ƛ x ⇒ N) ↓ A ⇒ B` 成立的证明一定是 `⊢ƛ ⊢N` 的形式，其中
    `⊢N` 是 `Γ , x ⦂ A ⊢ N ↓ B` 成立的证明，这构成了一个矛盾。

  <!--
  + If it succeeds, then `⊢N` is evidence that `Γ , x ⦂ A ⊢ N ↓ B`
    holds, and `⊢ƛ ⊢N` provides evidence that `Γ ⊢ (ƛ x ⇒ N) ↓ A ⇒ B`.
  -->

  + 如果成功了，那么 `⊢N` 是 `Γ , x ⦂ A ⊢ N ↓ B` 成立的证明，且 `⊢ƛ ⊢N`
    提供了 `Γ ⊢ (ƛ x ⇒ N) ↓ A ⇒ B` 成立的证明。

<!--
* If the term is a switch `M ↑` from inherited to synthesised,
  we recurse on the subterm `M`:
-->

* 如果项是从继承到生成的变向项 `M ↑`，我们在子项 `M` 上递归：

  <!--
  + If it fails, then `¬∃` is evidence there is no `A` such
    that `Γ ⊢ M ↑ A` holds.  Evidence that `Γ ⊢ (M ↑) ↓ B` holds
    must have the form `⊢↑ ⊢M _` where `⊢M` is evidence that
    `Γ ⊢ M ↑ _`, which yields a contradiction.
  -->

  + 如果失败了，那么 `¬∃` 是不存在使得 `Γ ⊢ M ↑ A` 成立的类型 `A` 的证明。
    `Γ ⊢ (M ↑) ↓ B` 成立的证明一定是 `⊢↑ ⊢M _` 的形式，其中 `⊢M`
    是 `Γ ⊢ M ↑ _` 成立的证明，这构成了一个矛盾。

  <!--
  + If it succeeds, then `⊢M` is evidence that `Γ ⊢ M ↑ A` holds.
    We apply `_≟Tp_` do decide whether `A` and `B` are equal:
  -->

  + 如果成功了，那么 `⊢M` 是 `Γ ⊢ M ↑ A` 成立的证明。
    我们应用 `_≟Tp_` 来判定 `A` 和 `B` 是否相等：

    <!--
    - If it fails, then `A≢B` is evidence that `A ≢ B`.
      By `¬switch` applied to `⊢M` and `A≢B` it follow that
      `Γ ⊢ (M ↑) ↓ B` cannot hold.
    -->

    - 如果失败了，那么 `A≢B` 是 `A ≢ B` 的证明。
      将 `¬switch` 应用于 `⊢M` 和 `A≢B`，我们可得
      `Γ ⊢ (M ↑) ↓ B` 无法成立。

    <!--
    - If it succeeds, then `A≡B` is evidence that `A ≡ B`,
      and `⊢↑ ⊢M A≡B` provides evidence that `Γ ⊢ (M ↑) ↓ B`.
    -->

    - 如果成功了，那么 `A≡B` 是 `A ≡ B` 的证明，
      且 `⊢↑ ⊢M A≡B` 提供了 `Γ ⊢ (M ↑) ↓ B` 成立的证明。

<!--
The remaining cases are similar, and their code can pretty much be
read directly from the corresponding typing rules.
-->

剩余的情况类似，它们的代码可以由对应的赋型规则直接对应得来。

<!--
## Testing the example terms
-->

## 测试项的例子

<!--
First, we copy the smart constructor `S′` introduced earlier that makes it easy to
access a variable in a context:
-->

首先，我们复制之前介绍过的智能构造子 `S′`，使得访问语境中的变量更加便利：

```
S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x
```

<!--
Here is the result of typing two plus two on naturals:
-->

下面是给自然数二加二赋型的结果：

```agda
⊢2+2 : ∅ ⊢ 2+2 ↑ `ℕ
⊢2+2 =
  (⊢↓
   (⊢μ
    (⊢ƛ
     (⊢ƛ
      (⊢case (⊢` (S′ Z)) (⊢↑ (⊢` Z) refl)
       (⊢suc
        (⊢↑
         (⊢`
          (S′
           (S′
            (S′ Z)))
          · ⊢↑ (⊢` Z) refl
          · ⊢↑ (⊢` (S′ Z)) refl)
         refl))))))
   · ⊢suc (⊢suc ⊢zero)
   · ⊢suc (⊢suc ⊢zero))
```

<!--
We confirm that synthesis on the relevant term returns
natural as the type and the above derivation:
-->

我们可以确认，对相应的项生成类型返回了自然数类型，和上述的推导：

```agda
_ : synthesize ∅ 2+2 ≡ yes ⟨ `ℕ , ⊢2+2 ⟩
_ = refl
```

<!--
Indeed, the above derivation was computed by evaluating the term on
the left, with minor editing of the result.  The only editing required
was to use the smart constructor `S′` to obtain the evidence that
two variable names (as strings) are unequal (which it cannot print nor read).
-->

的确，上述的推导是用左边的项求值所得的，再加上一些微小的修改。
所需的修改只是使用智能构造子 `S′` 来获取两个变量名（使用字符串）不同的证明（其无法打印或阅读）。

<!--
Here is the result of typing two plus two with Church numerals:
-->

下面是给 Church 数二加二赋型的结果：

```agda
⊢2+2ᶜ : ∅ ⊢ 2+2ᶜ ↑ `ℕ
⊢2+2ᶜ =
  ⊢↓
  (⊢ƛ
   (⊢ƛ
    (⊢ƛ
     (⊢ƛ
      (⊢↑
       (⊢`
        (S′
         (S′
          (S′ Z)))
        · ⊢↑ (⊢` (S′ Z)) refl
        ·
        ⊢↑
        (⊢`
         (S′
          (S′ Z))
         · ⊢↑ (⊢` (S′ Z)) refl
         · ⊢↑ (⊢` Z) refl)
        refl)
       refl)))))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (⊢` (S′ Z) ·
     ⊢↑ (⊢` (S′ Z) · ⊢↑ (⊢` Z) refl)
     refl)
    refl))
  ·
  ⊢ƛ
  (⊢ƛ
   (⊢↑
    (⊢` (S′ Z) ·
     ⊢↑ (⊢` (S′ Z) · ⊢↑ (⊢` Z) refl)
     refl)
    refl))
  · ⊢ƛ (⊢suc (⊢↑ (⊢` Z) refl))
  · ⊢zero
```

<!--
We confirm that synthesis on the relevant term returns
natural as the type and the above derivation:
-->

我们可以确认，对相应的项生成类型返回了自然数类型，和上述的推导：

```agda
_ : synthesize ∅ 2+2ᶜ ≡ yes ⟨ `ℕ , ⊢2+2ᶜ ⟩
_ = refl
```

<!--
Again, the above derivation was computed by evaluating the
term on the left and editing.
-->

同样，上面的推导使用对左手边的项求值所得，加上一些修改。

<!--
## Testing the error cases
-->

## 测试错误的例子

<!--
It is important not just to check that code works as intended,
but also that it fails as intended.  Here are checks for
several possible errors:
-->

很重要的是，不仅要检查代码是否按照意图工作，以及代码是否按照意图不工作。
下面是检查不同种类错误的例子：

<!--
Unbound variable:
-->

未约束的变量：

```agda
_ : synthesize ∅ ((ƛ "x" ⇒ ` "y" ↑) ↓ (`ℕ ⇒ `ℕ)) ≡ no _
_ = refl
```

<!--
Argument in application is ill typed:
-->

函数应用的参数不是良类型的：

```agda
_ : synthesize ∅ (plus · sucᶜ) ≡ no _
_ = refl
```

<!--
Function in application is ill typed:
-->

函数应用的函数不是良类型的：

```agda
_ : synthesize ∅ (plus · sucᶜ · two) ≡ no _
_ = refl
```

<!--
Function in application has type natural:
-->

函数应用的函数是自然数类型：

```agda
_ : synthesize ∅ ((two ↓ `ℕ) · two) ≡ no _
_ = refl
```

<!--
Abstraction inherits type natural:
-->

抽象继承了自然数类型：

```agda
_ : synthesize ∅ (twoᶜ ↓ `ℕ) ≡ no _
_ = refl
```

<!--
Zero inherits a function type:
-->

零继承了函数类型：

```agda
_ : synthesize ∅ (`zero ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl
```

<!--
Successor inherits a function type:
-->

后继继承了函数类型：

```agda
_ : synthesize ∅ (two ↓ `ℕ ⇒ `ℕ) ≡ no _
_ = refl
```

<!--
Successor of an ill-typed term:
-->

非良类型项的后继：

```agda
_ : synthesize ∅ (`suc twoᶜ ↓ `ℕ) ≡ no _
_ = refl
```

<!--
Case of a term with a function type:
-->

对函数类型的项分情况讨论：

```agda
_ : synthesize ∅
      ((`case (twoᶜ ↓ Ch) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl
```

<!--
Case of an ill-typed term:
-->

对不良类型的项分情况讨论：

```agda
_ : synthesize ∅
      ((`case (twoᶜ ↓ `ℕ) [zero⇒ `zero |suc "x" ⇒ ` "x" ↑ ] ↓ `ℕ) ) ≡ no _
_ = refl
```

<!--
Inherited and synthesised types disagree in a switch:
-->

变向时继承与生成的项不一致：

```agda
_ : synthesize ∅ (((ƛ "x" ⇒ ` "x" ↑) ↓ `ℕ ⇒ (`ℕ ⇒ `ℕ))) ≡ no _
_ = refl
```


<!--
## Erasure
-->

## 擦除

<!--
From the evidence that a decorated term has the correct type it is
easy to extract the corresponding intrinsically-typed term.  We use the
name `DB` to refer to the code in
Chapter [DeBruijn](/DeBruijn/).
It is easy to define an _erasure_ function that takes an extrinsic
type judgment into the corresponding intrinsically-typed term.
-->

从装饰过的项拥有正确的类型的证明中，我们可以简单地提取出对应的内在类型的项。
我们使用 `DB` 来指代 [DeBruijn](/DeBruijn/) 章节中的代码。
我们可以简单地定义一个**擦除**（Erasure）从外在的赋型判断，至对应的内在类型的项的函数。

<!--
First, we give code to erase a type:
-->

首先，我们给出擦除类型的代码：

```agda
∥_∥Tp : Type → DB.Type
∥ `ℕ ∥Tp             =  DB.`ℕ
∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp
```

<!--
It simply renames to the corresponding constructors in module `DB`.
-->

它简单地把对应的构造子重命名至 `DB` 模块中。

<!--
Next, we give the code to erase a context:
-->

接下来，我们给出擦除语境的代码：

```agda
∥_∥Cx : Context → DB.Context
∥ ∅ ∥Cx              =  DB.∅
∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp
```

<!--
It simply drops the variable names.
-->

它简单地丢弃了变量名。

<!--
Next, we give the code to erase a lookup judgment:
-->

接下来，我们给出擦除查询判断的代码：

```agda
∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
∥ Z ∥∋               =  DB.Z
∥ S x≢ ∋x ∥∋         =  DB.S ∥ ∋x ∥∋
```

<!--
It simply drops the evidence that variable names are distinct.
-->

它简单地丢弃了变量名不同的证明。

<!--
Finally, we give the code to erase a typing judgment.
Just as there are two mutually recursive typing judgments,
there are two mutually recursive erasure functions:
-->

最后，我们给出擦除赋型判断的代码。
正如由两个共同递归的赋型判断，我们有两个共同递归的擦除函数：

```agda
∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻

∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
∥ ⊢zero ∥⁻           =  DB.`zero
∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺
```

<!--
Erasure replaces constructors for each typing judgment
by the corresponding term constructor from `DB`.  The
constructors that correspond to switching from synthesized
to inherited or vice versa are dropped.
-->

擦除将每个赋型判断中的构造子替换成 `DB` 中对应的项构造子。
对应变向的构造子被丢弃。

<!--
We confirm that the erasure of the type derivations in
this chapter yield the corresponding intrinsically-typed terms
from the earlier chapter:
-->

我们证实本章中的赋型判断擦除后，与之前使用内在类型项章节中的那些一致：

```agda
_ : ∥ ⊢2+2 ∥⁺ ≡ DB.2+2
_ = refl

_ : ∥ ⊢2+2ᶜ ∥⁺ ≡ DB.2+2ᶜ
_ = refl
```

<!--
Thus, we have confirmed that bidirectional type inference
converts decorated versions of the lambda terms from
Chapter [Lambda](/Lambda/)
to the intrinsically-typed terms of
Chapter [DeBruijn](/DeBruijn/).
-->

因此，我们证实了双向类型推理把装饰后的 [Lambda](/Lambda/) 章节的
λ 项转换至 [DeBruijn](/DeBruijn) 章节中内在类型的项。

<!--
#### Exercise `inference-multiplication` (recommended)
-->

#### 练习 `inference-multiplication` （推荐）

<!--
Apply inference to your decorated definition of multiplication from
exercise [`bidirectional-mul`](/Inference/#bidirectional-mul), and show that
erasure of the inferred typing yields your definition of
multiplication from Chapter [DeBruijn](/DeBruijn/).
-->

对你在 [`bidirectional-mul`](/Inference/#bidirectional-mul) 练习中的乘法项应用双向推理，
并证明推理得到的赋型可以擦除至 [DeBruijn](/DeBruijn/) 章节中你的定义。

```agda
-- 请将代码写在此处。
```

<!--
#### Exercise `inference-products` (recommended)
-->

#### 练习 `inference-products` （推荐）

<!--
Using your rules from exercise
[`bidirectional-products`](/Inference/#bidirectional-products), extend
bidirectional inference to include products. Also extend erasure.
-->

使用你在 [`bidirectional-mul`](/Inference/#bidirectional-mul) 练习中的赋型规则，
将双向推理扩充至包括积。此外扩充对应的擦除。

```agda
-- 请将代码写在此处。
```

<!--
#### Exercise `inference-rest` (stretch)
-->

#### 练习 `inference-rest` （延伸）

<!--
Using your rules from exercise
[`bidirectional-rest`](/Inference/#bidirectional-rest), extend
bidirectional inference to include the rest of the constructs from
Chapter [More](/More/). Also extend erasure.
-->

使用你从练习 [`bidirectional-rest`](/Inference/#bidirectional-rest)
中得到的规则，扩充双向推导规则，来包括 [More](/More/) 章节的剩余构造。
此外扩充对应的擦除。

```agda
-- 请将代码写在此处。
```


<!--
## Bidirectional inference in Agda
-->

## Agda 中的双向推理

<!--
Agda itself uses bidirectional inference.  This explains why
constructors can be overloaded while other defined names cannot -
here by _overloaded_ we mean that the same name can be used for
constructors of different types.  Constructors are typed by
inheritance, and so the type is available when resolving the
constructor, whereas variables are typed by synthesis, and so each
variable must have a unique type.
-->

Agda 本身也使用双向推理。
这解释了为什么构造子可以被重载，而其他定义的名称不可以——此处的**重载**指的是我们可以给不同类型的构造子使用相同的名称。
构造子是由继承来赋型，而变量由生成来赋型，因此每个变量必须有唯一的类型。

<!--
Most top-level definitions in Agda are of functions, which are typed
by inheritance, which is why Agda requires a type declaration for
those definitions.  A definition with a right-hand side that is a term
typed by synthesis, such as an application, does not require a type
declaration.
-->

Agda 中多数的顶层声明时函数，其由继承来赋型，也就是为什么 Agda 会对这些定义要求类型声明。
一个由生成赋型的右手边的定义，比如说函数应用，则不需要类型声明。

```agda
answer = 6 * 7
```


## Unicode

<!--
This chapter uses the following unicode:
-->

本章中使用了以下 Unicode：

    ↓  U+2193:  DOWNWARDS ARROW (\d)
    ↑  U+2191:  UPWARDS ARROW (\u)
    ∥  U+2225:  PARALLEL TO (\||)
