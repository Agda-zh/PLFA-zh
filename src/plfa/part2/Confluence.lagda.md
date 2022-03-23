---
title     : "Confluence: 无类型 λ-演算的合流性"
layout    : page
prev      : /Untyped/
permalink : /Confluence/
next      : /BigStep/
translators : ["starxingchenc"]
progress  : 100
---

```
module plfa.part2.Confluence where
```

<!--
## Introduction
-->

## 简介

<!--
In this chapter we prove that beta reduction is _confluent_, a
property also known as _Church-Rosser_. That is, if there are
reduction sequences from any term `L` to two different terms `M₁` and
`M₂`, then there exist reduction sequences from those two terms to
some common term `N`. In pictures:
-->

在这一章我们将证明 β-规约是**合流的（Confluent）**
（又被称作 *Church-Rosser* 性质）：
如果有从任一项 `L` 至两个不同项 `M₁` 和 `M₂` 的规约序列，
那么一定存在从这两个项至某个相同项 `N` 的规约序列。
如图：

        L
       / \
      /   \
     /     \
    M₁      M₂
     \     /
      \   /
       \ /
        N

<!--
where downward lines are instances of `—↠`.
-->

其中向下的线是 `-↠` 的实例。

<!--
Confluence is studied in many other kinds of rewrite systems besides
the lambda calculus, and it is well known how to prove confluence in
rewrite systems that enjoy the _diamond property_, a single-step
version of confluence. Let `⇛` be a relation.  Then `⇛` has the
diamond property if whenever `L ⇛ M₁` and `L ⇛ M₂`, then there exists
an `N` such that `M₁ ⇛ N` and `M₂ ⇛ N`. This is just an instance of
the same picture above, where downward lines are now instance of `⇛`.
If we write `⇛*` for the reflexive and transitive closure of `⇛`, then
confluence of `⇛*` follows immediately from the diamond property.
-->

合流性（Confluence）也在许多 λ-演算外的重写系统中被研究，
并且如何在满足**菱形性质（Diamond Property）**，
一种合流性的单步版本的重写系统中证明合流性是广为人知的。
令 `⇛` 为一个关系。`⇛` 具有菱形性质，
如果对于任何 `L ⇛ M₁` 和 `L ⇛ M₂` 都存在 `N` ，
使得 `M₁ ⇛ N` 和 `M₂ ⇛ N`。
这只是上图的另一个例子，此处向下的线代表 `⇛`。
如果我们将 `⇛` 的自反传递闭包写作 `⇛*`，
那么可以立即从菱形性质推出 `⇛*` 的合流性。

<!--
Unfortunately, reduction in the lambda calculus does not satisfy the
diamond property. Here is a counter example.
-->

不幸的是 λ-演算的规约并不满足菱形性质。这是一个反例：

    (λ x. x x)((λ x. x) a) —→ (λ x. x x) a
    (λ x. x x)((λ x. x) a) —→ ((λ x. x) a) ((λ x. x) a)

<!--
Both terms can reduce to `a a`, but the second term requires two steps
to get there, not one.
-->

两个项都可以规约至 `a a`，但第二项需要两步来完成，而不是一步。

<!--
To side-step this problem, we'll define an auxiliary reduction
relation, called _parallel reduction_, that can perform many
reductions simultaneously and thereby satisfy the diamond property.
Furthermore, we show that a parallel reduction sequence exists between
any two terms if and only if a beta reduction sequence exists between them.
Thus, we can reduce the proof of confluence for beta reduction to
confluence for parallel reduction.
-->

为了回避这个问题，我们将定义一个辅助规约关系，
称为**平行规约（Parallel Reduction）** ，
它可以同时执行许多规约并因此满足菱形性质。
更进一步地，我们将证明在两个项间存在平行规约序列当且仅当这两个项间存在 β-规约序列。
因此，我们可以将 β-规约序列合流性的证明约化为平行规约合流性的证明。

<!--
## Imports
-->

## 导入

```
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import plfa.part2.Substitution using (Rename; Subst)
open import plfa.part2.Untyped
  using (_—→_; β; ξ₁; ξ₂; ζ; _—↠_; begin_; _—→⟨_⟩_; _—↠⟨_⟩_; _∎;
  abs-cong; appL-cong; appR-cong; —↠-trans;
  _⊢_; _∋_; `_; #_; _,_; ★; ƛ_; _·_; _[_];
  rename; ext; exts; Z; S_; subst; subst-zero)
```

<!--
## Parallel Reduction
-->

## 平行规约

<!--
The parallel reduction relation is defined as follows.
-->

平行规约关系被定义如下。

```
infix 2 _⇛_

data _⇛_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  pvar : ∀{Γ A}{x : Γ ∋ A}
      ---------
    → (` x) ⇛ (` x)

  pabs : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
    → N ⇛ N′
      ----------
    → ƛ N ⇛ ƛ N′

  papp : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
    → L ⇛ L′
    → M ⇛ M′
      -----------------
    → L · M ⇛ L′ · M′

  pbeta : ∀{Γ}{N N′  : Γ , ★ ⊢ ★}{M M′ : Γ ⊢ ★}
    → N ⇛ N′
    → M ⇛ M′
      -----------------------
    → (ƛ N) · M  ⇛  N′ [ M′ ]
```

<!--
The first three rules are congruences that reduce each of their
parts simultaneously. The last rule reduces a lambda term and
term in parallel followed by a beta step.
-->

前三种规则是同时规约每个部分的合同性。
最后一个规则平行地规约一个 λ-项和另一个项，接着是一步 β-规约。

<!--
We remark that the `pabs`, `papp`, and `pbeta` rules perform reduction
on all their subexpressions simultaneously. Also, the `pabs` rule is
akin to the `ζ` rule and `pbeta` is akin to `β`.
-->

我们注意到 `pabs`、`papp` 和 `pbeta` 规则同时对它们的所有子表达式执行归约。
此外，`pabs` 规则类似于 `ζ` 规则，`pbeta` 类似于 `β` 规则。

<!--
Parallel reduction is reflexive.
-->

平行规约是自反的。

```
par-refl : ∀{Γ A}{M : Γ ⊢ A} → M ⇛ M
par-refl {Γ} {A} {` x} = pvar
par-refl {Γ} {★} {ƛ N} = pabs par-refl
par-refl {Γ} {★} {L · M} = papp par-refl par-refl
```

<!--
We define the sequences of parallel reduction as follows.
-->

我们定义平行规约序列如下。

```
infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎

data _⇛*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M ⇛* M

  _⇛⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
```


<!--
#### Exercise `par-diamond-eg` (practice)
-->

#### 练习 `par-diamond-eg`（实践）

<!--
Revisit the counter example to the diamond property for reduction by
showing that the diamond property holds for parallel reduction in that
case.
-->

回顾上文中菱形性质的反例，证明在这种情况下平行规约具有菱形性质。

<!--
```
-- Your code goes here
```
-->

```
-- 请将代码写在此处。
```


<!--
## Equivalence between parallel reduction and reduction
-->

## 平行规约与规约间等价性

<!--
Here we prove that for any `M` and `N`, `M ⇛* N` if and only if `M —↠ N`.
The only-if direction is particularly easy. We start by showing
that if `M —→ N`, then `M ⇛ N`. The proof is by induction on
the reduction `M —→ N`.
-->

此处我们证明对于任何 `M` 和 `N`，`M ⇛* N` 当且仅当 `M —↠ N`。
必要性的证明非常容易，我们开始于说明若 `M —→ N`，则 `M ⇛ N`。
该证明通过对规约 `M —→ N` 进行归纳。

```
beta-par : ∀{Γ A}{M N : Γ ⊢ A}
  → M —→ N
    ------
  → M ⇛ N
beta-par {Γ} {★} {L · M} (ξ₁ r) = papp (beta-par {M = L} r) par-refl
beta-par {Γ} {★} {L · M} (ξ₂ r) = papp par-refl (beta-par {M = M} r)
beta-par {Γ} {★} {(ƛ N) · M} β = pbeta par-refl par-refl
beta-par {Γ} {★} {ƛ N} (ζ r) = pabs (beta-par r)
```

<!--
With this lemma in hand we complete the only-if direction,
that `M —↠ N` implies `M ⇛* N`. The proof is a straightforward
induction on the reduction sequence `M —↠ N`.
-->

证明了该引理后我们便可完成必要性的证明，
即 `M —↠ N` 蕴含 `M ⇛* N`。该证明是对 `M —↠ N` 规约序列的简单归纳。

```
betas-pars : ∀{Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M ⇛* N
betas-pars {Γ} {A} {M₁} {.M₁} (M₁ ∎) = M₁ ∎
betas-pars {Γ} {A} {.L} {N} (L —→⟨ b ⟩ bs) =
   L ⇛⟨ beta-par b ⟩ betas-pars bs
```

<!--
Now for the other direction, that `M ⇛* N` implies `M —↠ N`.  The
proof of this direction is a bit different because it's not the case
that `M ⇛ N` implies `M —→ N`. After all, `M ⇛ N` performs many
reductions. So instead we shall prove that `M ⇛ N` implies `M —↠ N`.
-->

现在考虑命题的充分性，即 `M ⇛* N` 蕴含 `M —↠ N`。
充分性的证明有一点不同，因为它不是 `M ⇛ N` 蕴含 `M —→ N` 的情形。
毕竟 `M ⇛ N` 执行了许多规约，
所以我们应当证明 `M ⇛ N` 蕴含 `M —↠ N`。

```
par-betas : ∀{Γ A}{M N : Γ ⊢ A}
  → M ⇛ N
    ------
  → M —↠ N
par-betas {Γ} {A} {.(` _)} (pvar{x = x}) = (` x) ∎
par-betas {Γ} {★} {ƛ N} (pabs p) = abs-cong (par-betas p)
par-betas {Γ} {★} {L · M} (papp {L = L}{L′}{M}{M′} p₁ p₂) =
    begin
    L · M   —↠⟨ appL-cong{M = M} (par-betas p₁) ⟩
    L′ · M  —↠⟨ appR-cong (par-betas p₂) ⟩
    L′ · M′
    ∎
par-betas {Γ} {★} {(ƛ N) · M} (pbeta{N′ = N′}{M′ = M′} p₁ p₂) =
    begin
    (ƛ N) · M                    —↠⟨ appL-cong{M = M} (abs-cong (par-betas p₁)) ⟩
    (ƛ N′) · M                   —↠⟨ appR-cong{L = ƛ N′} (par-betas p₂)  ⟩
    (ƛ N′) · M′                  —→⟨ β ⟩
     N′ [ M′ ]
    ∎
```

<!--
The proof is by induction on `M ⇛ N`.
-->

该证明通过对 `M ⇛ N` 进行归纳。

<!--
* Suppose `x ⇛ x`. We immediately have `x —↠ x`.

* Suppose `ƛ N ⇛ ƛ N′` because `N ⇛ N′`. By the induction hypothesis
  we have `N —↠ N′`. We conclude that `ƛ N —↠ ƛ N′` because
  `—↠` is a congruence.

* Suppose `L · M ⇛ L′ · M′` because `L ⇛ L′` and `M ⇛ M′`.
  By the induction hypothesis, we have `L —↠ L′` and `M —↠ M′`.
  So `L · M —↠ L′ · M` and then `L′ · M  —↠ L′ · M′`
  because `—↠` is a congruence.

* Suppose `(ƛ N) · M  ⇛  N′ [ M′ ]` because `N ⇛ N′` and `M ⇛ M′`.
  By similar reasoning, we have
  `(ƛ N) · M —↠ (ƛ N′) · M′`
  which we can following with the β reduction
  `(ƛ N′) · M′ —→ N′ [ M′ ]`.
-->

* 假定 `x ⇛ x`。我们立刻有 `x —↠ x`。

* 假定 `ƛ N ⇛ ƛ N′` 因为 `N ⇛ N′`。根据归纳假设我们有 `N —↠ N′`。
  我们得出 `ƛ N —↠ ƛ N′` 因为 `—↠` 具有合同性。

* 假定 `L · M ⇛ L′ · M′` 因为 `L ⇛ L′` 和 `M ⇛ M′`。
  根据归纳假设，我们有 `L —↠ L′` 和 `M —↠ M′`。
  所以有 `L · M —↠ L′ · M` 以及 `L′ · M  —↠ L′ · M′`
  因为 `—↠` 具有合同性。

* 假定 `(ƛ N) · M  ⇛  N′ [ M′ ]` 因为 `N ⇛ N′` 和 `M ⇛ M′`。
  根据类似的原因，我们有 `(ƛ N) · M —↠ (ƛ N′) · M′`，
  接着应用 β-规约我们得到 `(ƛ N′) · M′ —→ N′ [ M′ ]`。

<!--
With this lemma in hand, we complete the proof that `M ⇛* N` implies
`M —↠ N` with a simple induction on `M ⇛* N`.
-->

证明了该引理后我们便可通过对 `M ⇛* N` 的一步简单归纳完成 `M ⇛* N` 蕴含 `M —↠ N` 的证明。

```
pars-betas : ∀{Γ A} {M N : Γ ⊢ A}
  → M ⇛* N
    ------
  → M —↠ N
pars-betas (M₁ ∎) = M₁ ∎
pars-betas (L ⇛⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)
```


<!--
## Substitution lemma for parallel reduction
-->

## 平行规约的替换引理

<!--
Our next goal is to prove the diamond property for parallel
reduction. But to do that, we need to prove that substitution
respects parallel reduction. That is, if
`N ⇛ N′` and `M ⇛ M′`, then `N [ M ] ⇛ N′ [ M′ ]`.
We cannot prove this directly by induction, so we
generalize it to: if `N ⇛ N′` and
the substitution `σ` pointwise parallel reduces to `τ`,
then `subst σ N ⇛ subst τ N′`. We define the notion
of pointwise parallel reduction as follows.
-->

我们的下一个目标是对平行规约证明菱形性质。
为了完成该证明，我们还需证明替换遵从平行规约。
也就是说，如果有 `N ⇛ N′` 和 `M ⇛ M′`，那么 `N [ M ] ⇛ N′ [ M′ ]`。
我们不能直接通过归纳证明它，所以我们将其推广为：
如果 `N ⇛ N′` 并且替换 `σ` 逐点（Pointwise）平行规约至 `τ`，
则 `subst σ N ⇛ subst τ N′`。
我们如下定义逐点平行规约。

```
par-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
par-subst {Γ}{Δ} σ σ′ = ∀{A}{x : Γ ∋ A} → σ x ⇛ σ′ x
```

<!--
Because substitution depends on the extension function `exts`, which
in turn relies on `rename`, we start with a version of the
substitution lemma, called `par-rename`, that is specialized to
renamings.  The proof of `par-rename` relies on the fact that renaming
and substitution commute with one another, which is a lemma that we
import from Chapter [Substitution](/Substitution/)
and restate here.
-->

因为替换依赖于扩展函数 `exts`，而其又依赖于 `rename`，
我们开始于被称为 `par-rename` 的替换引理的一种版本，该引理专门用于重命名。
`par-rename` 依赖于重命名和替换可以相互交换的事实，
这是一个我们在 [Substitution](/Substitution/) 章节引入并在此处重申的引理。

```
rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {N = N} = plfa.part2.Substitution.rename-subst-commute {N = N}
```

<!--
Now for the `par-rename` lemma.
-->

现在证明 `par-rename` 引理。

```
par-rename : ∀{Γ Δ A} {ρ : Rename Γ Δ} {M M′ : Γ ⊢ A}
  → M ⇛ M′
    ------------------------
  → rename ρ M ⇛ rename ρ M′
par-rename pvar = pvar
par-rename (pabs p) = pabs (par-rename p)
par-rename (papp p₁ p₂) = papp (par-rename p₁) (par-rename p₂)
par-rename {Γ}{Δ}{A}{ρ} (pbeta{Γ}{N}{N′}{M}{M′} p₁ p₂)
    with pbeta (par-rename{ρ = ext ρ} p₁) (par-rename{ρ = ρ} p₂)
... | G rewrite rename-subst-commute{Γ}{Δ}{N′}{M′}{ρ} = G

```

<!--
The proof is by induction on `M ⇛ M′`. The first three cases
are straightforward so we just consider the last one for `pbeta`.
-->

证明通过对 `M ⇛ M′` 进行归纳来完成。前三种情况很简单，
所以我们只考虑最后一种，即 `pbeta`。

<!--
* Suppose `(ƛ N) · M  ⇛  N′ [ M′ ]` because `N ⇛ N′` and `M ⇛ M′`.
  By the induction hypothesis, we have
  `rename (ext ρ) N ⇛ rename (ext ρ) N′` and
  `rename ρ M ⇛ rename ρ M′`.
  So by `pbeta` we have
  `(ƛ rename (ext ρ) N) · (rename ρ M) ⇛ (rename (ext ρ) N) [ rename ρ M ]`.
  However, to conclude we instead need parallel reduction to
  `rename ρ (N [ M ])`. But thankfully, renaming and substitution
  commute with one another.
-->

* 假定 `(ƛ N) · M  ⇛  N′ [ M′ ]` 因为 `N ⇛ N′` 和 `M ⇛ M′`。
  根据归纳假设，我们有 `rename (ext ρ) N ⇛ rename (ext ρ) N′` 和 `rename ρ M ⇛ rename ρ M′`。
  所以根据 `pbeta` 我们有 `(ƛ rename (ext ρ) N) · (rename ρ M) ⇛ (rename (ext ρ) N) [ rename ρ M ]`。
  然而，为了得出结论我们需要平行规约至 `rename ρ (N [ M ])`。
  值得庆幸的是，重命名和规约可以相互交换。


<!--
With the `par-rename` lemma in hand, it is straightforward to show
that extending substitutions preserves the pointwise parallel
reduction relation.
-->

有了 `par-rename` 引理，很容易证明扩展替换保留了逐点平行归约关系。

```
par-subst-exts : ∀{Γ Δ} {σ τ : Subst Γ Δ}
  → par-subst σ τ
    ------------------------------------------
  → ∀{B} → par-subst (exts σ {B = B}) (exts τ)
par-subst-exts s {x = Z} = pvar
par-subst-exts s {x = S x} = par-rename s
```

<!--
The next lemma that we need for proving that substitution respects
parallel reduction is the following which states that
simultaneous substitution commutes with single substitution. We import this
lemma from Chapter [Substitution](/Substitution/)
and restate it below.
-->

为了证明替换遵从平行规约关系，我们需要证明的下一个引理如下文所示，
它声称同时规约可以与单步规约相交换。
我们从 [Substitution](/Substitution/) 章节导入这个引理，
并重申如下。

```
subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
  → subst (exts σ) N [ subst σ M ] ≡ subst σ (N [ M ])
subst-commute {N = N} = plfa.part2.Substitution.subst-commute {N = N}
```

<!--
We are ready to prove that substitution respects parallel reduction.
-->

我们准备好去证明替换遵从平行规约。

```
subst-par : ∀{Γ Δ A} {σ τ : Subst Γ Δ} {M M′ : Γ ⊢ A}
  → par-subst σ τ  →  M ⇛ M′
    --------------------------
  → subst σ M ⇛ subst τ M′
subst-par {Γ} {Δ} {A} {σ} {τ} {` x} s pvar = s
subst-par {Γ} {Δ} {A} {σ} {τ} {ƛ N} s (pabs p) =
  pabs (subst-par {σ = exts σ} {τ = exts τ}
        (λ {A}{x} → par-subst-exts s {x = x}) p)
subst-par {Γ} {Δ} {★} {σ} {τ} {L · M} s (papp p₁ p₂) =
  papp (subst-par s p₁) (subst-par s p₂)
subst-par {Γ} {Δ} {★} {σ} {τ} {(ƛ N) · M} s (pbeta{N′ = N′}{M′ = M′} p₁ p₂)
    with pbeta (subst-par{σ = exts σ}{τ = exts τ}{M = N}
                        (λ{A}{x} → par-subst-exts s {x = x}) p₁)
               (subst-par {σ = σ} s p₂)
... | G rewrite subst-commute{N = N′}{M = M′}{σ = τ} = G
```

<!--
We proceed by induction on `M ⇛ M′`.
-->

我们通过对 `M ⇛ M′` 归纳来证明。

<!--
* Suppose `x ⇛ x`. We conclude that `σ x ⇛ τ x` using
  the premise `par-subst σ τ`.

* Suppose `ƛ N ⇛ ƛ N′` because `N ⇛ N′`.
  To use the induction hypothesis, we need `par-subst (exts σ) (exts τ)`,
  which we obtain by `par-subst-exts`.
  So we have `subst (exts σ) N ⇛ subst (exts τ) N′`
  and conclude by rule `pabs`.

* Suppose `L · M ⇛ L′ · M′` because `L ⇛ L′` and `M ⇛ M′`.
  By the induction hypothesis we have
  `subst σ L ⇛ subst τ L′` and `subst σ M ⇛ subst τ M′`, so
  we conclude by rule `papp`.

* Suppose `(ƛ N) · M  ⇛  N′ [ M′ ]` because `N ⇛ N′` and `M ⇛ M′`.
  Again we obtain `par-subst (exts σ) (exts τ)` by `par-subst-exts`.
  So by the induction hypothesis, we have
  `subst (exts σ) N ⇛ subst (exts τ) N′` and
  `subst σ M ⇛ subst τ M′`. Then by rule `pbeta`, we have parallel reduction
  to `subst (exts τ) N′ [ subst τ M′ ]`.
  Substitution commutes with itself in the following sense.
  For any σ, N, and M, we have

        (subst (exts σ) N) [ subst σ M ] ≡ subst σ (N [ M ])

  So we have parallel reduction to `subst τ (N′ [ M′ ])`.
-->

* 假定 `x ⇛ x`。我们使用前提 `par-subst σ τ` 来得出 `σ x ⇛ τ x`。

* 假定 `ƛ N ⇛ ƛ N′` 因为 `N ⇛ N′`。
  为了使用归纳假设，我们需要 `par-subst (exts σ) (exts τ)`，
  它通过 `par-subst-exts` 得出。
  所以我们有 `subst (exts σ) N ⇛ subst (exts τ) N′`
  并且通过规则 `pabs` 来完成证明。

* 假定 `L · M ⇛ L′ · M′` 因为 `L ⇛ L′` 和 `M ⇛ M′`。
  根据归纳假设我们有 `subst σ L ⇛ subst τ L′` 和 `subst σ M ⇛ subst τ M′`，
  所以我们通过规则 `papp` 来完成证明。

* 假定 `(ƛ N) · M  ⇛  N′ [ M′ ]` 因为 `N ⇛ N′` 和 `M ⇛ M′`。
  同样我们根据 `par-subst-exts` 来得到 `par-subst (exts σ) (exts τ)`。
  所以根据归纳假设，我们有
  `subst (exts σ) N ⇛ subst (exts τ) N′` 和 `subst σ M ⇛ subst τ M′`。
  接着根据 `pbeta` 规则，我们平行规约至 `subst (exts τ) N′ [ subst τ M′ ]`。
  替换在以下意义中与自身交换：
  对于任意 σ、 N 和 M， 我们有

        (subst (exts σ) N) [ subst σ M ] ≡ subst σ (N [ M ])

  所以我们平行规约得到 `subst τ (N′ [ M′ ])`。


<!--
Of course, if `M ⇛ M′`, then `subst-zero M` pointwise parallel reduces
to `subst-zero M′`.
-->

显然，若 `M ⇛ M′`，则 `subst-zero M` 逐点平行规约至 `subst-zero M′`。

```
par-subst-zero : ∀{Γ}{A}{M M′ : Γ ⊢ A}
       → M ⇛ M′
       → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero {M} {M′} p {A} {Z} = p
par-subst-zero {M} {M′} p {A} {S x} = pvar
```

<!--
We conclude this section with the desired corollary, that substitution
respects parallel reduction.
-->

我们以所期望的推论来结束本节，即替换遵从平行规约。

```
sub-par : ∀{Γ A B} {N N′ : Γ , A ⊢ B} {M M′ : Γ ⊢ A}
  → N ⇛ N′
  → M ⇛ M′
    --------------------------
  → N [ M ] ⇛ N′ [ M′ ]
sub-par pn pm = subst-par (par-subst-zero pm) pn
```

<!--
## Parallel reduction satisfies the diamond property
-->

## 平行规约满足菱形性质

<!--
The heart of the confluence proof is made of stone, or rather, of
diamond!  We show that parallel reduction satisfies the diamond
property: that if `M ⇛ N` and `M ⇛ N′`, then `N ⇛ L` and `N′ ⇛ L` for
some `L`.  The typical proof is an induction on `M ⇛ N` and `M ⇛ N′`
so that every possible pair gives rise to a witness `L` given by
performing enough beta reductions in parallel.
-->

合流性证明的核心是石头制成的，更确切地说，是钻石！
【译注：在英文中 diamond 一词既指钻石，又指菱形。】
我们将证明平行规约满足菱形性质，即若有 `M ⇛ N` 和 `M ⇛ N′`，
那么对某个 `L` 有 `N ⇛ L` 和 `N′ ⇛ L`。
典型的证明通过对 `M ⇛ N` 和 `M ⇛ N′` 归纳来完成，
因此每一个可能的对都会在执行足够多次平行 β-规约后产生一个证明 `L`。

<!--
However, a simpler approach is to perform as many beta reductions in
parallel as possible on `M`, say `M ⁺`, and then show that `N` also
parallel reduces to `M ⁺`. This is the idea of Takahashi's _complete
development_. The desired property may be illustrated as
-->

然而，一个更简单的方法是对 `M` 执行尽可能多次平行 β-规约，
称其为 `M ⁺`，然后证明 `N` 也可以平行规约至 `M ⁺`。
这就是 Takahashi 的 _complete development_ 的想法。
所需的性质可以表示为：

        M
       /|
      / |
     /  |
    N   2
     \  |
      \ |
       \|
        M⁺

<!--
where downward lines are instances of `⇛`, so we call it the _triangle
property_.
-->

其中向下的线是 `⇛` 的实例。因此我们称其为**三角性质（Triangle Property）**。

```
_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺       =  ` x
(ƛ M) ⁺       = ƛ (M ⁺)
((ƛ N) · M) ⁺ = N ⁺ [ M ⁺ ]
(L · M) ⁺     = L ⁺ · (M ⁺)

par-triangle : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇛ N
    -------
  → N ⇛ M ⁺
par-triangle pvar          = pvar
par-triangle (pabs p)      = pabs (par-triangle p)
par-triangle (pbeta p1 p2) = sub-par (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ƛ _ } (pabs p1) p2) =
  pbeta (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ` _}   p1 p2) = papp (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = _ · _} p1 p2) = papp (par-triangle p1) (par-triangle p2)
```

<!--
The proof of the triangle property is an induction on `M ⇛ N`.
-->

三角性质的证明通过对 `M ⇛ N` 归纳来完成。

<!--
* Suppose `x ⇛ x`. Clearly `x ⁺ = x`, so `x ⇛ x ⁺`.

* Suppose `ƛ M ⇛ ƛ N`. By the induction hypothesis we have `N ⇛ M ⁺`
  and by definition `(λ M) ⁺ = λ (M ⁺)`, so we conclude that `λ N ⇛ λ
  (M ⁺)`.

* Suppose `(λ N) · M ⇛ N′ [ M′ ]`. By the induction hypothesis, we have
  `N′ ⇛ N ⁺` and `M′ ⇛ M ⁺`. Since substitution respects parallel reduction,
  it follows that `N′ [ M′ ] ⇛ N ⁺ [ M ⁺ ]`, but the right hand side
  is exactly `((λ N) · M) ⁺`, hence `N′ [ M′ ] ⇛ ((λ N) · M) ⁺`.

* Suppose `(λ L) · M ⇛ (λ L′) · M′`. By the induction hypothesis
  we have `L′ ⇛ L ⁺` and `M′ ⇛ M ⁺`; by definition `((λ L) · M) ⁺ = L ⁺ [ M ⁺ ]`.
  It follows `(λ L′) · M′ ⇛ L ⁺ [ M ⁺ ]`.

* Suppose `x · M ⇛ x · M′`. By the induction hypothesis we have `M′ ⇛ M ⁺`
  and `x ⇛ x ⁺` so that `x · M′ ⇛ x · M ⁺`.
  The remaining case is proved in the same way, so we ignore it.  (As
  there is currently no way in Agda to expand the catch-all pattern in
  the definition of `_⁺` for us before checking the right-hand side,
  we have to write down the remaining case explicitly.)
-->

  * 假定 `x ⇛ x`。显然 `x ⁺ = x`，所以 `x ⇛ x ⁺`。

  * 假定 `ƛ M ⇛ ƛ N`。根据归纳假设我们有 `N ⇛ M ⁺`，
  并且根据定义我们有 `(λ M) ⁺ = λ (M ⁺)`，所以我们得出 `λ N ⇛ λ(M ⁺)`。

  * 假定 `(λ N) · M ⇛ N′ [ M′ ]`。根据归纳假设我们有 `N′ ⇛ N ⁺` 和 `M′ ⇛ M ⁺`。
  因为替换遵从平行规约，于是得到 `N′ [ M′ ] ⇛ N ⁺ [ M ⁺ ]`，
  而右侧即为 `((λ N) · M) ⁺`，因此有 `N′ [ M′ ] ⇛ ((λ N) · M) ⁺`。

  * 假定 `(λ L) · M ⇛ (λ L′) · M′`。
  根据归纳假设我们有 `L′ ⇛ L ⁺` 和 `M′ ⇛ M ⁺`；
  根据定义有 `((λ L) · M) ⁺ = L ⁺ [ M ⁺ ]`。
  接着得出 `(λ L′) · M′ ⇛ L ⁺ [ M ⁺ ]`。

  * 假定 `x · M ⇛ x · M′`。
  根据归纳假设我们有 `M′ ⇛ M ⁺` 和 `x ⇛ x ⁺`，因此 `x · M′ ⇛ x · M ⁺`。
  剩余的情况可以以相同方式证明，所以我们忽略它。
  （由于 Agda 目前没有办法在检查右侧之前为我们扩展 `_⁺` 定义中的 catch-all 模式，我们必须明确地写下剩余的情况。）

<!--
The diamond property then follows by halving the diamond into two triangles.
-->

菱形性质接着通过将菱形折半成两个三角形得出。

        M
       /|\
      / | \
     /  |  \
    N   2   N′
     \  |  /
      \ | /
       \|/
        M⁺

<!--
That is, the diamond property is proved by applying the
triangle property on each side with the same confluent term `M ⁺`.
-->

也就是说，菱形性质通过在两侧应用具有相同合流项 `M ⁺`的三角性质而证明。

```
par-diamond : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛ N′
    ---------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛ L) × (N′ ⇛ L)
par-diamond {M = M} p1 p2 = ⟨ M ⁺ , ⟨ par-triangle p1 , par-triangle p2 ⟩ ⟩
```

<!--
This step is optional, though, in the presence of triangle property.
-->

不过，在存在三角性质的情况下，该步骤是可选的。

<!--
#### Exercise (practice)
-->

#### 练习（实践）

<!--
* Prove the diamond property `par-diamond` directly by induction on `M ⇛ N` and `M ⇛ N′`.

* Draw pictures that represent the proofs of each of the six cases in
  the direct proof of `par-diamond`. The pictures should consist of nodes
  and directed edges, where each node is labeled with a term and each
  edge represents parallel reduction.
-->

* 通过对 `M ⇛ N` 和 `M ⇛ N′` 归纳直接证明菱形性质 `par-diamond`。

* 作图表示 `par-diamond` 的直接证明中的六种情况。
  图应当包含节点和有向边，其中节点用项标记，边代表平行规约。

<!--
## Proof of confluence for parallel reduction
-->

## 平行规约合流性的证明

<!--
As promised at the beginning, the proof that parallel reduction is
confluent is easy now that we know it satisfies the triangle property.
We just need to prove the strip lemma, which states that
if `M ⇛ N` and `M ⇛* N′`, then
`N ⇛* L` and `N′ ⇛ L` for some `L`.
The following diagram illustrates the strip lemma
-->

像在开始承诺的那样，平行规约合流性的证明现在十分简单，
因为我们知道它满足三角性质。
我们只需证明带状引理（Strip Lemma），它声称若有 `M ⇛ N` 和 `M ⇛* N′`，
则对于某个 `L` 有 `N ⇛* L` 和 `N′ ⇛ L`。
下图解释了带状引理：

        M
       / \
      1   *
     /     \
    N       N′
     \     /
      *   1
       \ /
        L

<!--
where downward lines are instances of `⇛` or `⇛*`, depending on how
they are marked.
-->

此处向下的线是 `⇛` 或 `⇛*` 的实例，取决于它们如何被标记。

<!--
The proof of the strip lemma is a straightforward induction on `M ⇛* N′`,
using the triangle property in the induction step.
-->

带状引理的证明是对 `M ⇛* N′` 的简单归纳，并在归纳步骤使用三角性质。

```
strip : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
strip{Γ}{A}{M}{N}{N′} mn (M ∎) = ⟨ N , ⟨ N ∎ , mn ⟩ ⟩
strip{Γ}{A}{M}{N}{N′} mn (M ⇛⟨ mm' ⟩ m'n')
  with strip (par-triangle mm') m'n'
... | ⟨ L , ⟨ ll' , n'l' ⟩ ⟩ = ⟨ L , ⟨ N ⇛⟨ par-triangle mn ⟩ ll' , n'l' ⟩ ⟩
```

<!--
The proof of confluence for parallel reduction is now proved by
induction on the sequence `M ⇛* N`, using the above lemma in the
induction step.
-->

平行规约合流性的证明现在通过对序列 `M ⇛* N` 归纳来完成，并在归纳步骤使用上述引理。

```
par-confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L ⇛* M₁
  → L ⇛* M₂
    ------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ ⇛* N) × (M₂ ⇛* N)
par-confluence {Γ}{A}{L}{.L}{N} (L ∎) L⇛*N = ⟨ N , ⟨ L⇛*N , N ∎ ⟩ ⟩
par-confluence {Γ}{A}{L}{M₁′}{M₂} (L ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂
    with strip L⇛M₁ L⇛*M₂
... | ⟨ N , ⟨ M₁⇛*N , M₂⇛N ⟩ ⟩
      with par-confluence M₁⇛*M₁′ M₁⇛*N
...   | ⟨ N′ , ⟨ M₁′⇛*N′ , N⇛*N′ ⟩ ⟩ =
        ⟨ N′ , ⟨ M₁′⇛*N′ , (M₂ ⇛⟨ M₂⇛N ⟩ N⇛*N′) ⟩ ⟩
```

<!--
The step case may be illustrated as follows:
-->

归纳步骤可以如下图解释：

            L
           / \
          1   *
         /     \
        M₁ (a)  M₂
       / \     /
      *   *   1
     /     \ /
    M₁′(b)  N
     \     /
      *   *
       \ /
        N′

<!--
where downward lines are instances of `⇛` or `⇛*`, depending on how
they are marked. Here `(a)` holds by `strip` and `(b)` holds by
induction.
-->

此处向下的线是 `⇛` 或 `⇛*` 的实例，取决于它们如何被标记。
此处 `(a)` 根据 `strip` 而成立，`(b)` 根据归纳假设而成立。


<!--
## Proof of confluence for reduction
-->

## 规约合流性的证明

<!--
Confluence of reduction is a corollary of confluence for parallel
reduction. From
`L —↠ M₁` and `L —↠ M₂` we have
`L ⇛* M₁` and `L ⇛* M₂` by `betas-pars`.
Then by confluence we obtain some `L` such that
`M₁ ⇛* N` and `M₂ ⇛* N`, from which we conclude that
`M₁ —↠ N` and `M₂ —↠ N` by `pars-betas`.
-->

规约的合流性是平行规约合流性的一个推论。
从 `L —↠ M₁` 和 `L —↠ M₂` 根据 `betas-pars` 我们有 `L ⇛* M₁` 和 `L ⇛* M₂`。
接着根据合流性我们得到对于某个 `L` 有 `M₁ ⇛* N` 和 `M₂ ⇛* N`。
因此我们根据 `pars-betas` 得出 `M₁ —↠ N` 和 `M₂ —↠ N`。

```
confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L —↠ M₁
  → L —↠ M₂
    -----------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ —↠ N) × (M₂ —↠ N)
confluence L↠M₁ L↠M₂
    with par-confluence (betas-pars L↠M₁) (betas-pars L↠M₂)
... | ⟨ N , ⟨ M₁⇛N , M₂⇛N ⟩ ⟩ =
      ⟨ N , ⟨ pars-betas M₁⇛N , pars-betas M₂⇛N ⟩ ⟩
```


<!--
## Notes
-->

## 注记

<!--
Broadly speaking, this proof of confluence, based on parallel
reduction, is due to W. Tait and P. Martin-Löf (see Barendregt 1984,
Section 3.2).  Details of the mechanization come from several sources.
The `subst-par` lemma is the "strong substitutivity" lemma of Shafer,
Tebbi, and Smolka (ITP 2015). The proofs of `par-triangle`, `strip`,
and `par-confluence` are based on the notion of complete development
by Takahashi (1995) and Pfenning's 1992 technical report about the
Church-Rosser theorem. In addition, we consulted Nipkow and
Berghofer's mechanization in Isabelle, which is based on an earlier
article by Nipkow (JAR 1996).
-->

总而言之，这种基于平行规约的合流性的证明
归功于 W. Tait 和 P. Martin-Löf （参见 Barendregt 1984，章节 3.2）。
机械化的细节有多个来源。
`subst-par` 引理是 Shafer、Tebbi 和 Smolka (ITP 2015) 的 “强替换性（Strong Substitutivity）” 引理。
`par-triangle`、`strip` 和 `par-confluence` 的证明是基于
Takahashi (1995) 的 complete development
和 Pfenning 1992 年关于 Church-Rosser 定理的技术报告。
此外，我们咨询了 Nipkow 和 Berghofer 在 Isabelle 中的机械化，
它基于 Nipkow 的早期文章（JAR 1996）。

## Unicode

<!--
This chapter uses the following unicode:
-->

本章中使用了以下 Unicode：

    ⇛  U+21DB  RIGHTWARDS TRIPLE ARROW (\r== or \Rrightarrow)
    ⁺  U+207A  SUPERSCRIPT PLUS SIGN   (\^+)
