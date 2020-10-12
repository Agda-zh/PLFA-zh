---
layout: page
title: 使用说明
permalink: /GettingStarted/
translators : ["Rongxiao Fu", "Oling Cat"]
---

<!-- Status & Version Badges -->
[![Calendar Version][plfa-calver]][plfa-latest]
[![Build Status][plfa-zh-status]][plfa-zh-travis]
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]

《编程语言基础：Agda 语言描述》的使用方法与《Programming Language Foundations in Agda》一致。

**本书可访问 [PLFA-zh][plfa-zh] 在线阅读。**

**要参与翻译，请先阅读[翻译规范][trans-spec]。**


<!--
## Dependencies for users
-->

## 用户依赖

<!--
You can read PLFA [online][plfa] without installing anything.
However, if you wish to interact with the code or complete the exercises, you need several things:
-->

你可以[在线阅读][plfa-zh] PLFA，无需安装任何东西。
然而，如果你想要交互式编写代码或完成习题，那么就需要几样东西：

<!--
  - [Agda][agda]
  - [Agda standard library][agda-stdlib]
  - [PLFA][plfa-dev]
-->

  - [Agda][agda]
  - [Agda 标准库][agda-stdlib]
  - [PLFA][plfa-dev]（英文版）
  - [PLFA-zh][plfa-zh-dev]（中文版）

<!--
PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.
-->

PLFA 只针对特定的 Agda 和 标准库版本进行了测试，相应版本已在前面的徽章中指明。
Agda 和标准库变化得十分迅速，而这些改变经常搞坏 PLFA，因此使用旧版或新版通常会出现问题。

<!--
### Installing Agda using Stack
-->

### 用 Stack 安装 Agda

<!--
The easiest way to install any specific version of Agda is using [Stack][haskell-stack]. You can get the required version of Agda from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda]:
-->

安装特定 Agda 版本的最简方式是使用 [Stack][haskell-stack]。你可以从 GitHub 上获取需要的版本，
可以通过克隆源码库并切换到合适的分支，也可以直接下载 [Zip 包][agda]：

```bash
git clone https://github.com/agda/agda.git
cd agda
git checkout v2.6.1
```

<!--
To install Agda, run Stack from the Agda source directory:
-->

要安装 Agda，请在其源码目录中运行 Stack：

```bash
stack install --stack-yaml stack-8.8.3.yaml
```

<!--
If you want Stack to use you system installation of GHC, you can pass the `--system-ghc` flag and select the appropriate `stack-*.yaml` file. For instance, if you have GHC 8.2.2 installed, run:
-->

如果你想让 Stack 使用你系统上安装的 GHC 版本，可以传递 `--system-ghc` 选项并选择对应的
`stack-*.yaml` 文件。例如，若你安装了 GHC 8.2.2，请运行：

```bash
stack install --system-ghc --stack-yaml stack-8.2.2.yaml
```

<!--
### Installing the Standard Library and PLFA
-->

### 安装标准库和 PLFA-zh

<!--
You can get the required version of the Agda standard library from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda-stdlib]:
-->

你可以从 GitHub 上获取所需要的版本，可以通过克隆源码库并切换到合适的分支，也可以直接下载[ Zip
 包][agda-stdlib]：

```bash
git clone https://github.com/agda/agda-stdlib.git
cd agda-stdlib
git checkout v1.3
```

<!--
You can get the latest version of Programming Language Foundations in Agda from GitHub, either by cloning the repository, or by downloading [the zip archive][plfa-dev]:
-->

你也可以从 GitHub 克隆源码库，或者下载
[Zip 包][plfa-dev]来获取最新版的《编程语言基础：Agda 语言描述》：

```bash
git clone https://github.com/plfa/plfa.github.io
```

<!--
Finally, we need to let Agda know where to find the standard library. For this, you can follow the instructions [here][agda-docs-package-system].
-->

最后，我们需要让 Agda 知道如何找到标准库。你可以按照[这里][agda-docs-package-system]给出的步骤来设置。

<!--
It is possible to set up PLFA as an Agda library as well.  If you want to complete the exercises found in the `courses` folder, or to import modules from the book, you need to do this.  To do so, add the path to `plfa.agda-lib` to `~/.agda/libraries` and add `plfa` to `~/.agda/defaults`, both on lines of their own.
-->

如果你想完成 `courses` 目录中的习题，或者想导入书中的模块，
那么需要将 PLFA 设置为 Agda 库。完成此设置需要将 `plfa.agda-lib`
所在的路径作为单独的一行添加到 `~/.agda/libraries`，并将 `plfa`
作为单独的一行添加到 `~/.agda/defaults`。


<!--
## Setting up and using Emacs
-->

## 设置并使用 Emacs

<!--
The recommended editor for Agda is Emacs with `agda-mode`. Agda ships with `agda-mode`, so if you’ve installed Agda, all you have to do to configure `agda-mode` is run:
-->

推荐的 Agda 编辑器是 Emacs 加上 `agda-mode`。Agda 自带了 `agda-mode`，
因此如果你已经安装了 Agda，那么之需要运行以下命令就能配置好 `agda-mode` 了：

```bash
agda-mode setup
```

<!--
To load and type-check the file, use [`C-c C-l`][agda-docs-emacs-notation].
-->

要加载文件并对其执行类型检查，请使用 [`C-c C-l`][agda-docs-emacs-notation]。

<!--
Agda is edited interactively, using [“holes”][agda-docs-holes], which are bits of the program that are not yet filled in. If you use a question mark as an expression, and load the buffer using `C-c C-l`, Agda replaces the question mark with a hole. There are several things you can to while the cursor is in a hole:
-->

Agda 的编辑是通过使用「[洞][agda-docs-holes]」来交互的，它表示程序中尚未填充的片段。
如果用问号作为表达式，并用 `C-c C-l` 加载缓冲区，Agda 会将问号替换为一个「洞」。
当光标在洞中时，你可以做以下这些事情：

<!--
    C-c C-c x    split on variable x
    C-c C-space  fill in hole
    C-c C-r      refine with constructor
    C-c C-a      automatically fill in hole
    C-c C-,      goal type and context
    C-c C-.      goal type, context, and inferred type
-->

    C-c C-c x    在变量 x 上分项（自动模式匹配）
    C-c C-空格   填洞
    C-c C-r      用构造子精化
    C-c C-a      自动填洞
    C-c C-,      目标类型和上下文
    C-c C-.      目标类型，上下文，以及推断的类型

<!--
See [the emacs-mode docs][agda-docs-emacs-mode] for more details.
-->

更多细节请见 [emacs-mode 文档][agda-docs-emacs-mode]。

<!--
If you want to see messages beside rather than below your Agda code, you can do the following:
-->

如果你想在 Agda 代码的侧边而非底栏查看信息，那么可以这样做：

<!--
  - Open your Agda file, and load it using `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing;
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame;
  - type `C-x b` and switch to the buffer called “Agda information”.
-->

  - 打开 Agda 文件并按 `C-c C-l`；
  - 按 `C-x 1` 来仅显示当前 Agda 文件；
  - 按 `C-x 3` 来垂直分割窗口；
  - 将光标移动到右侧窗口；
  - 按 `C-x b` 并输入「Agda information」切换到该缓冲区。

<!--
Now, error messages from Agda will appear next to your file, rather than squished beneath it.
-->

现在，Agda 的错误消息将会在代码右侧显示，而非被挤压在底部的狭小空间里。


<!--
### Auto-loading `agda-mode` in Emacs
-->

### 在 Emacs 中自动加载 `agda-mode`

<!--
Since version 2.6.0, Agda has support for literate editing with Markdown, using the `.lagda.md` extension. One side-effect of this extension is that most editors default to Markdown editing mode, whereas
-->

从版本 2.6.0 开始，Agda 支持 Markdown 风格的文学编程，文件使用 `.lagda.md` 扩展名。
该扩展名的一个副作用就是大部分编辑器默认会进入 Markdown 编辑模式。

<!--
In order to have `agda-mode` automatically loaded whenever you open a file ending with `.agda` or `.lagda.md`, put the following on your Emacs configuration file:
-->

而为了让 `agda-mode` 在你打开 `.agda` 或 `.lagda.md` 文件时自动加载，
请将以下内容放到你的 Emacs 配置文件中。

```elisp
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

<!--
(The configuration file for Emacs is normally located in `~/.emacs` or `~/.emacs.d/init.el`, but Aquamacs users might need to move their startup settings to the `Preferences.el` file in `~/Library/Preferences/Aquamacs Emacs/Preferences`.)
-->

（Emacs 的配置文件通常位于 `~/.emacs` 或 `~/.emacs.d/init.el`，然而
Aquamacs 用户需要将启动设置放到位于 `~/Library/Preferences/Aquamacs Emacs/Preferences`
的 `Preferences.el` 文件中。


<!--
### Using mononoki in Emacs
-->

### 在 Emacs 中使用 mononoki

<!--
It is recommended that you install the font [mononoki][mononoki], and add the following to the end of your emacs configuration file at `~/.emacs`:
-->

我们推荐安装 [mononoki][mononoki] 字体，并将以下内容添加到你的 Emacs 配置文件
`~/.emacs` 的末尾。

``` elisp
;; default to mononoki
(set-face-attribute 'default nil
                    :family "mononoki"
                    :height 120
                    :weight 'normal
                    :width  'normal)
```

另外带有连体符号的 [FiraCode][FiraCode] 也是个不错的选择。

<!--
### Unicode characters
-->

### Unicode 字符

<!--
If you're having trouble typing the Unicode characters into Emacs, the end of each chapter should provide a list of the unicode characters introduced in that chapter.
-->

如果你在 Emacs 中输入 Unicode 时遇到了问题，可以在每章的最后找到当前章节中用到的
Unicode 字符。

<!--
`agda-mode` and emacs have a number of useful commands. Two of them are especially useful when you solve exercises.
-->

`agda-mode` 和 Emacs 有很多有用的命令。其中有两个在解题时特别有用。

<!--
For a full list of supported characters, use `agda-input-show-translations` with:
-->

支持的字符的完整列表可使用 `agda-input-show-translations` 命令查看：

    M-x agda-input-show-translations

<!--
All the supported characters in `agda-mode` are shown.
-->

`agda-mode` 支持的所有字符都会列出来。

<!--
If you want to know how you input a specific Unicode character in agda file, move the cursor onto the character and type the following command:
-->

如果你想知道如何在 agda 文件输入一个特定的 Unicode 字符，请将光标移动到该字符上并输入以下命令：

    M-x quail-show-key

<!--
You'll see the key sequence of the character in mini buffer.
-->

你会在迷你缓冲区中看到该字符对应的按键序列。


<!--
## Dependencies for developers
-->

## 开发者依赖

<!--
PLFA is available as both a website and an EPUB e-book, both of which can be built on Linux and macOS.
PLFA is written in literate Agda with [Kramdown Markdown][kramdown].
-->

PLFA 可同时在网站上和作为 EPUB 电子书来阅读，二者均可在 Linux 和 macOS 上构建。
PLFA 是以 [Kramdown Markdown][kramdown] 格式的文学化 Agda 编写的。


<!--
### Git hooks
-->

### Git 钩子脚本

<!--
The repository comes with several Git hooks:
-->

<!--
The repository comes with several Git hooks:

 1. The [fix-whitespace][fix-whitespace] program is run to check for whitespace violations.

 2. The test suite is run to check if everything type checks.
-->

本源码库包含了几个 Git 钩子：

 1. [fix-whitespace][fix-whitespace] 程序用来检查错误的空格。

 2. 可运行的测试套件用来保证一切都能通过类型检查。

<!--
You can install these Git hooks by calling `make init`.
You can install [fix-whitespace][fix-whitespace] by running:
-->

你可以运行 `make init` 来安装这些 Git 钩子。
你可以运行以下命令来安装 [fix-whitespace][fix-whitespace]：

```bash
git clone https://github.com/agda/fix-whitespace
cd fix-whitespace/
stack install --stack-yaml stack-8.8.3.yaml
```

<!--
If you want Stack to use your system installation of GHC, you can pass the `--system-ghc` flag and select the appropriate `stack-*.yaml` file, like when installing [Agda](#installing-agda-using-stack).
-->

如果你想让 Stack 使用你系统中安装的 GHC，那么可以传入 `--system-ghc` 参数并选择对应的
`stack-*.yaml` 文件，就像在安装 [Agda](#installing-agda-using-stack) 时那样。


<!--
### Building the website
-->

### 构建网站

<!--
The website version of the book is built in three stages:
-->

本书的网站版本是通过三步来构建的：

<!--
 1. The `.lagda.md` files are compiled to Markdown using Agda’s highlighter.
    (This requires several POSIX tools, such as `bash`, `sed`, and `grep`.)

 2. The Markdown files are converted to HTML using [Jekyll][ruby-jekyll], a widely-used static site builder.
    (This requires [Ruby][ruby] and [Jekyll][ruby-jekyll].)

 3. The HTML is checked using [html-proofer][ruby-html-proofer].
    (This requires [Ruby][ruby] and [html-proofer][ruby-html-proofer].)
-->

 1. `.lagda.md` 文件会使用 Agda 的高亮被编译到 Markdown。
    （这需要几个 POSIX 工具，包括 `bash`、`sed` 和 `grep`。）

 2. Markdown 文件会通过 [Jekyll][ruby-jekyll] 转换为 HTML，它是一个被广发使用的静态网站构建工具。
    （这需要 [Ruby][ruby] 和 [Jekyll][ruby-jekyll]。）

 3. HTML 会使用 [html-proofer][ruby-html-proofer] 来检查。
    （这需要 [Ruby][ruby] 和 [html-proofer][ruby-html-proofer]。）

<!--
Most recent versions of [Ruby][ruby] should work. The easiest way to install [Jekyll][ruby-jekyll] and [html-proofer][ruby-html-proofer] is using [Bundler][ruby-bundler]. You can install [Bundler][ruby-bundler] by running:
-->

最新版本的 [Ruby][ruby] 应该就可以了。安装 [Jekyll][ruby-jekyll] 和
[html-proofer][ruby-html-proofer] 最简单的方式是使用 [Bundler][ruby-bundler]。
你可以通过运行以下命令来安装 [Bundler][ruby-bundler]：

```bash
gem install bundler
```

<!--
You can install the remainder of the dependencies—[Jekyll][ruby-jekyll], [html-proofer][ruby-html-proofer], *etc.*—by running:
-->

你也可以运行以下命令来安装 [Jekyll][ruby-jekyll]、[html-proofer][ruby-html-proofer] 等其余的依赖：

```bash
bundle install
```

<!--
Once you have installed all of the dependencies, you can build a copy of the book, and host it locally, by running:
-->

当你安装完所有的依赖后，就能构建本书，并在本地架起网站了，运行以下命令即可：

```bash
make build
make serve
```

<!--
The Makefile offers more than just these options:

```bash
make                      # see make test
make build                # builds lagda->markdown and the website
make build-incremental    # builds lagda->markdown and the website incrementally
make test                 # checks all links are valid
make test-offline         # checks all links are valid offline
make serve                # starts the server
make server-start         # starts the server in detached mode
make server-stop          # stops the server, uses pkill
make clean                # removes all ~unnecessary~ generated files
make clobber              # removes all generated files
```
-->

Makefile 提供了更多可选的命令：

```bash
make                      （见 make test）
make build                （将 lagda 构建至 markdown 并构建网站）
make build-incremental    （将 lagda 构建至 markdown 并增量式构建网站）
make test                 （检查所有链接的有效性）
make test-offline         （离线检查所有链接的有效性）
make serve                （启动服务）
make server-start         （以分离模式启动服务）
make server-stop          （使用 pkill 停止服务）
make clean                （移除所有~不必要的~生成的文件）
make clobber              （移除所有生成的文件）
```

<!--
If you simply wish to have a local copy of the book, e.g. for offline reading, but don't care about editing and rebuilding the book, you can grab a copy of the [master branch][plfa-master], which is automatically built using Travis. You will still need [Jekyll][ruby-jekyll] and preferably [Bundler][ruby-bundler] to host the book (see above). To host the book this way, download a copy of the [master branch][plfa-master], unzip, and from within the directory run
-->

如果你只想获取本书的副本以供离线阅读，而并不关心如何编辑和构建本书，
那么你可以下载由 Travis 自动构建的 `master` 分支（[原书][plfa-master] / [中文版][plfa-zh-master]）。
若要在本地部署本书，你同样需要 [Jekyll][ruby-jekyll] 和 [Bundler][ruby-bundler]（见上文）。
请下载 `master` 分支的压缩包，并在解压后的目录中运行：

```bash
bundle install
bundle exec jekyll serve
```


<!--
### Building the EPUB
-->

### 构建 EPUB

<!--
The [EPUB version][epub] of the book is built using Pandoc.
-->

本书的 [EPUB 版本][epub-zh] 使用 Pandoc 构建。

<!--
Install a recent version of Pandoc, [available here][pandoc]. The easiest way to install Pandoc is using their official installer, which is much faster than compiling Pandoc from source with Haskell Stack.
-->

请安装最新版的 Pandoc，可从[这里][pandoc]下载。安装 Pandoc 最简单的方式是用是它的官方安装包，
这样比通过 Haskell Stack 从源码构建安装要快上许多。

<!--
Once you’ve installed Pandoc, you can build the EPUB by running:
-->

安装好 Pandoc 之后，你就可以运行以下命令来构建 EPUB 了：

```bash
make epub
```

<!--
The EPUB is written to `out/epub/plfa.epub`.
-->

EPUB 文件会输出到 `out/epub/plfa.epub`。

<!-- Links -->
[epub-zh]: https://agda-zh.github.io/PLFA-zh/out/epub/plfa.epub
[plfa-zh]: https://agda-zh.github.io/PLFA-zh/
[plfa-zh-dev]: https://github.com/Agda-zh/PLFA-zh/archive/dev.zip
[plfa-zh-status]: https://travis-ci.org/Agda-zh/PLFA-zh.svg?branch=dev
[plfa-zh-travis]: https://travis-ci.org/Agda-zh/PLFA-zh
[plfa-zh-master]: https://github.com/Agda-zh/PLFA-zh/archive/master.zip
[trans-spec]: https://github.com/Agda-zh/PLFA-zh/issues/1

[agda-zh]: https://agda-zh.rtfd.io/zh_CN/latest/getting-started/installation.html
[FiraCode]: https://github.com/tonsky/FiraCode

[epub]: https://plfa.github.io/out/epub/plfa.epub
[plfa]: http://plfa.inf.ed.ac.uk
[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-calver]: https://img.shields.io/badge/calver-20.07-22bfda
[plfa-latest]: https://github.com/plfa/plfa.github.io/releases/latest
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip

[agda]: https://github.com/agda/agda/releases/tag/v2.6.1
[agda-version]: https://img.shields.io/badge/agda-v2.6.1-blue.svg
[agda-docs-holes]: https://agda.readthedocs.io/en/v2.5.4/getting-started/quick-guide.html
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html
[agda-docs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.1/tools/emacs-mode.html#notation-for-key-combinations
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.1/tools/package-system.html#example-using-the-standard-library

[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.3-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.3

[haskell-stack]:  https://docs.haskellstack.org/en/stable/README/
[haskell-ghc]: https://www.haskell.org/ghc/

[fix-whitespace]: https://github.com/agda/fix-whitespace

[mononoki]: https://madmalik.github.io/mononoki/

[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer

[kramdown]: https://kramdown.gettalong.org/syntax.html
[pandoc]: https://pandoc.org/installing.html
[epubcheck]: https://github.com/w3c/epubcheck
