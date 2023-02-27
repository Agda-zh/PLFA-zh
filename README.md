---
title     : 使用说明
permalink: /GettingStarted/
translators : ["Rongxiao Fu", "Oling Cat"]
---

<!-- Status & Version Badges -->

[![Build Status][plfa-badge-status-svg]][plfa-badge-status-url]
[![Release Version][plfa-badge-version-svg]][plfa-badge-version-url]
[![agda][agda-badge-version-svg]][agda-badge-version-url]
[![standard-library][agda-stdlib-version-svg]][agda-stdlib-version-url]
[![pre-commit.ci status](https://results.pre-commit.ci/badge/github/plfa/plfa.github.io/dev.svg)](https://results.pre-commit.ci/latest/github/plfa/plfa.github.io/dev)

<!--

## Getting Started for Readers
-->

## 读者指南 {#getting-started-for-readers}

《编程语言基础：Agda 语言描述》的使用方法与《Programming Language Foundations in Agda》一致。

**本书可访问 [PLFA-zh][plfa-zh] 在线阅读。**

**要参与翻译，请先阅读[翻译规范][trans-spec]。**



<!--
You can read PLFA [online][plfa] without installing anything. However, if you wish to interact with the code or complete the exercises, you need several things:
-->

你可以[在线阅读][plfa-zh] PLFA，无需安装任何东西。
然而，如果你想要交互式编写代码或完成习题，那么就需要几样东西：

<!--
  - On macOS: [The XCode Command Line Tools](#on-macos-install-the-xcode-command-line-tools)
  - [Git](#install-git)
  - [GHC and Cabal](#install-ghc-and-cabal)
  - [Agda](#install-agda)
  - [Agda standard library](#install-plfa-and-the-agda-standard-library)
  - [PLFA](#install-plfa-and-the-agda-standard-library)
-->

  - macOS 上：[XCode 命令行工具](#on-macos-install-the-xcode-command-line-tools)
  - [Git](#install-git)
  - [GHC and Cabal](#install-ghc-and-cabal)
  - [Agda](#install-agda)
  - [Agda 标准库](#install-plfa-and-the-agda-standard-library)
  - [PLFA](#install-plfa-and-the-agda-standard-library)

<!--
PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.
-->

PLFA 只针对特定的 Agda 和 标准库版本进行了测试，相应版本已在前面的徽章中指明。
Agda 和标准库变化得十分迅速，而这些改变经常搞坏 PLFA，因此使用旧版或新版通常会出现问题。

<!--
There are several versions of Agda and its standard library online. If you are using a package manager, like Homebrew or Debian apt, the version of Agda available there may be out of date. Furthermore, Agda is under active development, so if you install the development version from the GitHub, you might find the developers have introduced changes which break the code here. Therefore, it’s important to have the specific versions of Agda and the standard library shown above.
-->

Agda 和 Agda 标准库有多个版本。如果你使用了包管理器（如 Homebrew 或者 Debian
apt），Agda 的版本可能不是最新的。除此之外，Agda
仍然在活跃的开发之中，如果你从 GitHub
上安装了开发版本，开发者的新变更也可能让这里的代码出现问题。
因此，使用上述版本的 Agda 和 Agda 标准库很重要。

<!--
### On macOS: Install the XCode Command Line Tools
-->

### macOS 平台：安装 XCode 命令行工具{#on-macos-install-the-xcode-command-line-tools}

<!--
On macOS, you’ll need to install [The XCode Command Line Tools][xcode]. For most versions of macOS, you can install these by running the following command:
-->

在 macOS 平台，你需要安装 [XCode 命令行工具][xcode]。
在大多数 macOS 系统版本上，你可以用下面的命令安装它们：


```bash
xcode-select --install
```


<!--
### Install Git
-->

### 安装 Git {#install-git}

<!--
You can check whether you have Git by running the following command:
-->

你可以使用下面的命令来检查你是否安装了 Git。

```bash
git --version
```


<!--
If you do not have Git, see [the Git downloads page][git].
-->

如果你没有 Git，请参阅 [Git 下载页面][git]。

<!--
### Install GHC and Cabal
-->

### 安装 GHC 和 Cabal {#install-ghc-and-cabal}

<!--
Agda is written in Haskell, so to install it we’ll need the _Glorious Haskell Compiler_ and its package manager _Cabal_. PLFA should work with any version of GHC >=8.10, but is tested with versions 8.10 and 9.2. We recommend installing GHC and Cabal using [ghcup][ghcup].  For instance, once `ghcup` is installed, by typing
-->


Agda 是用 Haskell 写成的，所以为了安装它我们需要 _Glorious Haskell Compiler_
和它的包管理器 _Cabal_。PLFA 应该在任何 >=8.10 的 GHC 版本下运行，在 8.10 和 9.2 版本下完成测试。我们建议使用 [ghcup][ghcup] 来安装两者。
在 `ghcup` 安装好之后，输入下列命令：

```bash
ghcup install ghc 9.2.4
ghcup install cabal recommended

ghcup set ghc 9.2.4
ghcup set cabal recommended
```

<!--
or using `ghcup tui` and choosing to `set` the appropriate tools.
-->

或使用 `ghcup tui` 来『设置』合适的工具。


<!--
### Install Agda
-->

### 安装 Agda {#install-agda}

<!--
The easiest way to install Agda is using Cabal. PLFA uses Agda version 2.6.3. Run the following command:
-->

安装 Agda 最简单的方法是通过 Cabal。PLFA 使用 Agda 版本
2.6.3。运行下面的命令：

```bash
cabal update
cabal install Agda-2.6.3
```

<!--
This step will take a long time and a lot of memory to complete.
-->

这一步会消耗很长时间和很多内存来完成。

<!--
If you have problems or for alternatives see the [Agda installation instructions][agda-readthedocs-installation].
-->

如果你遇到了问题，或者想参考替代的方法，可参阅 [Agda 安装指引][agda-readthedocs-installation]。

<!--
If you'd like, you can [test to see if you've installed Agda correctly][agda-readthedocs-hello-world].
-->


如果你愿意，你可以[测试 Agda 是否已正确安装][agda-readthedocs-hello-world]。


<!--
### Install PLFA and the Agda standard library
-->

### 安装 PLFA 和 Agda 标准库 {#install-plfa-and-the-agda-standard-library}

<!--
We recommend installing PLFA from Github into your home directory, by running the following command:
-->

我们建议您使用下面的命令把 PLFA 安装至你的家目录：

```bash
git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/plfa/plfa.github.io plfa
```


<!--
PLFA ships with the required version of the Agda standard library, so if you cloned with the `recurse-submodules` flag, you’ve already got it, in the `standard-library` directory!
-->

PLFA 包括了所需要的 Agda 标准库版本，如果你在克隆时使用了 `--recurse-submodule` 选项，你在 `standard-library` 文件夹中已经有了 Agda 标准库！

<!--
Finally, we need to let Agda know where to find the Agda standard library and PLFA. Two configuration files are required, one which lists paths to the libraries and one which specifies which libraries to load by default.
-->

最后，我们需要让 Agda 知道如何找到标准库。
你需要两个配置文件，一个用于指定库的路径，一个用于指定默认载入的库。


<!--
On macOS and Unix, if PLFA is installed in your home directory and you have no existing library configuration files you wish to preserve, run the following commands:
-->

在 macOS 和 Unix 上，如果 PLFA
已经安装至家目录，且你没有希望保存的配置文件，运行下面的命令：

```bash
mkdir -p ~/.agda
cp ~/plfa/data/dotagda/* ~/.agda
```

<!--
This provides access to both the Agda standard library and to PLFA as an Agda library.
-->

这条命令提供了 Agda 标准库，也让 PLFA 可以当作一个 Agda 库来使用。

<!--
Otherwise, you will need to edit the appropriate files. Both configuration files are located in the directory `AGDA_DIR`. On UNIX and macOS, `AGDA_DIR` defaults to `~/.agda`. On Windows, `AGDA_DIR` usually defaults to `%AppData%\agda`, where `%AppData%` usually defaults to `C:\Users\USERNAME\AppData\Roaming`.
-->

否则，你需要手动编辑相关的配置文件。两者都位于 `AGDA_DIR` 目录下。
在 UNIX 和 macOS 平台，`AGDA_DIR` 默认为
`~/.agda`。在 Windows 平台，`AGDA_DIR` 一般默认为 `%AppData%\agda`，而
`%AppData%` 默认为 `C:\Users\USERNAME\AppData\Roaming`。

<!--
- If the `AGDA_DIR` directory does not already exist, create it.
- In `AGDA_DIR`, create a plain-text file called `libraries` containing `AGDA_STDLIB/standard-library.agda-lib`, where `AGDA_STDLIB` is the path to where the Agda standard library is located (e.g., `~/plfa/standard-library/`). This lets Agda know that an Agda library called `standard-library` is available.
- In `AGDA_DIR`, create a plain-text file called `defaults` containing _just_ the line `standard-library`.
- If you want to complete the exercises or to import modules from the book, you will also need to provide access to PLFA as an Agda library. To do so, let `PLFA` be the path to the root directory for PLFA.
  Add `PLFA/src/plfa.agda-lib` to `AGDA_DIR/libraries` and add `plfa` to `AGDA_DIR/defaults`, each on a line of their own.
-->

- 如果 `AGDA_DIR` 文件夹不存在，创建它。
- 在 `AGDA_DIR` 中，创建一个纯文本文件 `libraries`，内容为
    `/path/to/standard-library.agda-lib` （即上文中记录的路径）。
  这个文件让 Agda 知道有一个名为 `standard-library` 的库可用。
- 在 `AGDA_DIR` 中，创建一个纯文本文件 `defaults`，内容__仅__为 `standard-library` 这一行。
- 如果你想完成 的习题，或者想导入书中的模块，
  那么需要将 PLFA 设置为 Agda 库。如果 `PLFA` 是 PLFA
  的根目录，完成此设置需要将 `PLFA/src/plfa.agda-lib` 作为单独的一行添加到
  `AGDA_DIR/libraries`，并将 `plfa` 作为单独的一行添加到 `AGDA_DIR/defaults`。

<!--
More information about placing the standard libraries is available from [the Library Management page][agda-readthedocs-package-system] of the Agda documentation.
-->

关于放置标准库的更多信息可以参阅 Agda 文档中的[库管理][agda-readthedocs-package-system]。

<!--
## Setting up an editor for Agda
-->

## 设置 Agda 的编辑器

### Emacs

<!--
The recommended editor for Agda is Emacs. To install Emacs:
-->
推荐的 Agda 编辑器是 Emacs。安装 Emacs 可以用下面的方法：

<!--
- _On UNIX_, the version of Emacs in your repository is probably fine as long as it is fairly recent. There are also links to the most recent release on the [GNU Emacs downloads page][emacs].

- _On MacOS_, [Aquamacs][aquamacs] is probably the preferred version of Emacs, but GNU Emacs can also be installed via Homebrew or MacPorts. See the [GNU Emacs downloads page][emacs] for instructions.

- _On Windows_. See the [GNU Emacs downloads page][emacs] for instructions.

-->

- __UNIX 平台__：包管理器中的 Emacs 应该可以使用（只要它的版本比较新），[GNU
   Emacs 下载页面][emacs]也有最近发布版本的链接。
- __MacOS 平台__：推荐的 Emacs 是 [Aquamacs][aquamacs]，但是 GNU Emacs
   也可以通过 Homebrew 或者 MacPorts 安装。参阅 [GNU Emacs
   下载页面][emacs]中的指示。
- __Windows 平台__：参阅 [GNU Emacs 下载页面][emacs]中的指示。

<!--
Make sure that you are able to open, edit, and save text files with your installation. The [tour of Emacs][emacs-tour] page on the GNU Emacs site describes how to access the tutorial within your Emacs installation.
-->

确保你可以用你安装的版本打开、编辑、保存文件。GNU Emacs 网站上的 [Emacs
向导][emacs-tour]描述了如果打开 Emacs 安装中的教程。

<!--
Agda ships with the editor support for Emacs built-in, so if you’ve installed Agda, all you have to do to configure Emacs is run:
-->

Agda 自带了 Emacs 编辑器支持，如果你安装了 Agda，运行下面的命令来配置 Emacs：

```bash
agda-mode setup
agda-mode compile
```

<!--
If you are already an Emacs user and have customized your setup, you may want to note the configuration which the `setup` appends to your `.emacs` file, and integrate it with your own preferred setup.
-->

如果你已经是 Emacs 用户，并有自己的设置，你会注意到 `setup` 命令向你的 `.emacs`
文件中追加了配置，来配合你已有的设置。

<!--
The recommended editor for Agda is Emacs with `agda-mode`. Agda ships with `agda-mode`, so if you’ve installed Agda, all you have to do to configure `agda-mode` is run:
-->

加上 `agda-mode`。Agda 自带了 `agda-mode`，
因此如果你已经安装了 Agda，那么之需要运行以下命令就能配置好 `agda-mode` 了：

<!--
#### Check if `agda-mode` was installed correctly
-->
#### 检查 `agda-mode` 是否正确安装

<!--
Open the `nats.agda` file you created earlier, and load and type-check the file by typing [`C-c C-l`][agda-readthedocs-emacs-notation].
-->

打开之前创建的 `nats.agda` 文件，使用 [`C-c C-l`][agda-readthedocs-emacs-notation]
来载入和类型检查这个文件。

<!--
#### Auto-loading `agda-mode` in Emacs
-->

#### 在 Emacs 中自动加载 `agda-mode`

<!--
Since version 2.6.0, Agda has had support for literate editing with Markdown, using the `.lagda.md` extension. One issue is that Emacs will default to Markdown editing mode for files with a `.md` suffix. In order to have `agda-mode` automatically loaded whenever you open a file ending with `.agda` or `.lagda.md`, add the following line to your Emacs configuration file:
-->

从版本 2.6.0 开始，Agda 支持 Markdown 风格的文学编程，文件使用 `.lagda.md` 扩展名。
该扩展名的一个问题就是 Emacs 默认会进入 Markdown 编辑模式。
而为了让 `agda-mode` 在你打开 `.agda` 或 `.lagda.md` 文件时自动加载，
请将以下内容放到你的 Emacs 配置文件中：



```elisp
;; auto-load agda-mode for .agda and .lagda.md
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```

<!--
If you already have settings which change your `auto-mode-alist` in your configuration, put these _after_ the ones you already have or combine them if you are comfortable with Emacs Lisp. The configuration file for Emacs is normally located in `HOME/.emacs` or `HOME/.emacs.d/init.el`, but Aquamacs users might need to move their startup settings to the “Preferences.el” file in `HOME/Library/Preferences/Aquamacs Emacs/Preferences`. For Windows, see [the GNU Emacs documentation][emacs-home] for a description of where the Emacs configuration is located.
-->

如果你配置中已有了改变 `auto-mode-alist`
的设置，将上述内容放置在已有的设置__之后__，或者将其与已有设置合并（如果你对
Emacs Lisp 足够了解）。
Emacs 的配置文件通常位于 `~/.emacs` 或 `~/.emacs.d/init.el`，然而
Aquamacs 用户需要将启动设置放到位于 `~/Library/Preferences/Aquamacs Emacs/Preferences`
的 `Preferences.el` 文件中。
对于 Windows 平台，请参阅 [GNU Emacs 文档][emacs-home] 来寻找配置文件的位置。

<!--
#### Optional: using the mononoki font with Emacs
-->

#### 可选：在 Emacs 中使用 Mononoki 字体

<!--
Agda uses Unicode characters for many key symbols, and it is important that the font which you use to view and edit Agda programs shows these symbols correctly. The most important part is that the font you use has good Unicode support, so while we recommend [mononoki][font-mononoki], fonts such as [Source Code Pro][font-sourcecodepro], [DejaVu Sans Mono][font-dejavusansmono], and [FreeMono][font-freemono] are all good alternatives.
-->

Agda 中的很多重要符号是用 Unicode 来表示的，因此用来显示和编辑 Agda
的字体需要正确地显示这些符号。最重要的是你使用的字体需要有好的 Unicode
字符支持。我们推荐 [Mononoki][font-mononoki]，
其他的备选字体有 [Source Code Pro][font-sourcecodepro]、
[DejaVu Sans Mono][font-dejavusansmono] 和 [FreeMono][font-freemono]。

<!--
You can download and install mononoki directly from [the website][font-mononoki]. For most systems, installing a font is merely a matter of clicking the downloaded `.otf` or `.ttf` file. If your package manager offers a package for mononoki, that might be easier. For instance, Homebrew on macOS offers the `font-mononoki` package, and APT on Debian offers the `fonts-mononoki` package. To configure Emacs to use mononoki as its default font, add the following to the end of your Emacs configuration file:
-->

你可以直接从[此网站][font-mononoki] 下载并安装
Mononoki。对于大多数系统来说，安装字体只是简单的下载 `.otf` 或者 `.ttf` 文件。
如果你的包管理器提供了 Mononoki 的包，那样可能更加简单。
例如，macOS 的 Homebrew 提供了
`font-mononiki` 包；Debian 的 APT 提供了 `fonts-mononoki` 包。
将下面的内容加入 Emacs 配置文件，可以把 Mononoki 设置为 Emacs 的默认字体：

```elisp
;; default to mononoki
(set-face-attribute 'default nil
                    :family "mononoki"
                    :height 120
                    :weight 'normal
                    :width  'normal)
```

<!--
#### Using `agda-mode` in Emacs
-->

#### 在 Emacs 中使用 `agda-mode`

<!--
To load and type-check the file, use [`C-c C-l`][agda-readthedocs-emacs-notation].
-->

要加载文件并对其执行类型检查，请使用 [`C-c C-l`][agda-readthedocs-emacs-notation]。

<!--
Agda is edited interactively, using [“holes”][agda-readthedocs-holes], which are bits of the program that are not yet filled in. If you use a question mark as an expression, and load the buffer using `C-c C-l`, Agda replaces the question mark with a hole. There are several things you can to while the cursor is in a hole:
-->

Agda 的编辑是通过使用「[洞][agda-readthedocs-holes]」来交互的，它表示程序中尚未填充的片段。
如果用问号作为表达式，并用 `C-c C-l` 加载缓冲区，Agda 会将问号替换为一个「洞」。
当光标在洞中时，你可以做以下这些事情：

<!--
- `C-c C-c`: **c**ase split (asks for variable name)
- `C-c C-space`: fill in hole
- `C-c C-r`: **r**efine with constructor
- `C-c C-a`: **a**utomatically fill in hole
- `C-c C-,`: goal type and context
- `C-c C-.`: goal type, context, and inferred type
-->

- `C-c C-c`: 分项（询问变量名，**c**ase）
- `C-c C-空格`：填洞
- `C-c C-r`：用构造子精化（**r**efine）
- `C-c C-a`：自动填洞（**a**utomatic）
- `C-c C-,`：目标类型和上下文
- `C-c C-.`：目标类型，上下文，以及推断的类型

<!--
See [the emacs-mode docs][agda-readthedocs-emacs-mode] for more details.
-->

更多细节请见 [emacs-mode 文档][agda-readthedocs-emacs-mode]。

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
#### Entering Unicode characters in Emacs with `agda-mode`
-->

#### 在 Emacs 中使用 `agda-mode` 输入 Unicode 字符

<!--
When you write Agda code, you will need to insert characters which are not found on standard keyboards. Emacs “agda-mode” makes it easier to do this by defining character translations: when you enter certain sequences of ordinary characters (the kind you find on any keyboard), Emacs will replace them in your Agda file with the corresponding special character.
-->

当你书写 Agda 代码时，你需要输入标准键盘上没有的字符。Emacs
的「Agda-mode」定义了字符翻译来让这件事更容易：当你输入特定普通字符的序列时，Emacs
会在 Agda 文件中使用对应的特殊字符来替换。

<!--
For example, we can add a comment line to one of the `.agda` test files.
Let's say we want to add a comment line that reads:
-->

例如，我们可以在之前的 `.agda` 测试文件中加入一条注释。
比如说，我们想要加入下面的注释：

```agda
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```

<!--
The first few characters are ordinary, so we would just type them as usual…
-->

前几个字符都是普通字符，我们可以如往常的方式输入它们……

```agda
{- I am excited to type
```


<!--
But after that last space, we do not find ∀ on the keyboard. The code for this character is the four characters `\all`, so we type those four characters, and when we finish, Emacs will replace them with what we want…
-->

在最后一个空格之后，我们无法在键盘上找到 ∀ 这个键。这个字符的输入序列是四个字符
`\all`，所以我们输入这四个字符，当我们完成时，Emacs 会把它们替换成我们想要的……

```agda
{- I am excited to type ∀
```

<!--
We can continue with the codes for the other characters. Sometimes the characters will change as we type them, because a prefix of our character's code is the code of another character. This happens with the arrow, whose code is `\->`. After typing `\-` we see…
-->

我们继续输入其他字符。有时字符会在输入时发生变化，因为一个字符的输入序列是另一个字符输入序列的前缀。
在我们输入箭头时会出现这样的情况，它的输入序列是 `\->`。在输入 `\-`
之后我们会看到……

```agda
{- I am excited to type ∀ and -
```

<!--
…because the code `\-` corresponds to a hyphen of a certain width. When we add the `>`, the `­` becomes `→`! The code for `≤` is `\<=`, and the code for `≡` is `\==`.
-->

……因为输入序列 `\-` 对应了一定长度的短横。当我们输入 `>` 时，`­` 变成了 `→`！
`≤` 的输入序列是 `\<=`，`≡` 的是 `\==`。


```agda
{- I am excited to type ∀ and → and ≤ and ≡
```

<!--
Finally the last few characters are ordinary again…
-->

最后几个字符又回归了普通字符……

```agda
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```


<!--
If you're having trouble typing the Unicode characters into Emacs, the end of each chapter should provide a list of the Unicode characters introduced in that chapter.
-->

如果你在 Emacs 中输入 Unicode 时遇到了问题，可以在每章的最后找到当前章节中用到的
Unicode 字符。

<!--
Emacs with `agda-mode` offers a number of useful commands, and two of them are especially useful when it comes to working with Unicode characters. For a full list of supported characters, use `agda-input-show-translations` with:
-->

带有 `agda-mode` 的 Emacs 提供了很多有用的命令，其中有两个对处理 Unicode
字符时特别有用。
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

### Spacemacs

<!--
[Spacemacs][spacemacs] is a “community-driven Emacs distribution” with native support for both Emacs and Vim editing styles. It comes with [integration for `agda-mode`][spacemacs-agda] out of the box. All that is required is that you enable the Agda layer in your `.spacemacs` file.
-->

[Spacemacs][spacemacs] 是一个「社区引领的 Emacs 版本」，对 Emacs 和 Vim
的编辑方式都有很好的支持。它自带[集成了
`agda-mode`][spacemacs-agda]，所需的只是将 `.spacemacs` 中启用 Agda 支持。

### Visual Studio Code

<!--
[Visual Studio Code][vscode] is a free source code editor developed by Microsoft. There is [a plugin for Agda support][vscode-agda] available on the Visual Studio Marketplace.
-->

[Visual Studio Code][vscode] 是一个微软开发的开源代码编辑器。
Visual Studio 市场中有 [Agda 插件][vscode-agda]。

### Atom

<!--
[Atom][atom] is a free source code editor developed by GitHub. There is [a plugin for Agda support][atom-agda] available on the Atom package manager.
-->

[Atom][atom] 是一个 GitHub 开发的开源代码编辑器。
Atom 包管理器中有 [Agda 插件][atom-agda]。


## Getting Started for Contributors

If you plan to build PLFA locally, please refer to [Contributing][plfa-contributing] for additional instructions.

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

[plfa-badge-version-svg]: https://img.shields.io/github/v/tag/plfa/plfa.github.io?label=release
[plfa-badge-version-url]: https://github.com/plfa/plfa.github.io/releases/latest
[plfa-badge-status-svg]: https://github.com/plfa/plfa.github.io/actions/workflows/build.yml/badge.svg
[plfa-badge-status-url]: https://github.com/plfa/plfa.github.io/actions/workflows/build.yml
[agda-badge-version-svg]: https://img.shields.io/badge/agda-v2.6.3-blue.svg
[agda-badge-version-url]: https://github.com/agda/agda/releases/tag/v2.6.3.
[agda-stdlib-version-svg]: https://img.shields.io/badge/agda--stdlib-v1.7.2-blue.svg
[agda-stdlib-version-url]: https://github.com/agda/agda-stdlib/releases/tag/v1.7.2
[plfa]: https://plfa.inf.ed.ac.uk
[plfa-epub]: https://plfa.github.io/plfa.epub
[plfa-contributing]: https://plfa.github.io/Contributing/
[ghcup]: https://www.haskell.org/ghcup/
[git]: https://git-scm.com/downloads
[xcode]: https://developer.apple.com/xcode/
[agda-readthedocs-installation]: https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html
[agda-readthedocs-hello-world]: https://agda.readthedocs.io/en/v2.6.3/getting-started/hello-world.html
[agda-readthedocs-holes]: https://agda.readthedocs.io/en/v2.6.3/getting-started/a-taste-of-agda.html#preliminaries
[agda-readthedocs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html
[agda-readthedocs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html#notation-for-key-combinations
[agda-readthedocs-package-system]: https://agda.readthedocs.io/en/v2.6.3/tools/package-system.html#example-using-the-standard-library
[emacs]: https://www.gnu.org/software/emacs/download.html
[emacs-tour]: https://www.gnu.org/software/emacs/tour/
[emacs-home]: https://www.gnu.org/software/emacs/manual/html_node/efaq-w32/Location-of-init-file.html
[aquamacs]: https://aquamacs.org/
[spacemacs]: https://www.spacemacs.org/
[spacemacs-agda]: https://develop.spacemacs.org/layers/+lang/agda/README.html
[vscode]: https://code.visualstudio.com/
[vscode-agda]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[atom]: https://atom.io/
[atom-agda]: https://atom.io/packages/agda-mode
[font-sourcecodepro]: https://github.com/adobe-fonts/source-code-pro
[font-dejavusansmono]: https://dejavu-fonts.github.io/
[font-freemono]: https://www.gnu.org/software/freefont/
[font-mononoki]: https://madmalik.github.io/mononoki/
[font-mononoki-debian]: https://packages.debian.org/sid/fonts/fonts-mononoki
