---
layout    : page
title     : 使用说明
prev      : /Preface/
permalink : /GettingStarted/
next      : /Naturals/
translators : ["Rongxiao Fu", "Oling Cat"]
---

<!-- Status & Version Badges -->

[![Calendar Version][plfa-calver]][plfa-latest]
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
  - [Stack](#install-the-haskell-tool-stack)
  - [Git](#install-git)
  - [Agda](#install-agda-using-stack)
  - [Agda standard library](#install-plfa-and-the-agda-standard-library)
  - [PLFA](#install-plfa-and-the-agda-standard-library)
-->

  - [Stack](#install-the-haskell-tool-stack)
  - [Git](#install-git)
  - [Agda](#installing-agda-using-stack)
  - [Agda 标准库](#install-plfa-and-the-agda-standard-library)
  - [PLFA](#install-plfa-and-the-agda-standard-library)

<!--
PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.
-->

PLFA 只针对特定的 Agda 和 标准库版本进行了测试，相应版本已在前面的徽章中指明。
Agda 和标准库变化得十分迅速，而这些改变经常搞坏 PLFA，因此使用旧版或新版通常会出现问题。

<!--
There are several versions of Agda and its standard library online. If you are using a package manager, like Homebrew or Debian apt, the version of Agda available there may be out-of date. Furthermore, Agda is under active development, so if you install the development version from the GitHub, you might find the developers have introduced changes which break the code here. Therefore, it’s important to have the specific versions of Agda and the standard library shown above.
-->

Agda 和 Agda 标准库有多个版本。如果你使用了包管理器（如 Homebrew 或者 Debian
apt），Agda 的版本可能不是最新的。除此之外，Agda
仍然在活跃的开发之中，如果你从 GitHub
上安装了开发版本，开发者的新变更也可能让这里的代码出现问题。
因此，使用上述版本的 Agda 和 Agda 标准库很重要。

<!--
### On macOS: Install the XCode Command Line Tools
-->

### macOS 平台：安装 XCode 命令行工具

<!--
On macOS, you’ll need to install the [XCode Command Line Tools][xcode]. For most versions of macOS, you can install these by running the following command:
-->

在 macOS 平台，你需要安装 [XCode 命令行工具][xcode]。
在大多数 macOS 系统版本上，你可以用下面的命令安装它们：

```bash
xcode-select --install
```

<!--
### Install the Haskell Tool Stack
-->

### 安装 Haskell 工具 Stack {name=install-the-haskell-tool-stack}

<!--
Agda is written in Haskell, so to install it we’ll need the *Haskell Tool Stack*, or *Stack* for short. Stack is a program for managing different Haskell compilers and packages:
-->

Agda 使用 Haskell 写的，因此我们需要 Haskell 工具 Stack （简称 Stack）来安装 Agda。
Stack 是管理不同版本的 Haskell 编译器和包的管理程序。

<!--
- *On UNIX and macOS.* If your package manager has a package for Stack, that’s probably your easiest option. For instance, Homebrew on macOS  and APT on Debian offer the “haskell-stack” package. Otherwise, you can follow the instructions on [the Stack website][haskell-stack]. Usually, Stack installs binaries at `HOME/.local/bin`. Please ensure this is on your PATH, by including the following in your shell configuration, e.g., in `HOME/.bash_profile`:
  ```bash
  export PATH="${HOME}/.local/bin:${PATH}"
  ```
  Finally, ensure that you’ve got the latest version of Stack, by running:
  ```bash
  stack upgrade
  ```
- *On Windows.* There is a Windows installer on [the Stack website][haskell-stack].
-->

- **UNIX 和 macOS** 平台：如果你的包管理程序有 Stack
  的包，这是大概是最简单的方法。 比如说 macOS 的 Homebrew 或者 Debian 的 APT
  提供了「haskell-stack」包。
  不然，你可以按照 [Stack 网站上][haskell-stack] 的指示进行安装。
  在一般情况下，Stack 将二进制文件安装至 `HOME/.local/bin`。
  请务必保证这个目录在你的 PATH 之内，你可以将下面的内容加入你的 shell
  配置中，例如 `HOME/.bash_profile` 中：

  ```bash
  export PATH="${HOME}/.local/bin:${PATH}"
  ```

  最后，请保证你有最新版的 Stack，运行：
  ```bash
  stack upgrade
  ```
- **Windows** 平台：[Stack 网站上][haskell-stack]提供 Windows 安装包。

<!--
### Install Git
-->

### 安装 Git {name=install-git}

<!--
If you do not already have Git installed, see [the Git downloads page][git].
-->

如果你没有已经安装 Git，请参阅 [Git 下载页面][git]。

<!--
### Installing Agda using Stack
-->

### 用 Stack 安装 Agda {name=installing-agda-using-stack}


<!--
The easiest way to install a *specific version* of Agda is using [Stack][haskell-stack]. You can get the required version of Agda from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda]:
-->

安装 **特定** Agda 版本的最简方式是使用 [Stack][haskell-stack]。你可以从 GitHub 上获取需要的版本，
可以通过克隆源码库并切换到合适的分支，也可以直接下载 [Zip 包][agda]：

```bash
git clone https://github.com/agda/agda.git
cd agda
git checkout v2.6.1.3
```

<!--
To install Agda, run Stack from the Agda source directory:
-->

要安装 Agda，请在其源码目录中运行 Stack：

```bash
stack install --stack-yaml stack-8.8.3.yaml
```

<!--
*This step will take a long time and a lot of memory to complete.*
-->

**这一步会消耗很长时间和很多内存来完成。**

<!--
#### Using an existing installation of GHC
-->

#### 使用已安装的 GHC

<!--
Stack is perfectly capable of installing and managing versions of the [Glasgow Haskell Compiler][haskell-ghc] for you. However, if you already have a copy of GHC installed, and you want Stack to use your system installation, you can pass the `--system-ghc` flag and select the appropriate `stack-*.yaml` file. For instance, if you have GHC 8.2.2 installed, run:
-->

Stack 可以为你安装和管理 [Glasgow Haskell 编译器（GHC）][haskell-ghc]。
然而，如果你已经安装了 GHC 并且想让 Stack 使用你系统上安装的 GHC 版本，可以传递
`--system-ghc` 选项并选择对应的 `stack-*.yaml` 文件。例如，若你安装了 GHC
8.2.2，请运行：

```bash
stack install --system-ghc --stack-yaml stack-8.2.2.yaml
```

<!--
#### Check if Agda was installed correctly
-->

#### 检查 Agda 是否被正确地安装

<!--
If you’d like, you can test to see if you’ve installed Agda correctly. Create a file called `hello.agda` with these lines:
-->

如果你愿意，你可以检查 Agda 是否已正确安装。
创建一个名为 `hello.agda` 的文件，并输入下面的内容：

```agda
data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello
```

<!--
From a command line, change to the same directory where your `hello.agda` file is located. Then run:
-->

从命令行中，切换到 `hello.agda` 所在的文件夹内，然后运行：

```bash
agda -v 2 hello.agda
```

<!--
You should see a short message like the following, but no errors:
-->

你会看到如下的消息，而不是错误：

```
Checking hello (/path/to/hello.agda).
Finished hello.
```

<!--
### Install PLFA and the Agda standard library
-->

### 安装 PLFA 和 Agda 标准库 {name=install-plfa-and-the-agda-standard-library}

<!--
You can get the latest version of Programming Language Foundations in Agda from GitHub, either by cloning the repository, or by downloading [the zip archive][plfa-dev]:
-->

你也可以从 GitHub 克隆源码库，或者下载
[Zip 包][plfa-dev]来获取最新版的《编程语言基础：Agda 语言描述》：

```bash
git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/plfa/plfa.github.io plfa
# Remove `--depth 1` and `--shallow-submodules` if you want the complete git history of PLFA and the standard library.
```

<!--
PLFA ships with the required version of the Agda standard library, so if you cloned with the `--recurse-submodules` flag, you’ve already got, in the `standard-library` directory!
-->

PLFA 包括了所需要的 Agda 标准库版本，如果你在克隆时使用了 `--recurse-submodule` 选项，你在 `standard-library` 文件夹中已经有了 Agda 标准库！

<!--
If you forgot to add the `--recurse-submodules` flag, no worries, we can fix that!
-->

如果你忘记使用了 `--recurse-submodules` 选项，也没有关系，我们可以修复它！

```bash
cd plfa/
git submodule update --init --recursive --depth 1
# Remove `--depth 1` if you want the complete git history of the standard library.
```

<!--
If you obtained PLFA by downloading the zip archive, you can get the required version of the Agda standard library from GitHub. You can either clone the repository and switch to the correct branch, or you can download the [the zip archive][agda-stdlib]:
-->

如果你用 Zip 包下载了 PLFA，你可以从 GitHub 上下载所需要的 Agda 标准库版本。
你可以从正确的分支克隆代码仓库，或者下载 [Zip 包][agda-stdlib]。

```bash
git clone https://github.com/agda/agda-stdlib.git --branch v1.6 --depth 1 agda-stdlib
# Remove `--depth 1` if you want the complete git history of the standard library.
```

<!--
Finally, we need to let Agda know where to find the Agda standard library.
You'll need the path where you installed the standard library. Check to see that the file “standard-library.agda-lib” exists, and make a note of the path to this file.
You will need to create two configuration files in `AGDA_DIR`. On UNIX and macOS, `AGDA_DIR` defaults to `~/.agda`. On Windows, `AGDA_DIR` usually defaults to `%AppData%\agda`, where `%AppData%` usually defaults to `C:\Users\USERNAME\AppData\Roaming`.
-->

最后，我们需要让 Agda 知道如何找到标准库。
你需要知道标准库安装的目录。
检查 `standard-library.agda-lib` 文件是否存在，并记录这个文件的路径。
你需要在 `AGDA_DIR` 创建两个配置文件。在 UNIX 和 macOS 平台，`AGDA_DIR` 默认为
`~/.agda`。在 Windows 平台，`AGDA_DIR` 一般默认为 `%AppData%\agda`，而
`%AppData%` 默认为 `C:\Users\USERNAME\AppData\Roaming`。

<!--
- If the `AGDA_DIR` directory does not already exist, create it.
- In `AGDA_DIR`, create a plain-text file called `libraries` containing the `/path/to/standard-library.agda-lib`. This lets Agda know that an Agda library called `standard-library` is available.
- In `AGDA_DIR`, create a plain-text file called `defaults` containing *just* the line `standard-library`.
-->

- 如果 `AGDA_DIR` 文件夹不存在，创建它。
- 在 `AGDA_DIR` 中，创建一个纯文本文件 `libraries`，内容为
    `/path/to/standard-library.agda-lib` （即上文中记录的路径）。
  这个文件让 Agda 知道有一个名为 `standard-library` 的库可用。
- 在 `AGDA_DIR` 中，创建一个纯文本文件 `defaults`，内容**仅**为 `standard-library` 这一行。

<!--
More information about placing the standard libraries is available from [the Library Management page][agda-docs-package-system] of the Agda documentation.
-->

关于放置标准库的更多信息可以参阅 Agda 文档中的[库管理][agda-docs-package-system]。

<!--
It is possible to set up PLFA as an Agda library as well.  If you want to complete the exercises found in the `courses` folder, or to import modules from the book, you need to do this.  To do so, add the path to `plfa.agda-lib` to `AGDA_DIR/libraries` and add `plfa` to `AGDA_DIR/defaults`, each on a line of their own.
-->

PLFA 也可以设置为一个 Agda 库。
如果你想完成 `courses` 目录中的习题，或者想导入书中的模块，
那么需要将 PLFA 设置为 Agda 库。完成此设置需要将 `plfa.agda-lib`
所在的路径作为单独的一行添加到 `AGDA_DIR/libraries`，并将 `plfa`
作为单独的一行添加到 `AGDA_DIR/defaults`。

<!--
#### Check if the Agda standard library was installed correctly
-->

#### 检查 Agda 标准库是否正确安装

<!--
If you’d like, you can test to see if you’ve installed the Agda standard library correctly. Create a file called `nats.agda` with these lines:
-->

如果你愿意，你可以测试 Agda 标准库是否已正确。创建一个名为 `nats.agda`
的文件，包括以下内容：

```agda
open import Data.Nat

ten : ℕ
ten = 10
```
<!--
(Note that the ℕ is a Unicode character, not a plain capital N. You should be able to just copy-and-paste it from this page into your file.)
-->

（注意 ℕ 是一个 Unicode 字符，而不是普通的大写字母 N。你可以直接从本页复制粘贴它到文件中。）

<!--
From a command line, change to the same directory where your `nats.agda` file is located. Then run:
-->

从命令行中，切换到 `nats.agda` 所在的文件夹内，然后运行：

```bash
agda -v 2 nats.agda
```

<!--
You should see a several lines describing the files which Agda loads while checking your file, but no errors:
-->

你会看见数行来描述 Agda 在检查你的文件时载入的文件，但是没有错误：

```
Checking nats (/path/to/nats.agda).
Loading  Agda.Builtin.Equality (…).
…
Loading  Data.Nat (…).
Finished nats.
```
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
 - *On UNIX*, the version of Emacs in your repository is probably fine as long as it is fairly recent. There are also links to the most recent release on the [GNU Emacs downloads page][emacs].
 - *On MacOS*, [Aquamacs][aquamacs] is probably the preferred version of Emacs, but GNU Emacs can also be installed via Homebrew or MacPorts. See the [GNU Emacs downloads page][emacs] for instructions.
 - *On Windows*. See the [GNU Emacs downloads page][emacs] for instructions.
-->

 - **UNIX 平台**：包管理器中的 Emacs 应该可以使用（只要它的版本比较新），[GNU
     Emacs 下载页面][emacs]也有最近发布版本的链接。
 - **macOS 平台**：推荐的 Emacs 是 [Aquamacs][aquamacs]，但是 GNU Emacs
     也可以通过 Homebrew 或者 MacPorts 安装。参阅 [GNU Emacs
     下载页面][emacs]中的指示。
 - **Windows 平台**：参阅 [GNU Emacs 下载页面][emacs]中的指示。

<!--
Make sure that you are able to open, edit, and save text files with your installation.  The [tour of Emacs][emacs-tour] page on the GNU Emacs site describes how to access the tutorial within your Emacs installation.
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
Open the `nats.agda` file you created earlier, and load and type-check the file by typing [`C-c C-l`][agda-docs-emacs-notation].
-->

打开之前创建的 `nats.agda` 文件，使用 [`C-c C-l`][agda-docs-emacs-notation]
来载入和类型检查这个文件。

<!--
### Auto-loading `agda-mode` in Emacs
-->

### 在 Emacs 中自动加载 `agda-mode`

<!--
Since version 2.6.0, Agda has support for literate editing with Markdown, using the `.lagda.md` extension. One side-effect of this extension is that most editors default to Markdown editing mode, whereas
In order to have `agda-mode` automatically loaded whenever you open a file ending with `.agda` or `.lagda.md`, put the following on your Emacs configuration file:
-->

从版本 2.6.0 开始，Agda 支持 Markdown 风格的文学编程，文件使用 `.lagda.md` 扩展名。
该扩展名的一个副作用就是大部分编辑器默认会进入 Markdown 编辑模式。
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
If you already have settings which change your `auto-mode-alist` in your configuration, put these *after* the ones you already have or combine them if you are comfortable with Emacs Lisp. The configuration file for Emacs is normally located in `HOME/.emacs` or `HOME/.emacs.d/init.el`, but Aquamacs users might need to move their startup settings to the “Preferences.el” file in `HOME/Library/Preferences/Aquamacs Emacs/Preferences`. For Windows, see [the GNU Emacs documentation][emacs-home] for a description of where the Emacs configuration is located.
-->

如果你配置中已有了改变 `auto-mode-alist`
的设置，将上述内容放置在已有的设置**之后**，或者将其与已有设置合并（如果你对
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
You can download and install mononoki directly from [GitHub][mononoki]. For most systems, installing a font is merely a matter of clicking the downloaded `.otf` or `.ttf` file. If your package manager offers a package for mononoki, that might be easier. For instance, Homebrew on macOS offers the `font-mononoki` package in the [`cask-fonts` cask][cask-fonts], and APT on Debian offers the [`fonts-mononoki` package][font-mononoki-debian]. To configure Emacs to use mononoki as its default font, add the following to the end of your Emacs configuration file:
-->

你可以直接从 [GitHub][mononoki] 下载并安装
Mononoki。对于大多数系统来说，安装字体只是简单的下载 `.otf` 或者 `.ttf` 文件。
如果你的包管理器提供了 Mononoki 的包，那样可能更加简单。
例如，macOS 的 Homebrew 在 [`cask-fonts` cask][cask-fonts] 中提供了
`font-mononiki` 包；Debian 的 APT 提供了 [`fonts-mononoki` 包][font-mononoki-debian]。
将下面的内容加入 Emacs 配置文件，可以把 Mononoki 设置为 Emacs 的默认字体：

``` elisp
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

```
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```

<!--
The first few characters are ordinary, so we would just type them as usual…
-->

前几个字符都是普通字符，我们可以如往常的方式输入它们……

```
{- I am excited to type
```


<!--
But after that last space, we do not find ∀ on the keyboard. The code for this character is the four characters `\all`, so we type those four characters, and when we finish, Emacs will replace them with what we want…
-->

在最后一个空格之后，我们无法在键盘上找到 ∀ 这个键。这个字符的输入序列是四个字符
`\all`，所以我们输入这四个字符，当我们完成时，Emacs 会把它们替换成我们想要的……

```
{- I am excited to type ∀
```

<!--
We can continue with the codes for the other characters. Sometimes the characters will change as we type them, because a prefix of our character's code is the code of another character. This happens with the arrow, whose code is `\->`.  After typing `\-` we see…
-->

我们继续输入其他字符。有时字符会在输入时发生变化，因为一个字符的输入序列是另一个字符输入序列的前缀。
在我们输入箭头时会出现这样的情况，它的输入序列是 `\->`。在输入 `\-`
之后我们会看到……

```
{- I am excited to type ∀ and
```

<!--
…because the code `\-` corresponds to a hyphen of a certain width. When we add the `>`, the `­` becomes `→`! The code for `≤` is `\<=`, and the code for `≡` is `\==`.
--->

……因为输入序列 `\-` 对应了一定长度的短横。当我们输入 `>` 时，`­` 变成了 `→`！
`≤` 的输入序列是 `\<=`，`≡` 的是 `\==`。


```
{- I am excited to type ∀ and → and ≤ and ≡
```

<!--
Finally the last few characters are ordinary again…
-->

最后几个字符又回归了普通字符……

```
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
[Spacemacs][spacemacs] is a “community-driven Emacs distribution” with native support for both Emacs and Vim editing styles. It comes with [integration for `agda-mode`][spacemacs-agda] out of the box. All that is required is that you turn it on.
-->

[Spacemacs][spacemacs] 是一个「社区引领的 Emacs 版本」，对 Emacs 和 Vim
的编辑方式都有很好的支持。它自带[集成了
`agda-mode`][spacemacs-agda]，所需的只是将它打开。

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

<!--
## Dependencies for developers
-->

## 开发者依赖

<!--
PLFA is written in literate Agda with [Pandoc Markdown][pandoc-markdown].
PLFA is available as both a website and an EPUB e-book, both of which can be built on UNIX and macOS.
Finally, to help developers avoid common mistakes, we provide a set of Git hooks.
-->

PLFA 是以 [Pandoc Markdown][pandoc-markdown] 格式的文学化 Agda 编写的。
PLFA 可同时在网站上和作为 EPUB 电子书来阅读，二者均可在 UNIX 和 macOS 上构建。
最后，为了帮助开发者避免常见错误，我们提供一系列 Git 钩子脚本。

<!--
### Building the website and e-book
-->

### 构建网站和电子书

<!--
If you’d like to build the web version of PLFA locally, [Stack](#install-the-haskell-tool-stack) is all you need! PLFA is built using [Hakyll][hakyll], a Haskell library for building static websites. We’ve setup a Makefile to help you run common tasks. For instance, to build PLFA, run:
-->

如果你想在本地构建 PLFA 的网站版，你只需要
[Stack](#install-the-haskell-tool-stack)！
PLFA 用 [Hakyll][hakyll] （一个构造静态网页的 Haskell 库）来构建。
我们配置了一个用于执行常见任务的 Makefile。例如，要构建 PLFA，运行：

```bash
make build
```

<!--
If you’d like to serve PLFA locally, rebuilding the website when any of the source files are changed, run:
-->

如果你想在本地架起 PLFA，并且在源文件修改时重新构造，润性：

```bash
make watch
```

<!--
The Makefile offers more than just building and watching, it also offers the following useful options:
-->

Makefile 除了构造和监视之外，还提供了下列有用的其他功能：

```make
build                      # 构造 PLFA
watch                      # 构造并架起 PLFA，监视文件变更并重新构造
test                       # 测试网页版是否有坏链、不合法的 HTML 等
test-epub                  # 测试 EPUB 电子书版是否符合 EPUB3 标准
clean                      # 清理 PLFA 构造
init                       # 设置 Git 钩子脚本（见下文）
update-contributors        # 从 GitHub 中拉取新贡献者信息至 contributors/
list                       # 列出所有构造功能
```

<!--
For completeness, the Makefile also offers the following options, but you’re unlikely to need these:
-->

完整来说，Makefile 还提供了下列选项，但你可能不会需要用到：

```make
legacy-versions            # 构造老版本的 PLFA
setup-install-bundler      # 安装 Ruby Bundler （‘legacy-versions’ 所需要）
setup-install-htmlproofer  # 安装 HTMLProofer （‘test’ 和 Git 钩子脚本所需要）
setup-check-fix-whitespace # 检查 fix-whitespace 是否已安装 （Git 钩子脚本所需要）
setup-check-epubcheck      # 检查 epubcheck 是否已安装 （EPUB 测试所需要）
setup-check-gem            # 检查 RubyGems 是否已安装
setup-check-npm            # 检查 Node 包管理器是否已安装
setup-check-stack          # 检查 Haskell 工具 Stack 是否已安装
```

<!--
The [EPUB version][epub] of the book is built as part of the website, since it’s hosted on the website.
-->

本书的 [EPUB 电子书版本][epub]会随着网站一起构造，因为网站上包括了电子书版本。

<!--
### Git hooks
-->

### Git 钩子脚本

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
stack install fix-whitespace
```

<!--
If you want Stack to use your system installation of GHC, you can pass the `--system-ghc` flag and select the appropriate `stack-*.yaml` file, like when installing [Agda](#installing-agda-using-stack).
-->

如果你想让 Stack 使用你系统中安装的 GHC，那么可以传入 `--system-ghc` 参数并选择对应的
`stack-*.yaml` 文件，就像在安装 [Agda](#installing-agda-using-stack) 时那样。

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

[epub]: https://plfa.github.io/plfa.epub
[plfa]: http://plfa.inf.ed.ac.uk
[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-calver]: https://img.shields.io/badge/calver-20.07-22bfda
[plfa-latest]: https://github.com/plfa/plfa.github.io/releases/latest
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip
[haskell-stack]:  https://docs.haskellstack.org/en/stable/README/
[haskell-ghc]: https://www.haskell.org/ghc/
[git]: https://git-scm.com/downloads
[agda]: https://github.com/agda/agda/releases/tag/v2.6.1.3
[agda-version]: https://img.shields.io/badge/agda-v2.6.1.3-blue.svg
[agda-docs-holes]: https://agda.readthedocs.io/en/v2.6.1.3/getting-started/quick-guide.html
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.1.3/tools/emacs-mode.html
[agda-docs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.1.3/tools/emacs-mode.html#notation-for-key-combinations
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.1.3/tools/package-system.html#example-using-the-standard-library
[emacs]: https://www.gnu.org/software/emacs/download.html
[emacs-tour]: https://www.gnu.org/software/emacs/tour/
[emacs-home]: https://www.gnu.org/software/emacs/manual/html_node/efaq-w32/Location-of-init-file.html
[aquamacs]: http://aquamacs.org/
[spacemacs]: https://www.spacemacs.org/
[spacemacs-agda]: https://develop.spacemacs.org/layers/+lang/agda/README.html
[vscode]: https://code.visualstudio.com/
[vscode-agda]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[atom]: https://atom.io/
[atom-agda]: https://atom.io/packages/agda-mode
[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.3-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.3
[fix-whitespace]: https://github.com/agda/fix-whitespace
[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer
[hakyll]: https://jaspervdj.be/hakyll/
[pandoc]: https://pandoc.org/installing.html
[pandoc-markdown]: https://pandoc.org/MANUAL.html#pandocs-markdown
[commonmark]: https://commonmark.org/
[epubcheck]: https://github.com/w3c/epubcheck
[xcode]: https://developer.apple.com/xcode/
[font-sourcecodepro]: https://github.com/adobe-fonts/source-code-pro
[font-dejavusansmono]: https://dejavu-fonts.github.io/
[mononoki]: https://github.com/madmalik/mononoki
[font-freemono]: https://www.gnu.org/software/freefont/
[font-mononoki]: https://madmalik.github.io/mononoki/
[font-mononoki-debian]: https://packages.debian.org/sid/fonts/fonts-mononoki
[cask-fonts]: https://github.com/Homebrew/homebrew-cask-fonts
