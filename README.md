---
layout: page
title: 使用说明
permalink: /GettingStarted/
translators : ["Rongxiao Fu"]
---

[![Build Status](https://travis-ci.org/Agda-zh/PLFA-zh.svg?branch=dev)](https://travis-ci.org/Agda-zh/PLFA-zh)
[![Agda](https://img.shields.io/badge/agda-2.5.4.2-blue.svg)](https://github.com/agda/agda/releases/tag/v2.5.4.2)
[![agda-stdlib](https://img.shields.io/badge/agda--stdlib-0.17-blue.svg)](https://github.com/agda/agda-stdlib/releases/tag/v0.17)
[![agda2html](https://img.shields.io/badge/agda2html-0.2.3.0-blue.svg)](https://github.com/wenkokke/agda2html/releases/tag/v0.2.3.0)

《编程语言基础：Agda 描述》的使用方法和《Programming Language Foundations in Agda》一致。

**要参与翻译请先阅读[翻译规范](https://github.com/Agda-zh/PLFA-zh/issues/1)**

<!---
Getting Started with PLFA
--->

# 开始使用 PLFA

<!---
There are several tools you need to work with PLFA:

  - [Agda](https://agda.readthedocs.io/en/v2.5.4.2/getting-started/installation.html)
  - [Agda standard library](https://github.com/agda/agda-stdlib/tree/5819a4dd9c965296224944f05b1481805649bdc2)
--->

为使用 PLFA，你需要以下工具：

  - [Agda](https://agda-zh.rtfd.io/zh_CN/latest/getting-started/installation.html)
  - [Agda 标准库](https://github.com/agda/agda-stdlib/tree/5819a4dd9c965296224944f05b1481805649bdc2)

<!---
For most of the tools, you can simply follow their respective build instructions.
We list the versions of our dependencies on the badges above.
--->

大部分工具的安装方式遵循其对应网页提供的说明即可。
本页顶部的徽章列出了 PLFA 使用的依赖版本。

<!---
You can get the latest version of Programming Language Foundations in Agda from Github,
either by cloning the repository,
or by downloading [the zip archive](https://github.com/plfa/plfa.github.io/archive/dev.zip):
--->

你可以执行下方的命令克隆仓库或者下载 zip 包（[原书](https://github.com/plfa/plfa.github.io/archive/dev.zip) / [中文版](https://github.com/Agda-zh/PLFA-zh/archive/dev.zip)）以从 GitHub 获取最新版的 PLFA。

原书：

    git clone https://github.com/plfa/plfa.github.io

中文版：

    git clone https://github.com/Agda-zh/PLFA-zh

<!---
Finally, we need to let Agda know where to find the standard library.
For this, you can follow the instructions [here](https://agda.readthedocs.io/en/v2.5.4.2/tools/package-system.html#example-using-the-standard-library).
--->

最后，我们需要让 Agda 知道标准库位于何处。[此处](https://agda-zh.rtfd.io/zh_CN/latest/tools/package-system.html#example-using-the-standard-library)的说明可供参考。

<!---
It is possible to set up PLFA as an Agda library as well.
If you are trying to complete the exercises found in the `tspl` folder, or otherwise want to import modules from the book, you need to do this.
To do so, add the path to `plfa.agda-lib` to `~/.agda/libraries` and add `plfa` to `~/.agda/defaults`, both on lines of their own.
--->

如果你想完成位于 `tspl` 目录内的习题，或者想导入书中的模块，PLFA 也可以被设置为一个 Agda 库。
完成此设置需要将 `plfa.agda-lib` 所处的路径作为单独的一行添加到 `~/.agda/libraries`，并将 `plfa` 作为单独的一行添加到 `~/.agda/defaults`。

<!---
Building the book
--->

# 构建本书

<!---
To build and host a local copy of the book, there are several tools you need *in addition to those listed above*:
--->

要在本地构建并部署本书，**在前文所列工具的基础之上**，你还需要：

  - [agda2html](https://github.com/wenkokke/agda2html)
  - [Ruby](https://www.ruby-lang.org/en/documentation/installation/)
  - [Bundler](https://bundler.io/#getting-started)

<!---
For most of the tools, you can simply follow their respective build instructions.
Most recent versions of Ruby should work.
--->

大部分工具的安装遵循其对应的网页提供的说明即可。Ruby 的较新版本应该都可以使用。

<!---
We advise installing agda2html using [Stack](https://docs.haskellstack.org/en/stable/README/):
--->

我们建议使用 [Stack](https://docs.haskellstack.org/en/stable/README/) 安装 agda2html：

    git clone https://github.com/wenkokke/agda2html.git
    cd agda2html
    stack install

<!---
Once you have installed these tools, you can build the book from source:
--->

安装完所有的工具后，我们就可以从源码构建本书了：

    make build

<!---
You can host your copy of the book locally by running:
--->

运行如下命令可以在本地部署本书：

    make serve

<!---
The Makefile offers more than just these options:

    make                      (see make test)
    make build                (builds lagda->markdown and the website)
    make build-offline        (builds lagda->markdown and the website offline)
    make build-incremental    (builds lagda->markdown and the website incrementally)
    make test                 (checks all links are valid)
    make test-offline         (checks all links are valid offline)
    make serve                (starts the server)
    make server-start         (starts the server in detached mode)
    make server-stop          (stops the server, uses pkill)
    make clean                (removes all ~unnecessary~ generated files)
    make clobber              (removes all generated files)
--->

Makefile 提供了更多可选的命令：

    make                      （见 make test）
    make build                （将 lagda 构建至 markdown 并构建网站）
    make build-offline        （将 lagda 构建至 markdown 并离线构建网站）
    make build-incremental    （将 lagda 构建至 markdown 并增量式构建网站）
    make test                 （检查所有链接的有效性）
    make test-offline         （离线检查所有链接的有效性）
    make serve                （启动服务）
    make server-start         （以分离模式启动服务）
    make server-stop          （使用 pkill 停止服务）
    make clean                （移除所有~非必要的~生成的文件）
    make clobber              （移除所有生成的文件）

<!---
If you simply wish to have a local copy of the book, e.g. for offline reading,
but don't care about editing and rebuilding the book, you can grab a copy of the
[master branch](https://github.com/plfa/plfa.github.io/archive/master.zip),
which is automatically built using Travis. You will still need Ruby and Bundler
to host the book (see above). To host the book this way, download a copy of the
[master branch](https://github.com/plfa/plfa.github.io/archive/master.zip),
unzip, and from within the directory run
--->

如果你只想获取本书的副本以供离线阅读，而并不关心如何编辑并构建本书，
那么你可以下载由 Travis 自动构建的 master 分支（[原书](https://github.com/plfa/plfa.github.io/archive/master.zip) / [中文版](https://github.com/Agda-zh/PLFA-zh/archive/master.zip)）。若要在本地部署本书，你需要 Ruby 和 Bundler（见上文）。请下载 master 分支的压缩包，并在解压后的目录中运行：

    bundle install
    bundle exec jekyll serve

<!---
GNU sed and macOS
--->

## GNU sed 和 macOS

<!---
The version of sed that ships with macOS is not fully compatible with the GNU sed.
Therefore, you may get errors such as:
--->

macOS 预装的 sed 版本和 GNU sed 并不完全兼容。因此，你可能会遇到类似这样的错误：

```
sed: 1: "out/plfa/Bisimulation.md": invalid command code o
```

<!---
You can fix this error by installing a GNU compatible version of sed, e.g. using [Homebrew](https://brew.sh/):
--->

你可以通过安装 GNU 兼容版 sed 来修复此错误，如执行以下 [Homebrew](https://brew.sh/) 命令：

```
brew install gnu-sed --with-default-names
```

<!---
Updating `agda2html`
--->

## 更新 `agda2html`

<!---
Sometimes we have to update agda2html.
To update your local copy, run the following commands from your clone of the
agda2html repository, or simply follow the installation instructions again:
--->

有时我们需要更新 agda2html。要更新你的本地副本，可以在你克隆的 agda2html 仓库中运行如下命令。
更简单的方法是按照前文所述的方法重新安装 agda2html。

    git pull
    stack install

<!---
Unicode characters
--->

## Unicode 字符

<!---
If you're having trouble typing the Unicode characters into Emacs, the end of
each chapter should provide a list of the unicode characters introduced in that
chapter. For a full list of supported characters, see
[agda-input.el](https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194).
--->

如果你在 Emacs 中输入 Unicode 字符时遇到困难，每一章的结尾都列出了该章引入的 Unicode 字符。所支持字符的完整列表请参阅 [agda-input.el](https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194)。

<!---
Using `agda-mode`
--->

## 使用 `agda-mode`

<!---
    ?            hole
    {!...!}      hole with contents
    C-c C-l      load buffer
--->

    ?            坑
    {!...!}      有内容的坑
    C-c C-l      加载缓冲区

<!---
Command to give when in a hole:

    C-c C-c x    split on variable x
    C-c C-space  fill in hole
    C-c C-r      refine with constructor
    C-c C-a      automatically fill in hole
    C-c C-,      Goal type and context
    C-c C-.      Goal type, context, and inferred type
--->

在洞上可用的命令：

    C-c C-c x    在变量 x 上分项（自动模式匹配）
    C-c C-空格   填坑
    C-c C-r      用构造器精化
    C-c C-a      自动填坑
    C-c C-,      目标类型和上下文
    C-c C-.      目标类型，上下文，以及推断的类型

<!---
See
[the emacs-mode docs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
for more details.
--->

更多细节请见 [emacs-mode 文档](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)

<!---
If you want to see messages beside rather than below your Agda code,
you can do the following:

Load your Agda file and do `C-c C-l`;
type `C-x 1` to get only your Agda file showing;
type `C-x 3` to split the window horizontally;
move your cursor to the right-hand half of your frame;
type `C-x b` and switch to the buffer called "Agda information"
--->

如果你希望在 Agda 代码侧边而非底部查看消息，可以参考如下操作：

  - 载入 Agda 文件并按 `C-c C-l`；
  - 按 `C-x 1` 以仅显示当前 Agda 文件；
  - 按 `C-x 3` 以垂直分割窗口；
  - 将光标移动到右侧窗口；
  - 按 `C-x b` 并输入 “Agda information” 以切换到该缓冲区。

<!---
Now, error messages from Agda will appear next to your file, rather than
squished beneath it.
--->

现在，来自 Agda 的错误消息将会在代码右侧显示，而非被压缩在底部的狭小空间里。

<!---
Fonts in Emacs
--->

## Emacs 中的字体

<!---
It is recommended that you add the following to the end of your emacs
configuration file at `~/.emacs`, if you have the mentioned fonts available:
--->

如果你有以下代码中提及的字体，推荐将这些代码添加到 Emacs 配置文件 `~/.emacs` 的末尾。

``` elisp
;; Setting up Fonts for use with Agda/PLFA
;;
;; default to DejaVu Sans Mono,
(set-face-attribute 'default nil
		    :family "DejaVu Sans Mono"
		    :height 120
		    :weight 'normal
		    :width  'normal)

;; fix \:
(set-fontset-font "fontset-default"
		  (cons (decode-char 'ucs #x2982)
			(decode-char 'ucs #x2982))
		  "STIX")
```

<!---
Markdown
--->

## Markdown

<!---
The book is written in
[Kramdown Markdown](https://kramdown.gettalong.org/syntax.html).
--->

本书使用 [Kramdown Markdown](https://kramdown.gettalong.org/syntax.html) 编写。

<!---
Travis Continuous Integration
--->

## Travis 持续集成

<!---
You can view the build history of PLFA at [travis-ci.org](https://travis-ci.org/plfa/plfa.github.io).
--->

你可以在 <https://travis-ci.org/> 查看 PLFA 的构建历史（[原书](https://travis-ci.org/plfa/plfa.github.io) / [中文版](https://travis-ci.org/Agda-zh/PLFA-zh)）。
