# Resources

We will work with the dependently typed functional programming
language
[Agda](https://agda.readthedocs.io/en/latest/index.html). There is a
standard library, but we are not going to use it.

## Agda installation

General instructions are available in the [Agda Manual](https://agda.readthedocs.io/en/latest/getting-started/installation.html).

## Agda resources that you will need for daily use

 * [Getting started](https://agda.readthedocs.io/en/latest/getting-started/index.html) with Agda.
 * [Language reference](https://agda.readthedocs.io/en/latest/language/index.html)
 * [Agda mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
 * [Agda mode key bindings](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#keybindings)
 * [Global commands](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#global-commands)
 * [Commands in context of a goal](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#commands-in-context-of-a-goal)
 * [Other commands](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#other-commands)
 * [Unicode input](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input)

## Emacs resources

Agda has a very nice interactive environment for writing programs which works in the text editor [emacs](http://www.gnu.org/software/emacs/).

 * [Install emacs](https://www.gnu.org/software/emacs/download.html)
 * [A guided tour of Emacs](https://www.gnu.org/software/emacs/tour/index.html)
 * [Emacs manual](https://www.gnu.org/software/emacs/manual/html_node/emacs/index.html)
 * [Emacs reference card](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf)
 * [A tutorial introduction to emacs](https://www2.lib.uchicago.edu/keith/tcl-course/emacs-tutorial.html)

The [Getting Started](https://plfa.github.io/GettingStarted/) section of the online book
[Programming Language Foundations in Agda](https://plfa.github.io/) has a nice installation guide as well as a summary of emacs commands.

We will maintain a sample emacs configuration file which you may wish to use as a reference [here](/files/Resources/sample.emacs).

### Sample emacs configuration

[Here](sample.emacs) is a sample `.emacs` Agda configuration file that
in particular will make sure that your fonts are rendered
correctly. Place the contents of this file at `~/.emacs` in your
computer. If this file doesn't exist, create it.

## Installing Agda in debian-based linux, including ubuntu

Run this in a terminal:
```terminal
$ sudo apt-get install agda
$ agda-mode setup
```
1. Add this line to your `~/.emacs` configuration file:

   `(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))`

## Installing Agda in MacOS

1. Install the [Homebrew](https://brew.sh/) package manager if you don't already have it.

Run this in a terminal:
```terminal
$ brew install agda
$ agda-mode setup
```

1. Add this line to your `~/.emacs` configuration file:

   `(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))`

## Installing Agda on Windows

For Windows users who want to install Agda locally, you can do the following:

1. Open `PowerShell` with Admin privileges

1. Install Chocolatey:

   `Set-ExecutionPolicy Bypass -Scope Process -Force; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))`

1. Install cabal:

   `choco install cabal`

1. Update cabal:

   `cabal update`

1. Install ghc:

   `choco install ghc`

1. *Reload PowerShell* and install Agda:

   `cabal install Agda`

1. Install emacs:

   `choco install emacs`

1. At this point you will need to add the Agda folder to your PATH. To do this:

   * Hit the windows key
   * Type "environment" and hit Enter
   * Click the "Environment Variables..." button
   * In the System variables list, scroll down to Path, click on it and click Edit
   * Click New
   * Add `C:\Users\YOURUSERNAME\.local\bin`

1. Setup Agda:

   `agda-mode setup`

1. Install DejaVu Sans Mono and Symbola fonts -- make the former your default font and the latter your fallback font by adding the following to your `.emacs` file:

   `(set-fontset-font "fontset-default" nil (font-spec :name "DejaVu Sans Mono"))`
   `(set-fontset-font t nil "Symbola" nil 'append)`

   * To find the `.emacs` file, load up emacs (type `emacs` into your terminal) and then do `C-x C-f`, then type `~\.emacs`

1. Add this line to your `~/.emacs` configuration file:

   `(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))`

**For questions about Windows installation, ask our lecturer Todd Ambridge.**

## Advanced Agda installation in various operating systems

[Read the docs](https://agda.readthedocs.io/en/latest/getting-started/installation.html).

## Visual Studio Code

There is a [plugin for Agda support](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode) available on the Visual Studio Marketplace. We haven't tried it.

## Further reading

 * [The Agda Wiki](https://wiki.portal.chalmers.se/agda/pmwiki.php)
 * [Agda tutorials](https://wiki.portal.chalmers.se/agda/Main/Othertutorials)
 * [Dependently Typed Programming in Agda](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf)
 * [Dependent types at work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)

## Advanced reading

 * [Programming Language Foundations in Agda](https://plfa.github.io/)
 * [Dependent types at work](https://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)
