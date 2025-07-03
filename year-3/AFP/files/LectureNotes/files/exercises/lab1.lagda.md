# Week 1 Lab Lecture

## Learning objectives

 * **[Install Agda](files/Resources/resources.md) in your own computer.**

 * Learn how to use the emacs [interactive Agda mode](https://my-agda.readthedocs.io/en/latest/getting-started/quick-guide.html).

 * [Basic emacs](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf).

 * Basic Agda interactive mode in emacs.

## GitLab

We are going to use GitLab for this module. If you have studied with us in the previous years, you should have `git` installed, including `ssh` keys. Otherwise, please ask for help in the lab.

  * We assume that you learned the basics of `git` in the module Functional Programming and possibly in other modules.

  * You will need to `git pull` regularly, as we update this repository regularly, in particular to get the weekly exercises.

  * **Don't modify** any of the existing files as you will get conflicts.

  * If you want to experiment with any of the provided files, which you should certainly do when you are studying, make a copy of the file with a new name. Don't forget to change the line `module filename where` with the new name you have chosen.

## Editing your first Agda file

 1. Now let's edit our first Agda file from the terminal.

    ```terminal
    $ git clone git@git.cs.bham.ac.uk:afp/afp-learning-2024-2025.git
    $ cd ~/afp-learning-2024-2025/files/LectureNotes/files/exercises
    $ cp lab1.lagda.md my-lab1.lagda.md
    $ emacs my-lab1.lagda.md
    ```

    * Now you should be seeing this file in emacs. Find this position and start working following our verbal instructions.

    * In a browser, go to [Key bindings](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#keybindings).

    * In a browser, open [Emacs reference card](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf).

## `ctrl-g ctrl-g`

You will need to type this when you start a sequence of emacs commands but want to give up without completing the sequence.

## Our first Agda file

Within emacs now type `ctrl-c ctrl-l`. This will "load" the Agda file and check it for correctness. The following program fragment has holes that we will fill interactively using the emacs mode for Agda. You can cheat by looking at the handout [introduction](/files/LectureNotes/files/introduction.lagda.md). But you *should not* copy and paste. Instead, you should learn and use the interactive mode following the lecturers verbal and visual instructions.

```agda
module exercises.my-lab1 where

Type = Set

data Bool : Type where
 true false : Bool

data Maybe (A : Type) : Type where
 nothing : Maybe A
 just    : A → Maybe A

data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 10 _::_

data BinTree (A : Type) : Type where
 empty : BinTree A
 fork  : A → BinTree A → BinTree A → BinTree A

data RoseTree (A : Type) : Type where
 fork : A → List (RoseTree A) → RoseTree A

not : Bool → Bool
not x = {!!}

_&&_ : Bool → Bool → Bool
x && y = {!!}


_||_ : Bool → Bool → Bool
x || y = {!!}

infixr 20 _||_
infixr 30 _&&_

if_then_else_ : {A : Type} → Bool → A → A → A
if b then x else y = {!!}

_+_ : ℕ → ℕ → ℕ
x + y = {!!}

_*_ : ℕ → ℕ → ℕ
x * y = {!!}

infixr 20 _+_
infixr 30 _*_

length : {A : Type} → List A → ℕ
length xs = {!!}

_++_ : {A : Type} → List A → List A → List A
xs ++ ys = {!!}

infixr 20 _++_

map : {A B : Type} → (A → B) → List A → List B
map f xs = {!!}

[_] : {A : Type} → A → List A
[ x ] = x :: []

reverse : {A : Type} → List A → List A
reverse xs = {!!}

rev-append : {A : Type} → List A → List A → List A
rev-append []        ys = ys
rev-append (x :: xs) ys = rev-append xs (x :: ys)

rev : {A : Type} → List A → List A
rev xs = rev-append xs []
```
