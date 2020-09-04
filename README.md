# stg-in-coq
Towards a formally verified Haskell compiler

This repository contains things I worked on for my MSc project: first steps towards a Coq-verified compiler for a call-by-need language via the [STG machine](https://www.microsoft.com/en-us/research/wp-content/uploads/1992/04/spineless-tagless-gmachine.pdf). The implementation dates back to __2010__ (:exclamation:), but it seems there's not been much progress in this direction since then.

Here, you'll find two separate projects:

- [stg](stg) - results described in my Haskell Symposium 2010 [paper](stg/pirog-biernacki-hs10.pdf): a Coq-verified derivation of the STG machine from a simpler big-step operational semantics,

- [vm](vm) - results described in my [MSc thesis](vm/thesis.pdf): a Coq-verified compiler from a core calculus to instructions of a virtual machine based on the STG machine (a Haskell version of the compiler was obtained via the Coq extraction mechanism).

:warning: The code itself does not contain much guidance, but the accompanying papers should suffice to understand what's going on. Also note that everything in this repo was written in a hurry, and I didn't go back to it after I defended the thesis.
