# LeanScratch

This repo collects some formalizations of books I am currently reading. Below
are short descriptions of each subdirectory.

## CTIC

This formalizes some results from *[Category Theory in
Context](https://math.jhu.edu/~eriehl/context.pdf)*. I use Mathlib, but try to do
so in a way that strikes a balance between utilizing existing background lemmas
and working through the proofs myself.

## Untyped

A formalization of the untyped lambda calculus with de Bruijn indices, with
proofs of confluence and progress. I primarily use Barendregt's *The Lambda
Calculus, Its Syntax and Semantics*, Pierce's *Types and Programming Languages*,
*[Software Foundations](https://softwarefoundations.cis.upenn.edu/)*, and
*[Programming Language Foundations in Agda](https://plfa.github.io/)* as
references. Other existing formalizations that were helpful are mentioned in
comments. (The shifting definitions especially are directly taken from an Agda
formalization)

## LocallyNameless

A formalization of the untyped lambda calculus using a locally nameless
representation, also with a confluence proof. This is where I will try to
formalize some categorical semantics, as the locally nameless representation
allows for talking about models in the sense that Barendregt does.
