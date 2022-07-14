# Duo

## About

Duo is a statically-typed, functional research programming language exploring ideas of duality and subtyping.
The general programming style is similar to programming languages in the ML tradition (SML, Miranda, Haskell, OCaml).
This means that the language provides a rich language for defining new types, and these types can be inferred using a powerful type inference mechanism.
Programs use familiar pattern matching constructs to work with algebraic datatypes, but also offer less familiar constructs like codata types and copattern matching.
The language de-emphasizes mutation, but we explore efficiency-oriented "on-the-metal" implementation issues.

## Guiding Ideas
Duo is a language focused on two central ideas; **Duality** and **Subtyping**.

- **Duality:** Duality is a well-known principle in logic, type theory and programming language theory.
  For example:
  - Monads are dual to Comonads.
  - Call-by-value evaluation is dual to call-by-name evaluation.
  - Data types are dual to codata types.
  - Producers/proofs are dual to consumers/refutations.
  - Sending is dual to receiving.

  Duo takes such dualities and explores how they can be used as a guiding principle in programming language design.
  The first-class treatment of consumers, in particular, allows for new ways to express programs which could otherwise only be expressed using continuation-passing style.

- **Subtyping:** Subtyping in programming languages is mostly associated with object-oriented programming and inheritance.
  Part of the reason for this association is that statically-typed functional programming languages heavily rely on type-inference, and it was widely thought that good type inference is incompatible with subtyping.
  We use the recently developed algebraic-subtyping approach to infer types.
  This approach allows to infer principal types with minimal need for user-provided type annotations, even in the presence of subtyping and parametric polymorphism.

## About Us

Duo is developed on [GitHub](https://github.com/ps-tuebingen/duolang) at the chair for programming languages at the University of Tübingen.
