# Further Reading

Duo is based on the work of many other researchers.
The general programming style and the syntax are inspired by languages from the ML family (SML, Miranda, Haskell, OCaml, Agda, Idris, Coq).
Below, we include some further reading on specific aspects of the Duo language.

## Algebraic Subtyping

Type inference uses the algebraic subtyping approach.
More specifically, we use constraint-based type inference with subtyping constraints.
We use a bi-unification algorithm to solve these constraints and type automata to simplify the resulting types.
We relied heavily on the following resources describing this approach.

- ["Algebraic Subtyping"](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf), the PhD thesis of Stephen Dolan.
- ["The Simple Essence of Algebraic Subtyping"](https://lptk.github.io/files/%5Bv1.8%5D%20simple-essence-algebraic-subtyping.pdf) by Lionel Parreaux.
- ["Polymorphism, Subtyping and Type Inference in MLsub"](https://www.repository.cam.ac.uk/bitstream/handle/1810/261583/Dolan_and_Mycrof-2017-POPL-AM.pdf) by Stephen Dolan and Alan Mycroft.

## Codata Types

Codata types have been known for a long time, but they haven't caught on in a popular programming language yet.
We provide some standard references on codata types below.

- "Codatatypes in ML" by Tatsuyo Hagino is the canonical early reference to codata types.
- "Codata in Action" by Paul Downen, Zachary Sullivan, Zena Ariola and Simon Peyton Jones provides a good motivation for, and introduction to, codata types.
- "Copatterns: programming infinite structures by observations" by Andreas Abel, Brigitte Pientka, David Thibodeau and Anton Setzer introduced copattern matching as a convenient and principled syntactic construct to work with codata types, similar to how pattern matching works for data types.
- "Automatic Refunctionalization to a Language with Copattern Matching: With Applications to the Expression Problem" by Tillmann Rendel, Julia Trieflinger and Klaus Ostermann show how data and codata types correspond to the two different axes of extensibility in the expression problem, and how defunctionalization and refunctionalization can be used to automatically transform data intro codata types, and vice versa.
Two follow-up papers, "Decomposition Diversity with Symmetric Data and Codata", and "Dualizing Generalized Algebraic Data Types by Matrix Transposition" extend this approach to nested and polymorphic programs, respectively. We plan to provide these transformations as editor actions for the Duo language.

## Producer/Consumer Duality

The duality between producers and consumers of a type corresponds, via the Curry-Howard isomorphism, to the duality between proofs and refutations in logic.
A proof system which exploits this duality of proofs and refutations is the Sequent Calculus, developed by Gentzen at the same time as his more popular relative, natural deduction.
At its core, Duo is based on a term assignment system for the sequent calculus, the \\(\lambda \mu \tilde\mu\\) calculus by Pierre-Louis Curien and Hugo Herbelin.
In this term assignment system, consumers correspond to a first-class notion of continuations.
We only cite some of the more important references of the extensive literature on term-assignment systems for the sequent calculus.

- TODO
