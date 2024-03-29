# Syntax Representations

We use multiple representations of the syntax in the compiler.
In the normal (i.e. forward) direction, we encounter them in the following order:

```
Text -parse-> CST -resolve-> RST -desugar-> Core -infer-> TST
```

This direction generally adds information to the syntax trees.
Additionally, we can go back in the opposite direction.
This is necessary for some tests, as well as for some LSP editor actions which require the output of some
transformation to be shown again to the user.

### CST

The concrete syntax tree (CST) is the output of the parser.
Operators are not yet resolved according to their precedence and associativity.

All Prettyprinting is done using the CST, other syntax representations are prettyprinted by first transforming back to the CST representation.

### RST

In the resolved syntax tree (RST), the precedence and associativity of operators have been resolved.
Every name is fully resolved with the module + declaration where it has been introduced.
Every unpolarized `Typ` has been replaced by a polarized `Typ Pos` resp. `Typ Neg`, and every `Term` has
been replaced by the corresponding `Term Prd` and `Term Cns`.

### Core

The core representation does not contain any of the syntactic sugar available in the surface language.
It is essentially a direct representation of the lambda mu/tilde mu calculus.
Core does not yet contain all the information from type inference.

### TST 

In the typed syntax tree (TST), every node contains type information which was generated during type inference.
The TST representation is used for optimization and as a source language for code generation.
