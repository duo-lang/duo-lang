# Terms

DualSub is based on a term language for the sequent calculus.
In distinction to lambda calculus, the term language of natural deduction, we have a first-class treatment of both
**producers** and **consumers** of each type.
In addition, there is a third syntactic category, commands.
Commands are executable pieces of code.
For example, it is possible to define producers, consumers and commands at the toplevel of the program, using `prd`, `cns` and `cmd` declarations:

```
prd someProducer := ...;
cns someConsumer := ...;
cmd someCommand := ...;
```

Toplevel declarations of consumers and producers can additionally be annotated with a type scheme.

```
prd someProducer : ... := ...;
cns someConsumer : ... := ...;
```

For example, the polymorphic identity function is defined like so:

```
prd id : forall (a : CBV). a -> a :=
  \x => x;
```

If a function is used recursively in its own body, the `rec` keyword is necessary:

```
prd rec add := \x y => case x of {
    Z => y,
    S(x) => S(add x y)
}
```

There are five categories of terms in DualSub:

- Core constructs, which are independent of any concrete type.
- Producer introduction rules
- Consumer introduction rules
- Producer elimination rules
- Consumer elimination rules

## Core constructs

DualSub supports control operators in the form of the mu and tilde/mu constructs of the lambda mu tilde/mu calculus.
Both constructs use identical syntax.

```
prd ex1 := mu x. Done;
cns ex2 := mu x. Done;
```

## Producer Introduction Rules

The rules for data and codata types are given separately

#### Data Types

Introduction rules for producers of codata types are just uses of the corresponding constructors:

```
data Nat : CBV { Z, S(Nat) };
prd ex1 := S(Z);
```

#### Codata Types

Introduction rules for producers of codata types consists of copattern matching.

```
codata Pair(+a : CBV, +b : CBV) : CBV {
    PiLeft[a],
    PiRight[b]
};

prd ex1 : Pair(Nat,Bool):= comatch
  { PiLeft[*] => 5,
    PiRight[*] => True
  };

prd ex2 : Pair(Nat,Bool):= comatch
  { PiLeft[k] => 5 >> k,
    PiRight[k] => True >> k
  };
```

## Consumer Introduction Rules

The rules for data and codata types are given separately

#### Data Types

A consumer of a data type is introduced using pattern matching

```
cns ex1 := match {
    Z => Done,
    S(x) => Done
};
```

#### Codata Types
Introduction rules for consumers of codata types use one of the available destructors.

```
cns ex1 : NatStream := Head[mu x.Done];
```


## Producer Elimination Rules

The rules for data and codata types are given separately

#### Data Types

TODO

#### Codata Types

TODO


## Consumer Elimination Rules

The rules for data and codata types are given separately

#### Data Types

TODO

#### Codata Types

TODO

