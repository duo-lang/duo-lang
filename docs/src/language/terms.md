# Terms

DualSub is based on a term language for the sequent calculus.
In distinction to lambda calculus, the term language of natural deduction, we have a first-class treatment of both
**producers** and **consumers** of each type.
In addition, there is a third syntactic category, commands.
Commands are executable pieces of code.
For example, it is possible to define producers, consumers and commands at the toplevel of the program:

```
def someProducer[*] := ...;
def someConsumer(*) := ...;
def someCommand := ...;
```

Toplevel declarations of consumers and producers can additionally be annotated with a type scheme.

```
def someProducer[*] : ... := ...;
def someConsumer(*) : ... := ...;
```

For example, the polymorphic identity function is defined like so:

```
def id[*] : forall (a : CBV). a -> a :=
  \x => x;
```

If a function is used recursively in its own body, the `rec` keyword is necessary:

```
def rec add[*] := \x y => case x of {
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

DualSub supports control operators in the form of the \\(\mu\\) and \\(\tilde\mu\\) constructs of the \\(\lambda\mu\tilde\mu\\) calculus.
Both constructs use identical syntax.

```
def ex1[*] := mu x. ExitSuccess;
def ex2(*) := mu x. ExitSuccess;
```

## Producer Introduction Rules

The rules for data and codata types are given separately

#### Data Types

Introduction rules for producers of codata types are just uses of the corresponding constructors:

```
data Nat : CBV { Z, S(Nat) };
def ex1[*] := S(Z);
```

#### Codata Types

Introduction rules for producers of codata types consists of copattern matching.

```
codata Pair(+a : CBV, +b : CBV) : CBV {
    PiLeft[a],
    PiRight[b]
};

def ex1[*] : Pair(Nat,Bool):= cocase
  { PiLeft[*] => 5,
    PiRight[*] => True
  };

def ex2[*] : Pair(Nat,Bool):= cocase
  { PiLeft[k] => 5 >> k,
    PiRight[k] => True >> k
  };
```

## Consumer Introduction Rules

The rules for data and codata types are given separately

#### Data Types

A consumer of a data type is introduced using pattern matching

```
def ex1(*) := case {
    Z => ExitSuccess,
    S(x) => ExitSuccess
};
```

#### Codata Types
Introduction rules for consumers of codata types use one of the available destructors.

```
def ex1(*) : NatStream := Head[mu x.ExitSuccess];
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

