# Types

## Kinds and Evaluation Order

TODO

## Builtin Types

There are three builtin types which correspond to the numeric types supported by most modern architectures.
They are given in the following table.

| Type       | Kind    | Explanation                                     |
|------------|---------|-------------------------------------------------|
| UnboxedI64 | KindI64 | Unboxed signed 64-Bit integers                  |
| UnboxedU64 | KindU64 | Unboxed unsigned 64-Bit integers                |
| UnboxedF64 | KindF64 | Unboxed 64-Bit precision floating point numbers |

Since they are unboxed, it is in general not possible to apply a polymorphic function to an argument of a builtin type.

## Nominal Types

DualSub has two different variants of nominal types; nominal data types and nominal codata types.

### Nominal Data Types

Nominal data types are declared using the `data` keyword.
For example, the following two declarations declare Booleans and Peano natural numbers, respectively.

```
data Bool : Type CBV { True, False };

data Nat : Type CBV { Zero, Succ(Nat) };
```

We can also use nominal data types to declare the unit and void type.

```
data Unit : Type CBV { MkUnit };
data Void : Type CBV {};
```

### Nominal Codata Types

Codata types are introduced using the `codata` keyword.

One of the standard examples of a codata type is the example of an infinite stream of natural numbers, called `NatStream`.

```
codata NatStream : Type CBN { Head[Nat], Tail[NatStream] };
```


## Structural Types

Similarly to nominal types, structural types also come in two variants; structural data types and structural codata types.

### Structural Data Types

```
constructor True;
```
TODO

### Structural Codata Types

```
destructor False;
```
TODO

## Structural Refinement Types

Structural refinement types are a novel idea in DualSub which combines features from both nominal and structural types.
They are declared similarly to nominal types, but use the additional keyword `refinement` in front of the declaration

```
refinement data Bool : Type CBV { True, False };
```
TODO

```
refinement codata TrafficLight : Type CBN { ... }
```

