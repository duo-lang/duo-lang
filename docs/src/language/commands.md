# Commands

Commands are the syntactic category that actually gets executed when you run a program.
The entry point to a program, the main function, is also a command.

## The Exit Commands

The simplest commands are called `ExitSuccess` and `ExitFailure`, which are used to terminate the program.

#### Example 1:

We can write a simple command which just exits directly after it is called.

```
def exitAtOnce := ExitSuccess;
```

## The Apply Command

The most important command is called "Apply".
In the underlying logical calculus, the sequent calculus, it corresponds to the Cut rule.
The user, on the other hand, doesn't need to know about this.
Apply intuitively just combines a producer with a consumer of the same type.

We use the `>>` symbol to express a cut, and write the producer on the left side of it, and the consumer on the right hand side.


#### Example 1:

The following program cuts the producer `True` against a pattern match on booleans, and then exits the program.

```
def exit :=  True >> match { True => ExitSuccess; False => ExitSuccess };
```

## IO Actions

There currently are only two IO actions provided; `Print` and `Read`.

The following program uses both to read in two numbers from the console, and to print the output back to the console.

```
import Prelude;

def rec addA[*] := \x => \y => case x of { Z => y
                                      , S(z) => addA z S(y)
					        };

def main := Read[ mu x. Read[mu y. Print(addA x y);ExitSuccess]];
```
