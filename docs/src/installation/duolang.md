# Installation

Duo is implemented in Haskell and can be compiled from the sources using the `stack` build tool.

## Obtaining the stack build tool

There are two recommended ways to install `stack` on your system; only installing `stack` or using `ghcup` to manage your stack installation.

- In order to just install the stack tool, follow the instructions on their website [here](https://docs.haskellstack.org/en/stable/install_and_upgrade/).
- You can use `ghcup` to manage multiple different versions of the ghc Haskell compiler and other tools from the Haskell ecosystem, including stack.
  To install stack using `ghcup`, follow the instructions on the ghcup website [here](https://www.haskell.org/ghcup/).


Verify that your installation was succesfull and that the binary is on your path:

```console
> stack --version
Version 2.7.3, Git revision 7927a3...
```
## Building Duo from the sources

Clone the duo repository to your system:

```
git clone git@github.com:ps-tuebingen/duolang.git
```

Then, change into the duolang directory and use stack to build the binary

```console
> stack build
```

During the first compilation this can take a while, since a lot of the dependencies have to be compiled as well.
Subsequent compilations will be much faster.

In order to use the editor plugin and the LSP server, the `duo` binary has to be on the path.
We use `stack install` for this.

```console
> stack install
```

It is possible that you have to add the directory that the program was installed to to your `$PATH` environment variable.

Verify that the duo binary has been correctly installed by querying it for its version:

```console
> duo --version
Duo Version: 0.1.0.0
Git Commit: 81ec55800707cfdcd43a685d2e6fecd44a0429b8
Git Branch: main
```

