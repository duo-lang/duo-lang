# Documentation

This folder contains the documentation for DualSub.
The docs are written in Markdown, and we use [mdbook](https://github.com/rust-lang/mdBook) to compile them to a html page.
The manual for mdbook can be found [here](https://rust-lang.github.io/mdBook/).

## Installing mdbook

In order to build the documentation locally you need the mdbook binary.
The simplest way to obtain mdbook is to get a rust toolchain using [rustup](https://rustup.rs/).
You can then use the `cargo` tool to install mdbook using [these](https://rust-lang.github.io/mdBook/guide/installation.html) instructions in the mdbook user guide.

## Building the documentation

The `mdbook` binary contains a builtin webserver which can serve the documentation.
In order to use this builtin webserver use:

```
mdbook serve --open
```
