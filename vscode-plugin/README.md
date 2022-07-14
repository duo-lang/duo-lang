# duolang-client

## Build the Visual Studio Code extension

Use the [vsce](https://github.com/microsoft/vscode-vsce) extension manager to build the language extension.
You can install vsce by invoking

```console
npm install -g vsce
vsce --version
```

You can build the extension by invoking the following command in this directory:

```console
vsce package
```

Alternatively, you can use the prebuilt .vsix file provided by the Github Action.

## Installing the Visual Studio Code extension

To install the vscode extension, use the following command

```console
code --install-extension duolang-client-0.0.1.vsix
```
