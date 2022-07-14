# Editor Integration

Editor integration is currently only available for VSCode.
The editor integration uses the language server protocol, so it should be possible to support other editors in the future.

## Installing the VSCode extension

We provide a prebuilt `.vsix` extension which can be installed as an extension to VSCode.
The prebuilt extension is available as a release on our [GitHub page](https://github.com/ps-tuebingen/duolang).
Once you have downloaded the extension, use the following command to install the extension as a plugin in VSCode.

```console
code --install-extension duolang-client-0.0.1.vsix
```
The extension itself provides syntax highlighting and indentation support.
The advanced features are implemented using a language server, and require the `duo` binary to be available on the path.
