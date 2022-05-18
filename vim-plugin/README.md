# Recognize Filetype

To recognize `.ds` files as `dualsub`, copy the the content of `ftdetect/` into `$VIMDIR/ftdetect/`
All other steps require the filetype to be set to `dualsub` to work properly.

# Syntax highlighting

To use syntax highlighting, copy the content of `syntax/` into `$VIMDIR/syntax/`

# Language Server

You need a plugin which supports the language server protocol.
I recommend [coc.nvim](https://github.com/neoclide/coc.nvim).

You should first install the language server with `stack install dualsub` and then configure your language server plugin to use `dualsub`.
If you are using `coc`, then the config looks like this:
```
{
  "languageserver": {
    "dualsub": {
        "command": "dualsub",
        "args": ["lsp"],
        "filetypes": ["dualsub"]
    }
  }
}
```
The config file can easily be found by invoking `:CocConfig` inside vim.

# Snippets

There are some snippets which can be used in conjunction with the [UltiSnip](https://github.com/SirVer/ultisnips) plugin.
Simply copy the content of `UltiSnip/` into `$VIMDIR/UltiSnip/`.

# Notes

Instead of copying, you might want to consider symlinks instead, e.g. `ln -s $(pwd)/ftdetect/dualsub.vim $VIMDIR/ftdetect/dualsub.vim`.
