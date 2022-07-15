
# Installation script
Copying and editing files should now be unnecessary.
All this is done by the installation script.
Simply run `./install.sh` inside this directory.

## Dependencies
The above script assumes that the `coc.nvim` and `ultisnips` plugins are installed.
If they are not, the script won't fail, but the new configuration will have no effect.
Further, `jq` is required to write the `coc` config.

# Manual installation

## Recognize Filetype

To recognize `.ds` files as `duo`, copy the the content of `ftdetect/` into `$VIMDIR/ftdetect/`
All other steps require the filetype to be set to `duo` to work properly.

## Syntax highlighting

To use syntax highlighting, copy the content of `syntax/` into `$VIMDIR/syntax/`

## Language Server

You need a plugin which supports the language server protocol.
I recommend [coc.nvim](https://github.com/neoclide/coc.nvim).

You should first install the language server with `stack install duo-lang` and then configure your language server plugin to use `duo`.
If you are using `coc`, then the config looks like this:
```
{
  "languageserver": {
    "duo": {
        "command": "duo",
        "args": ["lsp"],
        "filetypes": ["duo"]
    }
  }
}
```
The config file can easily be found by invoking `:CocConfig` inside vim.

## Snippets

There are some snippets which can be used in conjunction with the [UltiSnip](https://github.com/SirVer/ultisnips) plugin.
Simply copy the content of `UltiSnip/` into `$VIMDIR/UltiSnip/`.

## Notes

Instead of copying, you might want to consider symlinks instead, e.g. `ln -s $(pwd)/ftdetect/duo.vim $VIMDIR/ftdetect/duo.vim`.
