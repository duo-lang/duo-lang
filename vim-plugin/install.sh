#!/usr/bin/env sh

VIMDIR=$HOME/.vim/

cdir=$PWD
cd ..
stack install duo
cd $cdir

link_file() {
    dir=$VIMDIR/$1
    file=$dir/$2
    if ! test -d $dir; then
        echo "Directory $dir is missing!" >&2
    elif test -e $file; then
        echo "File $file already exists!" >&2
    else
        ln -s $PWD/$1/$2 $file
    fi
}

link_file ftdetect duo.vim
link_file syntax duo.vim
link_file UltiSnips duo.snippets

if type jq > /dev/null; then
    cocfile=$VIMDIR/coc-settings.json
    tmpf=$(mktemp --tmpdir=$(dirname $cocfile) -t)
    jq '.languageserver.duo = { command: "duo", args: [ "lsp" ], filetypes: [ "duo" ] }' $cocfile > $tmpf
    mv $tmpf $cocfile
else
    echo "jq not found. Please configure Coc by hand" >&2
fi
