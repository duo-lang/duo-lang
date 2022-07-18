
if exists("b:current_syntax")
  finish
endif

"syn keyword duoKeyword match comatch prd cns cmd def with Done Print forall data codata rec mu
syn keyword duoKeyword case cocase def of ExitSuccess ExitFailure Print forall data codata rec mu import return set Top Bot CBV CBN refinement constructor destructor type operator at leftassoc rightassoc cmd prd cns class instance

"syn match duoSymbs ':=\|=>\|>>\|\\/\|/\\\|<:\|<<:\|:>>'
syn match duoSymbs ':=\|=>\|>>\|\\/\|/\\\|<:'
syn match duoLit '\v<[0-9]+>'
"syn match duoComment '#.*$'
syn match duoComment '--.*$'


syn region duoPrdArgList start="(" end=")" contains=duoPrdArg
syn region duoCnsArgList start="\[" end="]" contains=duoCnsArg

syn match duoPrdArg '\v<\k*>' contained
syn match duoCnsArg '\v<\k*>' contained

let b:current_syntax = "duo-lang"

hi def link duoKeyword Keyword
hi def link duoLit Number
hi def link duoSymbs Macro
"hi def link duoSymbs Operator
hi def link duoComment Comment
