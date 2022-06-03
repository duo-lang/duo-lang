
if exists("b:current_syntax")
  finish
endif

"syn keyword dsKeyword match comatch prd cns cmd def with Done Print forall data codata rec mu
syn keyword dsKeyword case cocase def of ExitSuccess ExitFailure Print forall data codata rec mu import return set Top Bot CBV CBN refinement constructor destructor type operator at leftassoc rightassoc cmd prd cns

"syn match dsSymbs ':=\|=>\|>>\|\\/\|/\\\|<:\|<<:\|:>>'
syn match dsSymbs ':=\|=>\|>>\|\\/\|/\\\|<:'
syn match dsLit '\v<[0-9]+>'
"syn match dsComment '#.*$'
syn match dsComment '--.*$'


syn region dsPrdArgList start="(" end=")" contains=dsPrdArg
syn region dsCnsArgList start="\[" end="]" contains=dsCnsArg

syn match dsPrdArg '\v<\k*>' contained
syn match dsCnsArg '\v<\k*>' contained

let b:current_syntax = "dualsub"

hi def link dsKeyword Keyword
hi def link dsLit Number
hi def link dsSymbs Macro
"hi def link dsSymbs Operator
hi def link dsComment Comment
