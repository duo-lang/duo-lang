
" call like this: call MakeInstance('Foo', 'foo', [2,1,2])
" on signature of function to be converted
function! MakeInstance(instName,funName,paramsIdx)
  let l:signature = split(getline('.'), '\s*::\s*')
  let l:oldFunName = l:signature[0]
  let l:paramList = split(l:signature[1], '\s*->\s*')
  let l:idx = 0
  let l:len = len(a:paramsIdx)
  let l:params = []
  while l:idx < l:len
    let l:params += [l:paramList[a:paramsIdx[l:idx] - 1]]
    let l:idx += 1
  endwhile
  let l:paramLine = ""
  for pm in l:params
    let l:paramLine .= ((len(split(pm, " ")) > 1) ? '(' . pm . ')' : pm) . " "
  endfor
  let l:instanceLine = "instance " . a:instName . " " . l:paramLine . "where"

  call append(line('.')-1, l:instanceLine)
  normal! >}
  execute '%s/' . l:oldFunName . '/' . a:funName . '/g'
endfunction
