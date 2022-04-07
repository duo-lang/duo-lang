module Translate.EmbedCore where

import Syntax.Common
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Program qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core

embedCmdCase :: Core.CmdCase -> RST.CmdCase
embedCmdCase = undefined

embedCoreTerm :: Core.Term pc -> RST.Term pc
embedCoreTerm = undefined

embedCoreCommand :: Core.Command -> RST.Command
embedCoreCommand = undefined

embedCoreProg :: Core.Program -> RST.Program
embedCoreProg = fmap embedCoreDecl

embedCoreDecl :: Core.Declaration -> RST.Declaration
embedCoreDecl = undefined