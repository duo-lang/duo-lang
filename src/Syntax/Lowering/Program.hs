module Syntax.Lowering.Program where

import Data.Text (Text)    

import Syntax.Lowering.Terms (lowerTerm, lowerCommand)
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Terms qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.CommonTerm

-- TODO: Deprecate and unify
lowerIsRec :: CST.IsRec -> AST.IsRec
lowerIsRec CST.Recursive = AST.Recursive
lowerIsRec CST.NonRecursive = AST.NonRecursive

lowerAnnot :: PrdCnsRep pc -> CST.TypeScheme -> AST.TypeScheme (AST.PrdCnsToPol pc)
lowerAnnot = undefined

lowerMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> Maybe (AST.TypeScheme (AST.PrdCnsToPol pc))
lowerMaybeAnnot = undefined

-- TODO: Deprecate and unify
lowerModName :: CST.ModuleName -> AST.ModuleName
lowerModName mod = AST.ModuleName (CST.unModuleName mod)

lowerDecl :: CST.Declaration -> Either Text (AST.Declaration Parsed)
lowerDecl (CST.PrdCnsDecl loc Prd isrec fv annot tm) = AST.PrdCnsDecl loc PrdRep (lowerIsRec isrec) fv (lowerMaybeAnnot PrdRep annot) <$> (lowerTerm PrdRep tm)
lowerDecl (CST.PrdCnsDecl loc Cns isrec fv annot tm) = AST.PrdCnsDecl loc CnsRep (lowerIsRec isrec) fv (lowerMaybeAnnot CnsRep annot) <$> (lowerTerm CnsRep tm)
lowerDecl (CST.CmdDecl loc fv cmd) = AST.CmdDecl loc fv <$> (lowerCommand cmd)
lowerDecl (CST.DataDecl loc dd)    = pure $ AST.DataDecl loc dd
lowerDecl (CST.ImportDecl loc mod) = pure $ AST.ImportDecl loc (lowerModName mod)
lowerDecl (CST.SetDecl loc txt)    = pure $ AST.SetDecl loc txt
lowerDecl CST.ParseErrorDecl       = Left "Unreachable: ParseErrorDecl cannot be parsed"

lowerProgram :: CST.Program -> Either Text (AST.Program Parsed)
lowerProgram = sequence . fmap lowerDecl
