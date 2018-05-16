\begin{code}
module PrintTex where

import AST
import Subs
import CRL
import Formatter
import Data.List
import Data.Text hiding (map,concat)
import Data.Char hiding (toUpper, toTitle)
import OmegaDefs

print_tex_ZName :: ZName -> String
print_tex_ZName x = x

print_tex_ZGenFilt (Include _ZSExpr) = ""
print_tex_ZGenFilt (Choose _ZVar _ZExpr)
  = (print_tex_ZExpr (ZVar _ZVar)) ++" : " ++ (print_tex_ZExpr _ZExpr)
print_tex_ZGenFilt (Check _ZPred) = print_tex_ZPred _ZPred
print_tex_ZGenFilt (Evaluate _ZVar _ZExpr1 _ZExpr2) = ""

print_tex_ZExpr (ZVar (a,b,c)) = a
print_tex_ZExpr (ZInt _ZInt) = show (fromIntegral _ZInt)
print_tex_ZExpr (ZGiven _GivenValue)
  = "["++_GivenValue++"]"
print_tex_ZExpr (ZFree0 _ZVar)
  = (print_tex_ZExpr (ZVar _ZVar))
print_tex_ZExpr (ZFree1 _ZVar _ZExpr)
  = (print_tex_ZExpr (ZVar _ZVar))
    ++" \\ldata "
    ++(print_tex_ZExpr _ZExpr)
    ++" \\rdata"
print_tex_ZExpr (ZTuple _ZExpr_lst)
  = "("++(joinBy ", " $ (map print_tex_ZExpr _ZExpr_lst))++")"
print_tex_ZExpr (ZBinding _ZVar_ZExpr_lst) = ""
print_tex_ZExpr (ZSetDisplay _ZExpr_lst)
  = "{"++(joinBy ", " $ (map print_tex_ZExpr _ZExpr_lst))++"}"
print_tex_ZExpr (ZSeqDisplay _ZExpr_lst)
  = "\\langle"++(joinBy ", " $ (map print_tex_ZExpr _ZExpr_lst))++"\\rangle"
print_tex_ZExpr (ZFSet _ZFSet) = ""
print_tex_ZExpr (ZIntSet _ZInt1 _ZInt2) = ""
print_tex_ZExpr (ZGenerator _ZReln _ZExpr) = ""
print_tex_ZExpr (ZCross _ZExpr_lst)
  = (joinBy " \\cross " $  (map print_tex_ZExpr _ZExpr_lst))
print_tex_ZExpr (ZFreeType _ZVar _ZBranch_lst) = ""
print_tex_ZExpr (ZSetComp _ZGenFilt_lst ( _ZExpr)) = ""
print_tex_ZExpr (ZLambda _ZGenFilt_lst _ZExpr) = ""
print_tex_ZExpr (ZESchema _ZSExpr) = ""
print_tex_ZExpr (ZGivenSet _GivenSet) = ""
print_tex_ZExpr (ZUniverse) = ""
print_tex_ZExpr (ZCall _ZExpr1 _ZExpr2) = ""
print_tex_ZExpr (ZReln _ZReln) = ""
print_tex_ZExpr (ZFunc1 _ZFunc1) = ""
print_tex_ZExpr (ZFunc2 _ZFunc2) = ""
print_tex_ZExpr (ZStrange _ZStrange) = ""
print_tex_ZExpr (ZMu _ZGenFilt_lst ( _ZExpr)) = ""
print_tex_ZExpr (ZELet _ZVar_ZExpr_lst _ZExpr) = ""
print_tex_ZExpr (ZIf_Then_Else _ZPred _ZExpr1 _ZExpr2) = ""
print_tex_ZExpr (ZSelect _ZExpr _ZVar) = ""
print_tex_ZExpr (ZTheta _ZSExpr) = ""

print_tex_ZPred (ZFalse{reason=_}) = "\\false"
print_tex_ZPred (ZTrue{reason=_}) = "\\true"
print_tex_ZPred (ZAnd _ZPred1 _ZPred2)
  = "(" ++ (print_tex_ZPred _ZPred1) ++ " \\land " ++ (print_tex_ZPred _ZPred2)++")"
print_tex_ZPred (ZOr _ZPred1 _ZPred2)
  = "(" ++ (print_tex_ZPred _ZPred1) ++ " \\lor " ++ (print_tex_ZPred _ZPred2)++")"
print_tex_ZPred (ZImplies _ZPred1 _ZPred2)
  = "(" ++ (print_tex_ZPred _ZPred1) ++ " \\implies " ++ (print_tex_ZPred _ZPred2)++")"
print_tex_ZPred (ZIff _ZPred1 _ZPred2)
  = "(" ++ (print_tex_ZPred _ZPred1) ++ " \\iff " ++ (print_tex_ZPred _ZPred2)++")"
print_tex_ZPred (ZNot _ZPred)
  = "\\lnot (" ++ (print_tex_ZPred _ZPred)++")"
print_tex_ZPred (ZExists _ZGenFilt_lst _ZPred) = ""
print_tex_ZPred (ZExists_1 _ZGenFilt_lst _ZPred) = ""
print_tex_ZPred (ZForall _ZGenFilt_lst _ZPred) = ""
print_tex_ZPred (ZPLet _ZVar_ZExpr_lst _ZPred) = ""
print_tex_ZPred (ZEqual _ZExpr1 _ZExpr2)
  = "(" ++ (print_tex_ZExpr _ZExpr1) ++ " = " ++ (print_tex_ZExpr _ZExpr2)++")"
print_tex_ZPred (ZMember _ZExpr1 _ZExpr2)
  = "(" ++ (print_tex_ZExpr _ZExpr1) ++ " \\in " ++ (print_tex_ZExpr _ZExpr2)++")"
print_tex_ZPred (ZPre _ZSExpr) = "\\pre "++(print_tex_ZSExpr _ZSExpr)
print_tex_ZPred (ZPSchema _ZSExpr) = ""

print_tex_ZSExpr_decl_part (Choose _ZVar _ZExpr)
  = (print_tex_ZExpr (ZVar _ZVar))
    ++" : "
    ++(print_tex_ZExpr _ZExpr)
print_tex_ZSExpr_decl_part _ = ""

print_tex_ZSExpr_inv_part (Check _ZPred)
  = (print_tex_ZPred _ZPred)
print_tex_ZSExpr_inv_part _ = ""

print_tex_ZSExpr (ZSchema _ZGenFilt_lst)
  = (joinBy "; " $  (map print_tex_ZSExpr_decl_part _ZGenFilt_lst))
    ++ " | "
    ++ (joinBy " \\land " $  (map print_tex_ZSExpr_inv_part _ZGenFilt_lst))
print_tex_ZSExpr (ZSRef _ZSName _ZDecor_lst _ZReplace_lst) = ""
print_tex_ZSExpr (ZS1 _ZS1 _ZSExpr)
  = (print_tex_ZS1 _ZS1) ++ (print_tex_ZSExpr _ZSExpr)
print_tex_ZSExpr (ZS2 _ZS2 _ZSExpr1 _ZSExpr2)
  = (print_tex_ZSExpr _ZSExpr1) ++ (print_tex_ZS2 _ZS2) ++ (print_tex_ZSExpr _ZSExpr2)
print_tex_ZSExpr (ZSHide _ZSExpr _ZVar_lst) = ""
print_tex_ZSExpr (ZSExists _ZGenFilt_lst _ZSExpr) = ""
print_tex_ZSExpr (ZSExists_1 _ZGenFilt_lst _ZSExpr) = ""
print_tex_ZSExpr (ZSForall _ZGenFilt_lst _ZSExpr) = ""

print_tex_ZReplace (ZRename _ZVar1 _ZVar2) = ""
print_tex_ZReplace (ZAssign _ZVar _ZExpr) = ""

print_tex_ZSName (ZSPlain _String ) = _String
print_tex_ZSName (ZSDelta _String ) = "\\Delta "++_String
print_tex_ZSName (ZSXi _String) = "\\Xi "++_String

print_tex_ZS1 (ZSPre ) = "\\pre"
print_tex_ZS1 (ZSNot) = "\\lnot"

print_tex_ZS2 (ZSAnd ) = " \\land "
print_tex_ZS2 (ZSOr ) = " \\lor "
print_tex_ZS2 (ZSImplies ) = " \\implies "
print_tex_ZS2 (ZSIff) = " \\iff "
print_tex_ZS2 (ZSProject ) = " \\project "
print_tex_ZS2 (ZSSemi ) = " \\semi "
print_tex_ZS2 (ZSPipe) = ""

print_tex_ZBranch (ZBranch0 _ZVar) = ""
print_tex_ZBranch (ZBranch1 _ZVar _ZExpr) = ""

-- ZPara

print_text_channels (CircChannel cd) = [(CircChannel cd)]
print_text_channels (CircChanSet _ZName _CSExp) = [(CircChanSet _ZName _CSExp)]
print_text_channels _ = []

print_text_procs (Process cd) = [(Process cd)]
print_text_procs _ = []

print_text_assert (Assert cd) = [(Assert cd)]
print_text_assert _ = []

print_text_everything_else (CircChanSet _ZName _CSExp) = []
print_text_everything_else (CircChannel cd) = []
print_text_everything_else (Process cd) = []
print_text_everything_else (Assert cd) = []
print_text_everything_else x = [x]

print_tex_Circus :: [ZPara] -> String
print_tex_Circus x
    =  "\n\\begin{zed}"++(joinBy "" $ map print_tex_ZPara (concat$ map print_text_everything_else x))++"\n\\end{zed}\n"
    ++ "\n\\begin{circus}"++(joinBy "" $ map print_tex_ZPara (concat$ map print_text_channels x))++"\n\\end{circus}\n"
    ++ "\n\\begin{circus}"++(joinBy "" $ map print_tex_ZPara (concat$ map print_text_procs x))++"\n\\end{circus}\n"
    -- ++ "\n\\begin{assert}"++(joinBy "" $ map print_tex_ZPara (concat$ map print_text_assert x))++"\n\\end{assert}\n"

print_tex_ZPara :: ZPara -> String
print_tex_ZPara (ZGivenSetDecl _GivenSet) = ""
print_tex_ZPara (ZSchemaDef _ZSName _ZSExpr) = ""
print_tex_ZPara (CircChannel cd)
  = concat (map print_tex_CDecl cd)
print_tex_ZPara (CircChanSet _ZName _CSExp)
  = "\n\\circchannelset "++_ZName++" == "++( print_tex_CSExp _CSExp)++"\\\\"
print_tex_ZPara (Process _ProcDecl) = print_tex_ProcDecl _ProcDecl++"\\\\"
print_tex_ZPara (Assert _String) = ""--"\n\\also \""++_String++"\"\n"++"\\\\"
print_tex_ZPara _ = ""

-- CSExp
print_tex_CSExp (CSExpr _ZName)
  = _ZName
print_tex_CSExp (CSEmpty)
  = "\\emptyset"
print_tex_CSExp (CChanSet _ZName_lst)                       -- named chanset
  = "\\lchanset "
    ++(joinBy "," $(map print_tex_ZName _ZName_lst))
    ++" \\rchanset"
print_tex_CSExp (ChanSetUnion _CSExp1 _CSExp2)               -- chanset union
  = (print_tex_CSExp _CSExp1)
    ++" \\cup "
    ++(print_tex_CSExp _CSExp2)
print_tex_CSExp (ChanSetInter _CSExp1 _CSExp2)               -- chanset intersection
  = (print_tex_CSExp _CSExp1)
    ++" \\cap "
    ++(print_tex_CSExp _CSExp2)
print_tex_CSExp (ChanSetDiff _CSExp1 _CSExp2)
  = (print_tex_CSExp _CSExp1)
    ++" \\setminus "
    ++(print_tex_CSExp _CSExp2)

-- CDecl
print_tex_CDecl (CChan _ZName)
  = "\n\\circchannel "
    ++_ZName++"\\\\"
print_tex_CDecl (CChanDecl _ZName _ZExpr)
  = "\n\\circchannel "
    ++_ZName
    ++" : "
    ++(print_tex_ZExpr _ZExpr)++"\\\\"
print_tex_CDecl (CGenChanDecl _ZName _ZName1 _ZExpr)
  = "\n\\circchannel ["
     ++_ZName
     ++"] "
     ++_ZName1
     ++" : "
     ++(print_tex_ZExpr _ZExpr)++"\\\\"

print_tex_ProcDecl :: ProcDecl -> String
print_tex_ProcDecl (CProcess _ZName _ProcessDef)
  = "\n\\circprocess "
    ++_ZName
    ++" \\circdef "
    ++(print_tex_ProcessDef _ProcessDef)
    ++"\n"
print_tex_ProcDecl (CParamProcess _ZName _ZName_lst _ProcessDef)
  = "\n\\circprocess "
    ++_ZName
    ++" \\circdef N[N^{+}] \\circdef"
    ++(print_tex_ProcessDef _ProcessDef)
    ++"\n"
print_tex_ProcDecl (CGenProcess _ZName _ZName_lst _ProcessDef)
  = "\n\\circprocess ["
    ++(joinBy "," $(map print_tex_ZName _ZName_lst))
    ++"] "
    ++_ZName
    ++" \\circdef "
    ++(print_tex_ProcessDef _ProcessDef)
    ++"\n"

print_tex_ProcessDef :: ProcessDef -> String
print_tex_ProcessDef (ProcDefSpot _ZGenFilt_lst _ProcessDef)
  = (joinBy ";" $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot\n "++(print_tex_ProcessDef _ProcessDef)
print_tex_ProcessDef (ProcDefIndex _ZGenFilt_lst _ProcessDef)
  = (joinBy ";" $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circindex\n "++(print_tex_ProcessDef _ProcessDef)
print_tex_ProcessDef (ProcDef _CProc) = (print_tex_CProc _CProc)

print_tex_CProc :: CProc -> String
print_tex_CProc (CRepSeqProc _ZGenFilt_lst _CProc)
  = "\\Semi "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CProc _CProc)
print_tex_CProc (CRepExtChProc _ZGenFilt_lst _CProc)
  = "\\Extchoice "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CProc _CProc)
print_tex_CProc (CRepIntChProc _ZGenFilt_lst _CProc)
  = "\\Intchoice "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CProc _CProc)
print_tex_CProc (CRepParalProc _CSExp1 _ZGenFilt_lst _CProc)
  = "\\Parallel "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\lpar CS \\rpar \\circspot "++(print_tex_CProc _CProc)
print_tex_CProc (CRepInterlProc _ZGenFilt_lst _CProc)
  = "\\Interleave "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CProc _CProc)
print_tex_CProc (CHide _CProc _CSExp1)
  = (print_tex_CProc _CProc)++" \\circhide CS"
print_tex_CProc (CExtChoice _CProc1 _CProc2)
  = (print_tex_CProc _CProc1)++"  \\extchoice "++(print_tex_CProc _CProc2)
print_tex_CProc (CIntChoice _CProc1 _CProc2)
  = (print_tex_CProc _CProc1)++"  \\intchoice "++(print_tex_CProc _CProc2)
print_tex_CProc (CParParal _CSExp1 _CProc1 _CProc2)
  = (print_tex_CProc _CProc1)++"  \\lpar CS \\rpar "++(print_tex_CProc _CProc2)
print_tex_CProc (CInterleave _CProc1 _CProc2)
  = (print_tex_CProc _CProc1)++"  \\interleave "++(print_tex_CProc _CProc2)
print_tex_CProc (CGenProc _ZName _ZExpr_lst) = "PName[\\nat]"
print_tex_CProc (CParamProc _ZName _ZExpr_lst) = "PName(x, y)"
print_tex_CProc (CProcRename _ZName _Comm_lst _Comm_lst1)
  = "PName \\lcircrename c, d := e, f \\rcircrename"
print_tex_CProc (CSeq _CProc1 _CProc2)
  = (print_tex_CProc _CProc1)++" \\circseq "++(print_tex_CProc _CProc2)
print_tex_CProc (CSimpIndexProc _ZName _ZExpr_lst)
  = "PName \\lcircindex x \\rcircindex "
print_tex_CProc (CircusProc _ZName) = _ZName
print_tex_CProc (ProcMain (ZSchemaDef (ZSPlain _String) _ZSExpr) _PPar_lst _CAction)
  = "\\circbegin "
    ++"\n\\circstate "++_String++" == "++(print_tex_ZSExpr _ZSExpr)++"\n"
    ++(joinBy "\n\t" $(map print_tex_PPar _PPar_lst))
    ++"\n\t\\circspot "
    ++(print_tex_CAction 1 _CAction)
    ++"\n\\circend"
print_tex_CProc (ProcStalessMain _PPar_lst _CAction)
  = "\\circbegin\n"
    ++(joinBy "\n" $(map print_tex_PPar _PPar_lst))
    ++"\n\t\\circspot "
    ++(print_tex_CAction 1 _CAction)
    ++"\n\\circend"

-- print_tex_NSExp (NSExpEmpty) = ""
-- print_tex_NSExp (NSExprMult _ZVar_lst) = ""
-- print_tex_NSExp (NSExprSngl _ZName) = ""
-- print_tex_NSExp (NSExprParam _ZName _ZExpr_lst) = ""
-- print_tex_NSExp (NSUnion _NSExp1 _NSExp2) = ""
-- print_tex_NSExp (NSIntersect _NSExp1 _NSExp2) = ""
-- print_tex_NSExp (NSHide _NSExp1 _NSExp2) = ""
-- print_tex_NSExp (NSBigUnion _ZExpr) = ""
print_tex_NSExp [] = "\\emptyset"
print_tex_NSExp x = "{"++(joinBy "," $(map print_tex_ZExpr x))++"}"
print_tex_PPar (ProcZPara _ZPara) = ""
print_tex_PPar (CParAction _ZName _ParAction)
  = _ZName++" \\circdef "++(print_tex_ParAction _ParAction)
print_tex_PPar (CNameSet _ZName _ZExpr_lst)
  = "\\circnameset n == {~ x ~}"

print_tex_ParAction (CircusAction _CAction) = (print_tex_CAction 1 _CAction)
print_tex_ParAction (ParamActionDecl _ZGenFilt_lst _ParAction) = (joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_ParAction _ParAction)++"\\\\"

print_tex_tabs :: Int -> String
print_tex_tabs 0 = ""
print_tex_tabs n = "\t"++(print_tex_tabs (n-1))

print_tex_CAction :: Int -> CAction -> String
print_tex_CAction t (CActionName _ZName) = _ZName
print_tex_CAction t (CSPSkip ) = "\\Skip"++"\\\\"
print_tex_CAction t (CSPStop ) = "\\Stop"++"\\\\"
print_tex_CAction t (CSPChaos) = "\\Chaos"++"\\\\"
print_tex_CAction t (CSPCommAction _Comm _CAction)
  = (print_tex_Comm _Comm)++" \\then "++ (print_tex_CAction t _CAction)
print_tex_CAction t (CSPParAction _ZName _ZExpr_lst)
  = (print_tex_tabs t)
    ++ _ZName
    ++ "("++(joinBy "," $(map print_tex_ZExpr _ZExpr_lst))++")"
print_tex_CAction t (CSPRenAction _ZName _CReplace)
  = (print_tex_tabs t)
    ++ "AName[new/old, x/y]"
print_tex_CAction t c
  = "\\\\\n"
    ++(print_tex_tabs t)
    ++"\\begin{block}\n"
    ++(print_tex_CAction' (t+1) c)
    ++"\n"
    ++(print_tex_tabs t)
    ++"\\end{block}\\\\\n"++(print_tex_tabs t)
print_tex_CAction' t (CActionSchemaExpr _ZSExpr)
  = (print_tex_tabs t)
    ++ "\\lschexpract S \\rschexpract"
print_tex_CAction' t (CActionCommand _CCommand)
  = (print_tex_tabs t)
    ++ ""
print_tex_CAction' t (CSPGuard _ZPred _CAction)
  = (print_tex_tabs t)
  ++ "\\lcircguard "
  ++ (print_tex_ZPred _ZPred)
  ++" \\rcircguard \\circguard "
  ++ (print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPSeq _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction t _CAction1)++" \\circseq "++(print_tex_CAction t _CAction2)
print_tex_CAction' t (CSPExtChoice _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction1)++" \\extchoice "++(print_tex_CAction (t+1) _CAction2)
print_tex_CAction' t (CSPIntChoice _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction1)++" \\intchoice "++(print_tex_CAction (t+1) _CAction2)

print_tex_CAction' t (CSPNSParal _ZExpr_lst1 _CSExp _ZExpr_lst2 _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction1)
    ++" \\lpar "
    ++(print_tex_NSExp _ZExpr_lst1)
    ++" | "
    ++ (print_tex_CSExp _CSExp)
    ++" | "
    ++(print_tex_NSExp _ZExpr_lst2)
    ++" \\rpar "
    ++(print_tex_CAction (t+1) _CAction2)
print_tex_CAction' t (CSPParal _CSExp1 _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction1)
    ++" \\lpar "
    ++ (print_tex_CSExp _CSExp1)
    ++" \\rpar "
    ++(print_tex_CAction (t+1) _CAction2)
print_tex_CAction' t (CSPNSInter _ZExpr_lst1 _ZExpr_lst2 _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction1)
    ++" \\linter "
    ++(joinBy "," $(map print_tex_ZExpr _ZExpr_lst1))
    ++" | "
    ++(joinBy "," $(map print_tex_ZExpr _ZExpr_lst2))
    ++" \\rinter "
    ++(print_tex_CAction (t+1) _CAction2)
print_tex_CAction' t (CSPInterleave _CAction1 _CAction2)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction1)++" \\interleave "++(print_tex_CAction (t+1) _CAction2)
print_tex_CAction' t (CSPHide _CAction _CSExp)
  = (print_tex_tabs t)
    ++ (print_tex_CAction (t+1) _CAction)++"  \\circhide "++(print_tex_CSExp _CSExp)

print_tex_CAction' t (CSPRecursion _ZName _CAction)
  = (print_tex_tabs t)
    ++ "\\circmu "++_ZName++" \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPUnfAction _ZName _CAction)
  = (print_tex_tabs t)
    ++ "N (Action)"
print_tex_CAction' t (CSPUnParAction _ZGenFilt_lst _CAction _ZName)
  = (print_tex_tabs t)
    ++ "(Decl \\circspot Action) (ZName)"
print_tex_CAction' t (CSPRepSeq _ZGenFilt_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\Semi "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPRepExtChoice _ZGenFilt_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\Extchoice "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPRepIntChoice _ZGenFilt_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\Intchoice "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPRepParalNS _CSExp _ZGenFilt_lst _ZExpr_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\lpar "
    ++(print_tex_CSExp _CSExp)
    ++" \\rpar "
    ++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))
    ++" \\circspot \\lpar "
    ++(joinBy "," $(map print_tex_ZExpr _ZExpr_lst))
    ++" \\rpar "
    ++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPRepParal _CSExp _ZGenFilt_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\lpar CS \\rpar "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPRepInterlNS _ZGenFilt_lst _ZExpr_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\Interleave "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\linter NS \\rinter \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t (CSPRepInterl _ZGenFilt_lst _CAction)
  = (print_tex_tabs t)
    ++ "\\Interleave "++(joinBy "," $(map print_tex_ZGenFilt _ZGenFilt_lst))++" \\circspot "++(print_tex_CAction (t+1) _CAction)
print_tex_CAction' t x = print_tex_CAction t x

print_tex_Comm (ChanComm _ZName _CParameter_lst)
  = _ZName++(joinBy "" $(map print_tex_CParameter _CParameter_lst))
print_tex_Comm (ChanGenComm _ZName _ZExpr_lst _CParameter_lst) = ""

print_tex_CParameter (ChanInp _ZName)
  = "?"++_ZName
print_tex_CParameter (ChanInpPred _ZName _ZPred)
  = "?"++_ZName++" : "++(print_tex_ZPred _ZPred)
print_tex_CParameter (ChanOutExp _ZExpr)
  = "!"++(print_tex_ZExpr _ZExpr)
print_tex_CParameter (ChanDotExp _ZExpr)
  = "."++(print_tex_ZExpr _ZExpr)

print_tex_CCommand (CAssign _ZVar_lst _ZExpr_lst) = ""
print_tex_CCommand (CIf _CGActions) = ""
print_tex_CCommand (CVarDecl _ZGenFilt_lst _CAction) = ""
print_tex_CCommand (CValDecl _ZGenFilt_lst _CAction) = ""
print_tex_CCommand (CResDecl _ZGenFilt_lst _CAction) = ""
print_tex_CCommand (CVResDecl _ZGenFilt_lst _CAction) = ""
print_tex_CCommand (CAssumpt _ZName_lst _ZPred1 _ZPred2) = ""
print_tex_CCommand (CAssumpt1 _ZName_lst _ZPred) = ""
print_tex_CCommand (CPrefix _ZPred1 _ZPred2) = ""
print_tex_CCommand (CPrefix1 _ZPred) = ""
print_tex_CCommand (CommandBrace _ZPred) = ""
print_tex_CCommand (CommandBracket _ZPred) = ""

print_tex_CGActions (CircGAction _ZPred _CAction) = ""
print_tex_CGActions (CircThenElse _CGActions1 _CGActions2) = ""

print_tex_CReplace (CRename _ZVar_lst _ZVar_lst1) = ""
print_tex_CReplace (CRenameAssign _ZVar_lst _ZVar_lst1) = ""
\end{code}
