theory MappingFunStatelessCircus
imports AST Prelude
begin
 
fun omega_CAction :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "omega_CAction lst CSPSkip = CSPSkip"
| "omega_CAction lst CSPChaos = CSPChaos"
| "omega_CAction lst CSPStop = CSPStop"
| "omega_CAction lst (CActionCommand (CAssign va vb)) = (CActionCommand (CAssign va vb))"
| "omega_CAction lst (CActionCommand (CAssumpt va vb vc)) = (CActionCommand (CAssumpt va vb vc))"
| "omega_CAction lst (CActionCommand (CAssumpt1 va vb)) = (CActionCommand (CAssumpt1 va vb))"
| "omega_CAction lst (CActionCommand (CIf a)) = (CActionCommand (CIf a))"
| "omega_CAction lst (CActionCommand (CommandBrace g)) = omega_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_CAction lst (CActionCommand (CommandBracket g)) = omega_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_CAction lst (CActionCommand (CPrefix va vb)) = (CActionCommand (CPrefix va vb))"
| "omega_CAction lst (CActionCommand (CPrefix1 va)) = (CActionCommand (CPrefix1 va))"
| "omega_CAction lst (CActionCommand (CResDecl va vb)) = (CActionCommand (CResDecl va vb))"
| "omega_CAction lst (CActionCommand (CValDecl va vb)) = (CActionCommand (CValDecl va vb))"
| "omega_CAction lst (CActionCommand (CVarDecl va vb)) = (CActionCommand (CVarDecl va vb))"
| "omega_CAction lst (CActionCommand (CVResDecl va vb)) = (CActionCommand (CVResDecl va vb))"
| "omega_CAction lst (CActionName v) = (CActionName v)"
| "omega_CAction lst (CActionSchemaExpr v) = (CActionSchemaExpr v)"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "omega_CAction lst (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va)"
| "omega_CAction lst (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va)"
| "omega_CAction lst (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va)"
| "omega_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction lst a))"
| "omega_CAction lst (CSPCommAction (ChanGenComm vb vc vd) va) = (CSPCommAction (ChanGenComm vb vc vd) va)"
| "omega_CAction lst (CSPExtChoice v va) = (CSPExtChoice v va)"
| "omega_CAction lst (CSPGuard v va) = (CSPGuard v va)"
| "omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)"
| "omega_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPInterleave v va) = (CSPInterleave v va)"
| "omega_CAction lst (CSPNSInter v va vb vc) = (CSPNSInter v va vb vc)"
| "omega_CAction lst (CSPNSParal v va vb vc vd) = (CSPNSParal v va vb vc vd)"
| "omega_CAction lst (CSPParAction v va) = (CSPParAction v va)"
| "omega_CAction lst (CSPParal v va vb) = (CSPParal v va vb)"
| "omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))"
| "omega_CAction lst (CSPRenAction v va) = (CSPRenAction v va)"
| "omega_CAction lst (CSPRepExtChoice v va) = (CSPRepExtChoice v va)"
| "omega_CAction lst (CSPRepIntChoice v va) = (CSPRepIntChoice v va)"
| "omega_CAction lst (CSPRepInterl v va) = (CSPRepInterl v va)"
| "omega_CAction lst (CSPRepInterlNS v va vb) = (CSPRepInterlNS v va vb)"
| "omega_CAction lst (CSPRepParal v va vb) = (CSPRepParal v va vb)"
| "omega_CAction lst (CSPRepParalNS v va vb vc) = (CSPRepParalNS v va vb vc)"
| "omega_CAction lst (CSPRepSeq v va) = (CSPRepSeq v va)"
| "omega_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPUnParAction v va vb) = (CSPUnParAction v va vb)"

fun thy_omega :: "CAction \<Rightarrow> CAction"
where
  "thy_omega CSPSkip = CSPSkip"
| "thy_omega CSPChaos = CSPChaos"
| "thy_omega CSPStop = CSPStop"
| "thy_omega (CActionCommand (CAssign va vb)) = (CActionCommand (CAssign va vb))"
| "thy_omega (CActionCommand (CAssumpt va vb vc)) = (CActionCommand (CAssumpt va vb vc))"
| "thy_omega (CActionCommand (CAssumpt1 va vb)) = (CActionCommand (CAssumpt1 va vb))"
| "thy_omega (CActionCommand (CIf a)) = (CActionCommand (CIf a))"
| "thy_omega (CActionCommand (CommandBrace g)) = thy_omega (CActionCommand (CPrefix g (ZTrue Nil)))"
| "thy_omega (CActionCommand (CommandBracket g)) = thy_omega (CActionCommand (CPrefix1 g))"
| "thy_omega (CActionCommand (CPrefix va vb)) = (CActionCommand (CPrefix va vb))"
| "thy_omega (CActionCommand (CPrefix1 va)) = (CActionCommand (CPrefix1 va))"
| "thy_omega (CActionCommand (CResDecl va vb)) = (CActionCommand (CResDecl va vb))"
| "thy_omega (CActionCommand (CValDecl va vb)) = (CActionCommand (CValDecl va vb))"
| "thy_omega (CActionCommand (CVarDecl va vb)) = (CActionCommand (CVarDecl va vb))"
| "thy_omega (CActionCommand (CVResDecl va vb)) = (CActionCommand (CVResDecl va vb))"
| "thy_omega (CActionName v) = (CActionName v)"
| "thy_omega (CActionSchemaExpr v) = (CActionSchemaExpr v)"
| "thy_omega (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) = thy_omega (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "thy_omega (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va)"
| "thy_omega (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va)"
| "thy_omega (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va)"
| "thy_omega (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (thy_omega a))"
| "thy_omega (CSPCommAction (ChanGenComm vb vc vd) va) = (CSPCommAction (ChanGenComm vb vc vd) va)"
| "thy_omega (CSPExtChoice v va) = (CSPExtChoice v va)"
| "thy_omega (CSPGuard v va) = (CSPGuard v va)"
| "thy_omega (CSPHide a cs) = (CSPHide (thy_omega a) cs)"
| "thy_omega (CSPIntChoice ca cb) = (CSPIntChoice (thy_omega ca) (thy_omega cb))"
| "thy_omega (CSPInterleave v va) = (CSPInterleave v va)"
| "thy_omega (CSPNSInter v va vb vc) = (CSPNSInter v va vb vc)"
| "thy_omega (CSPNSParal v va vb vc vd) = (CSPNSParal v va vb vc vd)"
| "thy_omega (CSPParAction v va) = (CSPParAction v va)"
| "thy_omega (CSPParal v va vb) = (CSPParal v va vb)"
| "thy_omega (CSPRecursion x c) = (CSPRecursion x (thy_omega c))"
| "thy_omega (CSPRenAction v va) = (CSPRenAction v va)"
| "thy_omega (CSPRepExtChoice v va) = (CSPRepExtChoice v va)"
| "thy_omega (CSPRepIntChoice v va) = (CSPRepIntChoice v va)"
| "thy_omega (CSPRepInterl v va) = (CSPRepInterl v va)"
| "thy_omega (CSPRepInterlNS v va vb) = (CSPRepInterlNS v va vb)"
| "thy_omega (CSPRepParal v va vb) = (CSPRepParal v va vb)"
| "thy_omega (CSPRepParalNS v va vb vc) = (CSPRepParalNS v va vb vc)"
| "thy_omega (CSPRepSeq v va) = (CSPRepSeq v va)"
| "thy_omega (CSPSeq ca cb) = (CSPSeq (thy_omega ca) (thy_omega cb))"
| "thy_omega (CSPUnParAction v va vb) = (CSPUnParAction v va vb)"
 
fun omega_prime_CAction :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "omega_prime_CAction lst CSPSkip = CSPSkip"
| "omega_prime_CAction lst CSPStop = CSPStop"
| "omega_prime_CAction lst CSPChaos = CSPChaos"
| "omega_prime_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_prime_CAction lst a))"
| "omega_prime_CAction lst (CSPCommAction (ChanComm c x) a) = (CSPCommAction (ChanComm c x) (omega_prime_CAction lst a))"
| "omega_prime_CAction lst (CSPGuard g a) = (CSPGuard g (omega_prime_CAction lst a))"
| "omega_prime_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))"
| "omega_prime_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_prime_CAction lst ca) (omega_prime_CAction lst cb))"
| "omega_prime_CAction lst (CActionCommand (CIf (CircGAction g a))) = (CActionCommand (CIf (CircGAction g (omega_prime_CAction lst a))))"
| "omega_prime_CAction lst (CSPHide a cs) = (CSPHide (omega_prime_CAction lst a) cs)"
| "omega_prime_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_prime_CAction lst c))"
| "omega_prime_CAction lst (CActionCommand (CommandBrace g)) = omega_prime_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_prime_CAction lst (CActionCommand (CommandBracket g)) = omega_prime_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_prime_CAction lst (CSPRenAction a (CRenameAssign left right)) = (CSPRenAction a (CRename right left))"
| "omega_prime_CAction lst (CActionName n) = (CActionName n)"

 
fun get_proc_name :: "ZName \<Rightarrow> ((ZName * ZVar) * ZExpr) list \<Rightarrow> ZName"
where
  "get_proc_name x [(a, ((va, x1), b))] = (case eq x va of
                                              True \<Rightarrow> a
                                            | _ \<Rightarrow> '''')"
| "get_proc_name x ((a, ((va, x1), b)) # vst) = (case eq x va of
                                                    True \<Rightarrow> a
                                                  | _ \<Rightarrow> get_proc_name x vst)"

 
fun make_get_com :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZVar list \<Rightarrow> CAction \<Rightarrow> CAction"
where
  "make_get_com lst [(x, Nil)] c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanInp ((''v'' @ (get_proc_name x lst)) @ (''_'' @ x))]) c)"
| "make_get_com lst ((x, Nil) # xs) c = (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar ((get_proc_name x lst) @ (''_'' @ x), Nil)), ChanInp ((''v'' @ (get_proc_name x lst)) @ (''_'' @ x))]) (make_get_com lst xs c))"
| "make_get_com lst x c = c"

 
fun filter_state_comp :: "((ZName * ZVar) * ZExpr) list \<Rightarrow> ZVar list"
where
  "filter_state_comp Nil = Nil"
| "filter_state_comp [(_, (v, _))] = [v]"
| "filter_state_comp ((_, (v, _)) # xs) = ([v] @ (filter_state_comp xs))"

 
fun get_chan_param :: "CParameter list \<Rightarrow> ZVar list"
where
  "get_chan_param Nil = Nil"
| "get_chan_param [ChanDotExp (ZVar (x, _))] = [(x, Nil)]"
| "get_chan_param [ChanOutExp (ZVar (x, _))] = [(x, Nil)]"
| "get_chan_param [_] = Nil"
| "get_chan_param ((ChanDotExp (ZVar (x, _))) # xs) = ([(x, Nil)] @ (get_chan_param xs))"
| "get_chan_param ((ChanOutExp (ZVar (x, _))) # xs) = ([(x, Nil)] @ (get_chan_param xs))"
| "get_chan_param (_ # xs) = (get_chan_param xs)"

 
fun rename_vars_CReplace
where
  "rename_vars_CReplace lst (CRename zvarls1 zvarls) = (CRename zvarls1 zvarls)"
| "rename_vars_CReplace lst (CRenameAssign zvarls1 zvarls) = (CRenameAssign zvarls1 zvarls)"

 
fun inListVar
where
  "inListVar x Nil = False"
| "inListVar x [va] = (case eq x va of
                          True \<Rightarrow> True
                        | _ \<Rightarrow> False)"
| "inListVar x (va # vst) = (case eq x va of
                                True \<Rightarrow> True
                              | _ \<Rightarrow> inListVar x vst)"

 
fun rename_ZVar
where
  "rename_ZVar lst (va, x) = (case (inListVar va lst) of
                                 True \<Rightarrow> (''v_'' @ va, x)
                               | False \<Rightarrow> (va, x))"

 
fun rename_ZExpr and 
    bindingsVar
where
  "rename_ZExpr lst (ZVar (va, x)) = (case (inListVar va lst) of
                                         True \<Rightarrow> (ZVar (''v_'' @ va, x))
                                       | False \<Rightarrow> (ZVar (va, x)))"
| "rename_ZExpr lst (ZInt zi) = (ZInt zi)"
| "rename_ZExpr lst (ZGiven gv) = (ZGiven gv)"
| "rename_ZExpr lst (ZFree0 va) = (ZFree0 va)"
| "rename_ZExpr lst (ZFree1 va xpr) = (ZFree1 va (rename_ZExpr lst xpr))"
| "rename_ZExpr lst (ZTuple xprlst) = (ZTuple (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZBinding xs) = (ZBinding (bindingsVar lst xs))"
| "rename_ZExpr lst (ZSetDisplay xprlst) = (ZSetDisplay (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZSeqDisplay xprlst) = (ZSeqDisplay (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZFSet zf) = (ZFSet zf)"
| "rename_ZExpr lst (ZIntSet i1 i2) = (ZIntSet i1 i2)"
| "rename_ZExpr lst (ZGenerator zrl xpr) = (ZGenerator zrl (rename_ZExpr lst xpr))"
| "rename_ZExpr lst (ZCross xprlst) = (ZCross (map (rename_ZExpr lst) xprlst))"
| "rename_ZExpr lst (ZFreeType va lst1) = (ZFreeType va lst1)"
| "rename_ZExpr lst (ZPowerSet xpr b1 b2) = (ZPowerSet (rename_ZExpr lst xpr) b1 b2)"
| "rename_ZExpr lst (ZFuncSet expr1 expr2 b1 b2 b3 b4 b5 b6 b7) = (ZFuncSet (rename_ZExpr lst expr1) (rename_ZExpr lst expr2) b1 b2 b3 b4 b5 b6 b7)"
| "rename_ZExpr lst (ZSetComp lst1 (Some xpr)) = (ZSetComp lst1 (Some (rename_ZExpr lst xpr)))"
| "rename_ZExpr lst (ZSetComp lst1 None) = (ZSetComp lst1 None)"
| "rename_ZExpr lst (ZLambda lst1 xpr) = (ZLambda lst1 (rename_ZExpr lst xpr))"
| "rename_ZExpr lst (ZESchema zxp) = (ZESchema zxp)"
| "rename_ZExpr lst (ZGivenSet gs) = (ZGivenSet gs)"
| "rename_ZExpr lst ZUniverse = ZUniverse"
| "rename_ZExpr lst (ZCall xpr1 xpr2) = (ZCall (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZExpr lst (ZReln rl) = (ZReln rl)"
| "rename_ZExpr lst (ZFunc1 f1) = (ZFunc1 f1)"
| "rename_ZExpr lst (ZFunc2 f2) = (ZFunc2 f2)"
| "rename_ZExpr lst (ZStrange st) = (ZStrange st)"
| "rename_ZExpr lst (ZMu lst1 (Some xpr)) = (ZMu lst1 (Some (rename_ZExpr lst xpr)))"
| "rename_ZExpr lst (ZELet lst1 xpr1) = (ZELet (bindingsVar lst lst1) (rename_ZExpr lst xpr1))"
| "rename_ZExpr lst (ZIf_Then_Else zp xpr1 xpr2) = (ZIf_Then_Else zp (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZExpr lst (ZSelect xpr va) = (ZSelect xpr va)"
| "rename_ZExpr lst (ZTheta zs) = (ZTheta zs)"
| "bindingsVar lst Nil = Nil"
| "bindingsVar lst [((va, x), b)] = (case (inListVar va lst) of
                                        True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr lst b))]
                                      | False \<Rightarrow> [((va, x), (rename_ZExpr lst b))])"
| "bindingsVar lst (((va, x), b) # xs) = (case (inListVar va lst) of
                                             True \<Rightarrow> [((''v_'' @ va, x), (rename_ZExpr lst b))] @ (bindingsVar lst xs)
                                           | False \<Rightarrow> [((va, x), (rename_ZExpr lst b))] @ (bindingsVar lst xs))"

 
fun rename_ZPred
where
  "rename_ZPred lst (ZFalse a) = (ZFalse a)"
| "rename_ZPred lst (ZTrue a) = (ZTrue a)"
| "rename_ZPred lst (ZAnd p1 p2) = (ZAnd (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZOr p1 p2) = (ZOr (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZImplies p1 p2) = (ZImplies (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZIff p1 p2) = (ZIff (rename_ZPred lst p1) (rename_ZPred lst p2))"
| "rename_ZPred lst (ZNot p) = (ZNot (rename_ZPred lst p))"
| "rename_ZPred lst (ZExists lst1 p) = (ZExists lst1 (rename_ZPred lst p))"
| "rename_ZPred lst (ZExists_1 lst1 p) = (ZExists_1 lst1 (rename_ZPred lst p))"
| "rename_ZPred lst (ZForall lst1 p) = (ZForall lst1 (rename_ZPred lst p))"
| "rename_ZPred lst (ZPLet varxp p) = (ZPLet varxp (rename_ZPred lst p))"
| "rename_ZPred lst (ZEqual xpr1 xpr2) = (ZEqual (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZPred lst (ZMember xpr1 xpr2) = (ZMember (rename_ZExpr lst xpr1) (rename_ZExpr lst xpr2))"
| "rename_ZPred lst (ZPre sp) = (ZPre sp)"
| "rename_ZPred lst (ZPSchema sp) = (ZPSchema sp)"

 
fun rename_vars_CParameter
where
  "rename_vars_CParameter lst (ChanInp zn) = (ChanInp zn)"
| "rename_vars_CParameter lst (ChanInpPred zn zp) = (ChanInpPred zn (rename_ZPred lst zp))"
| "rename_vars_CParameter lst (ChanOutExp ze) = (ChanOutExp (rename_ZExpr lst ze))"
| "rename_vars_CParameter lst (ChanDotExp ze) = (ChanDotExp (rename_ZExpr lst ze))"

 
fun rename_vars_Comm
where
  "rename_vars_Comm lst (ChanComm zn cpls) = (ChanComm zn (map (rename_vars_CParameter lst) cpls))"
| "rename_vars_Comm lst (ChanGenComm zn zexprls cpls) = (ChanGenComm zn (map (rename_ZExpr lst) zexprls) (map (rename_vars_CParameter lst) cpls))"

 
fun rename_vars_CAction and 
    rename_vars_CCommand and 
    rename_vars_CGActions
where
  "rename_vars_CAction lst (CActionSchemaExpr zsexp) = (CActionSchemaExpr zsexp)"
| "rename_vars_CAction lst (CActionCommand cmd) = (CActionCommand (rename_vars_CCommand lst cmd))"
| "rename_vars_CAction lst (CActionName zn) = (CActionName zn)"
| "rename_vars_CAction lst CSPSkip = CSPSkip"
| "rename_vars_CAction lst CSPStop = CSPStop"
| "rename_vars_CAction lst CSPChaos = CSPChaos"
| "rename_vars_CAction lst (CSPCommAction c a) = (CSPCommAction (rename_vars_Comm lst c) (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPGuard zp a) = (CSPGuard (rename_ZPred lst zp) (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPSeq a1 a2) = (CSPSeq (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPExtChoice a1 a2) = (CSPExtChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPIntChoice a1 a2) = (CSPIntChoice (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPNSParal ns1 cs ns2 a1 a2) = (CSPNSParal ns1 cs ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPParal cs a1 a2) = (CSPParal cs (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPNSInter ns1 ns2 a1 a2) = (CSPNSInter ns1 ns2 (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPInterleave a1 a2) = (CSPInterleave (rename_vars_CAction lst a1) (rename_vars_CAction lst a2))"
| "rename_vars_CAction lst (CSPHide a cs) = (CSPHide (rename_vars_CAction lst a) cs)"
| "rename_vars_CAction lst (CSPParAction zn zexprls) = (CSPParAction zn (map (rename_ZExpr lst) zexprls))"
| "rename_vars_CAction lst (CSPRenAction zn crpl) = (CSPRenAction zn (rename_vars_CReplace lst crpl))"
| "rename_vars_CAction lst (CSPRecursion zn a) = (CSPRecursion zn (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPUnParAction zgf a zn) = (CSPUnParAction zgf (rename_vars_CAction lst a) zn)"
| "rename_vars_CAction lst (CSPRepSeq zgf a) = (CSPRepSeq zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepExtChoice zgf a) = (CSPRepExtChoice zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepIntChoice zgf a) = (CSPRepIntChoice zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepParalNS cs zgf ns a) = (CSPRepParalNS cs zgf ns (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepParal cs zgf a) = (CSPRepParal cs zgf (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepInterlNS zgf ns a) = (CSPRepInterlNS zgf ns (rename_vars_CAction lst a))"
| "rename_vars_CAction lst (CSPRepInterl zgf a) = (CSPRepInterl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CAssign zvarls1 zexprls) = (CAssign zvarls1 (map (rename_ZExpr lst) zexprls))"
| "rename_vars_CCommand lst (CIf ga) = (CIf (rename_vars_CGActions lst ga))"
| "rename_vars_CCommand lst (CVarDecl zgf a) = (CVarDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CAssumpt znls zp1 zp2) = (CAssumpt znls (rename_ZPred lst zp1) zp2)"
| "rename_vars_CCommand lst (CAssumpt1 znls zp) = (CAssumpt1 znls zp)"
| "rename_vars_CCommand lst (CPrefix zp1 zp2) = (CPrefix (rename_ZPred lst zp1) zp2)"
| "rename_vars_CCommand lst (CPrefix1 zp) = (CPrefix1 zp)"
| "rename_vars_CCommand lst (CommandBrace zp) = (CommandBrace zp)"
| "rename_vars_CCommand lst (CommandBracket zp) = (CommandBracket zp)"
| "rename_vars_CCommand lst (CValDecl zgf a) = (CValDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CResDecl zgf a) = (CResDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CCommand lst (CVResDecl zgf a) = (CVResDecl zgf (rename_vars_CAction lst a))"
| "rename_vars_CGActions lst (CircGAction zp a) = (CircGAction (rename_ZPred lst zp) (rename_vars_CAction lst a))"
| "rename_vars_CGActions lst (CircThenElse cga1 cga2) = (CircThenElse (rename_vars_CGActions lst cga1) (rename_vars_CGActions lst cga2))"
| "rename_vars_CGActions lst (CircElse pa) = (CircElse pa)"

 
fun nub'0
where
  "nub'0 Nil _ = Nil"
| "nub'0 (x # xs) ls = (if member x ls then nub'0 xs ls
                        else x # nub'0 xs (x # ls))"

 
fun nub :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "nub l = (let nub' = nub'0
            in nub' l Nil)"

 
fun intersectBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersectBy eq2 xs ys = ([x . x <- xs,
                                 list_ex (eq2 x) ys])"

 
definition intersect :: "('a :: eq) list \<Rightarrow> ('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "intersect = intersectBy eq"

 
fun take :: "('i :: Integral) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "take n _ = (if n <= 0 then Nil else undefined)"
| "take _ Nil = Nil"
| "take n (x # xs) = (x # take (n - 1) xs)"


end
