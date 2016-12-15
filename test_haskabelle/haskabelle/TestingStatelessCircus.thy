theory TestingStatelessCircus
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
| "omega_CAction lst (CActionCommand (CPrefix va vb)) = (CActionCommand (CPrefix va vb))"
| "omega_CAction lst (CActionCommand (CPrefix1 va)) = (CActionCommand (CPrefix1 va))"
| "omega_CAction lst (CActionCommand (CResDecl va vb)) = (CActionCommand (CResDecl va vb))"
| "omega_CAction lst (CActionCommand (CValDecl va vb)) = (CActionCommand (CValDecl va vb))"
| "omega_CAction lst (CActionCommand (CVarDecl va vb)) = (CActionCommand (CVarDecl va vb))"
| "omega_CAction lst (CActionCommand (CVResDecl va vb)) = (CActionCommand (CVResDecl va vb))"
| "omega_CAction lst (CActionName v) = (CActionName v)"
| "omega_CAction lst (CActionSchemaExpr v) = (CActionSchemaExpr v)"
| "omega_CAction lst (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va)"
| "omega_CAction lst (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va)"
| "omega_CAction lst (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va)"
| "omega_CAction lst (CSPCommAction (ChanGenComm vb vc vd) va) = (CSPCommAction (ChanGenComm vb vc vd) va)"
| "omega_CAction lst (CSPExtChoice v va) = (CSPExtChoice v va)"
| "omega_CAction lst (CSPGuard v va) = (CSPGuard v va)"
| "omega_CAction lst (CSPInterleave v va) = (CSPInterleave v va)"
| "omega_CAction lst (CSPNSInter v va vb vc) = (CSPNSInter v va vb vc)"
| "omega_CAction lst (CSPNSParal v va vb vc vd) = (CSPNSParal v va vb vc vd)"
| "omega_CAction lst (CSPParAction v va) = (CSPParAction v va)"
| "omega_CAction lst (CSPParal v va vb) = (CSPParal v va vb)"
| "omega_CAction lst (CSPRenAction v va) = (CSPRenAction v va)"
| "omega_CAction lst (CSPRepExtChoice v va) = (CSPRepExtChoice v va)"
| "omega_CAction lst (CSPRepIntChoice v va) = (CSPRepIntChoice v va)"
| "omega_CAction lst (CSPRepInterl v va) = (CSPRepInterl v va)"
| "omega_CAction lst (CSPRepInterlNS v va vb) = (CSPRepInterlNS v va vb)"
| "omega_CAction lst (CSPRepParal v va vb) = (CSPRepParal v va vb)"
| "omega_CAction lst (CSPRepParalNS v va vb vc) = (CSPRepParalNS v va vb vc)"
| "omega_CAction lst (CSPRepSeq v va) = (CSPRepSeq v va)"
| "omega_CAction lst (CSPUnParAction v va vb) = (CSPUnParAction v va vb)"
(*
| "omega_CAction lst (CActionCommand (CommandBrace g)) = omega_CAction lst (CActionCommand (CPrefix g (ZTrue Nil)))"
| "omega_CAction lst (CActionCommand (CommandBracket g)) = omega_CAction lst (CActionCommand (CPrefix1 g))"
| "omega_CAction lst (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) = omega_CAction lst (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "omega_CAction lst (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (omega_CAction lst a))"
| "omega_CAction lst (CSPHide a cs) = (CSPHide (omega_CAction lst a) cs)"
| "omega_CAction lst (CSPIntChoice ca cb) = (CSPIntChoice (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPSeq ca cb) = (CSPSeq (omega_CAction lst ca) (omega_CAction lst cb))"
| "omega_CAction lst (CSPRecursion x c) = (CSPRecursion x (omega_CAction lst c))"
*)
 
fun \<Omega> :: "CAction \<Rightarrow> CAction"
where
  "\<Omega> CSPSkip = CSPSkip"
| "\<Omega> CSPChaos = CSPChaos"
| "\<Omega> CSPStop = CSPStop"
| "\<Omega> (CActionCommand (CAssign va vb)) = (CActionCommand (CAssign va vb))"
| "\<Omega> (CActionCommand (CAssumpt va vb vc)) = (CActionCommand (CAssumpt va vb vc))"
| "\<Omega> (CActionCommand (CAssumpt1 va vb)) = (CActionCommand (CAssumpt1 va vb))"
| "\<Omega> (CActionCommand (CIf a)) = (CActionCommand (CIf a))"
| "\<Omega> (CActionCommand (CPrefix va vb)) = (CActionCommand (CPrefix va vb))"
| "\<Omega> (CActionCommand (CPrefix1 va)) = (CActionCommand (CPrefix1 va))"
| "\<Omega> (CActionCommand (CResDecl va vb)) = (CActionCommand (CResDecl va vb))"
| "\<Omega> (CActionCommand (CValDecl va vb)) = (CActionCommand (CValDecl va vb))"
| "\<Omega> (CActionCommand (CVarDecl va vb)) = (CActionCommand (CVarDecl va vb))"
| "\<Omega> (CActionCommand (CVResDecl va vb)) = (CActionCommand (CVResDecl va vb))"
| "\<Omega> (CActionName v) = (CActionName v)"
| "\<Omega> (CActionSchemaExpr v) = (CActionSchemaExpr v)"
| "\<Omega> (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va)"
| "\<Omega> (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va)"
| "\<Omega> (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va) = (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va)"
| "\<Omega> (CSPCommAction (ChanGenComm vb vc vd) va) = (CSPCommAction (ChanGenComm vb vc vd) va)"
| "\<Omega> (CSPExtChoice v va) = (CSPExtChoice v va)"
| "\<Omega> (CSPGuard v va) = (CSPGuard v va)"
| "\<Omega> (CSPInterleave v va) = (CSPInterleave v va)"
| "\<Omega> (CSPNSInter v va vb vc) = (CSPNSInter v va vb vc)"
| "\<Omega> (CSPNSParal v va vb vc vd) = (CSPNSParal v va vb vc vd)"
| "\<Omega> (CSPParAction v va) = (CSPParAction v va)"
| "\<Omega> (CSPParal v va vb) = (CSPParal v va vb)"
| "\<Omega> (CSPRenAction v va) = (CSPRenAction v va)"
| "\<Omega> (CSPRepExtChoice v va) = (CSPRepExtChoice v va)"
| "\<Omega> (CSPRepIntChoice v va) = (CSPRepIntChoice v va)"
| "\<Omega> (CSPRepInterl v va) = (CSPRepInterl v va)"
| "\<Omega> (CSPRepInterlNS v va vb) = (CSPRepInterlNS v va vb)"
| "\<Omega> (CSPRepParal v va vb) = (CSPRepParal v va vb)"
| "\<Omega> (CSPRepParalNS v va vb vc) = (CSPRepParalNS v va vb vc)"
| "\<Omega> (CSPRepSeq v va) = (CSPRepSeq v va)"
| "\<Omega> (CSPUnParAction v va vb) = (CSPUnParAction v va vb)"
(*
| "\<Omega> (CActionCommand (CommandBrace g)) = \<Omega> (CActionCommand (CPrefix g (ZTrue Nil)))"
| "\<Omega> (CActionCommand (CommandBracket g)) = \<Omega> (CActionCommand (CPrefix1 g))"
| "\<Omega> (CSPCommAction (ChanComm c ((ChanOutExp e) # xs)) a) = \<Omega> (CSPCommAction (ChanComm c ((ChanDotExp e) # xs)) a)"
| "\<Omega> (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (\<Omega> a))"
| "\<Omega> (CSPHide a cs) = (CSPHide (\<Omega> a) cs)"
| "\<Omega> (CSPIntChoice ca cb) = (CSPIntChoice (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPSeq ca cb) = (CSPSeq (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPRecursion x c) = (CSPRecursion x (\<Omega> c))"
*)
 
lemma "omega_CAction lst CSPSkip = (\<Omega> CSPSkip)"
  by simp
lemma "omega_CAction lst CSPChaos = (\<Omega> CSPChaos)"
  by simp

lemma "omega_CAction lst CSPStop = (\<Omega> CSPStop)"
  by simp

lemma "omega_CAction lst (CActionCommand (CAssign va vb)) = (\<Omega> (CActionCommand (CAssign va vb)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CAssumpt va vb vc)) = (\<Omega> (CActionCommand (CAssumpt va vb vc)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CAssumpt1 va vb)) = (\<Omega> (CActionCommand (CAssumpt1 va vb)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CIf a)) = (\<Omega> (CActionCommand (CIf a)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CPrefix va vb)) = (\<Omega> (CActionCommand (CPrefix va vb)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CPrefix1 va)) = (\<Omega> (CActionCommand (CPrefix1 va)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CResDecl va vb)) = (\<Omega> (CActionCommand (CResDecl va vb)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CValDecl va vb)) = (\<Omega> (CActionCommand (CValDecl va vb)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CVarDecl va vb)) = (\<Omega> (CActionCommand (CVarDecl va vb)))"
  by simp


lemma "omega_CAction lst (CActionCommand (CVResDecl va vb)) = (\<Omega> (CActionCommand (CVResDecl va vb)))"
  by simp


lemma "omega_CAction lst (CActionName v) = (\<Omega> (CActionName v))"
  by simp


lemma "omega_CAction lst (CActionSchemaExpr v) = (\<Omega> (CActionSchemaExpr v))"
  by simp


lemma "omega_CAction lst (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va) = (\<Omega> (CSPCommAction (ChanComm vb (ChanDotExp vc # ve)) va))"
  by simp

lemma "omega_CAction lst (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va) = (\<Omega> (CSPCommAction (ChanComm vb (ChanInp vc # ve)) va))"
  by simp

lemma "omega_CAction lst (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va) = (\<Omega> (CSPCommAction (ChanComm vb (ChanInpPred v vc # ve)) va))"
  by simp

lemma "omega_CAction lst (CSPCommAction (ChanGenComm vb vc vd) va) = (\<Omega> (CSPCommAction (ChanGenComm vb vc vd) va))"
  by simp


lemma "omega_CAction lst (CSPExtChoice v va) = (\<Omega> (CSPExtChoice v va))"
  by simp


lemma "omega_CAction lst (CSPGuard v va) = (\<Omega> (CSPGuard v va))"
  by simp


lemma "omega_CAction lst (CSPInterleave v va) = (\<Omega> (CSPInterleave v va))"
  by simp


lemma "omega_CAction lst (CSPNSInter v va vb vc) = (\<Omega> (CSPNSInter v va vb vc))"
  by simp


lemma "omega_CAction lst (CSPNSParal v va vb vc vd) = (\<Omega> (CSPNSParal v va vb vc vd))"
  by simp


lemma "omega_CAction lst (CSPParAction v va) = (\<Omega> (CSPParAction v va))"
  by simp


lemma "omega_CAction lst (CSPParal v va vb) = (\<Omega> (CSPParal v va vb))"
  by simp


lemma "omega_CAction lst (CSPRenAction v va) = (\<Omega> (CSPRenAction v va))"
  by simp


lemma "omega_CAction lst (CSPRepExtChoice v va) = (\<Omega> (CSPRepExtChoice v va))"
  by simp


lemma "omega_CAction lst (CSPRepIntChoice v va) = (\<Omega> (CSPRepIntChoice v va))"
  by simp


lemma "omega_CAction lst (CSPRepInterl v va) = (\<Omega> (CSPRepInterl v va))"
  by simp


lemma "omega_CAction lst (CSPRepInterlNS v va vb) = (\<Omega> (CSPRepInterlNS v va vb))"
  by simp


lemma "omega_CAction lst (CSPRepParal v va vb) = (\<Omega> (CSPRepParal v va vb))"
  by simp


lemma "omega_CAction lst (CSPRepParalNS v va vb vc) = (\<Omega> (CSPRepParalNS v va vb vc))"
  by simp


lemma "omega_CAction lst (CSPRepSeq v va) = (\<Omega> (CSPRepSeq v va))"
  by simp


lemma "omega_CAction lst (CSPUnParAction v va vb) = (\<Omega> (CSPUnParAction v va vb))"
  by simp

end