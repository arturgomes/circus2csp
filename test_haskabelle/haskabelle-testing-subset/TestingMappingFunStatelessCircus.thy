theory TestingMappingFunStatelessCircus
imports MappingFunStatelessCircus
begin
text{*The function omega applied to $CSPCommAction$ should evaluate somehow
the use of $c?x!y.p$, as currently, there's only space for $c$ or $c\<odot>x$, where $\<odot>$ can be 
$?,!,.$ and x is a single element of a list. It should, however, carry more elements of a list. 

Moreover, we need to check if it is the case of renaming the variables of an action $A$, like the
case of:

\begin{center}
\<Omega> (c.e(v0,\<dots>,vn,l0,\<dots>,lm) -> A)  \<triangleq> 
    get.v0?vv0 \<rightarrow> ··· ->  
    get.vn?vvn ->
    get.l0?vl0 -> ··· -> 
    get.ln?vln ->
    c.e(vv0,\<dots>,vvn,vl0,\<dots>,vlm) -> \<Omega>'(A)
\end{center}*}

text{* I wrote this function below prefixed with emph{isbl} as a function written
directly in Isabelle following the prog-prove.pdf tutorial *}
fun isbl_make_get_com :: "ZName list \<Rightarrow> CAction \<Rightarrow> CAction"
  where
   "isbl_make_get_com [] x = x"
  |"isbl_make_get_com [a] x =
      (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (a, Nil)), ChanInp (''v_'' @ a)]) x)"
  |"isbl_make_get_com (a#as) x =
      (CSPCommAction (ChanComm ''mget'' [ChanDotExp (ZVar (a, Nil)), ChanInp (''v_'' @ a)]) (isbl_make_get_com as x))"    

text{*I couldn' find a way to say it differently, as the translation from haskell is really
similar to this one. So here is the proof.*}
lemma "isbl_make_get_com a b = make_get_com a b"
  proof (induct a)
    case Nil
    then show ?case by simp
  next
    case (Cons a1 a2)
    then show ?case 
      proof (induct a2)
        case Nil
        then show ?case by simp
      next
        case (Cons a a2)
        then show ?case by simp
      qed
  qed

function (sequential) \<Omega> :: "CAction \<Rightarrow> CAction" and 
    \<Omega>' :: "CAction \<Rightarrow> CAction"
where
  "\<Omega> CSPSkip = CSPSkip"
| "\<Omega> CSPStop = CSPStop"
| "\<Omega> CSPChaos = CSPChaos"
| "\<Omega> (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (\<Omega> a))"
| "\<Omega> (CSPCommAction (ChanComm c [ChanInp x]) a) = (CSPCommAction (ChanComm c [ChanInp x]) (\<Omega> a))"
| "\<Omega> (CSPCommAction (ChanComm c [ChanDotExp e]) a )
      = (let lxs = concat (map get_ZVar_st (free_var_ZExpr e))
        in isbl_make_get_com lxs ( (CSPCommAction (ChanComm c [rename_vars_CParameter (ChanDotExp e)]) (\<Omega>' a))))"
| "\<Omega> (CSPCommAction (ChanComm c [ChanOutExp e]) a) = \<Omega> (CSPCommAction (ChanComm c [ChanDotExp e]) a)"
| "\<Omega> (CSPCommAction (ChanComm c [ChanInpPred (x#xs) p]) a) 
      = (let lsx = concat (map get_ZVar_st (free_var_ZPred p))
         in case Not (member (x#xs) (getWrtV a)) of
               True \<Rightarrow> isbl_make_get_com lsx (rename_vars_CAction (CSPCommAction (ChanComm c [ChanInpPred (x#xs) p]) (\<Omega> a)))
               | _ \<Rightarrow> (CSPCommAction (ChanComm c [ChanInpPred (x#xs) p]) a))"
(*| "\<Omega> (CActionCommand (CAssign varls valls)) 
      = (if (length varls) > 0 
         then isbl_make_get_com (map fst varls) (rename_vars_CAction (make_set_com \<Omega> varls valls CSPSkip)) 
         else CSPSkip)"
| "\<Omega> (CActionCommand (CIf (CircGAction g a))) 
      = (let lsx = (map fst (remdups (free_var_ZPred g)))
         in isbl_make_get_com lsx (rename_vars_CAction (CActionCommand (CIf (CircGAction g (\<Omega>'  a))))))"
| "\<Omega> (CActionCommand (CIf (CircThenElse gl glx))) 
      = (let guard_pair = get_guard_pair (CircThenElse gl glx);
              lsx = map fst (remdups (concat (map free_var_ZPred (map fst guard_pair))))
          in isbl_make_get_com lsx (rename_vars_CAction (CActionCommand (CIf (mk_guard_pair \<Omega>' guard_pair)))))"
*)| "\<Omega> (CSPGuard g a) 
      = (let lxs = concat (map get_ZVar_st (free_var_ZPred g))
         in isbl_make_get_com lxs ( (CSPGuard (rename_ZPred g) (\<Omega>' a))))"
| "\<Omega> (CSPSeq ca cb) = (CSPSeq (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPIntChoice ca cb) = (CSPIntChoice (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPExtChoice ca cb) 
      = (let lsx = (map fst (remdups (free_var_CAction (CSPExtChoice ca cb))))
         in isbl_make_get_com lsx (rename_vars_CAction (CSPExtChoice (\<Omega>' ca) (\<Omega>' cb))))"
| "\<Omega> (CSPNSParal ns1 cs ns2 a1 a2) 
      = (let lsx = union (map fst (remdups (free_var_CAction a1))) (map fst (remdups (free_var_CAction a2)))
         in isbl_make_get_com lsx (rename_vars_CAction (CSPHide (CSPNSParal NSExpEmpty (CSExpr ''MEMi'') NSExpEmpty (CSPNSParal NSExpEmpty cs NSExpEmpty (CSPHide (CSPNSParal NSExpEmpty (CSExpr ''MEMi'') NSExpEmpty (CSPSeq a1 (CSPCommAction (ChanComm ''terminate'' Nil) CSPSkip)) (CSPParAction ''MemoryMerge'' [ZSetDisplay Nil, ZVar (''LEFT'', Nil)])) (CSExpr ''MEMi'')) (CSPHide (CSPNSParal NSExpEmpty (CSExpr ''MEMi'') NSExpEmpty (CSPSeq a2 (CSPCommAction (ChanComm ''terminate'' Nil) CSPSkip)) (CSPParAction ''MemoryMerge'' [ZSetDisplay Nil, ZVar (''RIGHT'', Nil)])) (CSExpr ''MEMi''))) (CActionName ''Merge'')) (CChanSet [''mleft'', ''mright'']))))"
| "\<Omega> (CSPHide a cs) = (CSPHide (\<Omega> a) cs)"
| "\<Omega> (CSPRecursion x c) = (CSPRecursion x (\<Omega> c))"
| "\<Omega> x = x"
| "\<Omega>' (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (\<Omega>' a))"
| "\<Omega>' (CSPCommAction (ChanComm c [ChanDotExp e]) a) = (CSPCommAction (ChanComm c [ChanDotExp (rename_ZExpr e)]) (\<Omega>' a))"
| "\<Omega>' (CSPSeq ca cb) = (CSPSeq (\<Omega>' ca) (\<Omega> cb))"
| "\<Omega>' x = \<Omega> x"
by pat_completeness auto
termination sorry
 
value "\<Omega> ((CSPExtChoice (CSPSeq (CSPCommAction (ChanComm ''wrt'' [ChanDotExp (ZVar (''req'',[])),ChanInp ''x'']) (CActionCommand (CAssign [(''v'',[])] [ZVar (''x'',[])]))) (CSPCommAction (ChanComm ''wrt'' [ChanDotExp (ZVar (''ack'',[])),ChanDotExp (ZVar (''x'',[]))]) CSPSkip)) (CSPCommAction (ChanComm ''rrd'' [ChanDotExp (ZVar (''req'',[])),ChanInp ''dumb'']) (CSPCommAction (ChanComm ''rrd'' [ChanDotExp (ZVar (''ack'',[])),ChanOutExp (ZVar (''v'',[]))]) CSPSkip))))"
 
lemma omega_CSPSkip: "\<Omega> CSPSkip = omega_CAction CSPSkip" by simp

lemma omega_ChanComSngl1:"\<Omega> a = omega_CAction a \<Longrightarrow> \<Omega> (CSPCommAction (ChanComm c [x]) a) = (CSPCommAction (ChanComm c [x]) (\<Omega> a))" 
  proof (induct x)
    case (ChanInp x)
    then show ?case by simp
  next
    case (ChanInpPred x1a x2)
    then show ?case sorry
  next
    case (ChanOutExp x)
    then show ?case sorry
  next
    case (ChanDotExp x)
    then show ?case sorry
  qed
lemma omega_ChanComNil1:"\<Omega> a = omega_CAction a \<Longrightarrow> \<Omega> (CSPCommAction (ChanComm c []) a) = (CSPCommAction (ChanComm c []) (\<Omega> a))" by simp
lemma omega_ChanComNil2:"\<Omega> a = omega_CAction a \<Longrightarrow> omega_CAction (CSPCommAction (ChanComm c []) a) = (CSPCommAction (ChanComm c []) (omega_CAction a))" by simp
lemma omega_ChanComNil:"\<Omega> a = omega_CAction a \<Longrightarrow> \<Omega> (CSPCommAction (ChanComm c Nil) a) = omega_CAction (CSPCommAction (ChanComm c Nil) a)" by simp
lemma omega_CSPHideSkip:"\<Omega> (CSPHide CSPSkip cs) = omega_CAction (CSPHide CSPSkip cs)" by simp

lemma omega_Com: "\<Omega> a = omega_CAction a \<Longrightarrow> \<Omega> (CSPCommAction (ChanComm x1a x2a) a) = omega_CAction (CSPCommAction (ChanComm x1a x2a) a)"
 proof (induct x2a)
        case Nil
        then show ?case by simp
      next
        case (Cons a x2a)
        then show ?case 
        proof (induct x2a)
          case Nil
          then show ?case 
               apply (subst omega_ChanComNil)

        next
          case (Cons a x2a)
          then show ?case sorry
        qed
      qed
 

  
lemma omega_CAct: "\<Omega> a = omega_CAction a"
  apply(induct a)
  apply auto
    sorry

    
lemma omega_CSPRecursion1:"\<Omega> (CSPRecursion x c) = (CSPRecursion x (\<Omega> c))" by simp
lemma omega_CSPRecursion2:"omega_CAction (CSPRecursion x c) = (CSPRecursion x (omega_CAction c))" by simp
lemma omega_CSPRecursionSkip:"\<Omega> (CSPRecursion x CSPSkip) = omega_CAction (CSPRecursion x CSPSkip)" by simp
lemma omega_CSPSeqSkip1:"\<Omega> (CSPSeq CSPSkip CSPSkip) = (CSPSeq (\<Omega> CSPSkip) (\<Omega> CSPSkip))" by simp
lemma omega_CSPSeqSkip2:"omega_CAction (CSPSeq CSPSkip CSPSkip) = (CSPSeq (omega_CAction CSPSkip) (omega_CAction CSPSkip))" by simp
lemma omega_CSPSeqSkip:"omega_CAction (CSPSeq CSPSkip CSPSkip) = \<Omega> (CSPSeq CSPSkip CSPSkip)" by simp

    
lemma omega_ChanComSinglt:"omega_CAction (CSPCommAction (ChanComm c [x]) CSPSkip) = (CSPCommAction (ChanComm c [x]) CSPSkip)"
proof (induct x)
  case (ChanInp x)
  then show ?case 
    proof (induct x)
      case Nil
      then show ?case by auto
    next
      case (Cons a x)
      then show ?case by simp
    qed
next
  case (ChanInpPred x1a x2)
  then show ?case 
  proof(induction x1a)
    show "omega_CAction (CSPCommAction (ChanComm c [ChanInpPred [] x2]) CSPSkip) 
            = CSPCommAction (ChanComm c [ChanInpPred [] x2]) CSPSkip" by simp
  next
  case (Cons a x1a)
  then show ?case sorry
qed 
     
next
  case (ChanOutExp x)
  then show ?case 
    proof(induct x)
      case (Choose x1 x)
      then show ?thesis by auto
    next
      case (Check x)
      then show ?thesis sorry
    next
      case (Evaluate x1 x1 x2)
      then show ?thesis sorry
    next
      case (ZVar x)
      then show ?case sorry
    next
      case (ZInt x)
      then show ?case sorry
    next
      case (ZSetComp x1 x2)
      then show ?case sorry
    next
      case (ZBinding x)
      then show ?case sorry
    next
      case (ZSetDisplay x)
      then show ?case sorry
    next
      case (ZSeqDisplay x)
      then show ?case sorry
    next
      case (ZTuple x)
      then show ?case sorry
    next
      case (ZCross x)
      then show ?case sorry
    next
      case (ZCall x1 x2)
      then show ?case sorry
    next
      case (ZFalse x)
      then show ?thesis sorry
    next
      case (ZTrue x)
      then show ?thesis sorry
    next
      case (ZAnd x1 x2)
      then show ?thesis sorry
    next
      case (ZPSchema x)
      then show ?thesis sorry
    next
      case (ZSchema x)
      then show ?thesis sorry
    qed
next
  case (ChanDotExp x)
  then show ?case sorry
qed
  
lemma omega_CommAction:  "\<Omega> (CSPCommAction (ChanComm x1a x2a) CSPSkip) = omega_CAction (CSPCommAction (ChanComm x1a x2a) CSPSkip)"
proof (induct x2a)
  case Nil
  then show ?case 
    apply (subst omega_ChanComNil)
    apply (subst omega_ChanComNil1)
    by auto
  next
  case (Cons a x2a)
  then show ?case 
qed
  
      
next
  case (Cons a x1a)
  then show ?case sorry
qed
  
lemma omega_CSPSkip1: "\<Omega> x = omega_CAction x" 
  proof(induct x)
    case (CircusAction x)
    then show ?thesis by sorry
  next
    case (ParamActionDecl x1 x2)
    then show ?thesis sorry
  next
    case (CActionCommand x)
    then show ?case sorry
  next
    case (CActionName x)
    then show ?case by auto
  next
    case CSPSkip
    then show ?case by auto
  next
    case CSPStop
    then show ?case by auto
  next
    case CSPChaos
    then show ?case by auto
  next
    case (CSPCommAction x1 x)
    then show ?case 
    apply (induct x1)  

  next
    case (CSPGuard x1 x)
    then show ?case sorry
  next
    case (CSPSeq x1 x2)
    then show ?case sorry
  next
    case (CSPExtChoice x1 x2)
    then show ?case sorry
  next
    case (CSPIntChoice x1 x2)
    then show ?case sorry
  next
    case (CSPNSParal x1 x2 x3 x1 x2)
    then show ?case sorry
  next
    case (CSPNSInter x1 x2 x1 x2)
    then show ?case sorry
  next
    case (CSPHide x x2)
    then show ?case sorry
  next
    case (CSPParAction x1 x2)
    then show ?case sorry
  next
    case (CSPRecursion x1 x)
    then show ?case sorry
  next
    case (CSPUnParAction x1 x x3)
    then show ?case sorry
  next
    case (CSPRepSeq x1 x)
    then show ?case sorry
  next
    case (CSPRepExtChoice x1 x)
    then show ?case sorry
  next
    case (CSPRepIntChoice x1 x)
    then show ?case sorry
  next
    case (CSPRepParalNS x1 x2 x3 x)
    then show ?case sorry
  next
    case (CSPRepParal x1 x2 x)
    then show ?case sorry
  next
    case (CSPRepInterlNS x1 x2 x)
    then show ?case sorry
  next
    case (CSPRepInterl x1 x)
    then show ?case sorry
  next
    case (CAssign x1 x2)
    then show ?thesis sorry
  next
    case (CIf x)
    then show ?thesis sorry
  next
    case (CVarDecl x1 x)
    then show ?thesis sorry
  next
    case (CValDecl x1 x)
    then show ?thesis sorry
  next
    case (CircGAction x1 x)
    then show ?thesis sorry
  next
    case (CircThenElse x1 x2)
    then show ?thesis sorry
  next
    case (CircElse x)
    then show ?thesis sorry
  qed

    
 

end
