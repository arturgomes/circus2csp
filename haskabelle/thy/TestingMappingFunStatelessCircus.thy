section "Proofs and Tests over Omega Functions"

theory TestingMappingFunStatelessCircus imports MappingFunStatelessCircus AbstractOmegaDefs begin

fun \<Omega> :: "CAction \<Rightarrow> CAction" and 
    \<Omega>' :: "CAction \<Rightarrow> CAction"
where
  "\<Omega> CSPSkip = CSPSkip"
| "\<Omega> CSPStop = CSPStop"
| "\<Omega> CSPChaos = CSPChaos"
| "\<Omega> (CSPSeq ca cb) = (CSPSeq (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPExtChoice ca cb) 
    = (let lsx = (map fst (remdups (set_to_list (abs_fv_CAction (CSPExtChoice ca cb)))))
       in make_get_com lsx (abs_rename_vars_CAction (CSPExtChoice (\<Omega>' ca) (\<Omega>' cb))))"
| "\<Omega> x = x"
| "\<Omega>' CSPSkip = CSPSkip"
| "\<Omega>' CSPStop = CSPStop"
| "\<Omega>' CSPChaos = CSPChaos"
| "\<Omega>' (CSPSeq ca cb) = (CSPSeq (\<Omega>' ca) (\<Omega>' cb))"
| "\<Omega>' x = \<Omega> x"

lemma "set_to_list {} = []"
   by (meson finite.emptyI set_empty set_set_to_list)

lemma "a1 = CSPSkip \<and> a2 = CSPSkip \<Longrightarrow> \<Omega> (CSPExtChoice a1 a2) = omega_CAction (CSPExtChoice a1 a2)"
  apply simp
  by (metis Domain_empty OmegaDefs.remdups.simps(1) finite.emptyI fst_eq_Domain make_get_com.simps(3) set_empty set_map set_set_to_list)

lemma "a1 = CSPSkip \<and> a2 = CSPSkip \<Longrightarrow> \<Omega> (CSPSeq a1 a2) = omega_CAction  (CSPSeq a1 a2)"
 by simp
    
lemma "\<Omega> a = omega_CAction a"
proof (induction a)
  case CSPSkip
  then show ?case by simp
next
  case CSPStop
  then show ?case  by simp
next
  case CSPChaos
  then show ?case  by simp
next
  case (CSPCommAction x1 a)
  then show ?case by simp
next
  case (CSPSeq a1 a2)
  then show ?case  by simp
next
  case (CSPExtChoice a1 a2)
  then show ?case sorry   
qed
  
end
