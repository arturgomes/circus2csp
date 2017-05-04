section "Proofs and Tests over Omega Functions"

theory TestingMappingFunStatelessCircus imports MappingFunStatelessCircus AbstractOmegaDefs begin

fun \<Omega> :: "CAction \<Rightarrow> CAction" and 
    \<Omega>' :: "CAction \<Rightarrow> CAction"
where
  "\<Omega> CSPSkip = CSPSkip"
| "\<Omega> CSPStop = CSPStop"
| "\<Omega> CSPChaos = CSPChaos"
| "\<Omega> (CSPSeq ca cb) = (CSPSeq (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPHide ca x) = (CSPHide (\<Omega> ca) x)"
| "\<Omega> (CSPExtChoice ca cb) 
    = (let lsx = (map fst (abs_remdups (abs_free_var_CAction (CSPExtChoice ca cb))))
       in abs_make_get_com lsx (abs_rename_vars_CAction (CSPExtChoice (\<Omega>' ca) (\<Omega>' cb))))"
| "\<Omega> x = x"
| "\<Omega>' CSPSkip = CSPSkip"
| "\<Omega>' CSPStop = CSPStop"
| "\<Omega>' CSPChaos = CSPChaos"
| "\<Omega>' (CSPSeq ca cb) = (CSPSeq (\<Omega>' ca) (\<Omega>' cb))"
| "\<Omega>' x = \<Omega> x"

lemma "a1 = CSPSkip \<and> a2 = CSPSkip \<Longrightarrow> \<Omega> (CSPExtChoice a1 a2) = omega_CAction (CSPExtChoice a1 a2)" by simp
    
lemma "a1 = CSPSkip \<and> a2 = CSPSkip \<Longrightarrow> \<Omega> (CSPSeq a1 a2) = omega_CAction  (CSPSeq a1 a2)" by simp

lemma thm_omega_prime:"\<Omega>' a = omega_prime_CAction a"
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
  then show ?case 
    by (simp add: thm_rv_CAction thm_make_get_com thm_free_var_CAction thm_remdups)
qed
      
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
  then show ?case 
    by (simp add: thm_omega_prime thm_rv_CAction thm_make_get_com thm_free_var_CAction thm_remdups)
qed
  
end
