theory TestingMappingFunStatelessCircus
imports MappingFunStatelessCircus
begin
 
fun \<Omega> :: "CAction \<Rightarrow> CAction" and 
    \<Omega>' :: "CAction \<Rightarrow> CAction"
where
  "\<Omega> CSPSkip = CSPSkip"
| "\<Omega> CSPStop = CSPStop"
| "\<Omega> CSPChaos = CSPChaos"
| "\<Omega> (CSPSeq ca cb) = (CSPSeq (\<Omega> ca) (\<Omega> cb))"
| "\<Omega> (CSPExtChoice ca cb) = (let lsx = (map fst (remdups (free_var_CAction (CSPExtChoice ca cb))))
                                         in make_get_com lsx (rename_vars_CAction (CSPExtChoice (\<Omega>' ca) (\<Omega>' cb))))"
| "\<Omega> x = x"
| "\<Omega>' CSPSkip = CSPSkip"
| "\<Omega>' CSPStop = CSPStop"
| "\<Omega>' CSPChaos = CSPChaos"
| "\<Omega>' (CSPSeq ca cb) = (CSPSeq (\<Omega>' ca) (\<Omega>' cb))"
| "\<Omega>' x = \<Omega> x"


end
