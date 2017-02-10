section "Omega Function Definitions"
theory MappingFunStatelessCircus imports AST OmegaDefs Prelude begin
 
fun omega_CAction :: "CAction \<Rightarrow> CAction" and 
    omega_prime_CAction :: "CAction \<Rightarrow> CAction"
where
  "omega_CAction CSPSkip = CSPSkip"
| "omega_CAction CSPStop = CSPStop"
| "omega_CAction CSPChaos = CSPChaos"
| "omega_CAction (CSPSeq ca cb) = (CSPSeq (omega_CAction ca) (omega_CAction cb))"
| "omega_CAction (CSPExtChoice ca cb) = (let lsx = (map fst (remdups (free_var_CAction (CSPExtChoice ca cb))))
                                         in make_get_com lsx (rename_vars_CAction (CSPExtChoice (omega_prime_CAction ca) (omega_prime_CAction cb))))"
| "omega_CAction x = x"
| "omega_prime_CAction CSPSkip = CSPSkip"
| "omega_prime_CAction CSPStop = CSPStop"
| "omega_prime_CAction CSPChaos = CSPChaos"
| "omega_prime_CAction (CSPSeq ca cb) = (CSPSeq (omega_prime_CAction ca) (omega_prime_CAction cb))"
| "omega_prime_CAction x = omega_CAction x"


end
