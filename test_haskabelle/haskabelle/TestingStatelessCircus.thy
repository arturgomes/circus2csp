theory TestingStatelessCircus
imports MappingFunStatelessCircus
begin
 
fun thy_omega :: "CAction \<Rightarrow> CAction"
where
  "thy_omega CSPSkip = CSPSkip"
| "thy_omega CSPStop = CSPStop"
| "thy_omega CSPChaos = CSPChaos"
| "thy_omega (CSPCommAction (ChanComm c Nil) a) = (CSPCommAction (ChanComm c Nil) (thy_omega a))"

lemma "thy_omega (omega_CAction Nil a) = omega_CAction Nil (thy_omega a)"
  apply (induction a)