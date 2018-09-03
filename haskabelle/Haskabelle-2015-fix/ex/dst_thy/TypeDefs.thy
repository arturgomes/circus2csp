theory TypeDefs
imports Prelude
begin
 
type_synonym SomeType = int
 
fun "fun" :: "SomeType \<Rightarrow> SomeType"
where
  "fun x = x"


end
