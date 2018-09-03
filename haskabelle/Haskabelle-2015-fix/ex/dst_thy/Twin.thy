theory Twin
imports Prelude
begin
 
datatype ('a, 'b) Twin = Twin 'a 'b
 
fun dest_Twin :: "('a, 'b) Twin \<Rightarrow> 'a * 'b"
where
  "dest_Twin (Twin x y) = (x, y)"

 
definition mk_Twin :: "'a * 'b \<Rightarrow> ('a, 'b) Twin"
where
  "mk_Twin = uncurry Twin"


end
