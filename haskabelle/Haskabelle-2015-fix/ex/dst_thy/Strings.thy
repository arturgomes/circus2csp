theory Strings
imports Nats Prelude
begin
 
fun digit10 :: "Nat \<Rightarrow> char"
where
  "digit10 Zero = CHR ''0''"
| "digit10 (Suc Zero) = CHR ''1''"
| "digit10 (Suc (Suc Zero)) = CHR ''2''"
| "digit10 (Suc (Suc (Suc Zero))) = CHR ''3''"
| "digit10 (Suc (Suc (Suc (Suc Zero)))) = CHR ''4''"
| "digit10 (Suc (Suc (Suc (Suc (Suc Zero))))) = CHR ''5''"
| "digit10 (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))) = CHR ''6''"
| "digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))) = CHR ''7''"
| "digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero)))))))) = CHR ''8''"
| "digit10 (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))) = CHR ''9''"


end
