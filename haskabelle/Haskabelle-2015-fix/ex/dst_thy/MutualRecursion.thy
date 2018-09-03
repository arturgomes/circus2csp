theory MutualRecursion
imports Prelude
begin
 
datatype Exp = Plus Exp Exp
             | Times Exp Exp
             | Cond Bexp Exp Exp
             | Val int
and      Bexp = Equal Exp Exp
              | Greater Exp Exp
 
fun evalExp :: "Exp \<Rightarrow> int" and 
    evalBexp :: "Bexp \<Rightarrow> bool"
where
  "evalExp (Plus e1 e2) = (evalExp e1 + evalExp e2)"
| "evalExp (Times e1 e2) = (evalExp e1 * evalExp e2)"
| "evalExp (Cond b e1 e2) = (if evalBexp b then evalExp e1
                             else evalExp e2)"
| "evalExp (Val i) = i"
| "evalBexp (Equal e1 e2) = eq (evalExp e1) (evalExp e2)"
| "evalBexp (Greater e1 e2) = (evalExp e1 > evalExp e2)"


end
