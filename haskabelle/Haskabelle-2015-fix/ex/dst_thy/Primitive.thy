theory Primitive
imports Prelude
begin
 
datatype Nat = Zero
             | Succ Nat
 
fun id :: "'a \<Rightarrow> 'a"
where
  "id x = x"

 
definition foo :: "'a \<Rightarrow> 'a"
where
  "foo = (% x . x)"

 
fun incr :: "Nat \<Rightarrow> Nat"
where
  "incr n = Succ n"

 
fun decr :: "Nat \<Rightarrow> Nat"
where
  "decr (Succ n) = n"

 
datatype Boolean = Verum
                 | Falsum
 
fun isEven :: "Nat \<Rightarrow> Boolean" and 
    isOdd :: "Nat \<Rightarrow> Boolean"
where
  "isEven Zero = Verum"
| "isEven (Succ Zero) = Falsum"
| "isEven n = isOdd (decr n)"
| "isOdd Zero = Falsum"
| "isOdd (Succ Zero) = Verum"
| "isOdd n = isEven (decr n)"


end
