theory Radix
imports Nats Prelude
begin
 
function (sequential) divmod :: "Nat \<Rightarrow> Nat \<Rightarrow> Nat * Nat"
where
  "divmod m n = (if eq_nat n Zero | less_nat m n then (Zero, m)
                 else let (q, r) = divmod (minus_nat m n) n
                      in (Suc q, r))"
sorry termination sorry
 
function (sequential) rad0
where
  "rad0 _ _ Zero = Nil"
| "rad0 ch r n = (let (m, d) = divmod n r
                  in ch d # rad0 ch r m)"
sorry termination sorry
 
function (sequential) radix :: "(Nat \<Rightarrow> 'a) \<Rightarrow> Nat \<Rightarrow> Nat \<Rightarrow> 'a list"
where
  "radix ch _ Zero = [ch Zero]"
| "radix ch r n = (let rad = rad0
                   in rev (rad ch r n))"
sorry termination sorry
 
definition radix_10 :: "Nat \<Rightarrow> Nat list"
where
  "radix_10 = radix id (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc Zero))))))))))"


end
