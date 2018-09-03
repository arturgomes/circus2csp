theory LambdaFu
imports Prelude
begin
 
definition true
where
  "true = (% x y . x)"

 
definition false
where
  "false = (% x y . y)"

 
definition pair
where
  "pair = (% x y f . f x y)"

 
definition first
where
  "first = (% p . p true)"

 
definition second
where
  "second = (% p . p false)"

 
definition nil
where
  "nil = (% x . true)"

 
definition null
where
  "null = (% p . p (% x y . false))"

 
definition maybe_numbers
where
  "maybe_numbers = [Some 1, Some 3, Some 5, Some 7]"

 
definition numbers
where
  "numbers = map (% arg0 .
                    case arg0 of   (Some i) \<Rightarrow> i) maybe_numbers"


end
