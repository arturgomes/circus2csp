theory ListComprehensions
imports Prelude
begin
 
definition list
where
  "list = [1, 2, 3, 4, 5]"

 
fun dot_product
where
  "dot_product f l1 l2 = ([f x y . x <- l1,
                                   y <- l2])"

 
definition list2
where
  "list2 = dot_product (op +) list list"

 
definition list3
where
  "list3 = ([x * x . x <- list,
                     eq x 1 | eq x 2])"


end
