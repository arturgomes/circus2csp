theory Closure
imports Prelude
begin
 
fun addToX0
where
  "addToX0 x y = (x + y)"

 
fun addToY2
where
  "addToY2 y x = (x + y)"

 
fun sum3
where
  "sum3 y x = (let env4 = y
               in let w = addToY2 env4 x
                  in w + x)"

 
fun func
where
  "func x y = (let addToX = addToX0 x;
                   addToY = addToY2 y;
                   sum = sum3 y;
                   w = addToY x
               in sum x + addToX y)"


end
