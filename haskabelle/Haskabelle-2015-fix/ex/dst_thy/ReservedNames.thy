theory ReservedNames
imports Prelude
begin
 
fun knorks2
where
  "knorks2 x set10 = ([x] @ set10)"

 
fun zurp
where
  "zurp x = (let knorks = knorks2
             in knorks x Nil)"

 
fun frob0
where
  "frob0 nat8 set9 = (nat8 # set9)"

 
fun quux
where
  "quux nat7 = (let frob = frob0
                in frob nat7 Nil)"

 
fun foo
where
  "foo nat4 set5 = (nat4 # ([nat4] @ set5))"

 
fun bar
where
  "bar nat6 = (let set = [nat6]
               in set)"


end
