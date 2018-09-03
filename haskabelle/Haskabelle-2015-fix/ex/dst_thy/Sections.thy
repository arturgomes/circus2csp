theory Sections
imports Prelude
begin
 
fun foo
where
  "foo list = map (% arg0 . arg0 @ [42]) list"

 
fun bar
where
  "bar list = map (% arg1 . [23] @ arg1) list"


end
