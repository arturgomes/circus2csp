theory Depend
imports Depend_DependB Prelude
begin
 
definition alias
where
  "alias = 1"

 
definition somefun
where
  "somefun = (map $ (op +) 1)"


end
