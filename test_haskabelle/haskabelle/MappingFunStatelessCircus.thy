theory MappingFunStatelessCircus
imports AST OmegaDefs Prelude
begin

type_synonym AName = string
 
datatype CParameter = C1 AName
 
datatype Comm = ACom AName "CParameter list"
 
datatype MAct = AFinal
                 | ActCom Comm MAct

function(sequential) myfun1 :: "(MAct \<Rightarrow> MAct) \<Rightarrow> Comm \<Rightarrow> MAct \<Rightarrow> MAct"
where
  "myfun1 f (ACom c Nil) a = (ActCom (ACom c Nil) (f a))"
| "myfun1 f x a = f (ActCom x a)"
  by pat_completeness auto
  termination by lexicographic_order
 
function (sequential) transf_MAct :: "MAct \<Rightarrow> MAct" and 
    transf_prime_MAct :: "MAct \<Rightarrow> MAct"
where
  "transf_MAct AFinal = AFinal"
| "transf_MAct (ActCom c a) = myfun1 transf_MAct c a"
| "transf_prime_MAct (ActCom (ACom c Nil) a) = (ActCom (ACom c Nil) (transf_prime_MAct a))"
| "transf_prime_MAct x = transf_MAct x"
  by pat_completeness auto
  termination by lexicographic_order

end
