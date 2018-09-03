theory Records
imports Prelude
begin
 
datatype ('a) Identity = Id 'a
 
primrec this :: "'a Identity \<Rightarrow> 'a"
where
  "this (Id x) = x"

 
primrec update_this :: "'a \<Rightarrow> 'a Identity \<Rightarrow> 'a Identity"
where
  "update_this x (Id _) = (Id x)"

 
datatype MyRecord = A string bool int
                  | B bool int bool int
                  | C bool int string
 
primrec aField1 :: "MyRecord \<Rightarrow> string"
where
  "aField1 (A x _ _) = x"

 
primrec common1 :: "MyRecord \<Rightarrow> bool"
where
  "common1 (B _ _ x _) = x"
| "common1 (A _ x _) = x"

 
primrec common2 :: "MyRecord \<Rightarrow> int"
where
  "common2 (B _ _ _ x) = x"
| "common2 (A _ _ x) = x"

 
primrec bField1 :: "MyRecord \<Rightarrow> bool"
where
  "bField1 (B x _ _ _) = x"

 
primrec bField2 :: "MyRecord \<Rightarrow> int"
where
  "bField2 (B _ x _ _) = x"

 
primrec update_aField1 :: "string \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_aField1 x (A _ f2 f3) = (A x f2 f3)"

 
primrec update_common1 :: "bool \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_common1 x (B f1 f2 _ f4) = (B f1 f2 x f4)"
| "update_common1 x (A f1 _ f3) = (A f1 x f3)"

 
primrec update_common2 :: "int \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_common2 x (B f1 f2 f3 _) = (B f1 f2 f3 x)"
| "update_common2 x (A f1 f2 _) = (A f1 f2 x)"

 
primrec update_bField1 :: "bool \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_bField1 x (B _ f2 f3 f4) = (B x f2 f3 f4)"

 
primrec update_bField2 :: "int \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_bField2 x (B f1 _ f3 f4) = (B f1 x f3 f4)"

 
definition constr :: "MyRecord"
where
  "constr = A ''foo'' True undefined"

 
fun update :: "MyRecord \<Rightarrow> MyRecord"
where
  "update x = (update_common1 False o update_common2 1) x"

 
fun pattern :: "MyRecord \<Rightarrow> int"
where
  "pattern (A _ _ val) = val"
| "pattern (B _ val _ _) = val"
| "pattern (C _ val _) = val"


end
