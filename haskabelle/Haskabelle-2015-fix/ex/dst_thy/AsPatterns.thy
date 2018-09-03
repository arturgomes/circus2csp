theory AsPatterns
imports Prelude
begin
 
datatype MyRecord = A "int list" int char
 
primrec one :: "MyRecord \<Rightarrow> int list"
where
  "one (A x _ _) = x"

 
primrec two :: "MyRecord \<Rightarrow> int"
where
  "two (A _ x _) = x"

 
primrec three :: "MyRecord \<Rightarrow> char"
where
  "three (A _ _ x) = x"

 
primrec update_one :: "int list \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_one x (A _ f2 f3) = (A x f2 f3)"

 
primrec update_two :: "int \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_two x (A f1 _ f3) = (A f1 x f3)"

 
primrec update_three :: "char \<Rightarrow> MyRecord \<Rightarrow> MyRecord"
where
  "update_three x (A f1 f2 _) = (A f1 f2 x)"

 
fun f
where
  "f Unity = Unity"

 
fun foo
where
  "foo Nil = Nil"
| "foo ((x1, x2) # ((y1, y2) # rest)) = (let a = (x1, x2);
                                             b = (y1, y2)
                                         in a # (b # rest))"

 
fun bar
where
  "bar x = (case x of
               [(b, c)] \<Rightarrow> let a = (b, c)
                                      in a
             | ((x1, x2) # ((y1, y2) # rest)) \<Rightarrow> let a = (x1, x2);
                                                                b = (y1, y2);
                                                                c = ((x1, x2) # ((y1, y2) # rest))
                                                            in a)"

 
fun quux
where
  "quux x = (% arg0 .
               case arg0 of
                  (r, s) \<Rightarrow> let a = (r, s)
                                       in x @ [a])"

 
fun unsound :: "int list \<Rightarrow> int list"
where
  "unsound (a1 # a2) = (let l = (a1 # a2)
                        in 0 # l)"
| "unsound Nil = (let l = Nil
                  in 1 # l)"

 
fun "record" :: "MyRecord \<Rightarrow> MyRecord"
where
  "record (A Nil a3 a4) = (let a = (A Nil a3 a4)
                           in a)"

 
fun long :: "('a :: print) list \<Rightarrow> string"
where
  "long (a5 # (a6 # a7)) = (let l = (a5 # (a6 # a7))
                            in print l @ '' is long enough!'')"
| "long l = (print l @ '' is too short!'')"


end
