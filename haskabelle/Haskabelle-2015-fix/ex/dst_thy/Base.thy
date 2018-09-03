theory Base
imports Prelude
begin
 
fun map_index :: "(int * 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "map_index f = (let mapp = mapp0 f
                  in mapp 0)"

 
fun fold
where
  "fold f Nil y = y"
| "fold f (x # xs) y = fold f xs (f x y)"

 
fun fold_map :: "('a \<Rightarrow> 's \<Rightarrow> 'b * 's) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> ('b list) * 's"
where
  "fold_map f Nil y = (Nil, y)"
| "fold_map f (x # xs) y = (let (x', y') = f x y;
                                (xs', y'') = fold_map f xs y'
                            in (x' # xs', y''))"

 
fun maps :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "maps f Nil = Nil"
| "maps f (x # xs) = (f x @ maps f xs)"

 
fun mapp0
where
  "mapp0 f _ Nil = Nil"
| "mapp0 f i (x # xs) = (let env1 = f
                         in f (i, x) # mapp0 env1 (i + 1) xs)"

 
fun map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
where
  "map2 _ Nil Nil = Nil"
| "map2 f (x # xs) (y # ys) = (f x y # map2 f xs ys)"
| "map2 _ _ _ = error ''unequal lengths''"

 
fun map_split :: "('a \<Rightarrow> 'b * 'c) \<Rightarrow> 'a list \<Rightarrow> ('b list) * ('c list)"
where
  "map_split f Nil = (Nil, Nil)"
| "map_split f (x # xs) = (let (y, w) = f x;
                               (ys, ws) = map_split f xs
                           in (y # ys, (w # ws)))"

 
fun map_product :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
where
  "map_product f _ Nil = Nil"
| "map_product f Nil _ = Nil"
| "map_product f (x # xs) ys = (map (f x) ys @ map_product f xs ys)"

 
fun member :: "('a :: eq) list \<Rightarrow> ('a :: eq) \<Rightarrow> bool"
where
  "member Nil y = False"
| "member (x # xs) y = (eq x y | member xs y)"

 
fun distincts :: "('a :: eq) list \<Rightarrow> ('a :: eq) list"
where
  "distincts Nil = Nil"
| "distincts (x # xs) = (if member xs x then distincts xs
                         else x # distincts xs)"


end
