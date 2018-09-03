theory Finite_Map
imports Prelude
begin
 
fun mkBranch :: "int \<Rightarrow> ('key :: ord) \<Rightarrow> 'elt \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "mkBranch which key elt fm_l fm_r = (let unbox = unbox2;
                                           left_ok = case fm_l of
                                                        EmptyFM \<Rightarrow> True
                                                      | Branch left_key _ _ _ _ \<Rightarrow> let biggest_left_key = fst (findMax fm_l)
                                                                                              in biggest_left_key < key;
                                           right_ok = case fm_r of
                                                         EmptyFM \<Rightarrow> True
                                                       | Branch right_key _ _ _ _ \<Rightarrow> let smallest_right_key = fst (findMin fm_r)
                                                                                                in key < smallest_right_key;
                                           balance_ok = True;
                                           left_size = sizeFM fm_l;
                                           right_size = sizeFM fm_r
                                       in let result = Branch key elt (unbox ((1 + left_size) + right_size)) fm_l fm_r
                                          in result)"

 
fun isJust :: "'a option \<Rightarrow> bool"
where
  "isJust (Some _) = True"
| "isJust None = False"

 
datatype ('key, 'elt) FiniteMap = EmptyFM
                                | Branch 'key 'elt int "('key, 'elt) FiniteMap" "('key, 'elt) FiniteMap"
 
definition emptyFM :: "('key, 'elt) FiniteMap"
where
  "emptyFM = EmptyFM"

 
fun unitFM :: "'key \<Rightarrow> 'elt \<Rightarrow> ('key, 'elt) FiniteMap"
where
  "unitFM key elt = Branch key elt 1 emptyFM emptyFM"

 
fun foldFM :: "('key \<Rightarrow> 'elt \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('key, 'elt) FiniteMap \<Rightarrow> 'a"
where
  "foldFM k z EmptyFM = z"
| "foldFM k z (Branch key elt _ fm_l fm_r) = foldFM k (k key elt (foldFM k z fm_r)) fm_l"

 
fun mapFM :: "('key \<Rightarrow> 'elt1 \<Rightarrow> 'elt2) \<Rightarrow> ('key, 'elt1) FiniteMap \<Rightarrow> ('key, 'elt2) FiniteMap"
where
  "mapFM f EmptyFM = emptyFM"
| "mapFM f (Branch key elt size14 fm_l fm_r) = Branch key (f key elt) size14 (mapFM f fm_l) (mapFM f fm_r)"

 
fun sizeFM :: "('key, 'elt) FiniteMap \<Rightarrow> int"
where
  "sizeFM EmptyFM = 0"
| "sizeFM (Branch _ _ size15 _ _) = size15"

 
fun isEmptyFM :: "('key, 'elt) FiniteMap \<Rightarrow> bool"
where
  "isEmptyFM fm = eq (sizeFM fm) 0"

 
fun lookupFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) \<Rightarrow> 'elt option"
where
  "lookupFM EmptyFM key = None"
| "lookupFM (Branch key elt _ fm_l fm_r) key_to_find = (if key_to_find < key
                                                        then lookupFM fm_l key_to_find
                                                        else if key_to_find > key
                                                             then lookupFM fm_r key_to_find
                                                             else Some elt)"

 
fun elemFM :: "('key :: ord) \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> bool"
where
  "elemFM key fm = (case (lookupFM fm key) of
                       None \<Rightarrow> False
                     | Some elt \<Rightarrow> True)"

 
fun lookupWithDefaultFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> 'elt \<Rightarrow> ('key :: ord) \<Rightarrow> 'elt"
where
  "lookupWithDefaultFM fm deflt key = (case (lookupFM fm key) of
                                          None \<Rightarrow> deflt
                                        | Some elt \<Rightarrow> elt)"

 
fun fmToList :: "('key, 'elt) FiniteMap \<Rightarrow> ('key * 'elt) list"
where
  "fmToList fm = foldFM (% key elt rest .
                           (key, elt) # rest) Nil fm"

 
fun keysFM :: "('key, 'elt) FiniteMap \<Rightarrow> 'key list"
where
  "keysFM fm = foldFM (% key elt rest . key # rest) Nil fm"

 
fun eltsFM :: "('key, 'elt) FiniteMap \<Rightarrow> 'elt list"
where
  "eltsFM fm = foldFM (% key elt rest . elt # rest) Nil fm"

 
definition sIZE_RATIO :: "int"
where
  "sIZE_RATIO = 5"

 
fun unbox2
where
  "unbox2 x = x"

 
fun findMin :: "('key, 'elt) FiniteMap \<Rightarrow> 'key * 'elt"
where
  "findMin (Branch key elt _ EmptyFM _) = (key, elt)"
| "findMin (Branch key elt _ fm_l _) = findMin fm_l"

 
fun findMax :: "('key, 'elt) FiniteMap \<Rightarrow> 'key * 'elt"
where
  "findMax (Branch key elt _ _ EmptyFM) = (key, elt)"
| "findMax (Branch key elt _ _ fm_r) = findMax fm_r"

 
fun single_L8
where
  "single_L8 (elt, key) fm_l (Branch key_r elt_r _ fm_rl fm_rr) = mkBranch 3 key_r elt_r (mkBranch 4 key elt fm_l fm_rl) fm_rr"

 
fun double_L4
where
  "double_L4 (elt, key) fm_l (Branch key_r elt_r _ (Branch key_rl elt_rl _ fm_rll fm_rlr) fm_rr) = mkBranch 5 key_rl elt_rl (mkBranch 6 key elt fm_l fm_rll) (mkBranch 7 key_r elt_r fm_rlr fm_rr)"

 
fun single_R10
where
  "single_R10 (elt, key) (Branch key_l elt_l _ fm_ll fm_lr) fm_r = mkBranch 8 key_l elt_l fm_ll (mkBranch 9 key elt fm_lr fm_r)"

 
fun double_R6
where
  "double_R6 (elt, key) (Branch key_l elt_l _ fm_ll (Branch key_lr elt_lr _ fm_lrl fm_lrr)) fm_r = mkBranch 10 key_lr elt_lr (mkBranch 11 key_l elt_l fm_ll fm_lrl) (mkBranch 12 key elt fm_lrr fm_r)"

 
fun mkBalBranch :: "('key :: ord) \<Rightarrow> 'elt \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "mkBalBranch key elt fm_L fm_R = (let double_L = double_L4 (elt, key);
                                        double_R = double_R6 (elt, key);
                                        single_L = single_L8 (elt, key);
                                        single_R = single_R10 (elt, key);
                                        size_l = sizeFM fm_L;
                                        size_r = sizeFM fm_R
                                    in if (size_l + size_r) < 2 then mkBranch 1 key elt fm_L fm_R
                                       else if size_r > (sIZE_RATIO * size_l)
                                            then case fm_R of
                                                    Branch _ _ _ fm_rl fm_rr \<Rightarrow> if sizeFM fm_rl < (2 * sizeFM fm_rr)
                                                                                           then single_L fm_L fm_R
                                                                                           else double_L fm_L fm_R
                                            else if size_l > (sIZE_RATIO * size_r)
                                                 then case fm_L of
                                                         Branch _ _ _ fm_ll fm_lr \<Rightarrow> if sizeFM fm_lr < (2 * sizeFM fm_ll)
                                                                                                then single_R fm_L fm_R
                                                                                                else double_R fm_L fm_R
                                                 else mkBranch 2 key elt fm_L fm_R)"

 
fun addToFM_C :: "('elt \<Rightarrow> 'elt \<Rightarrow> 'elt) \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) \<Rightarrow> 'elt \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "addToFM_C combiner EmptyFM key elt = unitFM key elt"
| "addToFM_C combiner (Branch key elt size12 fm_l fm_r) new_key new_elt = (if new_key < key
                                                                           then mkBalBranch key elt (addToFM_C combiner fm_l new_key new_elt) fm_r
                                                                           else if new_key > key
                                                                                then mkBalBranch key elt fm_l (addToFM_C combiner fm_r new_key new_elt)
                                                                                else Branch new_key (combiner elt new_elt) size12 fm_l fm_r)"

 
fun add0
where
  "add0 combiner fmap (key, elt) = addToFM_C combiner fmap key elt"

 
fun addListToFM_C :: "('elt \<Rightarrow> 'elt \<Rightarrow> 'elt) \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord) * 'elt) list \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "addListToFM_C combiner fm key_elt_pairs = (let add = add0 combiner
                                              in foldl add fm key_elt_pairs)"

 
fun addListToFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord) * 'elt) list \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "addListToFM fm key_elt_pairs = addListToFM_C (% old new .
                                                   new) fm key_elt_pairs"

 
definition listToFM :: "(('key :: ord) * 'elt) list \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "listToFM = addListToFM emptyFM"

 
fun addToFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) \<Rightarrow> 'elt \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "addToFM fm key elt = addToFM_C (% old new . new) fm key elt"

 
fun mkVBalBranch :: "('key :: ord) \<Rightarrow> 'elt \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "mkVBalBranch key elt EmptyFM fm_r = addToFM fm_r key elt"
| "mkVBalBranch key elt fm_l EmptyFM = addToFM fm_l key elt"
| "mkVBalBranch key elt (Branch key_l elt_l a0 fm_ll fm_lr) (Branch key_r elt_r a1 fm_rl fm_rr) = (let fm_l = (Branch key_l elt_l a0 fm_ll fm_lr);
                                                                                                       fm_r = (Branch key_r elt_r a1 fm_rl fm_rr)
                                                                                                   in let size_l = sizeFM fm_l;
                                                                                                          size_r = sizeFM fm_r
                                                                                                      in if (sIZE_RATIO * size_l) < size_r
                                                                                                         then mkBalBranch key_r elt_r (mkVBalBranch key elt fm_l fm_rl) fm_rr
                                                                                                         else if (sIZE_RATIO * size_r) < size_l
                                                                                                              then mkBalBranch key_l elt_l fm_ll (mkVBalBranch key elt fm_lr fm_r)
                                                                                                              else mkBranch 13 key elt fm_l fm_r)"

 
fun plusFM_C :: "('elt \<Rightarrow> 'elt \<Rightarrow> 'elt) \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "plusFM_C combiner EmptyFM fm2 = fm2"
| "plusFM_C combiner fm1 EmptyFM = fm1"
| "plusFM_C combiner fm1 (Branch split_key elt2 _ left right) = (let lts = splitLT fm1 split_key;
                                                                     gts = splitGT fm1 split_key;
                                                                     new_elt = case lookupFM fm1 split_key of
                                                                                  None \<Rightarrow> elt2
                                                                                | Some elt1 \<Rightarrow> combiner elt1 elt2
                                                                 in mkVBalBranch split_key new_elt (plusFM_C combiner lts left) (plusFM_C combiner gts right))"

 
fun plusFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "plusFM EmptyFM fm2 = fm2"
| "plusFM fm1 EmptyFM = fm1"
| "plusFM fm1 (Branch split_key elt1 _ left right) = (let lts = splitLT fm1 split_key;
                                                          gts = splitGT fm1 split_key
                                                      in mkVBalBranch split_key elt1 (plusFM lts left) (plusFM gts right))"

 
fun deleteMin :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "deleteMin (Branch key elt _ EmptyFM fm_r) = fm_r"
| "deleteMin (Branch key elt _ fm_l fm_r) = mkBalBranch key elt (deleteMin fm_l) fm_r"

 
fun deleteMax :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "deleteMax (Branch key elt _ fm_l EmptyFM) = fm_l"
| "deleteMax (Branch key elt _ fm_l fm_r) = mkBalBranch key elt fm_l (deleteMax fm_r)"

 
fun glueBal :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "glueBal EmptyFM fm2 = fm2"
| "glueBal fm1 EmptyFM = fm1"
| "glueBal fm1 fm2 = (let (mid_key1, mid_elt1) = findMax fm1;
                          (mid_key2, mid_elt2) = findMin fm2
                      in if sizeFM fm2 > sizeFM fm1
                         then mkBalBranch mid_key2 mid_elt2 fm1 (deleteMin fm2)
                         else mkBalBranch mid_key1 mid_elt1 (deleteMax fm1) fm2)"

 
fun delFromFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "delFromFM EmptyFM del_key = emptyFM"
| "delFromFM (Branch key elt size13 fm_l fm_r) del_key = (if del_key > key
                                                          then mkBalBranch key elt fm_l (delFromFM fm_r del_key)
                                                          else if del_key < key
                                                               then mkBalBranch key elt (delFromFM fm_l del_key) fm_r
                                                               else glueBal fm_l fm_r)"

 
fun delListFromFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) list \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "delListFromFM fm keys = foldl delFromFM fm keys"

 
fun glueVBal :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "glueVBal EmptyFM fm2 = fm2"
| "glueVBal fm1 EmptyFM = fm1"
| "glueVBal (Branch key_l elt_l a2 fm_ll fm_lr) (Branch key_r elt_r a3 fm_rl fm_rr) = (let fm_l = (Branch key_l elt_l a2 fm_ll fm_lr);
                                                                                           fm_r = (Branch key_r elt_r a3 fm_rl fm_rr)
                                                                                       in let size_l = sizeFM fm_l;
                                                                                              size_r = sizeFM fm_r
                                                                                          in if (sIZE_RATIO * size_l) < size_r
                                                                                             then mkBalBranch key_r elt_r (glueVBal fm_l fm_rl) fm_rr
                                                                                             else if (sIZE_RATIO * size_r) < size_l
                                                                                                  then mkBalBranch key_l elt_l fm_ll (glueVBal fm_lr fm_r)
                                                                                                  else glueBal fm_l fm_r)"

 
fun minusFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "minusFM EmptyFM fm2 = emptyFM"
| "minusFM fm1 EmptyFM = fm1"
| "minusFM fm1 (Branch split_key elt _ left right) = (let lts = splitLT fm1 split_key;
                                                          gts = splitGT fm1 split_key
                                                      in glueVBal (minusFM lts left) (minusFM gts right))"

 
fun mapMaybeFM :: "(('key :: ord) \<Rightarrow> 'elt1 \<Rightarrow> 'elt2 option) \<Rightarrow> (('key :: ord), 'elt1) FiniteMap \<Rightarrow> (('key :: ord), 'elt2) FiniteMap"
where
  "mapMaybeFM f EmptyFM = emptyFM"
| "mapMaybeFM f (Branch key elt _ fm_l fm_r) = (case f key elt of
                                                   None \<Rightarrow> glueVBal (mapMaybeFM f fm_l) (mapMaybeFM f fm_r)
                                                 | Some elt' \<Rightarrow> mkVBalBranch key elt' (mapMaybeFM f fm_l) (mapMaybeFM f fm_r))"

 
fun filterFM :: "(('key :: ord) \<Rightarrow> 'elt \<Rightarrow> bool) \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "filterFM p EmptyFM = emptyFM"
| "filterFM p (Branch key elt _ fm_l fm_r) = (if p key elt
                                              then mkVBalBranch key elt (filterFM p fm_l) (filterFM p fm_r)
                                              else glueVBal (filterFM p fm_l) (filterFM p fm_r))"

 
fun splitLT :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "splitLT EmptyFM split_key = emptyFM"
| "splitLT (Branch key elt _ fm_l fm_r) split_key = (if split_key < key
                                                     then splitLT fm_l split_key
                                                     else if split_key > key
                                                          then mkVBalBranch key elt fm_l (splitLT fm_r split_key)
                                                          else fm_l)"

 
fun splitGT :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> ('key :: ord) \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "splitGT EmptyFM split_key = emptyFM"
| "splitGT (Branch key elt _ fm_l fm_r) split_key = (if split_key > key
                                                     then splitGT fm_r split_key
                                                     else if split_key < key
                                                          then mkVBalBranch key elt (splitGT fm_l split_key) fm_r
                                                          else fm_r)"

 
fun intersectFM_C :: "('elt1 \<Rightarrow> 'elt2 \<Rightarrow> 'elt3) \<Rightarrow> (('key :: ord), 'elt1) FiniteMap \<Rightarrow> (('key :: ord), 'elt2) FiniteMap \<Rightarrow> (('key :: ord), 'elt3) FiniteMap"
where
  "intersectFM_C combiner fm1 EmptyFM = emptyFM"
| "intersectFM_C combiner EmptyFM fm2 = emptyFM"
| "intersectFM_C combiner fm1 (Branch split_key elt2 _ left right) = (let lts = splitLT fm1 split_key;
                                                                          gts = splitGT fm1 split_key;
                                                                          maybe_elt1 = lookupFM fm1 split_key;
                                                                          elt1 = case maybe_elt1 of
                                                                                    Some x \<Rightarrow> x
                                                                      in if isJust maybe_elt1
                                                                         then mkVBalBranch split_key (combiner elt1 elt2) (intersectFM_C combiner lts left) (intersectFM_C combiner gts right)
                                                                         else glueVBal (intersectFM_C combiner lts left) (intersectFM_C combiner gts right))"

 
fun intersectFM :: "(('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap \<Rightarrow> (('key :: ord), 'elt) FiniteMap"
where
  "intersectFM fm1 fm2 = intersectFM_C (% left right .
                                          right) fm1 fm2"


end
