theory General_Union
  imports Main SGraph HOL.Real Extension_3
begin


(***************************mapper***************************)

primrec reach :: "fnode list \<Rightarrow> fnode list \<Rightarrow> (fnode\<times>fnode list) list" where
"reach [] fns2=[]"|
"reach (fn#fns1) fns2=(if (snd fn =True) then (fn,fns2)#(reach fns1 fns2) else reach fns1 fns2)"

lemma reach_size:"size (filter (\<lambda> t::fnode. snd t=True) fns1) =size (reach fns1 fns2)"
  apply (induct fns1)
  by simp+
lemma reach_member:"map_of fns1 n =Some True \<Longrightarrow> List.member (reach fns1 fns2) ((n,True),fns2)"
  apply (induct fns1) 
  apply (simp add:member_def)+
  apply auto
  apply (case_tac "n = a")
  apply simp+
  apply (case_tac "n = a")
   apply simp+
  done

fun mapper_GU :: "fnode\<times>fnode list \<Rightarrow> (fnode\<times>fnode list) list"where 
"mapper_GU (fn,fns) =(if (snd fn) =False then [] else (fn,fns)#(reach fns fns))"

value "map mapper_GU result_E3"
lemma mapper_GU_F:"(snd fn) =False \<Longrightarrow> mapper_GU (fn,fns) =[]"
  by auto
lemma mapper_GU_T:"(snd fn) =True \<Longrightarrow> mapper_GU (fn,fns) =(fn,fns)#(reach fns fns)"
  by auto

(***************************shuffer***************************)

definition "shuffer_GU ffss \<equiv> Shuffle_single_llist ffss []"

(***************************reducer***************************)

primrec Merge :: "'a list \<Rightarrow>'a list \<Rightarrow>'a list" where
"Merge [] as = as"|
"Merge (as#as1) as2 = (if (distinct (as#as2)) then (Merge as1 (as#as2)) else (Merge as1 as2))"

primrec Merge_list :: "'a list list \<Rightarrow>'a list" where
"Merge_list [] = []"|
"Merge_list (as#ass) = Merge as (Merge_list ass)"

lemma Merge_set:"distinct as2 \<Longrightarrow>set as1 \<union> set as2 = set (Merge as1 as2)"
  apply (induct as1 arbitrary:as2)
   apply simp+
  apply auto
  apply (metis distinct.simps(2) in_set_conv_decomp set_append)
  apply (metis UnCI Un_iff distinct.simps(2) list.set_intros(2))
  by (metis Un_iff distinct.simps(2) set_ConsD)
lemma Merge_distinct:"distinct as2 \<Longrightarrow> distinct (Merge as1 as2)"
  apply (induct as1 arbitrary:as2)
   by simp+
theorem Merge_list_distinct:"distinct (Merge_list fns)"
  apply (induct fns)
   apply simp+
  by (simp add: Merge_distinct)
theorem Merge_list_set:"set(concat fns) = set(Merge_list fns)"
  apply (induct fns)
   apply simp+
  apply (rule Merge_set)
  by (simp add:Merge_list_distinct)

fun quicksort :: "fnode list \<Rightarrow> fnode list" where
  "quicksort []     = []"
| "quicksort (x#xs) = quicksort [y\<leftarrow>xs. \<not> fst x\<le>fst y] 
                            @ [x] @ 
                           quicksort [y\<leftarrow>xs. fst x\<le>fst y]"

theorem quicksort_set:"set xs =set (quicksort xs)"
  apply (induct xs rule:quicksort.induct)
   apply simp+
  by auto

lemma quicksort_filter:"x \<in> set (quicksort (filter f  xs)) \<Longrightarrow> f x"
  apply (induct xs)
   apply simp+
  by (metis (full_types) quicksort_set set_ConsD) 

theorem quicksort_sorted:"sorted (map fst (quicksort xs))"
  apply (induct xs rule:quicksort.induct) 
   apply simp
  apply (simp add: sorted_append)
  apply auto
  apply (drule quicksort_filter,simp)+
  done

fun getVmin :: "fnode list \<Rightarrow> fnode" where
"getVmin fns = (quicksort fns)!0"

lemma "List.member fns fn \<Longrightarrow> fst fn \<ge> fst (getVmin fns)"
  apply (simp add:List.member_def)
  apply (induct fns)
   apply simp+
  apply auto
  oops

fun reducer_GU' :: "(fnode\<times>(fnode list) list) \<Rightarrow> (fnode\<times>fnode list)" where
"reducer_GU' (fn,fns) =(fn, quicksort (Merge_list fns))"

fun reducer_GU :: "(fnode\<times>(fnode list) list) \<Rightarrow> (fnode\<times>fnode list)" where
"reducer_GU (fn,fns) =((fst(getVmin (Merge_list fns)),True) , quicksort (Merge_list fns))"
(***************************result***************************)

definition result_GU :: "(fnode\<times>fnode list) list" where
"result_GU \<equiv> MapReduce result_E3 mapper_GU shuffer_GU reducer_GU"

value result_GU
definition "re = [((3, True), [(3, False), (4, True), (5, False), (6, True), (7, True)]),
  ((3, True), [(3, False), (4, True), (5, False), (6, True), (7, True)]),
  ((3, True), [(3, False), (4, True), (5, False), (6, True), (7, True)])]"

value "MapReduce result_GU mapper_GU shuffer_GU reducer_GU"
definition "result_GU' \<equiv> MapReduce result_GU mapper_GU shuffer_GU reducer_GU"

value "MapReduce result_GU' mapper_GU shuffer_GU reducer_GU"
end