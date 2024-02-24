theory Base_Min_Core_Union
  imports Main SGraph_update HOL.Real Extension_3 Inclusion_Removal
begin

definition MapReduce_BMCU :: 
  "(fnode\<times>fnode list) list \<Rightarrow>
    (fnode\<times>fnode list \<Rightarrow> (fnode\<times>fnode list) list) \<Rightarrow>
    (((fnode\<times>fnode list) list) list \<Rightarrow>(fnode\<times>(fnode list) list) list ) \<Rightarrow>
    ((fnode\<times>(fnode list) list) \<Rightarrow> (fnode\<times>fnode list)) \<Rightarrow>
    (fnode\<times>fnode list) list"
  where "MapReduce_BMCU input m s r \<equiv> Inclusion_Removal(map r (s (map m input)))"

(***************************mapper***************************)

definition  min_fnode :: "fnode \<Rightarrow> fnode \<Rightarrow> fnode" 
  where "min_fnode u v = (if fst u \<le> fst v then u else v)"

fun getVmin_True :: "fnode list \<Rightarrow> fnode" 
  where "getVmin_True [] = (0,True)"|
        "getVmin_True [fn] = fn"|
        "getVmin_True (fn#fns) = (if (snd fn) then min_fnode fn (getVmin_True fns) 
                                  else getVmin_True fns)"

fun mapper_BMCU_cur_clu :: "fnode\<times>fnode list\<Rightarrow> (fnode\<times>fnode list) option"
  where "mapper_BMCU_cur_clu (fn,fs_DN) =((if (fs_DN \<noteq> []) 
                             then Some ((getVmin_True fs_DN),fs_DN) else None))"

primrec mapper_BMCU_cur_reach_emit :: "fnode list \<Rightarrow> fnode \<Rightarrow> (fnode\<times>fnode list) list" 
  where "mapper_BMCU_cur_reach_emit [] fn = []"|
        "mapper_BMCU_cur_reach_emit (fn1#fns) fn2 = (if (snd fn1) =False then 
         mapper_BMCU_cur_reach_emit fns fn2 else (fn1,[fn2])#mapper_BMCU_cur_reach_emit fns fn2)"

fun mapper_BMCU_cur_reach :: "fnode\<times>fnode list\<Rightarrow> (fnode\<times>fnode list) list"
  where "mapper_BMCU_cur_reach (fn,fs_DN) =(if (fs_DN \<noteq> [])
         then mapper_BMCU_cur_reach_emit fs_DN ((getVmin_True fs_DN)) else [])"

lemma mapper_BMCU_cur_reach_emit_lemma: "(f, fs) \<in> set (mapper_BMCU_cur_reach_emit fs_DN fVmin) \<Longrightarrow> fs = [fVmin] \<and>  snd f"
  apply (induct fs_DN)
   apply simp
  apply (simp only:mapper_BMCU_cur_reach_emit.simps)
  apply (case_tac "\<not> snd a")
    apply simp+
  by auto

fun mapper_BMCU :: "fnode\<times>fnode list \<Rightarrow> (fnode\<times>fnode list) list"
  where "mapper_BMCU fnn = (if (snd(fst fnn)) then 
        (the(mapper_BMCU_cur_clu fnn) # (mapper_BMCU_cur_reach fnn)) else [])"

value "map mapper_BMCU result_E3"
theorem mapper_BMCU_theorem: " List.member (mapper_BMCU (fn,fs_DN)) (f,fs) \<Longrightarrow> (if (fs_DN \<noteq> []) then
                             ((f,fs) = (getVmin_True fs_DN,fs_DN) \<or> (fs = [getVmin_True fs_DN] \<and> (List.member (fs_DN) f \<longrightarrow> (snd f) =True)))
                              else (f,fs) = the None \<or> fs=[] )"
  apply (case_tac "(fs_DN \<noteq> [])")
  prefer 2 
  apply (metis mapper_BMCU.simps mapper_BMCU_cur_clu.simps mapper_BMCU_cur_reach.simps member_rec(1) member_rec(2))
  apply simp
  apply (case_tac "snd fn")
  apply (simp add:member_def set_ConsD)
  using mapper_BMCU_cur_reach_emit_lemma apply blast
  by (simp add: member_rec(2))

(***************************shuffer***************************)

definition shuffer_BMCU :: "((fnode\<times>fnode list) list) list \<Rightarrow>(fnode\<times>(fnode list) list) list "
  where"shuffer_BMCU ffss \<equiv> Shuffle_single_inputlistlist ffss "

theorem shuffer_BMCU_theorem : "List.member (shuffer_BMCU xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  by (simp add: Shuffle_single_inputlistlist_theorem shuffer_BMCU_def)

(***************************reducer***************************)

primrec Merge :: "'a list \<Rightarrow>'a list \<Rightarrow>'a list" 
  where "Merge [] as = as"|
        "Merge (as#as1) as2 = (if (distinct (as#as2)) then (Merge as1 (as#as2)) else (Merge as1 as2))"

primrec Merge_list :: "'a list list \<Rightarrow>'a list" 
  where "Merge_list [] = []"|
        "Merge_list (as#ass) = Merge as (Merge_list ass)"

fun reducer_BMCU :: "(fnode\<times>(fnode list) list) \<Rightarrow> (fnode\<times>fnode list)" 
  where "reducer_BMCU (fn,fnss) =(fn,Merge_list fnss)"

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
lemma Merge_list_distinct:"distinct (Merge_list fns)"
  apply (induct fns)
  apply simp+
  by (simp add: Merge_distinct)
lemma Merge_list_set:"set(concat fns) = set(Merge_list fns)"
  apply (induct fns)
  apply simp+
  apply (rule Merge_set)
  by (simp add:Merge_list_distinct)
theorem reducer_BMCU_distinct:"distinct (snd (reducer_BMCU (fn,fnss)))"
  by (simp add :Merge_list_distinct)
theorem reducer_BMCU_set:"set(concat fnss) = set (snd (reducer_BMCU (fn,fnss)))"
  apply (simp only :Merge_list_set)
  by auto

(***************************iteration***************************)

fun iteration_BMCU :: "(fnode\<times>fnode list) list \<Rightarrow> (fnode\<times>fnode list) list" 
  where "iteration_BMCU fs = (let res = (MapReduce_BMCU fs mapper_BMCU shuffer_BMCU reducer_BMCU)
         in (if (res=fs) then fs else (MapReduce_BMCU res mapper_BMCU shuffer_BMCU reducer_BMCU)))"


(***************************result***************************)
definition "result_bm = MapReduce result_E3 mapper_BMCU shuffer_BMCU reducer_BMCU"
value "result_bm"
definition result_BMCU :: "(fnode\<times>fnode list) list"
  where "result_BMCU \<equiv> iteration_BMCU result_E3"
value result_BMCU
end