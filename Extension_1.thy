theory Extension_1
  imports Main SGraph HOL.Real core
begin

definition MapReduce_E1 :: 
  "(node\<times>iscore) list \<Rightarrow>(edge\<times>real) list \<Rightarrow>
    ((node\<times>iscore) \<Rightarrow> (node\<times>iscore)) \<Rightarrow> ((edge\<times>real) \<Rightarrow> edge option) \<Rightarrow>
    ((node\<times>iscore) list \<Rightarrow> edge option list \<Rightarrow>(node\<times>(iscore\<times>(node list))) list) \<Rightarrow>
    ((node\<times>(iscore\<times>(node list))) \<Rightarrow> (edge\<times>(node\<times>iscore)) list) \<Rightarrow>
    (edge\<times>(node\<times>iscore)) list list"
  where "MapReduce_E1 input1 input2 Map1 Map2 Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map1 input1) (map Map2 input2))"

(***************************mapper***************************)

definition "mapper_E1_iscore \<equiv> BNF_Composition.id_bnf"
fun mapper_E1_filter :: "(edge\<times>real) \<Rightarrow> edge option" 
  where "mapper_E1_filter (e,sim) =(if (sim\<ge>\<epsilon>) then Some e else None)"

(***************************shuffer***************************)
primrec getNs :: "(('k \<times>'k) option)list\<Rightarrow> 'k \<Rightarrow>'k list" 
  where "getNs [] n = []"| 
        "getNs (e#es) n =(if (e=None) then getNs es n 
                          else(if (fst (the e) = n) then (snd (the e))#getNs es n 
                               else (if (snd (the e) = n) then (fst (the e))#getNs es n else getNs es n)))"

lemma getNs_set:" n \<in> set (a # as) \<Longrightarrow> n \<notin> set as \<Longrightarrow> n=a"
  by auto
theorem getNs_member:"List.member ( getNs es nn ) n \<Longrightarrow> List.member es ( Some (nn,n) ) \<or> List.member es (Some (n,nn))"
  apply (induct es)
  apply (simp add:member_def)+
  apply auto
  apply (split if_splits)
  apply simp
  apply (split if_splits)
  apply (case_tac "n \<in> set (getNs es nn)")
  apply simp
  using getNs_set prod.collapse apply auto[1]
  apply (split if_splits)
  apply (case_tac "n \<in> set (getNs es nn)")
  apply simp
  using getNs_set prod.collapse apply auto[1]
  by auto

primrec shuffler_E1 :: "(node\<times>iscore) list \<Rightarrow> (edge option)list \<Rightarrow> (node\<times>(iscore\<times>(node list))) list"
  where "shuffler_E1 [] es=[]"| 
        "shuffler_E1 (nc#ncs) es=(fst nc,(snd nc,getNs es (fst nc)))#shuffler_E1 ncs es"

theorem shuffler_E1_theorem:"map_of (shuffler_E1 ncs es) e = (if (map_of ncs e \<noteq> None) 
        then Some (the (map_of ncs e), getNs es e) else None)"
  apply (induct ncs)
   apply simp+
  done

(***************************reducer***************************)
fun reducer_E1 :: "(node\<times>(iscore\<times>(node list))) \<Rightarrow> (edge\<times>(node\<times>iscore)) list" 
  where "reducer_E1 (n,b,[]) =[]"|
        "reducer_E1 (n,b,(nn#nns)) =(form_edge n nn,(n,b))# (reducer_E1 (n,b,nns))"

theorem reducer_E1_size:"size nns = size (reducer_E1 (n,b,nns))"
  apply (induct nns)
  by auto

theorem reducer_E1_member:"List.member nns nn \<Longrightarrow> List.member (reducer_E1 (n,b,nns)) ((form_edge n nn,(n,b)))"
  apply (induct nns)
   apply (simp add:member_def)+
  by auto

(***************************result***************************)
definition result_E1 :: "(edge\<times>(node\<times>iscore)) list" 
  where "result_E1 \<equiv> concat (MapReduce_E1 result_Core result_Similarity 
                     mapper_E1_iscore mapper_E1_filter shuffler_E1 reducer_E1)"

value result_E1
end