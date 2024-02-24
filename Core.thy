theory Core
  imports Main HOL.Real Complex_Main SGraph Similarity
begin

(***************************mapper***************************)
fun mapper_Core :: "(edge\<times>similarity) \<Rightarrow> (node\<times>node\<times>similarity) list" 
  where "mapper_Core ((u,v),sim) = [(u,(v,sim)),(v,(u,sim))]"

value "map mapper_Core re_Similarity"
(***************************shuffer***************************)
definition shuffler_Core :: "((node\<times>node\<times>similarity) list) list \<Rightarrow>(node\<times>(node\<times>similarity) list) list"
  where "shuffler_Core xs \<equiv> Shuffle_single_inputnumlistlist xs"

value "shuffler_Core (map mapper_Core re_Similarity)"
(***************************reducer***************************)  
primrec count :: "(node\<times>similarity) list  \<Rightarrow>nat" 
  where "count []  = 0"|
        "count (a#as)  = (if (snd a\<ge>\<epsilon>) then Suc (count as) else count as)"

fun iscore :: "(node\<times>real) list \<Rightarrow>bool" 
  where "iscore as = (if (count as  \<ge> \<mu>) then True else False)"

fun reducer_Core :: "(node\<times>(node\<times>real) list)\<Rightarrow>(node\<times>iscore) " 
  where "reducer_Core (k,vlist) = (k, iscore vlist)"

definition "result_Core \<equiv> MapReduce result_Similarity mapper_Core shuffler_Core reducer_Core"

value result_Core

primrec counts :: "(node\<times>similarity) list  \<Rightarrow>node list" 
  where "counts []  = []"|
        "counts (a#as)  = (if (snd a\<ge>\<epsilon>) then ((fst a)#counts as)  else counts as)"

fun reducer_counts :: "(node\<times>(node\<times>real) list)\<Rightarrow>(node\<times> node list) " 
  where "reducer_counts (k,vlist) = (k, sort(counts vlist))"

definition "result_counts \<equiv> MapReduce result_Similarity mapper_Core shuffler_Core reducer_counts"

value result_counts


end