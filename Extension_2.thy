theory Extension_2
  imports Main SGraph HOL.Real Extension_1
begin

definition MapReduce_E2 :: 
  "(edge\<times>(node\<times>iscore)) list \<Rightarrow>
    ((edge\<times>(node\<times>iscore)) \<Rightarrow> (edge\<times>(node\<times>iscore))) \<Rightarrow>
    ((edge\<times>(node\<times>iscore)) list \<Rightarrow> (edge\<times>(node\<times>iscore) list) list) \<Rightarrow>
    ((edge\<times>(node\<times>iscore) list) \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore)) list) \<Rightarrow>
    ((node\<times>iscore)\<times>(node\<times>iscore)) list list"
  where "MapReduce_E2 input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

(***************************mapper***************************)
definition "mapper_E2 \<equiv> BNF_Composition.id_bnf"

(***************************shuffler***************************)
definition shuffler_E2 :: "(edge\<times>(node\<times>iscore)) list \<Rightarrow>(edge\<times>(node\<times>iscore) list) list"
  where "shuffler_E2 encss \<equiv> Shuffle_single_inputalist encss"

theorem shuffler_E2_theorem : "List.member (shuffler_E2 xs) (k,vs) \<Longrightarrow> (List.member xs (k,v)) = (List.member vs v) "
  by (metis Shuffle_single_inputalist_theorem shuffler_E2_def)

(***************************reducer***************************)
fun double :: "(node\<times>iscore) list \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore)) list" 
  where "double ncs =(hd ncs,hd (tl ncs))#[(hd (tl ncs),hd ncs)]"

fun reducer_E2 :: "(edge\<times>(node\<times>iscore) list) \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore)) list" 
  where "reducer_E2 (e,ncs) =double ncs"

(***************************result***************************)
definition result_E2 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list" 
  where "result_E2 \<equiv> concat (MapReduce_E2 result_E1 mapper_E2 shuffler_E2 reducer_E2)"

value result_E2
end