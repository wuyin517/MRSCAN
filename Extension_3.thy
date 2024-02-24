theory Extension_3
  imports Main SGraph HOL.Real Extension_2
begin
definition MapReduce_E3 :: 
  "((node\<times>iscore)\<times>(node\<times>iscore)) list \<Rightarrow>
    (((node\<times>iscore)\<times>(node\<times>iscore)) \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore))) \<Rightarrow>
    (((node\<times>iscore)\<times>(node\<times>iscore)) list \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore) list) list) \<Rightarrow>
    (((node\<times>iscore)\<times>(node\<times>iscore) list) \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore) list)) \<Rightarrow>
    ((node\<times>iscore)\<times>(node\<times>iscore) list) list"
  where "MapReduce_E3 input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

(***************************mapper***************************)
definition "mapper_E3 \<equiv> BNF_Composition.id_bnf"

(***************************shuffer***************************)

definition shuffler_E3 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list"
  where "shuffler_E3 niss \<equiv> Shuffle_single_inputalist niss"

theorem shuffler_E3_theorem : "List.member (shuffler_E3 xs) (k,vs) \<Longrightarrow> (List.member xs (k,v)) = (List.member vs v) "
  by (metis Shuffle_single_inputalist_theorem shuffler_E3_def)

(***************************reducer***************************)
definition "reducer_E3 \<equiv> BNF_Composition.id_bnf"

(***************************result***************************)

definition "result_E3 \<equiv> MapReduce_E3 result_E2 mapper_E3 shuffler_E3 reducer_E3"

value result_E3
end