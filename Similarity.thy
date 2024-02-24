theory Similarity
  imports Complex_Main HOL.Real  SGraph HOL.NthRoot preliminary Enumerating_Triangles
begin

fun mapper_similarity::"(edge\<times>nat\<times>nat) \<Rightarrow> (edge \<times> nat ) list \<Rightarrow> (edge \<times> nat \<times> nat \<times> nat) list" where
"mapper_similarity (e,d1,d2) f = (case (map_of f) e of None \<Rightarrow> [(e,0,0,0)]| Some t \<Rightarrow> [(e,d1,d2,t)])"

fun mapper_Similarity :: "(edge\<times>nat\<times>nat) \<Rightarrow> (edge\<times>nat\<times>nat\<times>nat) list" where 
"mapper_Similarity x = mapper_similarity x result_EoT"

definition shuffler_Similarity :: "(edge \<times> nat \<times> nat \<times> nat) list list\<Rightarrow>(edge\<times>(nat \<times> nat \<times> nat) list) list"
  where "shuffler_Similarity nes \<equiv>  Shuffle_single_inputlistlist nes"

fun reducer_Similarity :: "(edge\<times>(nat\<times>nat\<times>nat) list)\<Rightarrow> (edge\<times>real)" 
  where "reducer_Similarity (e,[(d1,d2,t)]) = (e,(t+2)*((t+2)) / ((d1+1)*(d2+1)))"

definition "result_Similarity \<equiv>
                 MapReduce result_EwDs mapper_Similarity shuffler_Similarity reducer_Similarity"

thm result_Similarity_def
value result_Similarity

value result_EoT

end