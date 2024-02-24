theory Enumerating_Triangles
  imports Main SGraph Edges_with_Degrees Shuffle
begin

(*enumerate open triads*)
fun mapper_EoT' ::"edge \<Rightarrow> (nat \<times> nat set) list \<Rightarrow> (edge\<times>nat set)list" where
"mapper_EoT' (n1,n2) f = (let ff = (map_of f) in [(form_edge n1 n2,the (ff n1) \<inter> the (ff n2))])"

fun mapper_EoT :: "(nat\<times>edge) \<Rightarrow> (edge\<times>nat set)list " where 
"mapper_EoT (n,e) = mapper_EoT' e result_Ewdset"

definition shuffler_EoT :: "(edge\<times>nat set)list list \<Rightarrow>(edge\<times>(nat set)list) list"
  where "shuffler_EoT nes \<equiv>  Shuffle_single_inputlistlist nes"

value "(map mapper_EwD graph_edge)"
value "shuffler_EoT(map mapper_EoT graph_edge)"

fun reducer_EoT :: "edge\<times>(nat set)list \<Rightarrow> (edge \<times> nat)"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
  where "reducer_EoT (k,vlist) = (k, card (hd vlist))" 

value "MapReduce graph_edge mapper_EoT shuffler_EoT reducer_EoT"

fun reducer_EoTset :: "edge\<times>(nat set)list \<Rightarrow> (edge \<times> nat set)"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       
  where "reducer_EoTset (k,vlist) = (k, hd vlist)" 


(* Trianles of edge*)
definition "result_EoT \<equiv> MapReduce graph_edge mapper_EoT shuffler_EoT reducer_EoT"
(* Common Neighbor Node of edge*)
definition "result_EoTset \<equiv> MapReduce graph_edge mapper_EoT shuffler_EoT reducer_EoTset"
value result_EoT

end