theory SGraph_update
  imports Main HOL.Real SGraph
begin

primrec nexts_iscore :: "[graph, node] \<Rightarrow> (node \<times> iscore) list \<Rightarrow> fnode list"where
  "nexts_iscore [] n iscore_list = []"| 
  "nexts_iscore (e#es) n iscore_list = 
  (if fst e = n then (snd e,the (map_of iscore_list (snd e))) # nexts_iscore es n iscore_list else 
   if snd e = n then (fst e,the (map_of iscore_list (fst e))) # nexts_iscore es n iscore_list else 
   nexts_iscore es n iscore_list)"

fun neighbors_iscore :: "[graph, fnode] \<Rightarrow> (node \<times> iscore) list \<Rightarrow> ( fnode list)"where
  "neighbors_iscore g fn iscore_list = (fn# (nexts_iscore g (fst fn) iscore_list))"

end