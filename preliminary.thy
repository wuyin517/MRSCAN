theory preliminary
imports Main SGraph Shuffle MapReduceLocal
begin

definition graph_edge0 :: "(nat\<times>edge) list" where
"graph_edge0 \<equiv> [(1,(1,2)),(2,(2,7)),(3,(3,4)),(4,(3,7)),
(5,(4,6)),(6,(4,7)),(7,(5,6)),(8,(5,7)),(9,(6,7))]"

definition graph_edge :: "(nat\<times>edge) list" where
"graph_edge \<equiv> [(1,(1,2)),(2,(2,5)),(3,(3,5)),(4,(3,4)),
(5,(4,5))]"


(*value definition*)
definition \<epsilon> :: "real" where
"\<epsilon> \<equiv> 0.49"
definition \<mu> :: "nat" where
"\<mu> \<equiv> 2"





end