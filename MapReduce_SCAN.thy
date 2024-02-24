theory MapReduce_SCAN
  imports Main SGraph Base_Min_Core_Union
begin



(*Similarity calculation*)
definition result_Similarity :: "(edge\<times>real) list" 
  where "result_Similarity\<equiv>MapReduce result_EwDs mapper_Similarity shuffler_Similarity reducer_Similarity"

(*Core node judgment*)
definition result_Core :: "(node \<times> iscore) list" 
  where "result_Core \<equiv>  MapReduce re_Similarity mapper_Core shuffler_Core reducer_Core"

(*Figure dimension extension*)
definition result_E1 :: "(edge\<times>(node\<times>iscore)) list" 
  where "result_E1 \<equiv> concat (MapReduce_E1 result_Core result_Similarity 
                     mapper_E1_iscore mapper_E1_filter shuffler_E1 reducer_E1)"
definition result_E2 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list" 
  where "result_E2 \<equiv> concat (MapReduce_E2 result_E1 mapper_E2 shuffler_E2 reducer_E2)"
definition result_E3 :: "((nat\<times>iscore)\<times>(nat\<times>iscore)list)list" 
  where "result_E3 \<equiv> MapReduce_E3 result_E2 mapper_E3 shuffler_E3 reducer_E3"

(*Base Min_Core Union*)
