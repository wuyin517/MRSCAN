theory Edges_with_Degrees
  imports Complex_Main  MapReduceLocal preliminary
begin


fun mapper_EwD :: "(nat\<times>edge) \<Rightarrow> edge list" where 
"mapper_EwD (n,e) = [e,((snd e), (fst e))]"

definition shuffler_EwD :: "(edge list) list \<Rightarrow>(node\<times>nat list) list"
  where "shuffler_EwD nes \<equiv>  Shuffle_single_inputnumlistlist nes"

value "(map mapper_EwD graph_edge)"
value "shuffler_EwD(map mapper_EwD graph_edge)"

fun reducer_EwD :: "node\<times>nat list \<Rightarrow> node\<times>nat"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
  where "reducer_EwD (k,vlist) = (k, size vlist)" 

fun reducer_EwDset :: "node\<times>nat list \<Rightarrow> node\<times>nat set"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
  where "reducer_EwDset (k,vlist) = (k, set vlist)" 


(* degree of node*)
definition "result_Ewd \<equiv> MapReduce graph_edge mapper_EwD shuffler_EwD reducer_EwD"

(* Neighbor node of node*)
definition "result_Ewdset \<equiv> MapReduce graph_edge mapper_EwD shuffler_EwD reducer_EwDset"

value result_Ewd
value "MapReduce graph_edge mapper_EwD shuffler_EwD reducer_EwDset"
value "map reducer_EwDset (shuffler_EwD(map mapper_EwD graph_edge))"


fun mapper_EwDs'::"(nat \<times> edge) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (edge \<times>nat\<times>nat) "where
"mapper_EwDs' (n,(n1,n2)) f = (let ff = (map_of f) in (form_edge n1 n2,the (ff n1), the (ff n2)) )"

fun mapper_EwDs :: "(nat\<times>edge) \<Rightarrow> (edge \<times>nat\<times>nat) " where
"mapper_EwDs e = mapper_EwDs' e result_Ewd"

value " map mapper_EwDs graph_edge "

(* degree of edge*)
definition "result_EwDs \<equiv> map mapper_EwDs graph_edge"
value result_EwDs



theorem shuffler_EwD_theorem : "List.member (shuffler_EwD xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) " 
  by (simp add: Shuffle_single_inputnumlistlist_theorem shuffler_EwD_def)






(*****
definition MapReduce_EwD :: 
  "(nat\<times>edge) list \<Rightarrow>
    ((nat\<times>edge) \<Rightarrow> (node\<times>edge) list) \<Rightarrow>
    ((node\<times>edge) list list \<Rightarrow> (node\<times>edge list) list) \<Rightarrow>
    ((node\<times>edge list) \<Rightarrow> (edge\<times>degree\<times>degree) list) \<Rightarrow>
    (edge\<times>degree\<times>degree) list list"
  where "MapReduce_EwD input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

fun mapper_EwD :: "(nat\<times>edge) \<Rightarrow> (node\<times>edge) list" where 
"mapper_EwD (n,e) = [(fst e,form_edge (fst e) (snd e)),(snd e,form_edge (fst e) (snd e))]"

value "mapper_EwD (1,(5,3))"
definition shuffler_EwD :: "((node\<times>edge) list) list \<Rightarrow>(node\<times>edge list) list"
  where "shuffler_EwD nes \<equiv>  Shuffle_single_inputlistlist nes"

theorem shuffler_EwD_theorem : "List.member (shuffler_EwD xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  by (simp add: Shuffle_single_inputlistlist_theorem shuffler_EwD_def)

fun reducer_EwD_emit :: "node\<times>edge list \<Rightarrow>degree \<Rightarrow>(edge\<times>degree\<times>degree) list"
  where "reducer_EwD_emit (n,[]) d = []" |
        "reducer_EwD_emit (n,e#es) d = (if (n=fst e) then (e,d,0) else (e,0,d))#reducer_EwD_emit (n,es) d"

fun reducer_EwD :: "node\<times>edge list \<Rightarrow>(edge\<times>degree\<times>degree) list"                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
  where "reducer_EwD n_es = reducer_EwD_emit n_es (size(snd n_es))" 

lemma reducer_EwD_emit_degree: "(e, d1, d2) \<in> set (reducer_EwD_emit (n, es) d) \<Longrightarrow> (if (n = fst e) then d1 = d \<and> d2 = 0 else d1 = 0 \<and> d2 = d)"
  apply (induct es)
  apply simp+
  apply (case_tac "n = fst a")
  apply simp+
  by auto

theorem reducer_EwD_theorem:"List.member (reducer_EwD (n,es)) (e,d1,d2) \<Longrightarrow> (if (fst e = n) then d1 = size es \<and> d2 = 0 else d1 = 0 \<and> d2 = size es)"
  apply (simp add:member_def)
  apply (induct es)
  apply simp+
  apply (case_tac "n = fst a")
  apply auto
  by (drule reducer_EwD_emit_degree,simp)+



definition result_EwD :: "(edge\<times>degree\<times>degree) list" where
"result_EwD \<equiv> concat(MapReduce_EwD graph_edge mapper_EwD shuffler_EwD reducer_EwD)"
value "(MapReduce_EwD graph_edge mapper_EwD shuffler_EwD reducer_EwD)"

term "MReduce mapper_EwD shuffler_EwD reducer_EwD"

interpretation Mre:MReduce
  where mapping = mapper_EwD and shuffling = shuffler_EwD and reduce = reducer_EwD 
proof (standard, goal_cases) oops
value "shuffler_EwD (map mapper_EwD graph_edge)"

definition MapReduce_EwDs :: 
  "(edge\<times>degree\<times>degree) list \<Rightarrow>
    ((edge\<times>degree\<times>degree) \<Rightarrow> (edge\<times>degree\<times>degree)) \<Rightarrow>
    ((edge\<times>degree\<times>degree) list  \<Rightarrow> (edge\<times>(degree\<times>degree) list) list) \<Rightarrow>
    ((edge\<times>(degree\<times>degree) list) \<Rightarrow> (edge\<times>degree\<times>degree)) \<Rightarrow>
    (edge\<times>degree\<times>degree) list "
  where "MapReduce_EwDs input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"

definition "mapper_EwDs \<equiv> BNF_Composition.id_bnf"

definition shuffler_EwDs :: "(edge\<times>degree\<times>degree) list \<Rightarrow>(edge\<times>(degree\<times>degree) list) list "
  where "shuffler_EwDs eds \<equiv> Shuffle_single_inputalist eds"

theorem shuffler_EwDs_theorem : "List.me
mber (shuffler_EwDs xs) (k,vs) \<Longrightarrow> (List.member xs (k,v)) = (List.member vs v) "
  by (metis Shuffle_single_inputalist_theorem shuffler_EwDs_def)

fun reducer_EwDs :: "edge\<times>(degree\<times>degree) list \<Rightarrow> (edge\<times>degree\<times>degree)"
  where "reducer_EwDs (e,d#ds) =(let de=hd(ds) in (if (fst d=0) then (e,fst de,snd d) else (e,fst d,snd de)))" 


definition result_EwDs :: "(edge\<times>degree\<times>degree) list" where
"result_EwDs \<equiv> MapReduce_EwDs result_EwD mapper_EwDs shuffler_EwDs reducer_EwDs"

value result_EwDs
****)

end
