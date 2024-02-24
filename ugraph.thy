theory ugraph
imports
   Complex_Main HOL.Real HOL.NthRoot 
begin
subsection \<open>Nodes and Edges\<close>  

typedef 'v ugraph 
  = "{ (V::'v set , E). E \<subseteq> V\<times>V \<and> finite V \<and> sym E \<and> irrefl E }"
  unfolding sym_def irrefl_def by blast

setup_lifting type_definition_ugraph

lift_definition nodes_internal :: "'v ugraph \<Rightarrow> 'v set" is fst .
lift_definition edges_internal :: "'v ugraph \<Rightarrow> ('v\<times>'v) set" is snd .
lift_definition graph_internal :: "'v set \<Rightarrow> ('v\<times>'v) set \<Rightarrow> 'v ugraph" 
  is "\<lambda>V E. if finite V \<and> finite E then (V\<union>fst`E\<union>snd`E, (E\<union>E\<inverse>)-Id) else ({},{})"
  by (auto simp: sym_def irrefl_def; force)     

definition nodes :: "'v ugraph \<Rightarrow> 'v set" 
  where "nodes = nodes_internal" 
definition edges :: "'v ugraph \<Rightarrow> ('v\<times>'v) set" 
  where "edges = edges_internal" 
definition graph :: "'v set \<Rightarrow> ('v\<times>'v) set \<Rightarrow> 'v ugraph" 
  where "graph = graph_internal" 

definition degree :: "'v ugraph \<Rightarrow> 'v \<Rightarrow> nat" where
  "degree G v = card {(v, y). (v, y) \<in> edges G}"

lemma edges_subset: "edges g \<subseteq> nodes g \<times> nodes g"
  unfolding edges_def nodes_def by transfer auto

lemma nodes_finite[simp, intro!]: "finite (nodes g)"
  unfolding edges_def nodes_def by transfer auto
  
lemma edges_sym: "sym (edges g)"    
  unfolding edges_def nodes_def by transfer auto

lemma edges_irrefl: "irrefl (edges g)"      
  unfolding edges_def nodes_def by transfer auto

lemma nodes_graph: "\<lbrakk>finite V; finite E\<rbrakk> \<Longrightarrow> nodes (graph V E) = V\<union>fst`E\<union>snd`E"    
  unfolding edges_def nodes_def graph_def by transfer auto
  
lemma edges_graph: "\<lbrakk>finite V; finite E\<rbrakk> \<Longrightarrow> edges (graph V E) = (E\<union>E\<inverse>)-Id"    
  unfolding edges_def nodes_def graph_def by transfer auto

lemmas graph_accs = nodes_graph edges_graph  
  
lemma nodes_edges_graph_presentation: "\<lbrakk>finite V; finite E\<rbrakk> 
    \<Longrightarrow> nodes (graph V E) = V \<union> fst`E \<union> snd`E \<and> edges (graph V E) = E\<union>E\<inverse> - Id"
  by (simp add: graph_accs)
      
lemma graph_eq[simp]: "graph (nodes g) (edges g) = g"  
  unfolding edges_def nodes_def graph_def
  apply transfer
  unfolding sym_def irrefl_def
  apply (clarsimp split: prod.splits)
  by (fastforce simp: finite_subset)

lemma edges_finite[simp, intro!]: "finite (edges g)"
  using edges_subset finite_subset by fastforce
  
lemma graph_cases[cases type]: obtains V E 
  where "g = graph V E" "finite V" "finite E" "E\<subseteq>V\<times>V" "sym E" "irrefl E"  
proof -
  show ?thesis
    apply (rule that[of "nodes g" "edges g"]) 
    using edges_subset edges_sym edges_irrefl[of g]
    by auto
qed     

lemma graph_eq_iff: "g=g' \<longleftrightarrow> nodes g = nodes g' \<and> edges g = edges g'"  
  unfolding edges_def nodes_def graph_def by transfer auto

lemma edges_sym': "(u,v)\<in>edges g \<Longrightarrow> (v,u)\<in>edges g" using edges_sym 
  by (blast intro: symD)
  
lemma edges_irrefl'[simp,intro!]: "(u,u)\<notin>edges g"
  by (meson edges_irrefl irrefl_def)
  
lemma edges_irreflI[simp, intro]: "(u,v)\<in>edges g \<Longrightarrow> u\<noteq>v" by auto 
  
lemma edgesT_diff_sng_inv_eq[simp]: 
  "(edges T - {(x, y), (y, x)})\<inverse> = edges T - {(x, y), (y, x)}"
  using edges_sym' by fast
  
lemma nodesI[simp,intro]: assumes "(u,v)\<in>edges g" shows "u\<in>nodes g" "v\<in>nodes g"
  using assms edges_subset by auto
  



definition neighbors :: "'v ugraph \<Rightarrow> 'v \<Rightarrow> 'v set" 
 where "neighbors G v = {u. (v, u) \<in> edges G}\<union>{v}"

definition sim ::"'v ugraph \<Rightarrow> 'v \<Rightarrow>'v \<Rightarrow> real" where
    "sim G v u =(card((neighbors G v)\<inter>(neighbors G u))) 
        /sqrt(card(neighbors G v)*card (neighbors G u))"

definition sneighbors :: "'v ugraph \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'v set" 
 where "sneighbors G v \<epsilon>= {u\<in> neighbors G v. sim G u v\<ge>\<epsilon>}"

definition iscore::"'v ugraph \<Rightarrow> 'v \<Rightarrow>real \<Rightarrow> nat\<Rightarrow> bool" where
"iscore G v \<epsilon> \<mu>\<equiv> card (sneighbors G v \<epsilon>)\<ge>\<mu>"

definition dirreach::"'v ugraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow>real \<Rightarrow> nat\<Rightarrow> bool" 
where "dirreach G v w \<epsilon> \<mu> \<equiv> iscore G v \<epsilon> \<mu>  \<and> w\<in>sneighbors G v \<epsilon>"

fun Reach where
  "Reach G v [] w \<epsilon> \<mu> \<longleftrightarrow> v=w"  
| "Reach G v (e#ps) w \<epsilon> \<mu> \<longleftrightarrow> (\<exists>u. e=(v,u)\<and> dirreach G v u \<epsilon> \<mu> \<and> Reach G v ps w \<epsilon> \<mu>)"  

definition "Conenect G v w \<epsilon> \<mu>\<equiv> \<exists>u\<in>nodes G. \<exists>p\<^sub>1 p\<^sub>2. Reach G u p\<^sub>1 v \<epsilon> \<mu> \<and> Reach G u p\<^sub>2 w \<epsilon> \<mu>"

definition "Cluster G \<epsilon> \<mu> C \<equiv>
   C\<subseteq>nodes G \<and> (\<forall>v\<in>C. \<forall>w\<in>C.  Conenect G v w \<epsilon> \<mu>)
  \<and>(\<forall>v\<in>nodes G. \<forall>w\<in>nodes G. \<exists>p. v\<in>C \<and> Reach G v p w \<epsilon> \<mu> \<longrightarrow> w\<in>C)"

end

