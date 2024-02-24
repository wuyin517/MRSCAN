theory MapReduceLocal
  imports Main
begin


locale MReduce = 
  fixes mapping  ::"'a \<Rightarrow> ('k * 'v)list "
  fixes shuffling::" (('k \<times>'v) list list \<Rightarrow> ('k \<times> ('v list)) list)"
  fixes reduce   ::"(('k \<times> ('v list)) \<Rightarrow> ('k \<times> 'v))"
(****
  assumes mapping_cor: "mapping"
***)
  assumes shuffling_cor:"List.member (shuffling xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "

begin


definition Mapreduce:: "'a list \<Rightarrow>('k \<times> 'v)list" where
  "Mapreduce s = map reduce(shuffling (map mapping s ))"

(***
definition Mapreduces::"'a list \<Rightarrow> 'a list \<Rightarrow>('k \<times> 'v)list" where
  "Mapreduces s t= map reduce( (shuffling (map mapping s)) @ (shuffling (map mapping t)))"
***)
end

definition MapReduce :: 
  "'a list \<Rightarrow> \<comment> \<open> input \<close>
    ('a \<Rightarrow> ('k1 \<times>'v1) list) \<Rightarrow>  \<comment> \<open> Map \<close>
    (('k1 \<times>'v1) list list \<Rightarrow> ('k2 \<times> ('v2 list)) list) \<Rightarrow>  \<comment> \<open> Shuffle \<close>
    (('k2 \<times> ('v2 list)) \<Rightarrow> ('k3 \<times> 'v3)) \<Rightarrow>  \<comment> \<open> Reduce \<close>
    ('k3 \<times> 'v3) list"  \<comment> \<open> output \<close>
  where "MapReduce input Map Shuffle Reduce \<equiv> map Reduce (Shuffle (map Map input))"






end
