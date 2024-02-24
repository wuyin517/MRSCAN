theory Duplicate_Removal
  imports Main 
begin

definition MapReduce_DR :: 
  "'a list \<Rightarrow>
    ('a \<Rightarrow> ('k1 \<times>'v1)) \<Rightarrow>
    (('k1 \<times>'v1) list  \<Rightarrow> ('k2 \<times> ('v2 list)) list) \<Rightarrow>
    (('k2 \<times> ('v2 list)) \<Rightarrow> ('k3 \<times> 'v3)) \<Rightarrow>
    ('k3 \<times> 'v3) list"
  where "MapReduce_DR input m s r \<equiv> map r (s (map m input))"

fun mapper_DR :: "('a\<times>'b) \<Rightarrow> ('b\<times>'a)" where
"mapper_DR (a,b) = (b,a)"
lemma "fst (mapper_DR ab) = snd ab \<and> snd (mapper_DR ab) = fst ab"
  by (metis mapper_DR.simps snd_swap surjective_pairing swap_simp)
  
primrec shuffer_DR_1 :: "('b\<times>'a)  \<Rightarrow> ('b\<times> ('a list)) list \<Rightarrow> ('b\<times> ('a list)) list" where
"shuffer_DR_1 ba [] = [(fst ba,[snd ba])] "|
"shuffer_DR_1 ba (x#xs) = (if fst ba = fst x then (fst x, (snd ba) # (snd x))#xs 
             else x # (shuffer_DR_1 ba xs))"

lemma shuffer_DR_1_None:"map_of xs (fst ff) = None \<Longrightarrow> 
set (shuffer_DR_1 ff xs) = insert (fst ff,[snd ff]) (set (shuffer_DR_1 ff xs))"
  apply (induct xs)
   apply simp+
  by auto
lemma shuffer_DR_1_Some:"map_of xs (fst ff) = Some s \<Longrightarrow> set (shuffer_DR_1 ff xs) = 
insert (fst ff,(snd ff)#s) (set (remove1 (fst ff,s) xs))"
  apply (induct xs)
   apply simp+
  by auto

primrec shuffer_DR_2 :: "('b\<times>'a) list \<Rightarrow> ('b\<times> ('a list)) list \<Rightarrow> ('b\<times> ('a list)) list" where
"shuffer_DR_2 [] xs = xs" |
"shuffer_DR_2 (ba # bas) xs = shuffer_DR_2 bas (shuffer_DR_1 ba xs)"

definition "shuffer_DR bas \<equiv> shuffer_DR_2 bas []"

fun reducer_DR :: "('b\<times> ('a list)) \<Rightarrow> ('a \<times> 'b)" where
"reducer_DR (b,as) = (hd as,b)"

value " mapper_DR ((3::nat),(4::nat))"
value "(map mapper_DR [((3::nat),(4::nat)),((3::nat),(4::nat)),((3::nat),(5::nat))])"
value "MapReduce_DR [((3::nat),[(3::nat),4,5,6,7]),
(3,[3,4,5,6,7]),(3,[3,4,5,6,7]),(2,[8,9,2])] 
mapper_DR shuffer_DR reducer_DR"

definition Duplicate_Removal :: 
  "('a\<times>'b) list \<Rightarrow> ('a\<times>'b) list"
  where "Duplicate_Removal input \<equiv> map reducer_DR (shuffer_DR (map mapper_DR input))"
value "Duplicate_Removal [((3::nat),[(3::nat),4,5,6,7]),
(3,[3,4,5,6,7]),(3,[3,4,5,6,7]),(2,[8,9,2])]"

end