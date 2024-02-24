theory Inclusion_Removal
  imports Main SGraph "HOL-Library.Multiset"
begin

definition MapReduce_IR :: 
  "('a\<times>'b list) list \<Rightarrow>
    (('a\<times>'b list) \<Rightarrow> ('b list\<times>'a)) \<Rightarrow>
    (('b list\<times>'a) list \<Rightarrow> ('b list\<times>'a) list) \<Rightarrow>
    (('b list\<times> 'a ) \<Rightarrow> ('a \<times> 'b list)) \<Rightarrow>
    ('a \<times> 'b list) list"
  where "MapReduce_IR input m s r \<equiv> map r (s (map m input))"

fun mapper_IR :: "('a\<times>'b list) \<Rightarrow> ('b list\<times>'a)" where
"mapper_IR (a,b) = (b,a)"
lemma "fst (mapper_IR ab) = snd ab \<and> snd (mapper_IR ab) = fst ab"
  by (metis mapper_IR.simps snd_swap surjective_pairing swap_simp)

primrec no_inclusion_a_list :: "'a list \<Rightarrow> 'a list list \<Rightarrow> bool" where
"no_inclusion_a_list a [] = True"|
"no_inclusion_a_list a (x#xs) = (if ((set(a) \<subseteq> set(x)) \<or> ((set(x) \<subseteq> set(a)))) then False else no_inclusion_a_list a xs)"

lemma "no_inclusion_a_list a xs \<Longrightarrow> List.member xs x \<Longrightarrow>  \<not>((set(a) \<subseteq> set(x)) \<or> ((set(x) \<subseteq> set(a)))) "
  apply (simp add:List.member_def)
  apply (induct xs)
   apply simp+
  apply auto
   apply (case_tac "set a \<subseteq> set aa \<or> set aa \<subseteq> set a")
    apply auto
  apply (case_tac "set a \<subseteq> set aa \<or> set aa \<subseteq> set a")
   apply auto
  done

primrec no_inclusion_list :: "'a list list \<Rightarrow> bool" where
"no_inclusion_list [] = True"|
"no_inclusion_list (x#xs) = ((no_inclusion_a_list x xs) \<and> (no_inclusion_list xs))"

lemma " x \<in> set xs \<Longrightarrow> \<not>no_inclusion_a_list x xs"
   apply (induct xs)
   apply simp+
  by auto

lemma help1:" x \<in> set xs  \<Longrightarrow> set x \<subseteq> set a  \<Longrightarrow> \<not>no_inclusion_a_list a xs"
   apply (induct xs)
   apply simp+
  by auto
lemma help2:" x \<in> set xs  \<Longrightarrow> set a \<subseteq> set x \<Longrightarrow> \<not>no_inclusion_a_list a xs"
   apply (induct xs)
   apply simp+
  by auto


lemma "no_inclusion_list xs \<Longrightarrow> List.member xs x \<Longrightarrow> no_inclusion_a_list x (remove1 x xs)"
  apply (simp add:List.member_def)
  apply (induct xs)
   apply simp
  apply (case_tac "x=a")
   apply simp+
  apply auto
   apply (drule help1)
    apply auto
  apply (drule help2)
  apply auto
  done

primrec shuffer_IR_1 :: "('b list\<times>'a)  \<Rightarrow> ('b list\<times>'a) list \<Rightarrow> ('b list\<times>'a) list" where
"shuffer_IR_1 ba [] = [ba] "|
"shuffer_IR_1 ba (x#xs) = (if set(fst ba) \<subseteq> set(fst x) then (x#xs)
             else (if set(fst x) \<subseteq> set(fst ba) then shuffer_IR_1 ba xs
             else x # (shuffer_IR_1 ba xs)))"

primrec less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where 
"less_list [] bs = True"|
"less_list (a#as) bs = (if (List.member bs a) then (less_list as (remove1 a bs)) else False)"

primrec shuffer_IR_2 :: "('b list\<times>'a) list \<Rightarrow> ('b list\<times>'a) list \<Rightarrow> ('b list\<times>'a) list" where
"shuffer_IR_2 [] xs = xs" |
"shuffer_IR_2 (ba # bas) xs = shuffer_IR_2 bas (shuffer_IR_1 ba xs)"

definition "shuffer_IR bas \<equiv> shuffer_IR_2 bas []"

fun reducer_IR :: "('b list\<times> 'a) \<Rightarrow> ('a \<times> 'b list)" where
"reducer_IR (b,a) = (a,b)"

definition Inclusion_Removal :: 
  "('a\<times>'b list) list \<Rightarrow> ('a\<times>'b list) list"
  where "Inclusion_Removal input \<equiv> map reducer_IR (shuffer_IR (map mapper_IR input))"
definition Inclusion_Removal' :: 
  "('a\<times>'b list) list \<Rightarrow> ('a\<times>'b list) list"
  where "Inclusion_Removal' input \<equiv> MapReduce_IR input mapper_IR shuffer_IR reducer_IR"

end