theory Shuffle
  imports Main SGraph
begin

(*************************shuffler_1**************************)

(*primrec Shuffle_single_one :: "('a\<times>'b) \<Rightarrow>('a\<times>'b list) list \<Rightarrow>('a\<times>'b list) list"
  where "Shuffle_single_one nn []=[(fst nn,[snd nn])]"|
        "Shuffle_single_one nn (x#xs)=(if fst nn = fst x then xs @ [(fst x, (snd nn) # (snd x))]
                                      else x # (Shuffle_single_one nn xs))" *)
primrec Shuffle_single_one :: "('k\<times>'v) \<Rightarrow>('k\<times>'v list) list \<Rightarrow>('k\<times>'v list) list"
  where "Shuffle_single_one x []=[(fst x,[snd x])]"|
        "Shuffle_single_one x (l#list)=(if fst x = fst l then (fst l, (snd x) # (snd l))#list 
                                      else l # (Shuffle_single_one x list))"

primrec Shuffle_single_list :: "('k\<times>'v) list \<Rightarrow>('k\<times>'v list) list \<Rightarrow>('k\<times>'v list) list"
  where "Shuffle_single_list [] list = list" |
        "Shuffle_single_list (x # xs) list = Shuffle_single_list xs (Shuffle_single_one x list)"

primrec Shuffle_single_llist :: "(('k\<times>'v) list) list \<Rightarrow>('k\<times>'v list) list \<Rightarrow>('k\<times>'v list) list"
  where "Shuffle_single_llist [] list = list" |
        "Shuffle_single_llist (xs # xss) list = Shuffle_single_llist xss (Shuffle_single_list xs list)"


definition "Shuffle_single_inputlistlist xxs \<equiv> Shuffle_single_llist xxs []"

lemma fst_lemma:" k \<noteq> fst a \<Longrightarrow> (k, vs) \<noteq> a "
  by auto

lemma Shuffle_single_one_list_right:"(k, vs) \<in> set list \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists> vs'' .((k, vs'') \<in> set (Shuffle_single_one a list) \<and> v \<in> set vs'' ) "
  apply (induct list )
  apply simp+
  by auto

lemma Shuffle_single_one_list_left:" (k, vs'') \<in> set (Shuffle_single_one a list) \<and> v \<in> set vs'' \<Longrightarrow> (\<exists> vs .(k, vs) \<in> set list \<and> v \<in> set vs) \<or> (k,v) = a "
  apply (induct list)
  apply auto
  apply (case_tac "fst a = aa")
  by auto

lemma Shuffle_single_list_list_right:"(k, vs) \<in> set list \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists> vs' .((k, vs') \<in> set (Shuffle_single_list xs list) \<and> v \<in> set vs')  "
  apply (induct xs arbitrary: list vs )
   apply auto
  apply (drule Shuffle_single_one_list_right)
  by auto

lemma Shuffle_single_list_list_left:" (k, vs') \<in> set (Shuffle_single_list xs list) \<and> v \<in> set vs' \<Longrightarrow> (\<exists> vs .(k, vs) \<in> set list \<and> v \<in> set vs) \<or> (k,v) \<in> set xs "
  apply (induct xs arbitrary: list vs' )
  apply auto[1]
  apply (simp only: Shuffle_single_list.simps)
  apply (subgoal_tac "(\<exists>vs. (k, vs) \<in> set (Shuffle_single_one a list) \<and> v \<in> set vs) \<or> (k, v) \<in> set xs")
   apply (erule disjE)
apply (erule exE) 
    apply (drule Shuffle_single_one_list_left)
  by auto

lemma Shuffle_single_one_aORlist: "aa \<notin>  set (map fst list) \<Longrightarrow> (aa, b) \<in> set (Shuffle_single_one a list) \<Longrightarrow> fst a = aa "
  apply (induct list)
   apply simp
  by (smt (verit, best) Shuffle_single_one.simps(2) fst_lemma image_iff list.set_intros(1) list.set_intros(2) list.set_map set_ConsD)

lemma Shuffle_single_one_distinct: "distinct (map fst list) \<Longrightarrow> distinct (map fst (Shuffle_single_one a list)) "
  apply (induct list)
   apply simp
  apply (simp only: Shuffle_single_one.simps)
  apply (case_tac " fst a = fst aa ")
  apply auto
  by (metis Shuffle_single_one_aORlist list.set_map)

lemma Shuffle_single_list_distinct: "distinct (map fst list) \<Longrightarrow> distinct (map fst (Shuffle_single_list a list)) "
  apply (induct a arbitrary: list)
  apply simp+
  by (simp add: Shuffle_single_one_distinct)

lemma Shuffle_single_one_kv:"(k, v) = a \<Longrightarrow> \<exists> vs . (k, vs) \<in> set (Shuffle_single_one a list) \<and> v \<in> set vs"
  apply (induct list)
   apply simp
  by auto

lemma Shuffle_single_list_kv:"(k, v) \<in> set xs \<Longrightarrow> \<exists> vs . (k, vs) \<in> set (Shuffle_single_list xs list) \<and> v \<in> set vs"
  apply (induct xs arbitrary: list)
   apply simp
  by (metis Shuffle_single_list.simps(2) Shuffle_single_list_list_right Shuffle_single_one_kv set_ConsD)

lemma Shuffle_single_llist_lemma_right:"distinct (map fst list) \<Longrightarrow> (k,vs_1) \<in> set(Shuffle_single_llist xss list)
        \<Longrightarrow> ((k,vs) \<in> set list \<and> v \<in> set vs ) \<or> ( xs \<noteq> [] \<and> xs \<in> set xss \<and> (k,v) \<in> set xs ) \<Longrightarrow>  v \<in> set vs_1 "
     apply (induct xss arbitrary: list vs)
  apply (metis Shuffle_single_llist.simps(1) eq_key_imp_eq_value in_set_member member_rec(2))
  apply (erule disjE)
   apply (erule conjE)
  apply (simp only: Shuffle_single_llist.simps)
    apply (drule_tac vs="vs" in Shuffle_single_list_list_right)
  apply simp
    apply (erule exE)
  apply (drule Shuffle_single_list_distinct)
   apply auto[1]
   apply (erule conjE)+
  apply (simp only: Shuffle_single_llist.simps)
  apply (drule Shuffle_single_list_distinct)
   apply auto[1]
  by (meson Shuffle_single_list_kv)

lemma Shuffle_single_llist_lemma_left:"distinct (map fst list) \<Longrightarrow> (k,vs_1) \<in> set(Shuffle_single_llist xss list)
        \<Longrightarrow>  v \<in> set vs_1 \<Longrightarrow> (\<exists> vs . (k,vs) \<in> set list \<and> v \<in> set vs ) \<or> (\<exists> xs . xs \<noteq> [] \<and> xs \<in> set xss \<and> (k,v) \<in> set xs ) "
  apply (induct xss arbitrary: list)
  apply (metis Shuffle_single_llist.simps(1))
  apply (simp only: Shuffle_single_llist.simps)
  apply (drule Shuffle_single_list_distinct)
  apply (subgoal_tac "(\<exists>vs. (k, vs) \<in> set ((Shuffle_single_list a list)) \<and> v \<in> set vs) \<or> (\<exists>xs. xs \<noteq> [] \<and> xs \<in> set xss \<and> (k, v) \<in> set xs)")
  apply (metis Shuffle_single_list_list_left in_set_member list.set_intros(1) list.set_intros(2) member_rec(2))
  by auto

lemma Shuffle_single_inputlistlist_lemma_right:" (k,vs) \<in> set (Shuffle_single_inputlistlist xss) 
        \<Longrightarrow> xs \<in> set xss \<Longrightarrow> (k,v) \<in> set xs \<Longrightarrow> v \<in> set vs "
  apply (induct xss)
  apply (simp add:Shuffle_single_inputlistlist_def)+
  by (metis Shuffle_single_list_distinct Shuffle_single_list_kv Shuffle_single_llist_lemma_right distinct.simps(1) in_set_member list.simps(8) member_rec(2))

lemma Shuffle_single_inputlistlist_lemma_left:" (k,vs) \<in> set (Shuffle_single_inputlistlist xss) \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists>xs. xs \<in> set xss \<and> (k, v) \<in> set xs "
  apply (induct xss)
   apply (simp add:Shuffle_single_inputlistlist_def)+
  apply (subgoal_tac "distinct (map fst (Shuffle_single_list a []))")
  apply (metis Shuffle_single_llist.simps(2) Shuffle_single_llist_lemma_left distinct.simps(1) list.distinct(1) list.map_disc_iff list.set_cases set_ConsD)
  by (simp add: Shuffle_single_list_distinct)

theorem Shuffle_single_inputlistlist_theorem: "List.member (Shuffle_single_inputlistlist xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  apply (auto simp: member_def)
  apply (metis Shuffle_single_inputlistlist_lemma_right)
  by (metis Shuffle_single_inputlistlist_lemma_left)






definition "Shuffle_single_inputalist xs \<equiv> Shuffle_single_list xs []"

lemma Shuffle_single_list_lemma_right:"distinct (map fst list) \<Longrightarrow> (k,vs_1) \<in> set(Shuffle_single_list xs list)
        \<Longrightarrow> ((k,vs) \<in> set list \<and> v \<in> set vs ) \<or> ((k,v) \<in> set xs) \<Longrightarrow>  v \<in> set vs_1 "
  apply (induct xs arbitrary: list vs)
  apply (metis Shuffle_single_list.simps(1) eq_key_imp_eq_value list.discI list.set_cases)
  by (metis (no_types, opaque_lifting) Shuffle_single_list.simps(2) Shuffle_single_list_distinct Shuffle_single_list_kv Shuffle_single_one_distinct Shuffle_single_one_list_right eq_key_imp_eq_value)

lemma Shuffle_single_inputalist_lemma_right:" (k,vs) \<in> set (Shuffle_single_inputalist xs) \<Longrightarrow> (k,v) \<in> set xs \<Longrightarrow> v \<in> set vs "
  apply (induct xs)      
  apply (simp add:Shuffle_single_inputalist_def)+
  apply (subgoal_tac "distinct (map fst [(fst a, [snd a])])")
  apply (metis Shuffle_single_list_lemma_right Shuffle_single_one.simps(1) Shuffle_single_one_kv)
  by force

lemma Shuffle_single_list_lemma_left:"distinct (map fst list) \<Longrightarrow> (k,vs_1) \<in> set(Shuffle_single_list xs list)
        \<Longrightarrow>  v \<in> set vs_1 \<Longrightarrow> ((k,vs) \<in> set list \<longrightarrow> v \<in> set vs ) \<or> ((k,v) \<in> set xs)"
  apply (induct xs arbitrary: list vs)
  apply (metis Shuffle_single_list.simps(1) eq_key_imp_eq_value)
  by (metis Shuffle_single_list_list_left eq_key_imp_eq_value)

lemma Shuffle_single_inputalist_lemma_left:"(k, vs) \<in> set (Shuffle_single_inputalist xs) \<Longrightarrow> v \<in> set vs \<Longrightarrow> (k, v) \<in> set xs"
  apply (induct xs)      
  apply (simp add:Shuffle_single_inputalist_def)+
  apply (subgoal_tac "distinct (map fst [(fst a, [snd a])])")
  apply (metis (no_types, opaque_lifting) Shuffle_single_list.simps(2) Shuffle_single_list_list_left Shuffle_single_one.simps(1) list.distinct(1) list.set_cases set_ConsD)
  by force

theorem Shuffle_single_inputalist_theorem: "List.member (Shuffle_single_inputalist xs) (k,vs) \<Longrightarrow> (List.member xs (k,v)) = (List.member vs v)"
  apply (auto simp: member_def)
  apply (simp add: Shuffle_single_inputalist_lemma_right)
  by (simp add: Shuffle_single_inputalist_lemma_left)

(*************************shuffler_2**************************)

fun getfsts :: "('k \<times>'v) list \<Rightarrow> 'k list"
  where "getfsts kvs = remdups (map fst kvs)"

primrec getSnds :: "('k \<times>'v) list \<Rightarrow> 'k \<Rightarrow>'v list "   
   where "getSnds [] k = []"|
         "getSnds (x# xs2) k =(if (fst x=k) then (snd x)#(getSnds xs2 k) else getSnds xs2 k)"

lemma getSnds_member: "List.member (getSnds xs k) v = List.member xs (k,v)"
  apply (induct xs)
  apply (simp add:member_def)+
  apply (case_tac "fst a=k")
  by auto

primrec Shuffle_multi_emit :: "'k list \<Rightarrow> ('k\<times>'v1) list \<Rightarrow> ('k\<times>'v2) list \<Rightarrow>('k\<times>'v1 list\<times>'v2 list) list"
   where " Shuffle_multi_emit [] xs1 xs2 = []"|
         " Shuffle_multi_emit (k# ks) xs1 xs2= (k,(getSnds xs1 k, getSnds xs2 k))# Shuffle_multi_emit ks xs1 xs2"

fun Shuffle_multi :: "('k\<times>'v1) list \<Rightarrow> ('k\<times>'v2) list \<Rightarrow>('k\<times>'v1 list\<times>'v2 list) list "
   where " Shuffle_multi xs1 xs2 = Shuffle_multi_emit (getfsts xs1) xs1 xs2"
value "Shuffle_multi ([(a\<^sub>1::nat, a\<^sub>2::nat), (a\<^sub>1, a\<^sub>1)]) ([]::(nat\<times>nat) list)"

lemma getfsts_member:"(getfsts (a # xs1)) = (if (List.member (getfsts xs1) (fst a)) then (getfsts xs1) else (fst a)#(getfsts xs1) )"
  by (simp add:member_def)

lemma Shuffle_multi_emit_ks:"(k, v1s, v2s) \<in> set(Shuffle_multi_emit (aa # ks)  xs1 xs2) \<Longrightarrow> 
(k, v1s, v2s) =(aa,getSnds xs1 aa,getSnds xs2 aa)\<or>(k, v1s, v2s) \<in> set(Shuffle_multi_emit  ks xs1 xs2)"
  by auto

lemma Shuffle_multi_emit_xs1:"List.member (Shuffle_multi_emit ks (a # xs1) xs2) (k, v1s, v2s) \<Longrightarrow>
(List.member (Shuffle_multi_emit ks xs1 xs2) (k, v1s, v2s) \<and> k \<noteq> fst a)\<or> 
(k, v1s, v2s) = (fst a,getSnds (a # xs1) (fst a),getSnds xs2 (fst a))"
  apply (induct ks)
    apply (simp add: member_def)
  apply (simp only:member_def getfsts_member)
  apply (drule Shuffle_multi_emit_ks)
  apply (erule disjE)
  by auto

lemma member_xs:" k \<noteq> fst a \<Longrightarrow> List.member xs (k, v) = List.member (a # xs) (k, v)"
  by (auto simp add: member_def)
lemma member_getSnds_lemma1:"List.member (getSnds xs k) v \<Longrightarrow> List.member xs (k, v)"
  apply (induct xs)
   apply (simp add: member_def)+
  apply (case_tac "fst a = k")
  by auto
lemma member_getSnds_lemma2:"List.member (a # xs) (k, v) \<Longrightarrow> List.member (getSnds xs k) v \<or> v = snd a"
  by (metis getSnds_member member_rec(1) sndI)

lemma member_getSnds:"List.member (snd a # getSnds xs1 (fst a)) v = List.member (a # xs1) (fst a, v)"
  apply auto
  apply (rule member_getSnds_lemma1)
  apply simp
  apply (drule member_getSnds_lemma2)
  by (metis member_rec(1))

theorem Shuffle_multi_theorem:"List.member (Shuffle_multi xs1 xs2) (k,v1s,v2s)
         \<Longrightarrow> List.member v1s v1 = List.member xs1 (k,v1) \<and> List.member v2s v2 = List.member xs2 (k,v2)"
  apply (rule conjI)
  apply (induct xs1)
    apply (simp add: member_def)
  apply (simp only:Shuffle_multi.simps)
   apply (simp only:getfsts_member)
   apply (case_tac "List.member (getfsts xs1) (fst a)")
  apply (simp del:getfsts.simps)
    apply (drule Shuffle_multi_emit_xs1)
    apply (erule disjE)
    apply (erule conjE)
     apply (simp del:getfsts.simps)
     apply (rule member_xs,simp)
    apply (simp add:member_getSnds)
  apply (simp del:getfsts.simps)
   apply (smt (verit, best) Shuffle_multi_emit_xs1 fst_conv getSnds.simps(2) getSnds_member snd_conv)
  apply (induct xs1)
   apply (simp add: member_def)
  apply (simp only:Shuffle_multi.simps)
   apply (simp only:getfsts_member)
   apply (case_tac "List.member (getfsts xs1) (fst a)")
  apply (simp del:getfsts.simps)
    apply (drule Shuffle_multi_emit_xs1)
    apply (erule disjE)
    apply (erule conjE)
     apply (simp del:getfsts.simps)
   apply (simp add: getSnds_member)+
  by (smt (verit, best) Shuffle_multi_emit_xs1 fst_conv getSnds_member member_rec(1) snd_conv)

primrec Shuffle_single_num_one :: "('a ::linorder\<times>'b) \<Rightarrow>('a\<times>'b list) list \<Rightarrow>('a\<times>'b list) list"
  where "Shuffle_single_num_one x []=[(fst x,[snd x])]"|
        "Shuffle_single_num_one x (l#list)=(if fst x = fst l then (fst l, (snd x) # (snd l))#list 
                                      else (if fst x > fst l then l # (Shuffle_single_num_one x list) 
                                            else (Shuffle_single_num_one x list)@[l]))"

primrec Shuffle_single_num_list :: "('a::linorder\<times>'b) list \<Rightarrow>('a\<times>'b list) list \<Rightarrow>('a\<times>'b list) list"
  where "Shuffle_single_num_list [] list = list" |
        "Shuffle_single_num_list (x # xs) list = Shuffle_single_num_list xs (Shuffle_single_num_one x list)"

primrec Shuffle_single_num_llist :: "(('a::linorder\<times>'b) list) list \<Rightarrow>('a\<times>'b list) list \<Rightarrow>('a\<times>'b list) list"
  where "Shuffle_single_num_llist [] list = list" |
        "Shuffle_single_num_llist (xs # xss) list = Shuffle_single_num_llist xss (Shuffle_single_num_list xs list)"



definition "Shuffle_single_inputnumlistlist xxs \<equiv> Shuffle_single_num_llist xxs []"



lemma Shuffle_single_num_one_list_right:"(k, vs) \<in> set list \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists> vs'' .((k, vs'') \<in> set (Shuffle_single_num_one a list) \<and> v \<in> set vs'' ) "
  apply (induct list )
  apply simp+
  by auto

lemma Shuffle_single_num_one_list_left:" (k, vs'') \<in> set (Shuffle_single_num_one a list) \<and> v \<in> set vs'' \<Longrightarrow> (\<exists> vs .(k, vs) \<in> set list \<and> v \<in> set vs) \<or> (k,v) = a "
  apply (induct list)
  apply auto
  apply (case_tac "fst a = aa") 
  apply auto[1] 
  by (smt (z3) old.prod.inject rotate1.simps(2) set_ConsD set_rotate1)

lemma Shuffle_single_num_list_list_right:"(k, vs) \<in> set list \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists> vs' .((k, vs') \<in> set (Shuffle_single_num_list xs list) \<and> v \<in> set vs')  "
  apply (induct xs arbitrary: list vs )
   apply auto
  apply (drule Shuffle_single_num_one_list_right)
  by auto

lemma Shuffle_single_num_list_list_left:" (k, vs') \<in> set (Shuffle_single_num_list xs list) \<and> v \<in> set vs' \<Longrightarrow> (\<exists> vs .(k, vs) \<in> set list \<and> v \<in> set vs) \<or> (k,v) \<in> set xs "
  apply (induct xs arbitrary: list vs')
  apply auto[1]
  apply (simp only: Shuffle_single_num_list.simps)
  apply (subgoal_tac "(\<exists>vs. (k, vs) \<in> set (Shuffle_single_num_one a list) \<and> v \<in> set vs) \<or> (k, v) \<in> set xs")
   apply (erule disjE)
apply (erule exE) 
    apply (drule Shuffle_single_num_one_list_left)
  by auto

lemma Shuffle_single_num_one_aORlist: "aa \<notin>  set (map fst list) \<Longrightarrow> (aa, b) \<in> set (Shuffle_single_num_one a list) \<Longrightarrow> fst a = aa "
  apply (induct list)
   apply simp 
  by (smt (verit) Shuffle_single_num_one.simps(2) fst_lemma in_set_conv_nth length_map list.set_intros(1) list.set_intros(2) list.simps(9) nth_map rotate1.simps(2) set_ConsD set_rotate1)

lemma Shuffle_single_num_one_distinct: "distinct (map fst list) \<Longrightarrow> distinct (map fst (Shuffle_single_num_one a list)) "
  apply (induct list)
   apply simp
  apply (simp only: Shuffle_single_num_one.simps)
  apply (case_tac " fst a = fst aa ")
  apply auto
  by (metis Shuffle_single_num_one_aORlist list.set_map)

lemma Shuffle_single_num_list_distinct: "distinct (map fst list) \<Longrightarrow> distinct (map fst (Shuffle_single_num_list a list)) "
  apply (induct a arbitrary: list)
  apply simp+ 
  by (simp add: Shuffle_single_num_one_distinct)


lemma Shuffle_single_num_one_kv:"(k, v) = a \<Longrightarrow> \<exists> vs . (k, vs) \<in> set (Shuffle_single_num_one a list) \<and> v \<in> set vs"
  apply (induct list)
   apply simp
  by auto

lemma Shuffle_single_num_list_kv:"(k, v) \<in> set xs \<Longrightarrow> \<exists> vs . (k, vs) \<in> set (Shuffle_single_num_list xs list) \<and> v \<in> set vs"
  apply (induct xs arbitrary: list)
   apply simp
  by (metis Shuffle_single_num_list.simps(2) Shuffle_single_num_list_list_right Shuffle_single_num_one_kv set_ConsD)

lemma Shuffle_single_num_llist_lemma_right:"distinct (map fst list) \<Longrightarrow> (k,vs_1) \<in> set(Shuffle_single_num_llist xss list)
        \<Longrightarrow> ((k,vs) \<in> set list \<and> v \<in> set vs ) \<or> ( xs \<noteq> [] \<and> xs \<in> set xss \<and> (k,v) \<in> set xs ) \<Longrightarrow>  v \<in> set vs_1 "
     apply (induct xss arbitrary: list vs)
  apply (metis Shuffle_single_num_llist.simps(1) eq_key_imp_eq_value in_set_member member_rec(2))
  apply (erule disjE)
   apply (erule conjE)
  apply (simp only: Shuffle_single_num_llist.simps)
    apply (drule_tac vs="vs" in Shuffle_single_num_list_list_right)
  apply simp
    apply (erule exE)
  apply (drule Shuffle_single_num_list_distinct)
   apply auto[1]
   apply (erule conjE)+
  apply (simp only: Shuffle_single_num_llist.simps)
  apply (drule Shuffle_single_num_list_distinct)
   apply auto[1] 
  by (meson Shuffle_single_num_list_kv)

lemma Shuffle_single_num_llist_lemma_left:"distinct (map fst list) \<Longrightarrow> (k,vs_1) \<in> set(Shuffle_single_num_llist xss list)
        \<Longrightarrow>  v \<in> set vs_1 \<Longrightarrow> (\<exists> vs . (k,vs) \<in> set list \<and> v \<in> set vs ) \<or> (\<exists> xs . xs \<noteq> [] \<and> xs \<in> set xss \<and> (k,v) \<in> set xs ) "
  apply (induct xss arbitrary: list)
  apply (metis Shuffle_single_num_llist.simps(1))
  apply (simp only: Shuffle_single_num_llist.simps)
  apply (drule Shuffle_single_num_list_distinct)
  apply (subgoal_tac "(\<exists>vs. (k, vs) \<in> set ((Shuffle_single_num_list a list)) \<and> v \<in> set vs) \<or> (\<exists>xs. xs \<noteq> [] \<and> xs \<in> set xss \<and> (k, v) \<in> set xs)")
  apply (metis Shuffle_single_num_list_list_left in_set_member list.set_intros(1) list.set_intros(2) member_rec(2))
  by auto

lemma Shuffle_single_inputnumlistlist_lemma_right:" (k,vs) \<in> set (Shuffle_single_inputnumlistlist xss) 
        \<Longrightarrow> xs \<in> set xss \<Longrightarrow> (k,v) \<in> set xs \<Longrightarrow> v \<in> set vs "
  apply (induct xss)
  apply (simp add:Shuffle_single_inputnumlistlist_def)+ 
  by (metis Shuffle_single_num_list_distinct Shuffle_single_num_list_kv Shuffle_single_num_llist_lemma_right distinct.simps(1) in_set_member list.simps(8) member_rec(2))

lemma Shuffle_single_inputnumlistlist_lemma_left:" (k,vs) \<in> set (Shuffle_single_inputnumlistlist xss) \<Longrightarrow> v \<in> set vs \<Longrightarrow> \<exists>xs. xs \<in> set xss \<and> (k, v) \<in> set xs "
  apply (induct xss)
   apply (simp add:Shuffle_single_inputnumlistlist_def)+
  apply (subgoal_tac "distinct (map fst (Shuffle_single_num_list a []))")
  apply (smt (z3) Shuffle_single_num_list_list_left Shuffle_single_num_llist_lemma_left empty_iff list.set(1))
  by (simp add: Shuffle_single_num_list_distinct)

theorem Shuffle_single_inputnumlistlist_theorem: "List.member (Shuffle_single_inputnumlistlist xss) (k,vs) \<Longrightarrow> (\<exists> xs . List.member xss xs \<and> List.member xs (k,v)) = (List.member vs v) "
  apply (auto simp: member_def)
  apply (metis Shuffle_single_inputnumlistlist_lemma_right)
  by (metis Shuffle_single_inputnumlistlist_lemma_left)



end