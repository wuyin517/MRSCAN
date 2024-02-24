theory Extension
  imports Main SGraph HOL.Real core
begin

definition \<epsilon> :: "real" where
"\<epsilon> \<equiv> 0.7"
(***************************one***************************)
definition MapReduce1 :: 
  "'a list \<Rightarrow>'b list \<Rightarrow>
    ('a \<Rightarrow> ('k1 \<times>'v11)) \<Rightarrow> ('b \<Rightarrow> ('k1 \<times>'v12)) \<Rightarrow>
    (('k1 \<times>'v11) list \<Rightarrow> ('k1 \<times>'v12) list \<Rightarrow>('k2 \<times> ('v11 \<times>'v12 list)) list) \<Rightarrow>
    (('k2 \<times> ('v11 \<times>'v12 list)) \<Rightarrow> ('k3 \<times> 'v2) list) \<Rightarrow>
    ('k3 \<times> 'v2) list list"
  where "MapReduce1 input1 input2 m1 m2 s r \<equiv> map r (s (map m1 input1) (map m2 input2))"

datatype valu = bl bool|nd node

fun mapper1_1 :: "(node\<times>iscore) \<Rightarrow> (node\<times>iscore)" where
"mapper1_1 (u,isc) = (u,isc)"

fun mapper1_2 :: "(edge\<times>real) \<Rightarrow> edge" where
"mapper1_2 ((u,v),sim) =(if (sim\<ge>\<epsilon>) then (u,v) else (0,0))"

fun getN :: "edge \<Rightarrow> node \<Rightarrow>node option" where
"getN (u,v) w =(if (u=w) then Some v else (if (v=w) then Some u else None))"

primrec getNs :: "edge list\<Rightarrow> node \<Rightarrow>node list" where
"getNs [] w = []"|
"getNs (e#es) w =(if (getN e w =None) then getNs es w 
                  else (the (getN e w))#(getNs es w))"
value "getNs [(1::nat,2::nat),(1,3)] 1"

value "map_of [(1::nat,2::nat),(1,3)] 1"

primrec shuffer1 :: "(node\<times>iscore) list \<Rightarrow> edge list \<Rightarrow> (node\<times>(iscore\<times>(node list))) list" where
"shuffer1 [] es=[]"|
"shuffer1 (nb#nbs) es=(fst nb,(snd nb,getNs es (fst nb)))#shuffer1 nbs es"

fun getE :: "node \<Rightarrow>node \<Rightarrow>edge" where
"getE  u v =(if (u<v) then (u,v) else (v,u))"

fun reducer1 :: "(node\<times>(iscore\<times>(node list))) \<Rightarrow> (edge\<times>(node\<times>iscore)) list" where
"reducer1 (n,b,[]) =[]"|
"reducer1 (n,b,(nn#nns)) =(getE n nn,(n,b))# (reducer1 (n,b,nns))"

definition input1_1 :: "(node\<times>iscore) list" where "input1_1\<equiv>n_iscore"
definition input1_2 :: "(edge\<times>real) list" where "input1_2\<equiv>similarities"
value "map mapper1_1 input1_1"
value "map mapper1_2 input1_2"
value "shuffer1 (map mapper1_1 input1_1) (map mapper1_2 input1_2)"
value "map reducer1 (shuffer1 (map mapper1_1 input1_1) (map mapper1_2 input1_2))"
value "MapReduce1 input1_1 input1_2 mapper1_1 mapper1_2 shuffer1 reducer1"
definition result1 :: "(edge\<times>(node\<times>iscore)) list list" where
"result1 \<equiv> MapReduce1 input1_1 input1_2 mapper1_1 mapper1_2 shuffer1 reducer1"

(***************************two***************************)
definition MapReduce2 :: 
  "'a list \<Rightarrow>
    ('a \<Rightarrow> ('k1 \<times>'v1) list) \<Rightarrow>
    (('k1 \<times>'v1) list list \<Rightarrow> ('k2 \<times> ('v2 list)) list) \<Rightarrow>
    (('k2 \<times> ('v2 list)) \<Rightarrow> ('k3 \<times> 'v2) list) \<Rightarrow>
    ('k3 \<times> 'v2) list list"
  where "MapReduce2 input m s r \<equiv> map r (s (map m input))"

fun mapper2 :: "(edge\<times>(node\<times>iscore)) list \<Rightarrow> (edge\<times>(node\<times>iscore)) list" where
"mapper2 enbs =enbs"

(*primrec merge :: "'a list list \<Rightarrow> 'a list" where
"merge [] =[]"|
"merge (a#as) = a @ (merge as)"

primrec split :: "(edge\<times>(node\<times>iscore)) list \<Rightarrow> (edge\<times>(node\<times>iscore) list) list" where
"split [] =[]"|
"split (enb#enbs) = (fst enb,assoc (enb#enbs) (fst enb)) # split enbs"*)

primrec shuffer2_1 :: "(edge\<times>(node\<times>iscore)) \<Rightarrow>(edge\<times>(node\<times>iscore) list) list 
                                           \<Rightarrow>(edge\<times>(node\<times>iscore) list) list "
  where "shuffer2_1 enb []=[(fst enb,[snd enb])]"|
        "shuffer2_1 enb (x#xs)=(if fst enb = fst x then (fst x, (snd enb) # (snd x))#xs 
             else x # (shuffer2_1 enb xs))"
primrec shuffer2_2 :: "(edge\<times>(node\<times>iscore)) list \<Rightarrow>(edge\<times>(node\<times>iscore) list) list 
                                                \<Rightarrow>(edge\<times>(node\<times>iscore) list) list "
  where "shuffer2_2 [] enbs = enbs" |
        "shuffer2_2 (x # xs) enbs = shuffer2_2 xs (shuffer2_1 x enbs)"

primrec shuffer2_3 :: "(edge\<times>(node\<times>iscore)) list list \<Rightarrow>(edge\<times>(node\<times>iscore) list) list 
                                                \<Rightarrow>(edge\<times>(node\<times>iscore) list) list "
  where "shuffer2_3 [] enbs = enbs" |
        "shuffer2_3 (x # xs) enbs = shuffer2_3 xs (shuffer2_2 x enbs)"

definition "shuffer2 enbss \<equiv> shuffer2_3 enbss []"

fun reducer2_1 :: "(node\<times>iscore) list \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore)) list" where
"reducer2_1 nbs =(hd nbs,hd (tl nbs))#[(hd (tl nbs),hd nbs)]"
(*"reducer2_1 (nb1#nb2#nbs) = [(nb1,nb2)]"|
"reducer2_1 _=[]"*)

fun reducer2 :: "(edge\<times>(node\<times>iscore) list) \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore)) list" where
"reducer2 (e,nbs) =reducer2_1 nbs"

value "map mapper2 result1"
value "shuffer2 (map mapper2 result1)"
value "reducer2_1 ( [(4, True), (3, False)])"
value "reducer2 (((1::nat), (2::nat)), [((2::nat), False), (1, False)])"
value "map reducer2 (shuffer2 (map mapper2 result1))"
value "MapReduce2 result1 mapper2 shuffer2 reducer2"
definition result2 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list list" where
"result2 \<equiv> MapReduce2 result1 mapper2 shuffer2 reducer2"

(***************************three***************************)

definition MapReduce3 :: 
  "'a list \<Rightarrow>
    ('a \<Rightarrow> ('k1 \<times>'v1) list) \<Rightarrow>
    (('k1 \<times>'v1) list list \<Rightarrow> ('k2 \<times> ('v2 list)) list) \<Rightarrow>
    (('k2 \<times> ('v2 list)) \<Rightarrow> ('k3 \<times> 'v3)) \<Rightarrow>
    ('k3 \<times> 'v3) list"
  where "MapReduce3 input m s r \<equiv> map r (s (map m input))"

fun mapper3 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list \<Rightarrow> ((node\<times>iscore)\<times>(node\<times>iscore)) list" where
"mapper3 nis =nis"

primrec shuffer3_1 :: "((node\<times>iscore)\<times>(node\<times>iscore)) \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list 
                                           \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list "
  where "shuffer3_1 ni []=[(fst ni,[snd ni])]"|
        "shuffer3_1 ni (x#xs)=(if fst ni = fst x then (fst x, (snd ni) # (snd x))#xs 
             else x # (shuffer3_1 ni xs))"
primrec shuffer3_2 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list 
                                                \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list "
  where "shuffer3_2 [] nis = nis" |
        "shuffer3_2 (x # xs) nis = shuffer3_2 xs (shuffer3_1 x nis)"

primrec shuffer3_3 :: "((node\<times>iscore)\<times>(node\<times>iscore)) list list \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list 
                                                \<Rightarrow>((node\<times>iscore)\<times>(node\<times>iscore) list) list "
  where "shuffer3_3 [] niss = niss" |
        "shuffer3_3 (x # xs) niss = shuffer3_3 xs (shuffer3_2 x niss)"

definition "shuffer3 niss \<equiv> shuffer3_3 niss []"

fun reducer3 :: "(node\<times>iscore)\<times>(node\<times>iscore) list \<Rightarrow> (node\<times>iscore)\<times>(node\<times>iscore) list"
  where "reducer3 nis=nis"
value "map mapper3 result2"
value "shuffer3 (map mapper3 result2)"
value "map reducer3 (shuffer3 (map mapper3 result2))"
value "MapReduce3 result2 mapper3 shuffer3 reducer3"
definition result3 :: "((nat\<times>iscore)\<times>(nat\<times>iscore)list)list" where
"result3 \<equiv> MapReduce3 result2 mapper3 shuffer3 reducer3"

end


