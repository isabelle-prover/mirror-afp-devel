(*  Author:     Tobias Nipkow
*)

header {* Checking Final Quadrilaterals *}

theory Plane4
imports While_Combinator Tame
begin

definition norm_subset :: "vertex list list \<Rightarrow> vertex list list \<Rightarrow> bool" where
"norm_subset xs ys \<equiv> let zs = map rotate_min ys
                     in \<forall>x \<in> set xs. rotate_min x \<in> set zs"

primrec remrevdups :: "'a list list \<Rightarrow> 'a list list" where
  "remrevdups [] = []"
| "remrevdups (xs#xss) = (if xs mem xss \<or> rev xs mem xss then remrevdups xss
                        else xs # remrevdups xss)"

definition find_cycles1 :: "nat \<Rightarrow> graph \<Rightarrow> vertex \<Rightarrow> vertex list list" where
"find_cycles1 n g v \<equiv>
 snd(snd(
 while (%(vs,wss,res). vs \<noteq> [])
 (%(vs,wss,res).
   let ws = hd wss in
   if ws = [] then (tl vs, tl wss, res)
   else if length vs = n
        then (tl vs, tl wss, if last vs \<in> set ws then vs#res else res)
        else let vs' = (if length vs + 1 = n then butlast vs else vs);
                 xs = filter (%x. x \<notin> set vs') (neighbors g (hd ws)) in
             (hd ws # vs, xs # tl ws # tl wss, res))
 ([v], [neighbors g v], [])
 ))"

definition  find_cycles :: "nat \<Rightarrow> graph \<Rightarrow> vertex list list" where
"find_cycles n g \<equiv>
 remrevdups(map rotate_min (foldr (%v vss. find_cycles1 n g v @ vss) (vertices g) []))"

definition
(* Not needed but could be used to get rid of makeTrianglesFinal
 ok3 :: "graph \<Rightarrow> vertex list \<Rightarrow> bool"
"ok3 g vs  \<equiv>
 let f = [hd vs, hd(tl vs), hd(tl(tl vs))];
     nf = rotate_min f; nrf = rotate_min(rev f)
 in \<exists>f' \<in> set(map (rotate_min o vertices) (faces g)). f' = nf \<or> f' = nrf"

 is_tame\<^isub>2 :: "graph \<Rightarrow> bool"
"is_tame\<^isub>2 g \<equiv> \<forall>vs \<in> set(find_cycles 3 g).
   distinct vs \<and> |vs| = 3 \<and> is_cycle g vs \<longrightarrow> ok3 g vs"
*)

 ok42 :: "vertex list \<Rightarrow> vertex list list \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool" where
"ok42 vs fs a b c d ==
  norm_subset (tameConf\<^isub>1 a b c d) fs \<or>
  norm_subset (tameConf\<^isub>2 a b c d) fs \<or>
  norm_subset (tameConf\<^isub>2 b c d a) fs \<or>
  (EX e:set vs. e \<notin> set[a,b,c,d] \<and>
       (norm_subset (tameConf\<^isub>3 a b c d e) fs \<or>
        norm_subset (tameConf\<^isub>3 b c d a e) fs \<or>
        norm_subset (tameConf\<^isub>3 c d a b e) fs \<or>
        norm_subset (tameConf\<^isub>3 d a b c e) fs \<or>
        norm_subset (tameConf\<^isub>4 a b c d e) fs)
  )"

definition ok4 :: "graph \<Rightarrow> vertex list \<Rightarrow> bool" where
"ok4 g vs  \<equiv>
 let fs = map vertices (faces g); gvs = vertices g;
     a = hd vs; b = hd(tl vs); c = hd(tl(tl vs)); d = hd(tl(tl(tl vs)))
 in ok42 gvs fs a b c d \<or> ok42 gvs fs d c b a"

definition is_tame\<^isub>3 :: "graph \<Rightarrow> bool" where
"is_tame\<^isub>3 g \<equiv> \<forall>vs \<in> set(find_cycles 4 g).
   is_cycle g vs \<and> distinct vs \<and> |vs| = 4 \<longrightarrow> ok4 g vs"

end
