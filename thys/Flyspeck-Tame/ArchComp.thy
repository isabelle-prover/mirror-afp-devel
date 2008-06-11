(*  ID:         $Id: ArchComp.thy,v 1.5 2008-06-11 14:22:50 lsf37 Exp $
    Author:     Tobias Nipkow
*)

header "Comparing Enumeration and Achive"

theory ArchComp
imports TameEnum TrieList Arch Efficient_Nat
begin

consts qsort :: "('a \<Rightarrow> 'a => bool) * 'a list \<Rightarrow> 'a list"
recdef qsort "measure (size o snd)"
    "qsort(le, [])   = []"
    "qsort(le, x#xs) = qsort(le, [y\<leftarrow>xs . ~ le x y]) @ [x] @
		       qsort(le, [y\<leftarrow>xs . le x y])"
(hints recdef_simp: length_filter_le[THEN le_less_trans])

constdefs
 nof_vertices :: "'a fgraph \<Rightarrow> nat"
"nof_vertices == length o remdups o concat"

 fgraph :: "graph \<Rightarrow> nat fgraph"
"fgraph g == map vertices (faces g)"

 hash :: "nat fgraph \<Rightarrow> nat list"
"hash fs == let n = nof_vertices fs in
   [n, size fs] @
   qsort (%x y. y < x, map (%i. foldl (op +) 0 (map size [f\<leftarrow>fs. i mem f]))
                           [0..<n])"

consts
 enum_finals :: "(graph \<Rightarrow> graph list) \<Rightarrow> nat \<Rightarrow> graph list \<Rightarrow> nat fgraph list
                 \<Rightarrow> nat fgraph list option"
primrec
"enum_finals succs 0 todo fins = None"
"enum_finals succs (Suc n) todo fins =
 (if todo = [] then Some fins
  else let g = hd todo; todo' = tl todo in
    if final g then enum_finals succs n todo' (fgraph g # fins)
    else enum_finals succs n (succs g @ todo') fins)"

constdefs
 tameEnum :: "nat \<Rightarrow> nat \<Rightarrow> nat fgraph list option"
"tameEnum p n == enum_finals (next_tame p) n [Seed p] []"

 diff2 :: "nat fgraph list \<Rightarrow> nat fgraph list \<Rightarrow>
           (nat * nat fgraph) list * (nat * nat fgraph)list"
"diff2 fgs ags ==
 let xfgs = map (%fs. (nof_vertices fs, fs)) fgs;
     xags = map (%fs. (nof_vertices fs, fs)) ags in
 (filter (%xfg. ~list_ex (iso_test xfg) xags) xfgs,
  filter (%xag. ~list_ex (iso_test xag) xfgs) xags)"

 same :: "nat fgraph list option \<Rightarrow> nat fgraph list \<Rightarrow> bool"
"same fgso ags == case fgso of None \<Rightarrow> False | Some fgs \<Rightarrow>
 let niso_test = (%fs1 fs2. iso_test (nof_vertices fs1,fs1)
                                     (nof_vertices fs2,fs2));
     tfgs = trie_of_list hash fgs;
     tags = trie_of_list hash ags in
 (list_all (%fg. list_ex (niso_test fg) (lookup_trie tags (hash fg))) fgs &
  list_all (%ag. list_ex (niso_test ag) (lookup_trie tfgs (hash ag))) ags)"

constdefs
 pre_iso_test :: "vertex fgraph \<Rightarrow> bool"
"pre_iso_test Fs \<equiv>
 [] \<notin> set Fs \<and> (\<forall>F\<in>set Fs. distinct F) \<and> distinct (map rotate_min Fs)"

lemma pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
by evaluation

lemma pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
by evaluation

lemma pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
by evaluation

lemma pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
by evaluation

lemma pre_iso_test7: "\<forall>g \<in> set Hept. pre_iso_test g"
by evaluation

lemma pre_iso_test8: "\<forall>g \<in> set Oct. pre_iso_test g"
by evaluation

ML "set Toplevel.timing"

lemma same3: "same (tameEnum 0 800000) Tri"
by evaluation

lemma same4: "same (tameEnum 1 8000000) Quad"
by evaluation

lemma same5: "same (tameEnum 2 20000000) Pent"
by evaluation

lemma same6: "same (tameEnum 3 4000000) Hex"
by evaluation

lemma same7: "same (tameEnum 4 1000000) Hept"
by evaluation

lemma same8: "same (tameEnum 5 2000000) Oct"
by evaluation

ML "reset Toplevel.timing"

end
