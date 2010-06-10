(*  Author:     Tobias Nipkow
*)

header {* Comparing Enumeration and Archive *}

theory ArchCompAux
imports TameEnum TrieList Arch
begin

function qsort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "qsort le []       = []"
  | "qsort le (x#xs) = qsort le [y\<leftarrow>xs . ~ le x y] @ [x] @
		       qsort le [y\<leftarrow>xs . le x y]"
by pat_completeness auto
termination by (relation "measure (size o snd)")
  (auto simp add: length_filter_le [THEN le_less_trans])

definition nof_vertices :: "'a fgraph \<Rightarrow> nat" where
  "nof_vertices = length o remdups o concat"

definition fgraph :: "graph \<Rightarrow> nat fgraph" where
  "fgraph g = map vertices (faces g)"

definition hash :: "nat fgraph \<Rightarrow> nat list" where
  "hash fs = (let n = nof_vertices fs in
     [n, size fs] @
     qsort (%x y. y < x) (map (%i. foldl (op +) 0 (map size [f\<leftarrow>fs. i mem f]))
                             [0..<n]))"

primrec enum_finals :: "(graph \<Rightarrow> graph list) \<Rightarrow> nat \<Rightarrow> graph list \<Rightarrow> nat fgraph list
                 \<Rightarrow> nat fgraph list option" where
  "enum_finals succs 0 todo fins = None"
  | "enum_finals succs (Suc n) todo fins =
     (if todo = [] then Some fins
      else let g = hd todo; todo' = tl todo in
        if final g then enum_finals succs n todo' (fgraph g # fins)
        else enum_finals succs n (succs g @ todo') fins)"

definition tameEnum :: "nat \<Rightarrow> nat \<Rightarrow> nat fgraph list option" where
  "tameEnum p n = enum_finals (next_tame p) n [Seed p] []"

definition diff2 :: "nat fgraph list \<Rightarrow> nat fgraph list \<Rightarrow>
           (nat * nat fgraph) list * (nat * nat fgraph)list" where
  "diff2 fgs ags =
   (let xfgs = map (%fs. (nof_vertices fs, fs)) fgs;
       xags = map (%fs. (nof_vertices fs, fs)) ags in
   (filter (%xfg. ~list_ex (iso_test xfg) xags) xfgs,
    filter (%xag. ~list_ex (iso_test xag) xfgs) xags))"

definition same :: "nat fgraph list option \<Rightarrow> nat fgraph list \<Rightarrow> bool" where
  "same fgso ags = (case fgso of None \<Rightarrow> False | Some fgs \<Rightarrow>
   let niso_test = (%fs1 fs2. iso_test (nof_vertices fs1,fs1)
                                       (nof_vertices fs2,fs2));
       tfgs = trie_of_list hash fgs;
       tags = trie_of_list hash ags in
   (list_all (%fg. list_ex (niso_test fg) (lookup_trie tags (hash fg))) fgs &
    list_all (%ag. list_ex (niso_test ag) (lookup_trie tfgs (hash ag))) ags))"

definition pre_iso_test :: "vertex fgraph \<Rightarrow> bool" where
  "pre_iso_test Fs \<longleftrightarrow>
   [] \<notin> set Fs \<and> (\<forall>F\<in>set Fs. distinct F) \<and> distinct (map rotate_min Fs)"

end
