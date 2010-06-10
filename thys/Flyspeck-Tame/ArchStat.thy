(*  Author:     Tobias Nipkow
*)

theory ArchStat
imports TameEnum TrieList Arch
begin

function qsort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "qsort le []       = []"
  | "qsort le (x#xs) = qsort le [y\<leftarrow>xs . ~ le x y] @ [x] @
		       qsort le [y\<leftarrow>xs . le x y]"
by pat_completeness auto
termination by (relation "measure (size o snd)")
  (auto simp add: length_filter_le [THEN le_less_trans])

definition fgraph :: "graph \<Rightarrow> nat fgraph" where
"fgraph g = map vertices (faces g)"

definition nof_vertices :: "'a fgraph \<Rightarrow> nat" where
"nof_vertices = length o remdups o concat"

definition hash :: "nat fgraph \<Rightarrow> nat list" where
"hash fs = (let n = nof_vertices fs in
   [n, size fs] @
   qsort (%x y. y < x) (map (%i. foldl (op +) 0 (map size [f:fs. i mem f]))
                           [0..<n]))"

primrec
 enum_finals :: "(graph \<Rightarrow> graph list) \<Rightarrow> nat \<Rightarrow> graph list \<Rightarrow> nat fgraph list
                 \<Rightarrow> nat fgraph list option" where
  "enum_finals succs 0 todo fins = None"
| "enum_finals succs (Suc n) todo fins =
   (if todo = [] then Some fins
    else let g = hd todo; todo' = tl todo in
      if final g then enum_finals succs n todo' (fgraph g # fins)
      else enum_finals succs n (succs g @ todo') fins)"

definition fins :: "nat \<Rightarrow> nat \<Rightarrow> nat fgraph list option" where
"fins p n = enum_finals (next_tame p) n [Seed p] []"

definition same :: "nat fgraph list option \<Rightarrow> nat fgraph list \<Rightarrow> bool" where
"same fgso ags = (case fgso of None \<Rightarrow> False | Some fgs \<Rightarrow>
 let niso_test = (%fs1 fs2. iso_test (nof_vertices fs1,fs1)
                                     (nof_vertices fs2,fs2));
     tfgs = trie_of_list hash fgs;
     tags = trie_of_list hash ags in
 (list_all (%fg. list_ex (niso_test fg) (lookup_trie tags (hash fg))) fgs &
  list_all (%ag. list_ex (niso_test ag) (lookup_trie tfgs (hash ag))) ags))"

definition stat :: "nat fgraph list \<Rightarrow> nat * nat * nat * nat * nat" where
"stat A =
 (length A,
  foldl (%x y. if x<y then y else x) 0 (map length A),
  foldl (op +) 0 (map length A),
  foldl (%x y. if x<y then y else x)  0 (map nof_vertices A),
  foldl (op +) 0 (map nof_vertices A)
 )"

value [code] "stat Tri"
value [code] "stat Quad"
value [code] "stat Pent"
value [code] "stat Hex"
value [code] "stat Hept"
value [code] "stat Oct"

(* 3: (  20, 32,   440, 18,   260) *)
(* 4: ( 923, 29, 16533, 18, 11444) *)
(* 5: (1545, 26, 27223, 17, 19668) *)
(* 6: ( 238, 24,  4045, 16,  2970) *)
(* 7: (  23, 18,   357, 13,   278) *)
(* 8: (  22, 19,   333, 14,   266) *)

primrec countgs :: "(graph \<Rightarrow> graph list) \<Rightarrow> nat \<Rightarrow> nat*nat \<Rightarrow> graph list \<Rightarrow> (nat*nat) option" where
  "countgs succs 0       ij todo = None"
| "countgs succs (Suc n) ij todo =
   (if todo = [] then Some ij
    else let g = hd todo; todo' = tl todo in
      if final g then countgs succs n (fst ij, snd ij + 1) todo'
      else countgs succs n (fst ij + 1, snd ij) (succs g @ todo'))"

definition count :: "nat \<Rightarrow> nat \<Rightarrow> (nat*nat) option" where
"count p n = countgs (next_tame p) n (1,0) [Seed p]"

ML"set Toplevel.timing"
value [code] "count 0 100000"
value [code] "count 1 8000000"
value [code] "count 2 20000000"
value [code] "count 3 4000000"
value [code] "count 4 1000000"
value [code] "count 5 2000000"

(* 3:    (58021,   793) *)
(* 4:  (5631754, 17486) in 30 *)
(* 5: (11444023, 15746) in 50 *)
(* 6:  (3728798,  2499) in 15 *)
(* 7:   (766463,   273) in  3 *)
(* 8:  (1402944,   234) in  6 *)
(* sum: 23069034 *)

end
