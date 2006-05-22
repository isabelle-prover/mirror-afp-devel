(*  ID:         $Id: ArchStat.thy,v 1.1 2006-05-22 09:53:59 nipkow Exp $
    Author:     Tobias Nipkow
*)

theory ArchStat
imports Evaluation TameEnum TrieList Arch
begin

consts qsort :: "('a \<Rightarrow> 'a => bool) * 'a list \<Rightarrow> 'a list"
recdef qsort "measure (size o snd)"
    "qsort(le, [])   = []"
    "qsort(le, x#xs) = qsort(le, [y:xs . ~ le x y]) @ [x] @
		       qsort(le, [y:xs . le x y])"
(hints recdef_simp: length_filter_le[THEN le_less_trans])

constdefs
 fgraph :: "graph \<Rightarrow> nat fgraph"
"fgraph g == map vertices (faces g)"

 nof_vertices :: "'a fgraph \<Rightarrow> nat"
"nof_vertices == length o remdups o concat"

 hash :: "nat fgraph \<Rightarrow> nat list"
"hash fs == let n = nof_vertices fs in
   [n, size fs] @
   qsort (%x y. y < x, map (%i. foldl (op +) 0 (map size [f:fs. i mem f]))
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
 fins :: "nat \<Rightarrow> nat \<Rightarrow> nat fgraph list option"
"fins p n == enum_finals (next_tame p) n [Seed p] []"

 same :: "nat fgraph list option \<Rightarrow> nat fgraph list \<Rightarrow> bool"
"same fgso ags == case fgso of None \<Rightarrow> False | Some fgs \<Rightarrow>
 let niso_test = (%fs1 fs2. iso_test (nof_vertices fs1,fs1)
                                     (nof_vertices fs2,fs2));
     tfgs = trie_of_list hash fgs;
     tags = trie_of_list hash ags in
 (list_all (%fg. list_ex (niso_test fg) (lookup_trie tags (hash fg))) fgs &
  list_all (%ag. list_ex (niso_test ag) (lookup_trie tfgs (hash ag))) ags)"


code_module test file "Test.ML" contains "same (fins 0 800000) []"

constdefs stat :: "nat fgraph list \<Rightarrow> nat * nat * nat * nat * nat"
"stat A ==
 (length A,
  foldl (%x y. if x<y then y else x) 0 (map length A),
  foldl (op +) 0 (map length A),
  foldl (%x y. if x<y then y else x)  0 (map nof_vertices A),
  foldl (op +) 0 (map nof_vertices A)
 )"

value "stat Tri"
value "stat Quad"
value "stat Pent"
value "stat Hex"
value "stat Hept"
value "stat Oct";

(* 3: (  20, 32,   440, 18,   260) *)
(* 4: ( 923, 29, 16533, 18, 11444) *)
(* 5: (1545, 26, 27223, 17, 19668) *)
(* 6: ( 238, 24,  4045, 16,  2970) *)
(* 7: (  23, 18,   357, 13,   278) *)
(* 8: (  22, 19,   333, 14,   266) *)

consts
 countgs :: "(graph \<Rightarrow> graph list) \<Rightarrow> nat \<Rightarrow> nat*nat \<Rightarrow> graph list \<Rightarrow> (nat*nat) option"
primrec
"countgs succs 0       ij todo = None"
"countgs succs (Suc n) ij todo =
 (if todo = [] then Some ij
  else let g = hd todo; todo' = tl todo in
    if final g then countgs succs n (fst ij, snd ij + 1) todo'
    else countgs succs n (fst ij + 1, snd ij) (succs g @ todo'))"

constdefs
 count :: "nat \<Rightarrow> nat \<Rightarrow> (nat*nat) option"
"count p n == countgs (next_tame p) n (1,0) [Seed p]"

ML"set Toplevel.timing"
value "count 0 100000"
value "count 1 8000000"
value "count 2 20000000"
value "count 3 4000000"
value "count 4 1000000"
value "count 5 2000000";

(* 3:    (58021,   793) *)
(* 4:  (5631754, 17486) in 30 *)
(* 5: (11444023, 15746) in 50 *)
(* 6:  (3728798,  2499) in 15 *)
(* 7:   (766463,   273) in  3 *)
(* 8:  (1402944,   234) in  6 *)
(* sum: 23069034 *)


end
