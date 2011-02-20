theory Test
imports "~~/src/HOL/Library/Efficient_Nat" FingerTree
begin
  text {*
    Test code generation, to early detect problems with code generator.
    *}

definition 
  fti_toList :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_toList == FingerTree.toList"
definition 
  fti_toTree :: "_ \<Rightarrow> ('e,nat) FingerTree"
  where "fti_toTree == FingerTree.toTree"
definition 
  fti_empty :: "_ \<Rightarrow> ('e,nat) FingerTree"
  where "fti_empty u == FingerTree.empty"
definition 
  fti_annot :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_annot == FingerTree.annot"
definition 
  fti_lcons :: "_ \<Rightarrow> ('e,nat) FingerTree \<Rightarrow> _"
  where "fti_lcons == FingerTree.lcons"
definition 
  fti_rcons :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_rcons == FingerTree.rcons"
definition 
  fti_viewL :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_viewL == FingerTree.viewL"
definition 
  fti_viewR :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_viewR == FingerTree.viewR"
definition 
  fti_isEmpty :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_isEmpty == FingerTree.isEmpty"
definition 
  fti_head :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_head == FingerTree.head"
definition 
  fti_tail :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_tail == FingerTree.tail"
definition 
  fti_headR :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_headR == FingerTree.headR"
definition 
  fti_tailR :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_tailR == FingerTree.tailR"
definition 
  fti_app :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_app == FingerTree.app"
definition 
  fti_splitTree :: "_ \<Rightarrow> nat \<Rightarrow> _"
  where "fti_splitTree == FingerTree.splitTree"
definition 
  fti_foldl :: "_ \<Rightarrow> _ \<Rightarrow> ('e,nat) FingerTree \<Rightarrow> _"
  where "fti_foldl == FingerTree.foldl"
definition 
  fti_foldr :: "_ \<Rightarrow> ('e,nat) FingerTree \<Rightarrow> _"
  where "fti_foldr == FingerTree.foldr"
definition 
  fti_count :: "('e,nat) FingerTree \<Rightarrow> _"
  where "fti_count == FingerTree.count"

export_code 
  fti_toList
  fti_toTree
  fti_empty
  fti_annot
  fti_lcons
  fti_rcons
  fti_viewL
  fti_viewR
  fti_isEmpty
  fti_head
  fti_tail
  fti_headR
  fti_tailR
  fti_app
  fti_splitTree
  fti_foldl
  fti_foldr
  fti_count
  in Haskell file -
  in OCaml file -
  in SML file -

ML {*
  val t1 = @{code fti_toTree} [("a",1),("b",2),("c",3)];
  val t2 = @{code fti_toTree} [("d",1),("e",2),("f",3)];
  val t3 = @{code fti_app} t1 t2;
  val t3 = @{code fti_app} t3 (@{code fti_empty} ());

  val t4 = @{code fti_lcons} ("g",7) t3;
  val t4 = @{code fti_rcons} t3 ("g",7);
  @{code fti_toList} t4;
  @{code fti_annot} t4;
  @{code fti_viewL} t4;
  @{code fti_viewR} t4;
  @{code fti_head} t4;
  @{code fti_tail} t4;
  @{code fti_headR} t4;
  @{code fti_tailR} t4;
  @{code fti_count} t4;
  @{code fti_isEmpty} t4;
  @{code fti_isEmpty} (@{code fti_empty} ());

  val (tl,(e,tr)) = @{code fti_splitTree} (fn a => a>=10) 0 t4;
  @{code fti_toList} tl; e; @{code fti_toList} tr;

  @{code fti_foldl} (fn s => fn (_,a) => s+a) 0 t4;
  @{code fti_foldr} (fn (_,a) => fn s => s+a) t4 0;
*}

end
