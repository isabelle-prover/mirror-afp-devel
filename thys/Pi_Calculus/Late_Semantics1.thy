(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Late_Semantics1
  imports Late_Semantics
begin

rep_datatype InputS BoundOutputS
apply(auto simp add: subject.inject)
by(induct_tac subject rule: subject.induct) auto

rep_datatype OutputR TauR
apply(auto simp add: freeRes.inject)
by(induct_tac freeRes rule: freeRes.induct) auto

end