(*  Title:      Jinja/J/Examples.thy
    ID:         $Id: Examples.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Christoph Petzinger
    Copyright   2004 Technische Universitaet Muenchen
*)

header {* \isaheader{Example Expressions - for use in execute_ theories} *}

theory Examples imports Expr begin

types_code
  set ("_ list")

consts_code
  "{}"     ("[]")
  "insert" ("(_ ins _)")
  "op :"   ("(_ mem _)")
  "op Un"  ("(_ union _)")

ML {*
fun new_addr z s alloc some hp =
  let fun nr i = if alloc (hp i) then some i else nr (s i);
  in nr z end;
*}

consts_code
  "new_Addr"
   ("new'_addr {* 0::nat *} {* Suc *}
               {* %x. case x of None => True | Some y => False *} {* Some *}")

  "arbitrary" ("(raise ERROR)")


constdefs
  classObject::"J_mb cdecl"
  "classObject == (''Object'','''',[],[])"


  classI :: "J_mb cdecl"
  "classI ==
  (''I'', Object,
  [],
  [(''mult'',[Integer,Integer],Integer,[''i'',''j''],
   if (Var ''i'' \<guillemotleft>Eq\<guillemotright> Val(Intg 0)) (Val(Intg 0))
   else Var ''j'' \<guillemotleft>Add\<guillemotright>
       Var this \<bullet> ''mult''([Var ''i'' \<guillemotleft>Add\<guillemotright> Val(Intg -1),Var ''j'']))
  ])"


  classL :: "J_mb cdecl"
  "classL ==
  (''L'', Object,
  [(''F'',Integer), (''N'',Class ''L'')],
  [(''app'',[Class ''L''],Void,[''l''],
   if (Var this \<bullet> ''N''{''L''} \<guillemotleft>Eq\<guillemotright> null)
      (Var this \<bullet> ''N''{''L''} := Var ''l'')
   else (Var this \<bullet> ''N''{''L''}) \<bullet> ''app''([Var ''l'']))
  ])"


  testExpr_BuildList :: "expr"
  "testExpr_BuildList ==
  {''l1'':Class ''L'' := new ''L'';
   Var ''l1''\<bullet>''F''{''L''} := Val(Intg 1);;
  {''l2'':Class ''L'' := new ''L'';
   Var ''l2''\<bullet> ''F''{''L''} := Val(Intg 2);;
  {''l3'':Class ''L'' := new ''L'';
   Var ''l3''\<bullet> ''F''{''L''} := Val(Intg 3);;
  {''l4'':Class ''L'' := new ''L'';
   Var ''l4''\<bullet> ''F''{''L''} := Val(Intg 4);;
   Var ''l1''\<bullet>''app''([Var ''l2'']);;
   Var ''l1''\<bullet>''app''([Var ''l3'']);;
   Var ''l1''\<bullet>''app''([Var ''l4''])}}}}"

  testExpr1 ::"expr"
  "testExpr1 == Val(Intg 5)"
  testExpr2 ::"expr"
  "testExpr2 == BinOp (Val(Intg 5)) Add (Val(Intg 6))"
  testExpr3 ::"expr"
  "testExpr3 == BinOp (Var ''V'') Add (Val(Intg 6))"
  testExpr4 ::"expr"
  "testExpr4 == ''V'' := Val(Intg 6)"
  testExpr5 ::"expr"
  "testExpr5 == new ''Object'';; {''V'':(Class ''C'') := new ''C''; Var ''V''\<bullet>''F''{''C''} := Val(Intg 42)}"
  testExpr6 ::"expr"
  "testExpr6 == {''V'':(Class ''I'') := new ''I''; Var ''V''\<bullet>''mult''([Val(Intg 40),Val(Intg 4)])}"

constdefs
  mb_isNull:: "expr"
  "mb_isNull == Var this \<bullet> ''test''{''A''} \<guillemotleft>Eq\<guillemotright> null "

  mb_add:: "expr"
  "mb_add == (Var this \<bullet> ''int''{''A''} :=( Var this \<bullet> ''int''{''A''} \<guillemotleft>Add\<guillemotright> Var ''i''));; (Var this \<bullet> ''int''{''A''})"

    mb_mult_cond:: "expr"  
    "mb_mult_cond == (Var ''j'' \<guillemotleft>Eq\<guillemotright> Val (Intg 0)) \<guillemotleft>Eq\<guillemotright> Val (Bool False)"
    mb_mult_block:: "expr"
    "mb_mult_block == ''temp'':=(Var ''temp'' \<guillemotleft>Add\<guillemotright> Var ''i'');;''j'':=(Var ''j'' \<guillemotleft>Add\<guillemotright> Val (Intg -1))"
  mb_mult:: "expr"
  "mb_mult == {''temp'':Integer:=Val (Intg 0); While (mb_mult_cond) mb_mult_block;; ( Var this \<bullet> ''int''{''A''} := Var ''temp'';; Var ''temp'' )}"

  classA:: "J_mb cdecl"
  "classA ==
  (''A'', Object,
  [(''int'',Integer),
   (''test'',Class ''A'') ],
  [(''isNull'',[],Boolean,[], mb_isNull),
   (''add'',[Integer],Integer,[''i''], mb_add),
   (''mult'',[Integer,Integer],Integer,[''i'',''j''], mb_mult) ])"
  

  testExpr_ClassA:: "expr"
  "testExpr_ClassA ==
  {''A1'':Class ''A'':= new ''A''; 
  {''A2'':Class ''A'':= new ''A''; 
  {''testint'':Integer:= Val (Intg 5);
   (Var ''A2''\<bullet> ''int''{''A''} := (Var ''A1''\<bullet> ''add''([Var ''testint''])));;
   (Var ''A2''\<bullet> ''int''{''A''} := (Var ''A1''\<bullet> ''add''([Var ''testint''])));;
   Var ''A2''\<bullet> ''mult''([Var ''A2''\<bullet> ''int''{''A''}, Var ''testint'']) }}}"


end