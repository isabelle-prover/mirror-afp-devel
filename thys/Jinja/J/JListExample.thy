(*  Title:      Jinja/J/JListExample.thy
    ID:         $Id: JListExample.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Stefan Berghofer
*)

header {* \isaheader{Example for generating executable code from Jinja semantics} *}

theory JListExample imports Eval SystemClasses begin

ML {* Syntax.ambiguity_level := 100000 *}

consts
  list_name :: cname
  append_name :: mname
  val_nam :: vnam
  next_nam :: vnam
  l_nam :: vnam
  l1_nam :: vnam
  l2_nam :: vnam
  l3_nam :: vnam
  l4_nam :: vnam

constdefs
  val_name :: vname
  "val_name == VName val_nam"

  next_name :: vname
  "next_name == VName next_nam"

  l_name :: vname
  "l_name == VName l_nam"

  l1_name :: vname
  "l1_name == VName l1_nam"

  l2_name :: vname
  "l2_name == VName l2_nam"

  l3_name :: vname
  "l3_name == VName l3_nam"

  l4_name :: vname
  "l4_name == VName l4_nam"

  list_class :: "J_mb class"
  "list_class ==
    (Object,
     [(val_name, PrimT Integer), (next_name, RefT (ClassT list_name))],
     [(append_name, [RefT (ClassT list_name)], PrimT Void,
      ([l_name], [],
       If(BinOp Eq ({list_name}(Var This)\<bullet>next_name) (Lit Null))
         Expr ({list_name}(Var This)\<bullet>next_name:=Var l_name)
       Else
         Expr (({list_name}(Var This)\<bullet>next_name)\<bullet>
           append_name([Var l_name]));;
       Expr(LAss Result (Lit Unit))))])"

  example_prg :: "J_mb prog"
  "example_prg == [ObjectC, (list_name, list_class)]"

types_code
  cname ("string")
  vnam ("string")
  mname ("string")
  loc_ ("int")

consts_code
  "new_Addr" ("new'_addr {* %x. case x of None => True | Some y => False *}/ {* None *} {* Loc *}")

  "arbitrary" ("(raise ERROR)")
  "arbitrary" :: "val" ("{* Unit *}")
  "arbitrary" :: "cname" ("\"\"")

  "Object" ("\"Object\"")
  "list_name" ("\"list\"")
  "append_name" ("\"append\"")
  "val_nam" ("\"val\"")
  "next_nam" ("\"next\"")
  "l_nam" ("\"l\"")
  "l1_nam" ("\"l1\"")
  "l2_nam" ("\"l2\"")
  "l3_nam" ("\"l3\"")
  "l4_nam" ("\"l4\"")

ML {*
fun new_addr p none loc hp =
  let fun nr i = if p (hp (loc i)) then (loc i, none) else nr (i+1);
  in nr 0 end;
*}

generate_code
  test = "example_prg\<turnstile>Norm (Map.empty, Map.empty)
    -(Expr (l1_name:=New list_name);;
      Expr ({list_name}(Var l1_name)\<bullet>val_name:=Lit (Intg 1));;
      Expr (l2_name:=New list_name);;
      Expr ({list_name}(Var l2_name)\<bullet>val_name:=Lit (Intg 2));;
      Expr (l3_name:=New list_name);;
      Expr ({list_name}(Var l3_name)\<bullet>val_name:=Lit (Intg 3));;
      Expr (l4_name:=New list_name);;
      Expr ({list_name}(Var l4_name)\<bullet>val_name:=Lit (Intg 4));;
      Expr ((Var l1_name)\<bullet>append_name([Var l2_name]));;
      Expr ((Var l1_name)\<bullet>append_name([Var l3_name]));;
      Expr ((Var l1_name)\<bullet>append_name([Var l4_name])))\<rightarrow> _"

section {* Big step execution *}

ML {*

val Library.Some ((_, (heap, locs)), _) = Seq.pull test;
locs l1_name;
locs l2_name;
locs l3_name;
locs l4_name;
snd (the (heap (Loc 0))) (val_name, "list");
snd (the (heap (Loc 0))) (next_name, "list");
snd (the (heap (Loc 1))) (val_name, "list");
snd (the (heap (Loc 1))) (next_name, "list");
snd (the (heap (Loc 2))) (val_name, "list");
snd (the (heap (Loc 2))) (next_name, "list");
snd (the (heap (Loc 3))) (val_name, "list");
snd (the (heap (Loc 3))) (next_name, "list");

*}

end
