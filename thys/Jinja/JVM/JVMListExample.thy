(*  Title:      Jinja/JVM/JVMListExample.thy
    ID:         $Id: JVMListExample.thy,v 1.5 2007-07-19 19:50:53 fhaftmann Exp $
    Author:     Stefan Berghofer, Gerwin Klein
*)

header {* \isaheader{Example for generating executable code from JVM semantics}\label{sec:JVMListExample} *}

theory JVMListExample
imports SystemClasses JVMExec Efficient_Nat
begin

constdefs
  list_name :: string
  "list_name == ''list''"

  test_name :: string
  "test_name == ''test''"

  val_name :: string
  "val_name == ''val''"

  next_name :: string
  "next_name == ''next''"

  append_name :: string
  "append_name == ''append''"

  makelist_name :: string
  "makelist_name == ''makelist''"

  append_ins :: bytecode
  "append_ins == 
       [Load 0,
        Getfield next_name list_name,
        Load 0,
        Getfield next_name list_name,
        Push Null,
        CmpEq,
        IfFalse 7,
        Pop,
        Load 0,
        Load 1,
        Putfield next_name list_name,
        Push Unit,
        Return,
        Load 1,       
        Invoke append_name 1,
        Return]"

  list_class :: "jvm_method class"
  "list_class ==
    (Object,
     [(val_name, Integer), (next_name, Class list_name)],
     [(append_name, [Class list_name], Void,
        (3, 0, append_ins, [(1, 2, NullPointer, 7, 0)]))])"

  make_list_ins :: bytecode
  "make_list_ins ==
       [New list_name,
        Store 0,
        Load 0,
        Push (Intg 1),
        Putfield val_name list_name,
        New list_name,
        Store 1,
        Load 1,
        Push (Intg 2),
        Putfield val_name list_name,
        New list_name,
        Store 2,
        Load 2,
        Push (Intg 3),
        Putfield val_name list_name,
        Load 0,
        Load 1,
        Invoke append_name 1,
        Pop,
        Load 0,
        Load 2,
        Invoke append_name 1,
        Return]"

  test_class :: "jvm_method class"
  "test_class ==
    (Object, [],
     [(makelist_name, [], Void, (3, 2, make_list_ins, []))])"

  E :: jvm_prog
  "E == SystemClasses @ [(list_name, list_class), (test_name, test_class)]"


consts_code
  "new_Addr"
   ("\<module>new'_addr {* 0::nat *} {* Suc *}
               {* %x. case x of None => True | Some y => False *} {* Some *}")
attach {*
fun new_addr z s alloc some hp =
  let fun nr i = if alloc (hp i) then some i else nr (s i);
  in nr z end;
*}

  "arbitrary" ("(error \"arbitrary\")")
  "arbitrary :: val" ("{* Unit *}")
  "arbitrary :: cname" ("Object")

declare method_def2 [unfolded Method_def, OF exI, OF conjI, code ind]
declare fields_def2 [code ind]
lemmas [code unfold] = SystemClasses_def [unfolded ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def]

subsection {* Single step execution *}

code_module JVM
contains
  test = "exec (E, start_state E test_name makelist_name)"

ML {* JVM.test *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* JVM.exec (JVM.E, JVM.the it) *}
ML {* val JVM.Some (_, (f, _)) = it *}
ML {* if snd (JVM.the (f 3)) (JVM.val_name, JVM.list_name) = JVM.Some (JVM.Intg 1) then () else error "wrong result" *}
ML {* if snd (JVM.the (f 3)) (JVM.next_name, JVM.list_name) = JVM.Some (JVM.Addr 4) then () else error "wrong result" *}
ML {* if snd (JVM.the (f 4)) (JVM.val_name, JVM.list_name) = JVM.Some (JVM.Intg 2) then () else error "wrong result" *}
ML {* if snd (JVM.the (f 4)) (JVM.next_name, JVM.list_name) = JVM.Some (JVM.Addr 5) then () else error "wrong result" *}
ML {* if snd (JVM.the (f 5)) (JVM.val_name, JVM.list_name) = JVM.Some (JVM.Intg 3) then () else error "wrong result" *}
ML {* if snd (JVM.the (f 5)) (JVM.next_name, JVM.list_name) = JVM.Some JVM.Null then () else error "wrong result" *}

end
