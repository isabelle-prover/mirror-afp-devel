(*  Title:      Jinja/Compiler/Compiler2.thy
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Compilation Stage 2} *}

theory Compiler2
imports PCompiler J1 "../JVM/JVMExec"
begin

primrec compE\<^isub>2 :: "expr\<^isub>1 \<Rightarrow> instr list"
  and compEs\<^isub>2 :: "expr\<^isub>1 list \<Rightarrow> instr list" where
  "compE\<^isub>2 (new C) = [New C]"
| "compE\<^isub>2 (Cast C e) = compE\<^isub>2 e @ [Checkcast C]"
| "compE\<^isub>2 (Val v) = [Push v]"
| "compE\<^isub>2 (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = compE\<^isub>2 e\<^isub>1 @ compE\<^isub>2 e\<^isub>2 @ 
  (case bop of Eq \<Rightarrow> [CmpEq]
            | Add \<Rightarrow> [IAdd])"
| "compE\<^isub>2 (Var i) = [Load i]"
| "compE\<^isub>2 (i:=e) = compE\<^isub>2 e @ [Store i, Push Unit]"
| "compE\<^isub>2 (e\<bullet>F{D}) = compE\<^isub>2 e @ [Getfield F D]"
| "compE\<^isub>2 (e\<^isub>1\<bullet>F{D} := e\<^isub>2) =
       compE\<^isub>2 e\<^isub>1 @ compE\<^isub>2 e\<^isub>2 @ [Putfield F D, Push Unit]"
| "compE\<^isub>2 (e\<bullet>M(es)) = compE\<^isub>2 e @ compEs\<^isub>2 es @ [Invoke M (size es)]"
| "compE\<^isub>2 ({i:T; e}) = compE\<^isub>2 e"
| "compE\<^isub>2 (e\<^isub>1;;e\<^isub>2) = compE\<^isub>2 e\<^isub>1 @ [Pop] @ compE\<^isub>2 e\<^isub>2"
| "compE\<^isub>2 (if (e) e\<^isub>1 else e\<^isub>2) =
	(let cnd   = compE\<^isub>2 e;
	     thn   = compE\<^isub>2 e\<^isub>1;
	     els   = compE\<^isub>2 e\<^isub>2;
	     test  = IfFalse (int(size thn + 2)); 
	     thnex = Goto (int(size els + 1))
	 in cnd @ [test] @ thn @ [thnex] @ els)"
| "compE\<^isub>2 (while (e) c) =
	(let cnd   = compE\<^isub>2 e;
	     bdy   = compE\<^isub>2 c;
	     test  = IfFalse (int(size bdy + 3)); 
	     loop  = Goto (-int(size bdy + size cnd + 2))
	 in cnd @ [test] @ bdy @ [Pop] @ [loop] @ [Push Unit])"
| "compE\<^isub>2 (throw e) = compE\<^isub>2 e @ [instr.Throw]"
| "compE\<^isub>2 (try e\<^isub>1 catch(C i) e\<^isub>2) =
   (let catch = compE\<^isub>2 e\<^isub>2
    in compE\<^isub>2 e\<^isub>1 @ [Goto (int(size catch)+2), Store i] @ catch)"

| "compEs\<^isub>2 []     = []"
| "compEs\<^isub>2 (e#es) = compE\<^isub>2 e @ compEs\<^isub>2 es"

text{* Compilation of exception table. Is given start address of code
to compute absolute addresses necessary in exception table. *}

primrec compxE\<^isub>2  :: "expr\<^isub>1      \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table"
  and compxEs\<^isub>2 :: "expr\<^isub>1 list \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table" where
  "compxE\<^isub>2 (new C) pc d = []"
| "compxE\<^isub>2 (Cast C e) pc d = compxE\<^isub>2 e pc d"
| "compxE\<^isub>2 (Val v) pc d = []"
| "compxE\<^isub>2 (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) pc d =
   compxE\<^isub>2 e\<^isub>1 pc d @ compxE\<^isub>2 e\<^isub>2 (pc + size(compE\<^isub>2 e\<^isub>1)) (d+1)"
| "compxE\<^isub>2 (Var i) pc d = []"
| "compxE\<^isub>2 (i:=e) pc d = compxE\<^isub>2 e pc d"
| "compxE\<^isub>2 (e\<bullet>F{D}) pc d = compxE\<^isub>2 e pc d"
| "compxE\<^isub>2 (e\<^isub>1\<bullet>F{D} := e\<^isub>2) pc d =
   compxE\<^isub>2 e\<^isub>1 pc d @ compxE\<^isub>2 e\<^isub>2 (pc + size(compE\<^isub>2 e\<^isub>1)) (d+1)"
| "compxE\<^isub>2 (e\<bullet>M(es)) pc d =
   compxE\<^isub>2 e pc d @ compxEs\<^isub>2 es (pc + size(compE\<^isub>2 e)) (d+1)"
| "compxE\<^isub>2 ({i:T; e}) pc d = compxE\<^isub>2 e pc d"
| "compxE\<^isub>2 (e\<^isub>1;;e\<^isub>2) pc d =
   compxE\<^isub>2 e\<^isub>1 pc d @ compxE\<^isub>2 e\<^isub>2 (pc+size(compE\<^isub>2 e\<^isub>1)+1) d"
| "compxE\<^isub>2 (if (e) e\<^isub>1 else e\<^isub>2) pc d =
	(let pc\<^isub>1   = pc + size(compE\<^isub>2 e) + 1;
	     pc\<^isub>2   = pc\<^isub>1 + size(compE\<^isub>2 e\<^isub>1) + 1
	 in compxE\<^isub>2 e pc d @ compxE\<^isub>2 e\<^isub>1 pc\<^isub>1 d @ compxE\<^isub>2 e\<^isub>2 pc\<^isub>2 d)"
| "compxE\<^isub>2 (while (b) e) pc d =
   compxE\<^isub>2 b pc d @ compxE\<^isub>2 e (pc+size(compE\<^isub>2 b)+1) d"
| "compxE\<^isub>2 (throw e) pc d = compxE\<^isub>2 e pc d"
| "compxE\<^isub>2 (try e\<^isub>1 catch(C i) e\<^isub>2) pc d =
   (let pc\<^isub>1 = pc + size(compE\<^isub>2 e\<^isub>1)
    in compxE\<^isub>2 e\<^isub>1 pc d @ compxE\<^isub>2 e\<^isub>2 (pc\<^isub>1+2) d @ [(pc,pc\<^isub>1,C,pc\<^isub>1+1,d)])"

| "compxEs\<^isub>2 [] pc d    = []"
| "compxEs\<^isub>2 (e#es) pc d = compxE\<^isub>2 e pc d @ compxEs\<^isub>2 es (pc+size(compE\<^isub>2 e)) (d+1)"

primrec max_stack :: "expr\<^isub>1 \<Rightarrow> nat"
  and max_stacks :: "expr\<^isub>1 list \<Rightarrow> nat" where
  "max_stack (new C) = 1"
| "max_stack (Cast C e) = max_stack e"
| "max_stack (Val v) = 1"
| "max_stack (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = max (max_stack e\<^isub>1) (max_stack e\<^isub>2) + 1"
| "max_stack (Var i) = 1"
| "max_stack (i:=e) = max_stack e"
| "max_stack (e\<bullet>F{D}) = max_stack e"
| "max_stack (e\<^isub>1\<bullet>F{D} := e\<^isub>2) = max (max_stack e\<^isub>1) (max_stack e\<^isub>2) + 1"
| "max_stack (e\<bullet>M(es)) = max (max_stack e) (max_stacks es) + 1"
| "max_stack ({i:T; e}) = max_stack e"
| "max_stack (e\<^isub>1;;e\<^isub>2) = max (max_stack e\<^isub>1) (max_stack e\<^isub>2)"
| "max_stack (if (e) e\<^isub>1 else e\<^isub>2) =
  max (max_stack e) (max (max_stack e\<^isub>1) (max_stack e\<^isub>2))"
| "max_stack (while (e) c) = max (max_stack e) (max_stack c)"
| "max_stack (throw e) = max_stack e"
| "max_stack (try e\<^isub>1 catch(C i) e\<^isub>2) = max (max_stack e\<^isub>1) (max_stack e\<^isub>2)"
 
| "max_stacks [] = 0"
| "max_stacks (e#es) = max (max_stack e) (1 + max_stacks es)"

lemma max_stack1: "1 \<le> max_stack e"
(*<*)by(induct e) (simp_all add:max_def)(*>*)


definition compMb\<^isub>2 :: "expr\<^isub>1 \<Rightarrow> jvm_method"
where
  "compMb\<^isub>2  \<equiv>  \<lambda>body.
  let ins = compE\<^isub>2 body @ [Return];
      xt = compxE\<^isub>2 body 0 0
  in (max_stack body, max_vars body, ins, xt)"

definition compP\<^isub>2 :: "J\<^isub>1_prog \<Rightarrow> jvm_prog"
where
  "compP\<^isub>2  \<equiv>  compP compMb\<^isub>2"

(*<*)
declare compP\<^isub>2_def [simp]
(*>*)

lemma compMb\<^isub>2 [simp]:
  "compMb\<^isub>2 e = (max_stack e, max_vars e, compE\<^isub>2 e @ [Return], compxE\<^isub>2 e 0 0)"
(*<*)by (simp add: compMb\<^isub>2_def)(*>*)


end
