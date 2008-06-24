(*  Title:      Jinja/BV/BVExample.thy
    ID:         $Id: BVExample.thy,v 1.7 2008-06-24 22:23:28 makarius Exp $
    Author:     Gerwin Klein
*)

header {* \isaheader{Example Welltypings}\label{sec:BVExample} *}

theory BVExample
imports JVMListExample BVSpecTypeSafe BVExec Executable_Set
begin

text {*
  This theory shows type correctness of the example program in section 
  \ref{sec:JVMListExample} (p. \pageref{sec:JVMListExample}) by
  explicitly providing a welltyping. It also shows that the start
  state of the program conforms to the welltyping; hence type safe
  execution is guaranteed.
*}

section "Setup"

lemma distinct_classes':
  "list_name \<noteq> test_name"
  "list_name \<noteq> Object"
  "list_name \<noteq> ClassCast"
  "list_name \<noteq> OutOfMemory"
  "list_name \<noteq> NullPointer"
  "test_name \<noteq> Object"
  "test_name \<noteq> OutOfMemory"
  "test_name \<noteq> ClassCast"
  "test_name \<noteq> NullPointer"
  "ClassCast \<noteq> NullPointer"
  "ClassCast \<noteq> Object"
  "NullPointer \<noteq> Object"
  "OutOfMemory \<noteq> ClassCast"
  "OutOfMemory \<noteq> NullPointer"
  "OutOfMemory \<noteq> Object"
  by (simp_all add: list_name_def test_name_def Object_def NullPointer_def
    OutOfMemory_def ClassCast_def)

lemmas distinct_classes = distinct_classes' distinct_classes' [symmetric]

lemma distinct_fields:
  "val_name \<noteq> next_name"
  "next_name \<noteq> val_name"
  by (simp_all add: val_name_def next_name_def)

text {* Abbreviations for definitions we will have to use often in the
proofs below: *}
lemmas system_defs = SystemClasses_def ObjectC_def NullPointerC_def 
                     OutOfMemoryC_def ClassCastC_def
lemmas class_defs  = list_class_def test_class_def

text {* These auxiliary proofs are for efficiency: class lookup,
subclass relation, method and field lookup are computed only once:
*}
lemma class_Object [simp]:
  "class E Object = Some (arbitrary, [],[])"
  by (simp add: class_def system_defs E_def)

lemma class_NullPointer [simp]:
  "class E NullPointer = Some (Object, [], [])"
  by (simp add: class_def system_defs E_def distinct_classes)

lemma class_OutOfMemory [simp]:
  "class E OutOfMemory = Some (Object, [], [])"
  by (simp add: class_def system_defs E_def distinct_classes)

lemma class_ClassCast [simp]:
  "class E ClassCast = Some (Object, [], [])"
  by (simp add: class_def system_defs E_def distinct_classes)

lemma class_list [simp]:
  "class E list_name = Some list_class"
  by (simp add: class_def system_defs E_def distinct_classes)
 
lemma class_test [simp]:
  "class E test_name = Some test_class"
  by (simp add: class_def system_defs E_def distinct_classes)

lemma E_classes [simp]:
  "{C. is_class E C} = {list_name, test_name, NullPointer, 
                        ClassCast, OutOfMemory, Object}"
  by (auto simp add: is_class_def class_def system_defs E_def class_defs)

text {* The subclass releation spelled out: *}
lemma subcls1:
  "subcls1 E = {(list_name,Object), (test_name,Object), (NullPointer, Object),
                (ClassCast, Object), (OutOfMemory, Object)}"
(*<*)
  apply (simp add: subcls1_def2)
  apply (simp add: class_defs system_defs E_def class_def)
  (* FIXME: cannot simply expand class names, since
     inequality proofs on strings are too inefficient *)
  apply (auto simp: distinct_classes split: split_if_asm)
  done
(*>*)

text {* The subclass relation is acyclic; hence its converse is well founded: *}
lemma notin_rtrancl:
  "(a,b) \<in> r\<^sup>* \<Longrightarrow> a \<noteq> b \<Longrightarrow> (\<And>y. (a,y) \<notin> r) \<Longrightarrow> False"
  by (auto elim: converse_rtranclE)

lemma acyclic_subcls1_E: "acyclic (subcls1 E)"
(*<*)
  apply (rule acyclicI)
  apply (simp add: subcls1)
  apply (auto dest!: tranclD)
  apply (auto elim!: notin_rtrancl simp add: distinct_classes)
  done
(*>*)

lemma wf_subcls1_E: "wf ((subcls1 E)\<inverse>)"
(*<*)
  apply (rule finite_acyclic_wf_converse)
  apply (simp add: subcls1)
  apply (rule acyclic_subcls1_E)
  done  
(*>*)

text {* Method and field lookup: *}

lemma method_append [simp]:
  "method E list_name append_name =
  (list_name, [Class list_name], Void, 3, 0, append_ins, [(1, 2, NullPointer, 7, 0)])"
(*<*)
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (fastsimp simp add: Method_def distinct_classes intro: method_def2 Methods.intros)
  done
(*>*)

lemma method_makelist [simp]:
  "method E test_name makelist_name = 
  (test_name, [], Void, 3, 2, make_list_ins, [])"
(*<*)
  apply (insert class_test)
  apply (unfold test_class_def)
  apply (fastsimp simp add: Method_def distinct_classes intro: method_def2 Methods.intros)
  done
(*>*)

lemma field_val [simp]:
  "field E list_name val_name = (list_name, Integer)"
(*<*)
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (fastsimp simp add: sees_field_def distinct_classes intro: field_def2 Fields.intros)
  done
(*>*)

lemma field_next [simp]:
  "field E list_name next_name = (list_name, Class list_name)"
(*<*)
  apply (insert class_list)
  apply (unfold list_class_def)
  apply (fastsimp simp add: distinct_fields sees_field_def distinct_classes intro: field_def2 Fields.intros)
  done
(*>*)

lemma [simp]: "fields E Object = []"
  by (fastsimp intro: fields_def2 Fields.intros)
 
lemma [simp]: "fields E NullPointer = []"
  by (fastsimp simp add: distinct_classes intro: fields_def2 Fields.intros)

lemma [simp]: "fields E ClassCast = []"
  by (fastsimp simp add: distinct_classes intro: fields_def2 Fields.intros)

lemma [simp]: "fields E OutOfMemory = []"
  by (fastsimp simp add: distinct_classes intro: fields_def2 Fields.intros)

lemma [simp]: "fields E test_name = []"
(*<*)
  apply (insert class_test)
  apply (unfold test_class_def)
  apply (fastsimp simp add: distinct_classes intro: fields_def2 Fields.intros)
  done
(*>*)

lemmas [simp] = is_class_def


section "Program structure"

text {*
  The program is structurally wellformed:
*}
lemma wf_struct:
  "wf_prog (\<lambda>G C mb. True) E" (is "wf_prog ?mb E")
(*<*)
proof -
  have "distinct_fst E" 
    by (simp add: system_defs E_def class_defs distinct_classes)
  moreover
  have "set SystemClasses \<subseteq> set E" by (simp add: system_defs E_def)
  hence "wf_syscls E" by (rule wf_syscls)
  moreover
  have "wf_cdecl ?mb E ObjectC" by (simp add: wf_cdecl_def ObjectC_def)
  moreover
  have "wf_cdecl ?mb E NullPointerC" 
    by (auto elim: notin_rtrancl 
            simp add: wf_cdecl_def distinct_classes NullPointerC_def subcls1)
  moreover
  have "wf_cdecl ?mb E ClassCastC" 
    by (auto elim: notin_rtrancl 
            simp add: wf_cdecl_def distinct_classes ClassCastC_def subcls1)
  moreover
  have "wf_cdecl ?mb E OutOfMemoryC" 
    by (auto elim: notin_rtrancl 
            simp add: wf_cdecl_def distinct_classes OutOfMemoryC_def subcls1)
  moreover
  have "wf_cdecl ?mb E (list_name, list_class)"
    apply (auto elim!: notin_rtrancl 
            simp add: wf_cdecl_def wf_fdecl_def list_class_def 
                      wf_mdecl_def subcls1)
    apply (auto simp add: distinct_classes distinct_fields Method_def elim: Methods.cases)
    done    
  moreover
  have "wf_cdecl ?mb E (test_name, test_class)" 
    apply (auto elim!: notin_rtrancl 
            simp add: wf_cdecl_def wf_fdecl_def test_class_def 
                      wf_mdecl_def subcls1)
    apply (auto simp add: distinct_classes distinct_fields Method_def elim: Methods.cases)
    done       
  ultimately
  show ?thesis by (simp add: wf_prog_def E_def SystemClasses_def)
qed
(*>*)

section "Welltypings"
text {*
  We show welltypings of the methods @{term append_name} in class @{term list_name}, 
  and @{term makelist_name} in class @{term test_name}:
*}
lemmas eff_simps [simp] = eff_def norm_eff_def xcpt_eff_def
(*declare app'Invoke [simp del]*)

constdefs
  phi_append :: ty\<^isub>m ("\<phi>\<^sub>a")
  "\<phi>\<^sub>a \<equiv> map (\<lambda>(x,y). Some (x, map OK y)) [ 
   (                                    [], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   ([NT, Class list_name, Class list_name], [Class list_name, Class list_name]),
   (            [Boolean, Class list_name], [Class list_name, Class list_name]),

   (                        [Class Object], [Class list_name, Class list_name]),
   (                                    [], [Class list_name, Class list_name]),
   (                     [Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   (                                    [], [Class list_name, Class list_name]),
   (                                [Void], [Class list_name, Class list_name]),

   (                     [Class list_name], [Class list_name, Class list_name]),
   (    [Class list_name, Class list_name], [Class list_name, Class list_name]),
   (                                [Void], [Class list_name, Class list_name])]"

text {*
  The next definition and three proof rules implement an algorithm to
  enumarate natural numbers. The command @{text "apply (elim pc_end pc_next pc_0"} 
  transforms a goal of the form
  @{prop [display] "pc < n \<Longrightarrow> P pc"} 
  into a series of goals
  @{prop [display] "P 0"} 
  @{prop [display] "P (Suc 0)"} 

  @{text "\<dots>"}

  @{prop [display] "P n"} 
*}
constdefs 
  intervall :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<in> [_, _')")
  "x \<in> [a, b) \<equiv> a \<le> x \<and> x < b"

lemma pc_0: "x < n \<Longrightarrow> (x \<in> [0, n) \<Longrightarrow> P x) \<Longrightarrow> P x"
  by (simp add: intervall_def)

lemma pc_next: "x \<in> [n0, n) \<Longrightarrow> P n0 \<Longrightarrow> (x \<in> [Suc n0, n) \<Longrightarrow> P x) \<Longrightarrow> P x"
(*<*)
  apply (cases "x=n0")
  apply (auto simp add: intervall_def)
  done
(*>*)

lemma pc_end: "x \<in> [n,n) \<Longrightarrow> P x" 
  by (unfold intervall_def) arith


lemma types_append [simp]: "check_types E 3 (Suc (Suc 0)) (map OK \<phi>\<^sub>a)"
(*<*)
  by (auto simp add: check_types_def phi_append_def JVM_states_unfold)
(*>*)

lemma wt_append [simp]:
  "wt_method E list_name [Class list_name] Void 3 0 append_ins
             [(Suc 0, 2, NullPointer, 7, 0)] \<phi>\<^sub>a"
(*<*)
  apply (simp add: wt_method_def wt_start_def wt_instr_def)
  apply (simp add: append_ins_def phi_append_def)
  apply clarify
  apply (drule sym)
  apply (erule_tac P="?x = ?y" in rev_mp)
  apply (elim pc_end pc_next pc_0)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add: matches_ex_entry_def subcls1
    relevant_entries_def is_relevant_entry_def sees_field_def list_class_def
    distinct_classes distinct_fields intro: Fields.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def sees_field_def list_class_def
    distinct_classes distinct_fields intro: Fields.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add: relevant_entries_def is_relevant_entry_def subcls1)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def sees_field_def list_class_def
    distinct_classes distinct_fields intro: Fields.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def list_class_def
    distinct_classes Method_def intro: Methods.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  done
(*>*)

text {* Some abbreviations for readability *} 
abbreviation "Clist == Class list_name"
abbreviation "Ctest == Class test_name"

constdefs
  phi_makelist :: ty\<^isub>m ("\<phi>\<^sub>m")
  "\<phi>\<^sub>m \<equiv> map (\<lambda>(x,y). Some (x, y)) [ 
    (                                   [], [OK Ctest, Err     , Err     ]),
    (                              [Clist], [OK Ctest, Err     , Err     ]),
    (                                   [], [OK Clist, Err     , Err     ]),
    (                              [Clist], [OK Clist, Err     , Err     ]),
    (                     [Integer, Clist], [OK Clist, Err     , Err     ]),

    (                                   [], [OK Clist, Err     , Err     ]),
    (                              [Clist], [OK Clist, Err     , Err     ]),
    (                                   [], [OK Clist, OK Clist, Err     ]),
    (                              [Clist], [OK Clist, OK Clist, Err     ]),
    (                     [Integer, Clist], [OK Clist, OK Clist, Err     ]),

    (                                   [], [OK Clist, OK Clist, Err     ]),
    (                              [Clist], [OK Clist, OK Clist, Err     ]),
    (                                   [], [OK Clist, OK Clist, OK Clist]),
    (                              [Clist], [OK Clist, OK Clist, OK Clist]),
    (                     [Integer, Clist], [OK Clist, OK Clist, OK Clist]),

    (                                   [], [OK Clist, OK Clist, OK Clist]),
    (                              [Clist], [OK Clist, OK Clist, OK Clist]),
    (                       [Clist, Clist], [OK Clist, OK Clist, OK Clist]),
    (                               [Void], [OK Clist, OK Clist, OK Clist]),
    (                                   [], [OK Clist, OK Clist, OK Clist]),
    (                              [Clist], [OK Clist, OK Clist, OK Clist]),
    (                       [Clist, Clist], [OK Clist, OK Clist, OK Clist]),
    (                               [Void], [OK Clist, OK Clist, OK Clist])]"

lemma types_makelist [simp]: "check_types E 3 (Suc (Suc (Suc 0))) (map OK \<phi>\<^sub>m)"
(*<*)
  by (auto simp add: check_types_def phi_makelist_def JVM_states_unfold)
(*>*)

lemma wt_makelist [simp]:
  "wt_method E test_name [] Void 3 2 make_list_ins [] \<phi>\<^sub>m"
(*<*)
  apply (simp add: wt_method_def)
  apply (unfold make_list_ins_def phi_makelist_def)
  apply (simp add: wt_start_def nat_number)
  apply (simp add: wt_instr_def)
  apply clarify
  apply (drule sym)
  apply (erule_tac P="?x = ?y" in rev_mp)
  apply (elim pc_end pc_next pc_0)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def sees_field_def list_class_def
    distinct_classes intro: Fields.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def sees_field_def list_class_def
    distinct_classes intro: Fields.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def sees_field_def list_class_def
    distinct_classes intro: Fields.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def list_class_def
    distinct_classes Method_def intro: Methods.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  apply (fastsimp simp add:
    relevant_entries_def is_relevant_entry_def list_class_def
    distinct_classes Method_def intro: Methods.intros)
  apply (simp add: relevant_entries_def is_relevant_entry_def)
  done
(*>*)

lemma wf_md'E:
  "\<lbrakk> wf_prog wf_md P; 
     \<And>C S fs ms m.\<lbrakk>(C,S,fs,ms) \<in> set P; m \<in> set ms\<rbrakk> \<Longrightarrow> wf_md' P C m \<rbrakk>
  \<Longrightarrow> wf_prog wf_md' P"
(*<*)
  apply (simp add: wf_prog_def)
  apply auto
  apply (simp add: wf_cdecl_def wf_mdecl_def)
  apply fastsimp
  done
(*>*)

text {* The whole program is welltyped: *}
constdefs 
  Phi :: ty\<^isub>P ("\<Phi>")
  "\<Phi> C mn \<equiv> if C = test_name \<and> mn = makelist_name then \<phi>\<^sub>m else 
             if C = list_name \<and> mn = append_name then \<phi>\<^sub>a else []"

lemma wf_prog:
  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> E" 
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (rule wf_md'E [OF wf_struct])
  apply (simp add: E_def)
  apply clarify
  apply (fold E_def)
  apply (simp add: system_defs class_defs Phi_def)
  apply auto
  apply (simp add: distinct_classes)
  done 
(*>*)


section "Conformance"
text {* Execution of the program will be typesafe, because its
  start state conforms to the welltyping: *}

lemma "E,\<Phi> \<turnstile> start_state E test_name makelist_name \<surd>"
(*<*)
  apply (rule BV_correct_initial)
    apply (rule wf_prog)
  apply (fastsimp simp add: test_class_def distinct_classes Method_def intro: Methods.intros)
  done
(*>*)


section "Example for code generation: inferring method types"

constdefs
  test_kil :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
             ex_table \<Rightarrow> instr list \<Rightarrow> ty\<^isub>i' err list"
  "test_kil G C pTs rT mxs mxl et instr \<equiv>
   (let first  = Some ([],(OK (Class C))#(map OK pTs)@(replicate mxl Err));
        start  = OK first#(replicate (size instr - 1) (OK None))
    in  kiljvm G mxs (1+size pTs+mxl) rT instr et start)"

lemma [code]:
  "unstables r step ss = (UN p:{..<size ss}. if \<not>stable r step ss p then {p} else {})"
(*<*)
  apply (unfold unstables_def)
  apply (rule equalityI)
  apply (rule subsetI)
  apply (erule CollectE)
  apply (erule conjE)
  apply (rule UN_I)
  apply simp
  apply simp
  apply (rule subsetI)
  apply (erule UN_E)
  apply (case_tac "\<not> stable r step ss p")
  apply simp+
  done
(*>*)

constdefs
  some_elem :: "'a set \<Rightarrow> 'a"
  "some_elem == (%S. SOME x. x : S)"

lemma [code]:
"iter f step ss w =
 while (%(ss,w). w \<noteq> {})
       (%(ss,w). let p = some_elem w
                 in propa f (step p (ss!p)) ss (w-{p}))
       (ss,w)"
  by (unfold iter_def some_elem_def, rule refl)

consts_code
  "some_elem" ("hd")

lemma JVM_sup_unfold [code]:
 "JVM_SemiType.sup S m n = lift2 (Opt.sup
       (Product.sup (Listn.sup (SemiType.sup S))
         (\<lambda>x y. OK (map2 (lift2 (SemiType.sup S)) x y))))" 
(*<*)
  apply (unfold JVM_SemiType.sup_def JVM_SemiType.sl_def Opt.esl_def Err.sl_def
         stk_esl_def loc_sl_def Product.esl_def  
         Listn.sl_def upto_esl_def SemiType.esl_def Err.esl_def) 
  by simp

lemmas [code] =
  meta_eq_to_obj_eq [OF SemiType.sup_def [unfolded exec_lub_def]]
  meta_eq_to_obj_eq [OF JVM_le_unfold]
(*>*)

lemmas [code ind_set] = rtrancl_refl converse_rtrancl_into_rtrancl

lemma [code]:
  "is_refT T = (case T of NT \<Rightarrow> True | Class C \<Rightarrow> True | _ \<Rightarrow> False)"
  by (simp add: is_refT_def split add: ty.split)

lemma [code ind params: 1]: "P \<turnstile> C has_fields FDTs  \<Longrightarrow>
  map_of (map (\<lambda>((F, D), T). (F, D, T)) FDTs) F = \<lfloor>(D, T)\<rfloor> \<Longrightarrow> P \<turnstile> C sees F:T in D"
  by (auto simp add: sees_field_def)

lemma [code ind params: 1]: "P \<turnstile> C sees_methods Mm \<Longrightarrow>
  Mm M = \<lfloor>((Ts, T, m), D)\<rfloor> \<Longrightarrow> P \<turnstile> C sees M: Ts\<rightarrow>T = m in D"
  by (auto simp add: Method_def)

lemma [code]:
  "app\<^isub>i (Getfield F C, P, pc, mxs, T\<^isub>r, (T#ST, LT)) = 
    (\<exists>T\<^isub>f\<in>{T\<^isub>f. sees_field P C F T\<^isub>f C}. P \<turnstile> T \<le> Class C)"
  by auto

lemma [code]:
  "app\<^isub>i (Putfield F C, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST, LT)) = 
    (\<exists>T\<^isub>f\<in>{T\<^isub>f. sees_field P C F T\<^isub>f C}. P \<turnstile> T\<^isub>2 \<le> (Class C) \<and> P \<turnstile> T\<^isub>1 \<le> T\<^isub>f)" 
  by auto

lemma [code]:
  "app\<^isub>i (Invoke M n, P, pc, mxs, T\<^isub>r, (ST,LT)) =
    (n < length ST \<and> 
    (ST!n \<noteq> NT \<longrightarrow>
      (case ST!n of
         Class C \<Rightarrow> (\<exists>(Ts, T, m, D)\<in>{(Ts, T, m, D). Method P C M Ts T m D}. P \<turnstile> rev (take n ST) [\<le>] Ts)
       | _ \<Rightarrow> False)))"
  by (fastsimp split add: ty.split_asm)

declare field_def2 [code ind]

code_module BV
contains
  test1 = "test_kil E list_name [Class list_name] Void 3 0
    [(Suc 0, 2, NullPointer, 7, 0)] append_ins"
  test2 = "test_kil E test_name [] Void 3 2 [] make_list_ins"
  test3 = "\<phi>\<^sub>a"
  test4 = "\<phi>\<^sub>m"

ML {* if BV.test1 = map BV.OK BV.test3 then () else error "wrong result" *}
ML {* if BV.test2 = map BV.OK BV.test4 then () else error "wrong result" *}

end
