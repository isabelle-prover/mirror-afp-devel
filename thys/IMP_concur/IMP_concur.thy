chapter\<open>\<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>-A Shallow Embedding in HOL-CSP\<close>

theory IMP_concur
imports "HOL-CSPM" (* changeset 16909:83221a878a3a, 28.8.26 *) 

begin

section\<open>Introduction\<close>

text\<open>
\<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> is intended to provide a more common (though still theoretic)
programming-language aspect to CSP, and could be an interesting object
of study in itself. This thin layer over HOL-CSP establishes a link 
between programming languages and process-algebras, a link that had already
been present in the influential OCCAM language.

\<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> comprises the standard elements of the IMP - language (\<open>SKIP\<close>, \<open>assignment\<close>,
\<open>IF _ THEN _ ELSE\<close>, \<open>WHILE _ DO _\<close> and the sequential composition \<open>_ ; _\<close>), plus 
the new features:
   \<^enum> semaphores with \<open>lock\<close> and \<open>unlock\<close>, and
   \<^enum> thread-global shared variables accessible 
     via \<open>LOAD\<close> and \<open>STORE\<close> operations.

This file contains:
   \<^enum> the abstract and concrete syntax of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>
   \<^enum> bricks-specifications for semaphores and global shared variables,
   \<^enum> a denotational semantics of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> converting \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>-program 
     systems into HOL-CSPM, and
   \<^enum> some examples and tests.

The general theory should be developed elsewhere; this sample file shows the 
global construction principle of a combined semantics.\<close>


section\<open>The Syntax of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>\<close>

type_synonym SV = string  \<comment> \<open>Shared Variables\<close>
type_synonym V  = string  \<comment> \<open>(Thread-)Local Variables\<close>
type_synonym MV = int     \<comment> \<open>Mutual exclusion variables (MUTEX ids)\<close>

type_synonym D = int

type_synonym "\<sigma>" = \<open>V \<Rightarrow> D\<close>

type_synonym "E\<^sub>a\<^sub>r\<^sub>i\<^sub>t\<^sub>h" = \<open>\<sigma> \<Rightarrow> D\<close>
type_synonym "E\<^sub>b\<^sub>o\<^sub>o\<^sub>l"  = \<open>\<sigma> \<Rightarrow> bool\<close>
type_synonym "F"     = "\<sigma> \<Rightarrow> \<sigma>"

datatype com = SKIP
             | assign  V E\<^sub>a\<^sub>r\<^sub>i\<^sub>t\<^sub>h       (" _ := _" [90,90]80)
             | seq     com com       (infixr ";" 78)
             | cond   "E\<^sub>b\<^sub>o\<^sub>o\<^sub>l" com com ("IF (_)/ THEN (_)/ ELSE (_)/" 
                                               [0,0,79]79)
             | while  "E\<^sub>b\<^sub>o\<^sub>o\<^sub>l" com     ("WHILE (_)/ DO (_)" [0,80]80)
             | call    F

             | STOP
             | lock    MV
             | unlock  MV            
             | send    E\<^sub>a\<^sub>r\<^sub>i\<^sub>t\<^sub>h SV      ("STORE _ TO  _" [90,90]80)              
             | rec     V SV          ("LOAD _ FROM _" [90,90]80)


text\<open>Note that it is straight forward to formulate the assert primitive in \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>:\<close>

definition assert where \<open>assert E \<equiv> IF E THEN SKIP ELSE STOP \<close>

text\<open>... which reduces the checking of assertions to the proof of deedlock-freeness. \<close>

text\<open>Two (non-sensical) example threads:\<close>

definition Thread1 where
      \<open> Thread1 \<equiv> SKIP ; 
                  ''a'' :=  (\<lambda>\<sigma>. 1 + 2); 
                  IF (\<lambda>\<sigma>. \<sigma> ''d'' > 3) THEN lock 4 ELSE lock 3;  
                  WHILE (\<lambda>\<sigma>. \<sigma> ''e'' > 3) DO lock 4 ;  
                  STORE (\<lambda>\<sigma>. \<sigma> ''d'' + 1) TO ''b''; 
                  LOAD ''a'' FROM  ''b''; 
                  unlock 3
      \<close>

definition Thread2 where
      \<open> Thread2 \<equiv> SKIP ; 
                  ''a'' :=  (\<lambda>\<sigma>. 1 + 2); 
                  IF (\<lambda>\<sigma>. \<sigma> ''d'' > 3) THEN lock 4 ELSE lock 3;  
                  WHILE (\<lambda>\<sigma>. True) DO lock 4 ;  
                  STORE (\<lambda>\<sigma>. \<sigma> ''d'' + 1) TO ''b''; 
                  LOAD ''a'' FROM  ''b''; 
                  unlock 3
      \<close>

thm Thread2_def
definition Thread3 where 
  "Thread3 = SKIP ;
             ( ''var_local'' := (\<lambda>\<sigma>. 4 + 42) ;
             ( ''test'' := (\<lambda>\<sigma>. 2 * \<sigma> ''var_local'') ;
             ( ''test'' := (\<lambda>\<sigma>. \<sigma> ''test'' + 3) ;
              IF (\<lambda>\<sigma>. \<sigma> ''x''>5)
              THEN WHILE (\<lambda>\<sigma>. \<sigma> ''x'' >5) DO  ''test'' := (\<lambda>\<sigma>. \<sigma> ''test'' - 3)
              ELSE  ''test'' := (\<lambda>\<sigma>. \<sigma> ''test'' + 3))))"

ML\<open>val Thread2_term = \<^term>\<open>Thread2\<close>;
   val _ $ _ $ Thread2_rhs = Thm.concl_of @{thm Thread2_def}\<close>


section\<open>Events, States and Semaphores ("Bricks").\<close>

text\<open>The common set of events in a thread-system\<close>

datatype evs = lock int | unlock int | read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l SV D | upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l  SV D 
                                     | read\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l SV D | update\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l SV D 

definition LOCKS where \<open>LOCKS \<equiv> range lock \<union> range unlock\<close>
definition GVARS where \<open>GVARS \<equiv> {e. \<exists>x. \<exists>y. e = read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l x y } \<union> 
                                 {e. \<exists>x. \<exists>y. e = upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l x y }\<close>

lemma L1 [simp]: \<open>lock n \<notin> GVARS\<close>   unfolding GVARS_def by auto
lemma L2 [simp]: \<open>lock n \<in> LOCKS\<close>   unfolding LOCKS_def by auto
lemma L3 [simp]: \<open>unlock n \<notin> GVARS\<close> unfolding GVARS_def by auto
lemma L4 [simp]: \<open>unlock n \<in> LOCKS\<close> unfolding LOCKS_def by auto

lemma L5 [simp]: \<open>read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l n m \<notin> LOCKS\<close>   unfolding LOCKS_def GVARS_def by auto
lemma L6 [simp]: \<open>read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l n m \<in> GVARS\<close>   unfolding LOCKS_def GVARS_def by auto
lemma L7 [simp]: \<open>upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l n m \<notin> LOCKS\<close>    unfolding LOCKS_def GVARS_def by auto
lemma L8 [simp]: \<open>upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l n m \<in> GVARS\<close>    unfolding LOCKS_def GVARS_def by auto

lemma L9 [simp]: \<open>read\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l n m \<notin> LOCKS\<close>    unfolding LOCKS_def GVARS_def by auto
lemma L10[simp]: \<open>read\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l n m \<notin> GVARS\<close>    unfolding LOCKS_def GVARS_def by auto
lemma L11[simp]: \<open>update\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l n m \<notin> LOCKS\<close>  unfolding LOCKS_def GVARS_def by auto
lemma L12[simp]: \<open>update\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l n m \<notin> GVARS\<close>  unfolding LOCKS_def GVARS_def by auto



subsection\<open>A simple Model of a Semaphore Family\<close>
(* (this should be a locale, see HOL-CSP-Bricks.) *)
(* datatype   sema_evs = lock int | unlock int *)


definition semaphore :: \<open>int \<Rightarrow> evs process\<close>
  where   \<open>semaphore \<equiv> \<mu> X. (\<lambda>n. lock n \<rightarrow> unlock n \<rightarrow> X n)\<close>

lemma sema_rec : \<open>semaphore n = lock n \<rightarrow> unlock n \<rightarrow> semaphore n\<close>
  by (subst cont_process_rec[OF semaphore_def[THEN meta_eq_to_obj_eq]]) simp_all

subsection\<open>A simple Model of a Global Variable Family\<close>

definition global_vars :: \<open>\<sigma> \<Rightarrow> SV \<Rightarrow> evs process\<close> 
  where   \<open>global_vars \<equiv> \<mu> X.   (\<lambda> \<sigma>. (\<lambda> id.  ((read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l id)\<^bold>!(\<sigma> id) \<rightarrow> X \<sigma> id ) 
                                            \<box> ((upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l id)\<^bold>?v \<rightarrow> X (\<sigma>(id := v)) id )))\<close>


lemma global_vars_rec : \<open>global_vars \<sigma> n =    ((read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l n)\<^bold>!(\<sigma> n) \<rightarrow> global_vars \<sigma> n) 
                                           \<box> ((upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l n)\<^bold>?v \<rightarrow> global_vars (\<sigma>(n := v)) n)\<close> 
  by (subst cont_process_rec[OF global_vars_def[THEN meta_eq_to_obj_eq]]) simp_all


subsection\<open>A simple Model of a Local Variable Family (Optional)\<close>

definition local_vars :: " \<sigma> \<Rightarrow> SV \<Rightarrow> evs process" 
  where   \<open>local_vars \<equiv> \<mu> X.   (\<lambda> \<sigma>. (\<lambda> id.  ((read\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l id)\<^bold>!(\<sigma> id) \<rightarrow> X \<sigma> id) 
                                           \<box> ((update\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l id)\<^bold>?v \<rightarrow> X (\<sigma>(id := v)) id )))\<close>

lemma local_vars_rec : \<open>local_vars \<sigma> n =     ((read\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l n)\<^bold>!(\<sigma> n) \<rightarrow> local_vars \<sigma> n) 
                                           \<box> ((update\<^sub>l\<^sub>o\<^sub>c\<^sub>a\<^sub>l n)\<^bold>?v \<rightarrow> local_vars (\<sigma>(n := v)) n)\<close> 
  by (subst cont_process_rec[OF local_vars_def[THEN meta_eq_to_obj_eq]]) simp_all


section\<open>Denotational Semantics of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>\<close>

text\<open>The denotational semantics of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> is a straight recursive interpretation 
in the domain of HOL-CSP processes. Thread local variables were represented in this 
presentation by updates on a thread-local environment, not by interactions with processes.
The recursive definition of the semantic function fits on a post-card:\<close>

fun Sem\<^sub>0 :: "com \<Rightarrow> (\<sigma> \<Rightarrow> evs  process) \<Rightarrow> \<sigma> \<Rightarrow> evs process" 
  where "Sem\<^sub>0 SKIP C                  = C" 
       |"Sem\<^sub>0 (x := E) C              = (\<lambda> \<sigma>. C (\<sigma>(x := E \<sigma>)))"
       |"Sem\<^sub>0 (P ; Q) C               = (Sem\<^sub>0 P (Sem\<^sub>0 Q C))" 
       |"Sem\<^sub>0 (IF E THEN C1 ELSE C2) C= (\<lambda> \<sigma>. if E \<sigma> 
                                              then Sem\<^sub>0 C1 C \<sigma> 
                                              else Sem\<^sub>0 C2 C \<sigma>)"
       |"Sem\<^sub>0 (WHILE E DO B) C        = (\<mu> X. (\<lambda> \<sigma>. if E \<sigma> 
                                                    then Sem\<^sub>0 B X \<sigma> 
                                                    else C \<sigma>))"
       |"Sem\<^sub>0 (call F) C              = (\<lambda> \<sigma>. C (F \<sigma>))"
       |"Sem\<^sub>0 (com.STOP) C            = (\<lambda> \<sigma>. Constant_Processes.STOP)"
       |"Sem\<^sub>0 (com.lock n) C          = (\<lambda> \<sigma>. evs.lock n \<rightarrow> C \<sigma>)"
       |"Sem\<^sub>0 (com.unlock n) C        = (\<lambda> \<sigma>. evs.unlock n  \<rightarrow> C \<sigma>)"
       |"Sem\<^sub>0 (STORE E TO X\<^sub>g\<^sub>l\<^sub>o) C      = (\<lambda> \<sigma>. upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l X\<^sub>g\<^sub>l\<^sub>o (E \<sigma>) \<rightarrow> C \<sigma>)"
       |"Sem\<^sub>0 (LOAD X\<^sub>l\<^sub>o\<^sub>c FROM X\<^sub>g\<^sub>l\<^sub>o) C   = (\<lambda> \<sigma>. (read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l X\<^sub>g\<^sub>l\<^sub>o)\<^bold>?x 
                                                  \<rightarrow> C(\<sigma>(X\<^sub>l\<^sub>o\<^sub>c:=x)))"
(* Fascinating: We don't need the sequential composition of CSP in this construction;
   continuation passing is sufficient. *)

definition initial_state :: \<sigma> (\<open>\<sigma>\<^sub>0\<close>)
  where   \<open>\<sigma>\<^sub>0 \<equiv> (\<lambda>_. 0::int)\<close>

definition some_state :: \<sigma> (\<open>\<sigma>\<^sub>e\<^sub>x\<^sub>p\<^sub>l\<close>)
  where   \<open>\<sigma>\<^sub>e\<^sub>x\<^sub>p\<^sub>l v \<equiv> if v = ''a'' then 3 else 0\<close>

text\<open>In case that an \<^verbatim>\<open>assume\<close>-primitive on initial states has to be modeled
(the usual contruct for modeling preconditions), this can be done by the 
Hilbert-Choice operator \<^term>\<open>SOME \<sigma>. E\<close> on initial local and global states. \<close>


definition Sem         where \<open>Sem Thread \<equiv> Sem\<^sub>0 Thread (\<lambda>_. Skip) \<sigma>\<^sub>0\<close>  
   \<comment> \<open>final continuation: \<^term>\<open>Skip\<close>, execution starts with initialized local vars
       for simplicity. \<close>

section\<open>A Thread-System as HOL-CSPM-Architecture\<close>

text\<open>An example of a global \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>-System with 2 threads, 3 global variables and 4 semaphores:\<close>

definition\<open>Thread3_sem \<equiv> ( \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [''a'',''b'',''c''].  global_vars \<sigma>\<^sub>0 idx  
                           |||
                           \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [1..4]. semaphore idx )
          
                           ||
            
                           (Sem Thread1 ||| Sem Thread2)
                           \<close>


ML\<open>(* ... and this reads at the term-level as follows : *)
   val _ $ _ $ temp= Thm.concl_of @{thm Thread3_sem_def}  
   val temp2= \<^term>\<open>\<^bold>|\<^bold>|\<^bold>| idx \<in># mset [''a'',''b'',''c''].  global_vars \<sigma>\<^sub>0 idx\<close>
  \<close>

text\<open>Tests:\<close>

lemma Thread2_sem : 
  "Sem(Thread2) =  evs.lock 3 \<rightarrow> (\<mu> x. (\<lambda>\<sigma>::\<sigma>. evs.lock 4 \<rightarrow> x \<sigma>)) \<sigma>\<^sub>e\<^sub>x\<^sub>p\<^sub>l"
  unfolding Thread2_def Sem_def some_state_def initial_state_def
  by (simp add: fun_upd_def)

(* symbolic evaluation : *)
schematic_goal K : "Thread3_sem = ?X"
  unfolding Thread3_sem_def Sem_def
  unfolding Thread1_def Thread2_def
   apply(rule trans)
   apply (simp add: List.upto.simps cong: HOL.if_cong)
  by (rule refl)
  


lemma Thread3_sem : 
    \<open> Thread3_sem = ((global_vars \<sigma>\<^sub>0 ''a'' ||| (global_vars \<sigma>\<^sub>0 ''b'' ||| global_vars \<sigma>\<^sub>0 ''c'')) 
                     ||| (semaphore 1 ||| (semaphore 2 ||| (semaphore 3 ||| semaphore 4))))
                    || 
                    ((evs.lock 3 \<rightarrow> (\<mu> x. (\<lambda>\<sigma>. if 3 < \<sigma> ''e'' 
                                               then evs.lock 4 \<rightarrow> x \<sigma>
                                               else upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l ''b'' (\<sigma> ''d'' + 1)
                                                     \<rightarrow> read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l ''b''\<^bold>?x 
                                                     \<rightarrow> evs.unlock 3 \<rightarrow> Skip))
                       ((\<lambda>_. 0::int)(''a'' := 3::int))) 
                     ||| 
                     (evs.lock 3 \<rightarrow> (\<mu> x. (\<lambda>\<sigma>. evs.lock 4 \<rightarrow> x \<sigma>)) ((\<lambda>_. 0::int)(''a'':= 3::int)))) 
    \<close>
  unfolding Thread3_sem_def Sem_def Thread1_def Thread2_def initial_state_def
  by (simp add: List.upto.simps cong: HOL.if_cong)
  

(* A look into the term structure *)
ML\<open>
val x =HOLogic.dest_eq (HOLogic.dest_Trueprop ( Thm.concl_of  @{thm K})) ; 
val y = @{thm Thread3_sem} |> Thm.concl_of 
                           |> HOLogic.dest_Trueprop 
                           |> HOLogic.dest_eq
\<close>

section\<open>A Semantic Corner-Case of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>\<close>

text\<open>We study the case of three global variables and 4 locks 
and a computation that spends its time in an infinite loop without
communicating. (The result would be the same if inside the loop,
only compuations on local variables were done.\<close>

definition Thread4 where 
  "Thread4 = WHILE (\<lambda>\<sigma>. True) DO  SKIP"

definition Thread4_sem where 
"Thread4_sem \<equiv> ( \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [''a'',''b'',''c''].  global_vars \<sigma>\<^sub>0 idx  
                  |||
                  \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [1..4]. semaphore idx )
                 
                ||
   
                  (Sem Thread4)"

text\<open>The following theory shows that this type of programs collapses to \<^term>\<open>\<bottom>\<close>. \<close>
theorem bang : \<open>Thread4_sem = \<bottom>\<close>
  unfolding Thread4_sem_def Thread4_def Sem_def
  by (simp add: List.upto.simps Fixrec.fix_id cong: HOL.if_cong) (* Eh bim ! *)


section\<open>Another Semantic Corner-Case: Deadlock\<close>

text\<open>For simplicity of the subsequent proof, we model a system without global variables:\<close>

definition Thread5 where 
  "Thread5 = WHILE (\<lambda>\<sigma>. True) DO (com.lock 1)"

definition Thread5_sem where 
"Thread5_sem \<equiv>  ( \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [1..4]. semaphore idx )  
                 
                  ||
 
                   Sem Thread5"

lemma Thread5_while_rec : "(\<mu> x::'b \<Rightarrow> evs process. (\<lambda>\<sigma>. evs.lock (1::int) \<rightarrow> x \<sigma>)) A 
             = evs.lock 1 \<rightarrow> (\<mu> x. (\<lambda>\<sigma>. evs.lock (1::int) \<rightarrow> x \<sigma>)) A"
  by(subst cont_process_rec[where P = \<open>(\<mu> x. (\<lambda>\<sigma>. evs.lock (1::int) \<rightarrow> x \<sigma>))\<close>, OF refl]) simp_all 

text\<open>This process system will deadlock after the first attempt to get \<^term>\<open>com.lock 0\<close>.
This can be formally proven in HOL-CSP by stating: 

@{cartouche [indent=10] \<open>\<not> deadlock_free Thread5_sem\<close>}.

The proof is shown in the following subsection.
\<close>

subsection\<open>A Technique to rewrite Interleaves to MPrefixes\<close>

text\<open>Note that the following description is not necessarily the most effective manner to establish
deadlock-freeness via fixed-point induction; it is  clear that it will not scale up to large
process systems. (For a more powerful and automated approach, we refer to the handling via Proc-Omata 
\cite{BallenghienW24} or the approach in \cite{ITP2026}). Our proceeding has, though, the advantage 
to use only very basic means and is therefore a self-contained demonstration.
\<close>

text\<open>A key obstacle for the establishment of deadlock-properties is that we need to bring
both sides of the parallel composition operator \<open>_ || _\<close> into the form \<^term>\<open>Mprefix A P\<close> in order
to apply the rule:

 @{thm [indent=10, display] Mprefix_Par_Mprefix} 

The  \<^term>\<open>Mprefix\<close>-terms are typically
quite large if-then-else cascades representing some form of decision diagram that collapse to 
small terms after synchronization.\<close>

lemma inter2Mprefix1: 
  assumes  "a \<noteq> b" 
  shows "(a \<rightarrow> P ||| b \<rightarrow> Q) 
          = Mprefix {a,b} (\<lambda>x. if x = a then (P ||| b \<rightarrow> Q) 
                                        else (a \<rightarrow> P) ||| Q )"
  apply(simp add:write0_Inter_write0)
  by(subst (3) write0_def,subst write0_Det_Mprefix,simp add: assms)


lemma inter2Mprefix2: 
  assumes * : "a \<notin> A"
  shows "((a \<rightarrow> P) ||| Mprefix A Q) 
          = Mprefix (insert a A) (\<lambda>x. if x = a then (P ||| Mprefix A Q) 
                                               else ((a \<rightarrow> P) ||| Q x) )"
  apply(subst write0_def,simp add: Mprefix_Inter_Mprefix)
  apply(subst Mprefix_Det_Mprefix, simp add: assms)
  by(fold write0_def, simp)

lemma inter2Mprefix3:
  "a \<noteq> b \<Longrightarrow> ((a \<rightarrow> P a) \<box> (b \<rightarrow> Q b)) 
             = Mprefix {a,b} (\<lambda>x. if x= a then P a else Q b)"
  apply(simp add: Mprefix_singl[symmetric] )
  by (smt (verit, ccfv_threshold) Mprefix_Un_distrib Mprefix_singl 
          Un_insert_right insert_commute sup_bot.right_neutral)

text\<open>After these generalities, we turn to the core lemmas relevant to the subsequent proofs.
They construct compact normalforms for states (represented by CSPM-expressions) linked
by the events \<^term>\<open>evs.lock 1\<close> and  \<^term>\<open>evs.unlock 1\<close>. They proceed by blowing both sides
up into a lower-level normalform in which their equality can be demonstrated.\<close>

lemma contractMultiInter1 : 
  "MultiInter (mset [1..4]) semaphore || evs.lock 1 \<rightarrow> P 
   =  evs.lock 1 \<rightarrow> ((evs.unlock 1 \<rightarrow> semaphore 1  ||| MultiInter (mset [2..4]) semaphore) || P)"
  (is "?lhs = evs.lock 1 \<rightarrow> ?rhs")
proof -
  have * : "?lhs = evs.lock 1 \<rightarrow>
                    ((evs.unlock 1 \<rightarrow> semaphore 1 
                     ||| \<box>x\<in>{evs.lock 2, evs.lock 3, evs.lock 4}
                                \<rightarrow> (if x = evs.lock 2
                                    then evs.unlock 2 \<rightarrow> semaphore 2 
                                         ||| 
                                         \<box>x\<in>{evs.lock 3, evs.lock 4}
                                               \<rightarrow> (if x = evs.lock 3 
                                                   then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                                   else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                                    else semaphore 2 
                                         ||| 
                                         (if x = evs.lock 3 
                                          then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                          else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4))) || P)"
    (is "_ = evs.lock 1 \<rightarrow> ?rhs'")
           apply(rule trans)
           apply(simp add: List.upto.simps)
           apply(subst sema_rec[where n=\<open>1\<close>],
                 subst sema_rec[where n=\<open>2\<close>],
                 subst sema_rec[where n=\<open>3\<close>],
                 subst sema_rec[where n=\<open>4\<close>]) 
           apply(rule trans)
            apply(simp add: inter2Mprefix1 inter2Mprefix2)
             apply(simp add: sema_rec[where n=\<open>1\<close>,symmetric] 
                             sema_rec[where n=\<open>2\<close>,symmetric] 
                             sema_rec[where n=\<open>3\<close>,symmetric] 
                             sema_rec[where n=\<open>4\<close>,symmetric] 
                        cong: HOL.if_cong)
             apply(subst write0_def[THEN meta_eq_to_obj_eq, of"evs.lock (1::int)"])
             by(subst Mprefix_Par_Mprefix, simp add: Mprefix_singl) \<comment> \<open>et bang!\<close>
  define X where "X = ?rhs'"
  have ** : "?rhs = X" 
           apply(subst write0_def[THEN meta_eq_to_obj_eq])
           apply(simp add: List.upto.simps)  
           apply(subst sema_rec[where n=\<open>1\<close>],subst sema_rec[where n=\<open>2\<close>],
                 subst sema_rec[where n=\<open>3\<close>],subst sema_rec[where n=\<open>4\<close>]) 
           apply(simp add: inter2Mprefix1 inter2Mprefix2) 
           by (metis X_def sema_rec Mprefix_singl)
  show ?thesis
    by (metis * ** X_def)
qed


lemma contractMultiInter2: 
      "  ((evs.unlock 1 \<rightarrow> semaphore 1  ||| MultiInter (mset [2..4]) semaphore) 
         ||  evs.lock 1 \<rightarrow> P) 
       = Constant_Processes.STOP"
         (is "(?R || ?S) = _")
proof - 
  have 1 : "?R = \<box>x\<in>{evs.unlock 1, evs.lock 2, evs.lock 3, evs.lock 4}
       \<rightarrow> (if x = evs.unlock 1
           then semaphore 1
                ||| \<box>x\<in>{evs.lock 2, evs.lock 3, evs.lock 4}
                          \<rightarrow> (if x = evs.lock 2
                              then evs.unlock 2 \<rightarrow> semaphore 2
                              ||| \<box>x\<in>{evs.lock 3, evs.lock 4}
                                      \<rightarrow> (if x = evs.lock 3 
                                          then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                          else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                              else semaphore  2
                                   ||| (if x = evs.lock 3 
                                        then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                        else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4))
           else evs.unlock 1 \<rightarrow> semaphore 1
               ||| (if x = evs.lock 2
                    then evs.unlock 2 \<rightarrow> semaphore 2
                         ||| \<box>x\<in>{evs.lock 3, evs.lock 4}
                             \<rightarrow> (if x = evs.lock 3 then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                    else semaphore 2 
                         ||| (if x = evs.lock 3
                              then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                              else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)))"
         apply(simp add: List.upto.simps)
         apply(subst sema_rec[where n=\<open>1\<close>],subst sema_rec[where n=\<open>2\<close>],
               subst sema_rec[where n=\<open>3\<close>],subst sema_rec[where n=\<open>4\<close>]) 
         apply(simp add: inter2Mprefix1 inter2Mprefix2)
         by(simp add: sema_rec[where n=\<open>1\<close>,symmetric] 
                      sema_rec[where n=\<open>2\<close>,symmetric] 
                      sema_rec[where n=\<open>3\<close>,symmetric] 
                      sema_rec[where n=\<open>4\<close>,symmetric] 
                 cong: HOL.if_cong)
  show ?thesis
    apply(subst(2) write0_def[THEN meta_eq_to_obj_eq])
    apply(subst 1)
    by (simp add: Mprefix_Par_Mprefix)
qed


text\<open>After these preparatory lemmas, the path to the deadlock is straight-forward:
it proceeds by unroling the while-loop two times; unfolding
\<^term>\<open>semaphore 1\<close> and its fixpoint two times; simplifying to \<^term>\<open>STOP\<close>
since \<^term>\<open>lock 0\<close> and \<^term>\<open>unlock 0\<close> are forced  to be synchronized, 
propagating this result to the refinement level and reduce it to a contradiction
of the refinement statement with the \<^term>\<open>DF UNIV\<close> process.
We skip the formal proof here since it is out of scope of this presentation. \<close>


theorem bullocks: \<open>\<not> deadlock_free Thread5_sem\<close>
  unfolding Thread5_sem_def Sem_def Thread5_def
proof - 
  show \<open>\<not> deadlock_free
               ( MultiInter (mset [1..4]) semaphore
                || Sem\<^sub>0 (WHILE \<lambda>\<sigma>. True DO com.lock 1) (\<lambda>_. Skip) \<sigma>\<^sub>0)\<close>
                (is \<open>\<not> deadlock_free (?SEMA || ?P )\<close>)
  proof - 
    have 1 : \<open>?P = evs.lock 1 \<rightarrow> ?P\<close> using Thread5_while_rec by auto
    have 2 : \<open>(?SEMA || evs.lock 1 \<rightarrow> ?P) 
              =  evs.lock 1 \<rightarrow> ((evs.unlock 1 \<rightarrow> semaphore 1  
                                ||| MultiInter (mset [2..4]) semaphore) || ?P)\<close>
             (is "?lhs = evs.lock 1 \<rightarrow> ?R'")
      by (metis contractMultiInter1)
    have 3 : \<open>(\<not> deadlock_free Thread5_sem) = (\<not> deadlock_free ?R')\<close>
      by (metis 1 2 Sem_def Thread5_def Thread5_sem_def deadlock_free_write0_iff)
    have 4: \<open>?R' = Constant_Processes.STOP\<close> 
      by (metis 1 contractMultiInter2)
    show ?thesis
      using 3 4 Sem_def Thread5_def Thread5_sem_def non_deadlock_free_STOP by auto
  qed
qed


text\<open>This proof can be drastically shortened / automatized if we would use a more advanced 
background theory of HOL-CSP, for example:\<close>

term\<open>Initials Q \<subseteq> ev ` S 
     \<Longrightarrow> Initials Q \<inter> ev ` T = {} 
     \<Longrightarrow>  ((P \<box> Q) \<lbrakk>S\<rbrakk> (Mprefix T R)) = P \<lbrakk>S\<rbrakk> (Mprefix T R)\<close>

term\<open>\<alpha>(Q) \<subseteq> S 
     \<Longrightarrow> \<alpha>(Q) \<inter> T = {} 
     \<Longrightarrow> \<alpha>(Q) \<inter> \<alpha>(R) = {} 
     \<Longrightarrow> ((P ||| Q) \<lbrakk>S\<rbrakk> R) = P \<lbrakk>S\<rbrakk> R\<close>

term\<open>\<alpha>(Q) \<subseteq> S 
     \<Longrightarrow> \<alpha>(Q) \<inter> T = {} 
     \<Longrightarrow> Initials Q \<inter> \<alpha>((Mprefix T R)) = {} 
     \<Longrightarrow> ((P ||| Q) \<lbrakk>S\<rbrakk> (Mprefix T R)) = P \<lbrakk>S\<rbrakk> (Mprefix T R)\<close>

section\<open>Yet another Semantic Corner-Case: A Deadlock-Freeness Proof\<close>

text\<open>We slightly mofify the previous example by adding the following thread into the
architecture:\<close>

definition Thread6 where 
  "Thread6 = WHILE (\<lambda>\<sigma>. True) DO (com.unlock 1)"

lemma Thread6_while_rec : 
          "(\<mu> x::'b \<Rightarrow> evs process. (\<lambda>\<sigma>. evs.unlock (1::int) \<rightarrow> x \<sigma>)) A 
            = evs.unlock 1 \<rightarrow> (\<mu> x. (\<lambda>\<sigma>. evs.unlock (1::int) \<rightarrow> x \<sigma>)) A"
  by(subst cont_process_rec[where P = \<open>(\<mu> x. (\<lambda>\<sigma>. evs.unlock (1::int) \<rightarrow> x \<sigma>))\<close>, 
                            OF refl]) simp_all


definition Thread6_sem where 
"Thread6_sem \<equiv> ( \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [1..4]. semaphore idx )  
                 
                 ||
 
                 (Sem Thread5 ||| Sem Thread6)"

text\<open>The architecture \<^term>\<open>Thread6\<close>, however, will not deadlock, although each single thread will.
This shows that in \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> locks can mutually deblock each other and have ---
together with the global variables --- global  visibility inside the thread system.\<close>


text\<open>The statement for this claim looks as follows:\<close>

term  \<open>deadlock_free Thread6_sem\<close>  

text\<open>We will present in this theory a straight-forward proof approach (HOL-CSP has more
sophisticated and also more automatic methods than the suggested one). We need a little
background theory concerning \<^term>\<open>deadlock_free\<close>'ness here; in principle, it can be 
established via a consequence of the fixpoint induction. A complication to be tackled
is that we need a format of this induction that takes two events --- instead of just one ---
to arrive at the anchor of the induction, namely \<^term>\<open>lock\<close> and \<^term>\<open>unlock\<close>. \<close>

subsection\<open>On Coinduction for deadlock-freeness.\<close> 

text\<open>In the following, we derive the necessary deadlock-coinduction:\<close>

lemma lasso_equiv1: "DF UNIV = (\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow>  \<sqinter>a\<in>UNIV \<rightarrow> x)"
unfolding DF_def
proof(rule FD_antisym)
  have * : \<open>X = (X \<and> X)\<close> for X by simp
  show \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D (\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x)\<close>
    apply(subst *)
    apply(subst cont_process_rec[where P = \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> 
                                   and f = \<open>\<lambda>x. \<sqinter>a\<in>UNIV \<rightarrow> x\<close>],simp_all)
    apply(rule fix_ind[where F = \<open>(\<Lambda> x. \<sqinter>a\<in>UNIV \<rightarrow> x)\<close>], simp,simp) 
     apply(subst cont_process_rec[where P = \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> 
                                    and f = \<open>\<lambda>x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x\<close>], simp_all)
     apply(rule mono_Mndetprefix_FD, simp) 
    apply(subst cont_process_rec[where P = \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> 
                                       and f = \<open>\<lambda>x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x\<close>], simp_all)
    by (simp add: mono_Mndetprefix_FD)
next 
  show \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D (\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> 
    apply(rule fix_ind[where F = \<open>(\<Lambda> x. \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x)\<close>] )  
      apply (simp_all)
    apply(subst cont_process_rec[where P = \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> 
                                       and f = \<open>\<lambda>x. \<sqinter>a\<in>UNIV \<rightarrow> x\<close>], simp_all)
    apply(subst cont_process_rec[where P = \<open>(\<mu> x. \<sqinter>a\<in>UNIV \<rightarrow> x)\<close> 
                                       and f = \<open>\<lambda>x. \<sqinter>a\<in>UNIV \<rightarrow> x\<close>], simp_all)
    apply(rule mono_Mndetprefix_FD, simp) 
    by(rule mono_Mndetprefix_FD, simp) 
qed



text\<open>Here is the neccessary versions of \<^term>\<open>deadlock_free\<close>-ness induction for
cases with a lasso-length 1 and 2:\<close>
lemma deadlock_free_1_coinduct :
          \<open>    (\<And>x. x \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D P)
           \<Longrightarrow> deadlock_free (P::('\<alpha>, '\<delta>) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
  apply(rule DF_Univ_freeness[of UNIV], simp,unfold DF_def)
  by(rule fix_ind)(simp_all)
 
lemma deadlock_free_2_coinduct :
       \<open> (\<And>x. x \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> \<sqinter>a\<in>UNIV \<rightarrow> \<sqinter>a\<in>UNIV \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D P)
         \<Longrightarrow> deadlock_free (P::('\<alpha>, '\<delta>) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
  apply(rule DF_Univ_freeness[of UNIV],simp_all add: lasso_equiv1)
  by(rule fix_ind)(simp_all)

text\<open>And we need two more technical lemmas (analogously to the proofs in the previous session)
that enable us to represent the intermediate process states by compact process expressions 
in \<^verbatim>\<open>HOL-CSPM\<close>.\<close>


lemma contractMultiInter1':
  assumes \<open>evs.unlock 1 \<rightarrow> P2 = P2\<close>
  shows   \<open>MultiInter (mset [1..4]) semaphore
           || 
           \<box>x\<in>{evs.lock 1, evs.unlock 1}
              \<rightarrow> (if x = evs.lock 1 then P1 ||| evs.unlock 1 \<rightarrow> P2 else evs.lock 1 \<rightarrow> P1 ||| P2) =
           evs.lock 1 \<rightarrow>
           (   (evs.unlock 1 \<rightarrow> semaphore 1 ||| MultiInter (mset [2..4]) semaphore) 
           || (P1 ||| P2))\<close>
  (is "?lhs = evs.lock 1 \<rightarrow> ?rhs")
proof - 
   have * : "?lhs = evs.lock 1 \<rightarrow>
                    ((evs.unlock 1 \<rightarrow> semaphore 1 
                     ||| \<box>x\<in>{evs.lock 2, evs.lock 3, evs.lock 4}
                                \<rightarrow> (if x = evs.lock 2
                                    then evs.unlock 2 \<rightarrow> semaphore 2 
                                         ||| 
                                         \<box>x\<in>{evs.lock 3, evs.lock 4}
                                               \<rightarrow> (if x = evs.lock 3 
                                                   then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                                   else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                                    else semaphore 2 
                                         ||| 
                                         (if x = evs.lock 3 
                                          then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                          else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4))) 
                    || (P1 ||| evs.unlock 1 \<rightarrow> P2))"
    (is "_ = evs.lock 1 \<rightarrow> ?rhs'")
          apply(rule trans)
           apply(simp add: List.upto.simps)
          apply(subst sema_rec[where n=\<open>1\<close>],subst sema_rec[where n=\<open>2\<close>],
                subst sema_rec[where n=\<open>3\<close>],subst sema_rec[where n=\<open>4\<close>]) 
          apply(rule trans)
          apply(simp add: inter2Mprefix1 inter2Mprefix2)
          apply(simp add: sema_rec[where n=\<open>1\<close>,symmetric] 
                          sema_rec[where n=\<open>2\<close>,symmetric] 
                          sema_rec[where n=\<open>3\<close>,symmetric] 
                          sema_rec[where n=\<open>4\<close>,symmetric]
                     cong: HOL.if_cong)
          apply(subst write0_def[THEN meta_eq_to_obj_eq, of"evs.lock (1::int)"])
          by(subst Mprefix_Par_Mprefix, simp add: Mprefix_singl)
  define X where "X = ?rhs'"
  have ** : "?rhs = X" 
          apply(subst write0_def[THEN meta_eq_to_obj_eq])
          apply(simp add: List.upto.simps)  
          apply(subst sema_rec[where n=\<open>1\<close>],subst sema_rec[where n=\<open>2\<close>],
                subst sema_rec[where n=\<open>3\<close>],subst sema_rec[where n=\<open>4\<close>]) 
          apply(simp add: inter2Mprefix1 inter2Mprefix2) 
          apply(simp only: X_def) 
          by (metis sema_rec assms Mprefix_singl)
  show ?thesis
    by (metis * ** X_def)
qed


lemma contractMultiInter1'' : 
  assumes "evs.lock 1 \<rightarrow> P1 = P1"
  shows \<open>
          (evs.unlock 1 \<rightarrow> semaphore 1  ||| MultiInter (mset [2..4]) semaphore) 
        || \<box>x\<in>{evs.lock 1, evs.unlock 1}
              \<rightarrow> (if x = evs.lock 1 
                  then P1 ||| evs.unlock 1 \<rightarrow> P2 
                  else evs.lock 1 \<rightarrow> P1 ||| P2) 
        = 
          (evs.unlock 1 \<rightarrow> ((MultiInter (mset [1..4]) semaphore) 
                            || (P1  ||| P2)))
        \<close>
       (is "(?R || ?S) = evs.unlock 1 \<rightarrow> ?rhs") 
proof -
  have 1 : "?R = \<box>x\<in>{evs.unlock 1, evs.lock 2, evs.lock 3, evs.lock 4}
                 \<rightarrow> (if x = evs.unlock 1
                     then semaphore 1
                          ||| \<box>x\<in>{evs.lock 2, evs.lock 3, evs.lock 4}
                              \<rightarrow> (if x = evs.lock 2
                                  then evs.unlock 2 \<rightarrow> semaphore 2
                                       ||| \<box>x\<in>{evs.lock 3, evs.lock 4}
                                           \<rightarrow> (if x = evs.lock 3 
                                               then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                               else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                                  else semaphore  2
                                       ||| (if x = evs.lock 3 
                                            then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                            else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4))
                     else evs.unlock 1 \<rightarrow> semaphore 1
                          ||| (if x = evs.lock 2
                               then evs.unlock 2 \<rightarrow> semaphore 2
                                    ||| \<box>x\<in>{evs.lock 3, evs.lock 4}
                                        \<rightarrow> (if x = evs.lock 3 
                                            then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                            else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                               else semaphore 2 
                                    ||| (if x = evs.lock 3
                                         then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                         else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)))"
           apply(simp add: List.upto.simps)
           apply(subst sema_rec[where n=\<open>1\<close>],subst sema_rec[where n=\<open>2\<close>],
                 subst sema_rec[where n=\<open>3\<close>],subst sema_rec[where n=\<open>4\<close>]) 
           apply(simp add: inter2Mprefix1 inter2Mprefix2)
           by(simp add: sema_rec[where n=\<open>1\<close>,symmetric] 
                        sema_rec[where n=\<open>2\<close>,symmetric] 
                        sema_rec[where n=\<open>3\<close>,symmetric] 
                        sema_rec[where n=\<open>4\<close>,symmetric] 
                   cong: HOL.if_cong)
  have 2: "evs.unlock 1 \<rightarrow> ?rhs = \<box>x\<in>{evs.unlock 1} \<rightarrow> ?rhs" by (metis write0_def)
  have 3: "?rhs = \<box>x\<in>{evs.lock 1, evs.lock 2, evs.lock 3, evs.lock 4}
                    \<rightarrow> (if x = evs.lock 1
                        then evs.unlock 1 \<rightarrow> semaphore  1 
                             ||| \<box>x\<in>{evs.lock 2, evs.lock 3, evs.lock 4}
                                 \<rightarrow> (if x = evs.lock 2
                                     then evs.unlock 2 \<rightarrow> semaphore 2 
                                          ||| \<box>x\<in>{evs.lock 3, evs.lock 4}
                                              \<rightarrow> (if x = evs.lock 3 
                                                  then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                                  else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                                     else semaphore 2 
                                          ||| (if x = evs.lock 3 
                                               then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                               else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4))
                      else semaphore 1 
                           ||| (if x = evs.lock 2
                                then evs.unlock 2 \<rightarrow>  semaphore 2 
                                     ||| \<box>x\<in>{evs.lock 3, evs.lock 4}
                                         \<rightarrow> (if x = evs.lock 3 
                                             then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                             else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4)
                                else semaphore 2 
                                     ||| (if x = evs.lock 3 
                                          then evs.unlock 3 \<rightarrow> semaphore 3 ||| semaphore 4
                                          else semaphore 3 ||| evs.unlock 4 \<rightarrow> semaphore 4))) 
                        || (P1 ||| P2)"
         apply(simp add: List.upto.simps)
         apply(subst sema_rec[where n=\<open>1\<close>],subst sema_rec[where n=\<open>2\<close>],
               subst sema_rec[where n=\<open>3\<close>],subst sema_rec[where n=\<open>4\<close>]) 
         apply(simp add: inter2Mprefix1 inter2Mprefix2)
         by(simp add: sema_rec[where n=\<open>1\<close>,symmetric] 
                      sema_rec[where n=\<open>2\<close>,symmetric] 
                      sema_rec[where n=\<open>3\<close>,symmetric] 
                      sema_rec[where n=\<open>4\<close>,symmetric] 
                 cong: HOL.if_cong)
  show ?thesis
    apply(subst 1, subst 2)
    apply(subst Mprefix_Par_Mprefix, simp_all)
    apply(simp_all add: Mprefix_singl  cong: HOL.if_cong)
    apply(subst sema_rec[where n=\<open>1\<close>])
    apply(subst inter2Mprefix2, simp)
    apply(subst inter2Mprefix2, simp)
    apply(subst assms)
    apply(subst sema_rec[where n=\<open>1\<close>, symmetric])
    apply(subst 3)
    by (metis (no_types,lifting) empty_iff evs.distinct(1) insert_iff 
              inter2Mprefix2 mono_Mprefix_eq)
  qed


text\<open>And now we attack the main theorem:\<close>

theorem bullocks2 :  \<open>deadlock_free Thread6_sem\<close>  
  unfolding Thread6_sem_def Sem_def Thread5_def Thread6_def
proof - 
  show \<open>deadlock_free
               ( MultiInter (mset [1..4]) semaphore
                || (    Sem\<^sub>0 (WHILE \<lambda>\<sigma>. True DO com.lock 1) (\<lambda>_. Skip) \<sigma>\<^sub>0 
                    ||| Sem\<^sub>0 (WHILE \<lambda>\<sigma>. True DO com.unlock 1) (\<lambda>_. Skip) \<sigma>\<^sub>0))\<close>
                (is \<open>deadlock_free (?SEMA || (?P1  ||| ?P2))\<close>)
  proof -
    have 1 : \<open>?P1 = evs.lock 1 \<rightarrow> ?P1\<close> using Thread5_while_rec by auto
    have 2 : \<open>?P2 = evs.unlock 1 \<rightarrow> ?P2\<close> using Thread6_while_rec by auto
    have 3 : \<open>?P1  ||| ?P2 = \<box>x\<in>{evs.lock 1, evs.unlock 1}
                             \<rightarrow> (if x = evs.lock 1 then ?P1 ||| evs.unlock 1 \<rightarrow> ?P2
                                                   else evs.lock 1 \<rightarrow> ?P1 ||| ?P2)\<close>
             apply(subst 1, subst 2) by(subst inter2Mprefix1,simp_all)
    have 4 : \<open>(?SEMA || ...) 
              = evs.lock 1 \<rightarrow> ((evs.unlock 1 \<rightarrow> semaphore 1  ||| MultiInter (mset [2..4]) semaphore) 
                || (?P1 ||| ?P2))\<close>
             (is \<open>_ = evs.lock 1 \<rightarrow> ?P3\<close>)
             using 2 contractMultiInter1' by auto
    have 5 : \<open> (evs.unlock 1 \<rightarrow> semaphore 1  ||| MultiInter (mset [2..4]) semaphore) || (?P1|||?P2) 
              = 
               (evs.unlock 1 \<rightarrow> ((MultiInter (mset [1..4]) semaphore) || (?P1|||?P2)))\<close>
             using 1 3 contractMultiInter1'' by fastforce
    show ?thesis
      apply(rule deadlock_free_2_coinduct) 
      apply(subst 3, subst 4)
      apply(rule Mndetprefix_FD_write0[of \<open>evs.lock 1\<close>, THEN trans_FD],simp)
      apply(rule mono_write0_FD)
      apply(subst 5) 
      by (metis Mndetprefix_FD UNIV_I mono_write0_FD)
  qed
qed


section\<open>A more serious Example: An MPI Program\<close>

text\<open>The example is drawn from Steven F. Siegels paper:
``Parameterized Verification of Deterministic MPI Programs''
\<^url>\<open>https://arxiv.org/pdf/2607.18049\<close>, 2026. It addresses 
the verification of message passing programs (MPI) 
\<^footnote>\<open>Message-Passing Interface Forum. 2025. MPI: A Message-Passing
Interface Standard, Version 5.0. 
\<^url>\<open>https://www.mpi-forum.org/docs/mpi-5.0/mpi50-report.pdf\<close>.\<close>

The informal spec of the running example reads as follows:
The program \<^verbatim>\<open>cycsum\<close> is a cyclic sum reduction to all processes. Each
process stores a int number in \<open>x\<close>, then repeatedly sends to
its left, receives from its right, and adds the received value to
sum. At the end, each process holds the sum of the original
array \<open>A\<close> of values.

A bit more formally, this reads as follows:
@{cartouche [indent=10, display]
\<open>1  param A;
2  var i, x, sum, left, right;
3  assume isRealArray(A,NP) \<and> x = A[pid];
4  left := (pid + NP−1)%NP;
5  right := (pid + 1)%NP;
6  i := 1;
7  sum := x;
8  while ( i < NP ) {
9     send x to left;
10    recv x from right;
11    sum := sum + x;
12    x := x+1;
13 }
14 assert sum = \<Sigma>\<^sup>N\<^sup>P\<^sup>−\<^sup>1\<^sub>i\<^sub>=\<^sub>0 A[i];\<close>}

Note that this is a conceptual notation. The full fledged proof in Frama-C
involves several transformations and an unverfied VCG in the tool-chain; however, it
offers automated proofs of the  program code annotated by assertions, which 
comprises 17 pages of dense Frama-C code. 

Our modeling in \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> reads as follows:\<close> 

consts NP:: int \<comment> \<open>Parameter of spec as unspecified constant\<close>

consts array :: \<open>string \<times> int \<Rightarrow> string\<close> 
                \<comment> \<open>array-name + offset :
                    the only thing we need to know: array is injective.\<close>
consts array_offset :: \<open>string \<times> int \<Rightarrow> int\<close>
                \<comment> \<open>the only thing we need to know: \<open>array_offset(array(X,i)) = i\<close>.\<close>

term\<open>[1..N]\<close>
definition sums where  \<open>sums A = fold (+) A (0::int) \<close>

definition Thread7 where
\<open>Thread7 pid A = ( ''left''  := (\<lambda>\<sigma>. (pid + NP - 1) mod NP)) ;
                 ( ''right'' := (\<lambda>\<sigma>. (pid + 1) mod NP)) ;
                 ( ''i''     := (\<lambda>\<sigma>. 1)) ;
                 com.lock pid;
                 LOAD ''x'' FROM array(''A'',pid);
                 com.unlock pid ;
                 ( ''sum''     := (\<lambda>\<sigma>. \<sigma> ''x'')) ;
                 WHILE (\<lambda>\<sigma>. \<sigma> ''i'' < NP) DO
                      (com.lock ((pid - 1 + NP) mod NP);
                       STORE (\<lambda>\<sigma>. \<sigma> ''x'') TO (array(''A'',(pid - 1 + NP) mod NP));
                       com.unlock ((pid - 1 + NP) mod NP) ;
                       com.lock ((pid + 1) mod NP);
                       LOAD ''x'' FROM array(''A'',(pid + 1) mod NP);
                       com.unlock ((pid + 1) mod NP);
                       (''sum'' := (\<lambda>\<sigma>. \<sigma> ''sum'' + \<sigma> ''x''));
                       (''i'' := (\<lambda>\<sigma>. \<sigma> ''i'' + 1))
                      );
                  assert (\<lambda>\<sigma>. \<sigma> ''sum'' = sums A)
\<close>

text\<open>Some remarks: we assume that the \<open>send\<close> and \<open>recv\<close> semantics of the
above informal notation implies an implicit lock-unlock mechanism  of these
global variables. Moreover, the notation is not quite consequent: while MPI programs
are explicitely designed for fixed architectures (in our case: a ring), the notation
implies access to the local variables which could be modified. In our example \<^verbatim>\<open>cycsum\<close>,
\<open>left\<close> and \<open>right\<close> are constants which have obviously been introduced just to increase
readability. The assertion syntax is, as common in PL-annotation languages, a mixture
of logical variables and program variables which are syntactically identified: the array \<open>A\<close> is
referring to the \<^emph>\<open>content\<close> of the state of the array \<open>A\<close>. This has to be made explicit
in the correctness statement.
\<close>


definition Thread7_sem where 
"Thread7_sem A A' \<equiv> 
          ( \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [''a'',''b'',''c''].  global_vars \<sigma>\<^sub>0 idx  
            |||
            \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [1..4]. semaphore idx )  
                 
          ||

          ( \<^bold>|\<^bold>|\<^bold>| idx \<in># mset [1..NP]. semaphore idx )"

text\<open>... where \<open>A'\<close>, the array-cell-environment, should be set to its content \<open>A\<close>: 
     \<open>A'(array(''A'',idx)) = A!(idx-1)\<close> for all idx in \<open>[1..NP]\<close>. 
     See remark on the difference between array and its content above.\<close>

text\<open>Again, the functional correctness proof boils down to a deadlock-freeness proof:\<close>

theorem correct: 
  assumes \<open>\<forall> i \<in> set[1..NP]. A'(array(''A'',idx)) = A!(nat(idx-1))\<close> 
   and    \<open>length A = nat NP\<close>
  shows   \<open>deadlock_free (Thread7_sem A A')\<close>
  unfolding deadlock_free_def Thread7_sem_def Sem_def Thread7_def
  oops

text\<open>We consider a formal proof here as out of scope.\<close>


section\<open>An Architectural Extension: Parameterized Threads\<close>

text\<open>With a tiny bit of tinkering, we can extend the language \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> to a language
allowing to express dynamic calculations of architectural connections:\<close>

type_synonym "LV\<^sub>e\<^sub>x\<^sub>p\<^sub>r"  = \<open>\<sigma> \<Rightarrow> V\<close>       \<comment> \<open>Local Variable Expr\<close>
type_synonym "SV\<^sub>e\<^sub>x\<^sub>p\<^sub>r"  = \<open>\<sigma> \<Rightarrow> MV\<close>      \<comment> \<open>Semaphore Expr\<close>
type_synonym  GV\<^sub>e\<^sub>x\<^sub>p\<^sub>r   = \<open>\<sigma> \<Rightarrow> string\<close>  \<comment> \<open>Global Variable Expr\<close>

datatype com\<^sub>a = SKIP
             | assign  LV\<^sub>e\<^sub>x\<^sub>p\<^sub>r E\<^sub>a\<^sub>r\<^sub>i\<^sub>t\<^sub>h        (" _ :=\<^sub>a _" [90,90]80)
             | seq     com\<^sub>a com\<^sub>a          (infixl ";;" 78)
             | cond   "E\<^sub>b\<^sub>o\<^sub>o\<^sub>l" com\<^sub>a com\<^sub>a    ("IF\<^sub>a (_)/ THEN (_)/ ELSE (_)/" [0,0,79]79)
             | while  "E\<^sub>b\<^sub>o\<^sub>o\<^sub>l" com\<^sub>a         ("WHILE\<^sub>a (_)/ DO (_)" [0,80]80)
             | call    F

             | lock    SV\<^sub>e\<^sub>x\<^sub>p\<^sub>r
             | unlock  SV\<^sub>e\<^sub>x\<^sub>p\<^sub>r            
             | send    E\<^sub>a\<^sub>r\<^sub>i\<^sub>t\<^sub>h GV\<^sub>e\<^sub>x\<^sub>p\<^sub>r        ("STORE\<^sub>a _ TO  _" [90,90]80)              
             | rec     E\<^sub>a\<^sub>r\<^sub>i\<^sub>t\<^sub>h GV\<^sub>e\<^sub>x\<^sub>p\<^sub>r        ("LOAD\<^sub>a _ FROM _" [90,90]80)


section\<open>Denotational Semantics of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>-P, a parametric version of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>\<close>

consts VarName :: \<open>int \<Rightarrow> string\<close> \<comment> \<open>converts a reference to a global var name\<close>

fun Sem\<^sub>a\<^sub>0 :: "com\<^sub>a \<Rightarrow> (\<sigma> \<Rightarrow> evs  process) \<Rightarrow> \<sigma> \<Rightarrow> evs process" 
  where \<open>Sem\<^sub>a\<^sub>0 SKIP C                    = C\<close> 
       |\<open>Sem\<^sub>a\<^sub>0 (x :=\<^sub>a E) C               = (\<lambda> \<sigma>. C (\<sigma>((x \<sigma>) := E \<sigma>)))\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (P ;; Q) C                = (Sem\<^sub>a\<^sub>0 P (Sem\<^sub>a\<^sub>0 Q C))\<close> 
       |\<open>Sem\<^sub>a\<^sub>0 (IF\<^sub>a E THEN C1 ELSE C2) C = (\<lambda> \<sigma>. if E \<sigma> 
                                                then Sem\<^sub>a\<^sub>0 C1 C \<sigma> 
                                                else Sem\<^sub>a\<^sub>0 C2 C \<sigma>)\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (WHILE\<^sub>a E DO B) C         = (\<mu> X. (\<lambda> \<sigma>. if E \<sigma> 
                                                      then Sem\<^sub>a\<^sub>0 B X \<sigma> 
                                                      else C \<sigma>))\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (com\<^sub>a.call F) C           = (\<lambda> \<sigma>. C (F \<sigma>))\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (com\<^sub>a.lock n) C           = (\<lambda> \<sigma>. evs.lock (n \<sigma>) \<rightarrow> C \<sigma>)\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (com\<^sub>a.unlock n) C         = (\<lambda> \<sigma>. evs.unlock (n \<sigma>)  \<rightarrow> C \<sigma>)\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (STORE\<^sub>a E TO X\<^sub>g\<^sub>l\<^sub>o) C       = (\<lambda> \<sigma>. upd\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l (X\<^sub>g\<^sub>l\<^sub>o \<sigma>) (E \<sigma>) \<rightarrow> C \<sigma>)\<close>
       |\<open>Sem\<^sub>a\<^sub>0 (LOAD\<^sub>a X\<^sub>l\<^sub>o\<^sub>c FROM  X\<^sub>g\<^sub>l\<^sub>o) C   = (\<lambda> \<sigma>. (read\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l (X\<^sub>g\<^sub>l\<^sub>o \<sigma>))\<^bold>?x
                                                     \<rightarrow> C(\<sigma>((VarName(X\<^sub>l\<^sub>o\<^sub>c \<sigma>)):=x)))\<close>

section\<open>Conclusion and Future Work\<close>

text\<open>We have shown the language and semantics of \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close>, a thin layer over HOL-CSP
giving this process-algebra a more programming language flavor. It is conceived to 
show the close link between both worlds considered quite distinct by many.

The embedding provides:
   \<^enum> a clear semantic foundation via HOL-CSP to HOL,
     comprising  computation and concurrency, 
   \<^enum> an end-to-end verification of a verification method inside 
     a highly trustable interactive proof assistant, 
   \<^enum> a path to theorem proving of functional properties,
     via deadlock-freeness proofs,
   \<^enum> a path to model-checking of functional properties,
     via deadlock-freeness inside FDR4 (unpublished so far).
\<close>

text\<open>
An interesting direction for future work is, for example, how  a Hoare Calculus for \<open>IMP\<^sub>c\<^sub>o\<^sub>n\<^sub>c\<^sub>u\<^sub>r\<close> 
would look like, or how a conversion to FDR4 could be used in a SPIN-like manner 
for finitized programs as model-checking-based backend for practical purposes.\<close>


(*<*) 
end
(*>*)