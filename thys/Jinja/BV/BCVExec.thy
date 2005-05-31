theory BCVExec = BVExec + BVNoTypeError + Exceptions:

section {* Preliminaries *}

text {* represent sets as lists *}

types_code
  set ("(_) list")

consts_code
  "{}"     ("[]")
  "insert" ("(_ ins _)")
  "op :"   ("(_ mem _)")
  "op Un"  ("(_ union _)")
  "image"  ("map")
  "UNION"  ("(fn A => fn f => flat (map f A))")
  "Bex"    ("(fn A => fn f => exists f A)")
  "Ball"   ("(fn A => fn f => forall f A)")


text {* some default values *}

consts_code
  arbitrary :: nat ("{* (0::nat) *}")
  arbitrary :: string ("{* ''''Arbitrary'''' *}")
  arbitrary :: val ("{* Unit *}")
  arbitrary :: obj (" {* ((''''ArbitraryClassName'''',(\<lambda>x. None))::obj) *}")

text {* code for the subclass relation, avoids non-termination due to 
        left-recursion in the transitive closure. *}
lemmas [code ind] = rtrancl_refl converse_rtrancl_into_rtrancl 
declare subcls1I [code ind]

section {* Semilattice *}


(* types' replaces Decl.types, which uses the unexecutable Collect function. *)
constdefs types'::"jvm_prog \<Rightarrow> ty list"
"types' P \<equiv> [Void,Boolean,Integer,NT]@(map Class (map fst P))"

lemma types_exec:
"types P = set (types' P)"
proof (rule set_ext, rule iffI)
  fix x 
  assume xtypes:  "x \<in> types P"
  show  "x \<in> set (types' P)"
  proof -
    from xtypes show ?thesis
      apply (simp add: is_class_def class_def 
             is_type_def types'_def split add: ty.split_asm)
      apply (erule exE)+
      apply (drule map_of_SomeD)
      apply (rule imageI)
      apply (drule_tac f="fst" in imageI)
      apply simp
      done
    qed

next

  fix x 
  assume xtypes': "x \<in> set (types' P)"
  show "x \<in> types P"
  proof -
    from xtypes' show ?thesis
    apply (simp add: is_class_def class_def is_type_def types'_def)
    apply (case_tac "x::ty")
    apply simp+
    --{* x = Class list *}
    apply (erule imageE)+
    apply (simp only: is_class_def class_def not_None_eq)
    apply (rule_tac x="snd xa" in weak_map_of_SomeI)
    apply simp
    done
  qed
qed
 

declare fun_of_def [code unfold]

lemma esl_exec [code]:
"esl (P::jvm_prog) = (set (types' P), subtype P, SemiType.sup P)"
by (simp add: SemiType.esl_def types_exec)


lemma is_RefT_exec[code]:
"is_refT T = (case T of NT \<Rightarrow> True | Class C \<Rightarrow> True | _ \<Rightarrow> False)"
by (simp add: is_refT_def split add: ty.split)

declare exec_lub_def[code unfold]

lemmas [code] =
  meta_eq_to_obj_eq [OF JVM_le_unfold]

lemma JVM_sup_unfold [code]:
 "JVM_SemiType.sup S m n = lift2 (Opt.sup
       (Product.sup (Listn.sup (SemiType.sup S))
         (\<lambda>x y. OK (map2 (lift2 (SemiType.sup S)) x y))))" 
apply (unfold JVM_SemiType.sup_def JVM_SemiType.sl_def Opt.esl_def Err.sl_def
       stk_esl_def loc_sl_def Product.esl_def Listn.sl_def upto_esl_def 
       SemiType.esl_def Err.esl_def) 
by simp

section {* Lookup Functions *}

constdefs methodnames :: "jvm_prog \<Rightarrow> (cname \<times> mname) list"
"methodnames P \<equiv> concat (map (\<lambda> (C,(S,Fs,Ms)). (map (\<lambda>(M,Ts,T,bd). (C,M)) Ms)) P)"

lemma field' [code ind]:
"P \<turnstile> C has_fields FDTs \<Longrightarrow>
  map_of (map (\<lambda>((F,D),T). (F,(D,T))) FDTs) F = Some(D,T) \<Longrightarrow> field P C F = (D, T)"
  apply (rule field_def2)
  apply (fastsimp simp add: sees_field_def)
  done

generate_code 
  field = "field"


lemma fields' [code ind]:"P \<turnstile> C has_fields FDTs \<Longrightarrow> TypeRel.fields P C = FDTs"
by simp


generate_code
  fields = "fields"


lemma method' [code ind]:
"P \<turnstile> C sees_methods Mm \<Longrightarrow> Mm M = Some((Ts,T,m),D) \<Longrightarrow> method P C M = (D,Ts,T,m)"
  apply (rule method_def2)
  apply (fastsimp simp add: Method_def)
  done

generate_code 
 method = "method"


consts FLookup::"('m prog \<times> cname \<times> vname) set"

inductive "FLookup"
intros
init:"\<lbrakk> P \<turnstile> C has_fields FDTs ;
        map_of (map (\<lambda>((F,D),T). (F,(D,T))) FDTs) F = Some(C,T) \<rbrakk> \<Longrightarrow> (P,C,F) \<in> FLookup"

(* @Stefan: inductive auxiliary set used to generate code for existentially/universally 
            quantified lookup in an inductive set. This could be automated.  *)

lemma app_i_Getfield_exec [code]:
"app\<^isub>i (Getfield F C, P, pc, mxs, T\<^isub>r, (T#ST, LT)) = ((P,C,F) \<in> FLookup \<and> P \<turnstile> T \<le> Class C)"
apply (rule iffI)
apply (simp add: app\<^isub>i.simps TypeRel.sees_field_def)
apply (erule conjE | erule exE)+
apply (rule_tac T="vT" and FDTs="FDTs" and C="C" in  FLookup.init)
apply simp
apply simp

apply (erule conjE)
apply (simp add: app\<^isub>i.simps TypeRel.sees_field_def)
apply (erule  FLookup.elims)
apply (rule_tac x="Ta" in exI)
apply (rule_tac x="FDTs" in exI)
apply simp
done

consts FLookup2::"('m prog \<times> cname \<times> vname \<times> ty) set"

inductive "FLookup2"
intros
init:"\<lbrakk> P \<turnstile> C has_fields FDTs ;
        map_of (map (\<lambda>((F,D),T). (F,(D,T))) FDTs) F = Some(C,T);
        P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow> (P,C,F,T') \<in> FLookup2"

(* @Stefan: inductive auxiliary set used to generate code for existentially/universally 
            quantified lookup in an inductive set. This could be automated.  *)

lemma app_i_Putfield_exec [code]:
"app\<^isub>i (Putfield F C, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST, LT)) = ((P,C,F,T\<^isub>1) \<in> FLookup2 \<and> P \<turnstile> T\<^isub>2 \<le> (Class C))"
apply (rule iffI)
apply (simp add: app\<^isub>i.simps TypeRel.sees_field_def)
apply (erule conjE | erule exE)+
apply simp
apply (rule_tac T="vT'" and FDTs="FDTs" in  FLookup2.init)
apply simp
apply simp
apply simp

apply (erule conjE)
apply (erule FLookup2.elims)

apply (simp add: app\<^isub>i.simps TypeRel.sees_field_def)
apply (rule_tac x="T" in exI)
apply simp
apply (rule_tac x="FDTs" in exI)
apply simp
done


consts MLookup::"('m prog \<times> mname \<times> nat \<times> ty list) set"

inductive "MLookup"
intros
init: 
"\<lbrakk> P \<turnstile> C sees M:Ts \<rightarrow> T = m in D; 
   ST!n = Class C; 
   P \<turnstile> rev (take n ST) [\<le>] Ts \<rbrakk>  \<Longrightarrow> (P,M,n,ST) \<in> MLookup"

(* @Stefan: inductive auxiliary set used to generate code for existentially/universally 
            quantified lookup in an inductive set. This could be automated.  *)

lemma app_i_Invoke_exec [code]:
"app\<^isub>i (Invoke M n, P, pc, mxs, T\<^isub>r, (ST,LT)) = (n < length ST \<and> (ST!n \<noteq> NT \<longrightarrow> (P,M,n,ST) \<in> MLookup))"
apply (rule iffI)
apply (simp add: app\<^isub>i.simps)
apply (rule impI)
apply simp
apply (erule conjE | erule exE)+
apply (rule_tac C="C" and Ts="Ts" and D="D" and m="m" in  MLookup.init)
apply simp
apply simp
apply simp

apply (simp add: app\<^isub>i.simps)
apply (rule impI)
apply simp
apply(erule conjE)+
apply (erule MLookup.elims)
apply (rule_tac x="C" in exI)
apply simp
apply (rule_tac x="D" in exI)
apply (rule_tac x="Ts" in exI)
apply simp
apply (rule_tac x="T" in exI)
apply (rule_tac x="m" in exI)
apply simp
done


lemmas MLookup_intros[unfolded Method_def fun_of_def, OF exI, OF conjI, code ind ] = MLookup.intros

lemmas [THEN meta_eq_to_obj_eq, simplified list_all_conv [symmetric], code] = wf_mdecl_def


lemma wf_syscls_code [code]:
"wf_syscls P  =  (list_all (\<lambda> x. x \<in> (set (map fst P))) [Object, NullPointer, ClassCast, OutOfMemory])"
(*<*)
apply (simp add: wf_syscls_def list_all_conv sys_xcpts_def)
apply blast
done
(*>*)


consts MLookup2::"(jvm_prog \<times> cname \<times> mname \<times> ty list \<times> ty) set"
  
inductive "MLookup2"
intros
init: "\<lbrakk> P \<turnstile> D sees M:Ts' \<rightarrow> T' = m' in D'; \<not> (P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T') \<rbrakk> \<Longrightarrow> (P,D,M,Ts,T) \<in> MLookup2"

lemma MLookup2_conv: "((P,D,M,Ts,T) \<notin>  MLookup2) = (\<forall> D' Ts' T' m'.  (P \<turnstile> D sees M:Ts' \<rightarrow> T' = m' in D') \<longrightarrow> (P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T'))"
apply (rule iffI)
apply (rule allI)+
apply (rule impI)
apply (rule classical)
apply (drule MLookup2.init)
apply simp
apply simp

apply (rule classical)
apply simp
apply (erule MLookup2.elims)
apply (erule_tac x="D'" in allE)
apply (erule_tac x="Ts'" in allE)
apply (erule_tac x="T'" in allE)
apply fastsimp
done


lemmas [unfolded Method_def fun_of_def, OF exI, OF conjI, code ind] = MLookup2.intros

lemma wf_cdecl_code:
"wf_cdecl (wf_md:: jvm_method wf_mdecl_test) (P::jvm_prog)  \<equiv>  \<lambda>(C,(D,fs,ms)).
 (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
 (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>  distinct_fst ms \<and>
 (C \<noteq> Object \<longrightarrow>
  is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
  (\<forall>(M,Ts,T,m)\<in>set ms.
     \<not> (P,D,M,Ts,T) \<in> MLookup2))"
sorry

lemmas wf_cdecl_code_s [THEN meta_eq_to_obj_eq, simplified list_all_conv [symmetric], code] = wf_cdecl_code

thm wf_cdecl_code_s
(*
lemma [code]:
"wf_prog (wf_md::jvm_method wf_mdecl_test) (P::jvm_prog) = wf_syscls P \<and> (list_all (wf_cdecl wf_md P) P) \<and> distinct_fst P"
sorry
*)

lemma [code]:
"wf_prog (wf_md:: jvm_method wf_mdecl_test) = (\<lambda> (P::jvm_prog) . wf_syscls P \<and> (list_all (wf_cdecl wf_md P) P) \<and> distinct_fst P)"
sorry


lemma is_relevant_entry_exec [code]:
"is_relevant_entry P i pc e = (let (f,t,C,h,d) = e in is_relevant_class i P C \<and> (f \<le> pc) \<and> (pc < t))"
apply (simp add: is_relevant_entry_def split_def )
done

lemma [code]:
"(p\<in>SetInterval.lessThan n) = ((0::nat) \<le> p \<and> p < n)"
apply (simp add: SetInterval.lessThan_def)
done

lemma [code]:
"unstables r step ss = (UN p:set ([0 ..< size ss]). if \<not>stable r step ss p then {p} else {})"
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
  "op -" :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"  ("(_ \\\\ _)") 

(* @Stefan : parser or printer eats backslashes.  Workaround: quotations *)


constdefs
  method_kil :: "jvm_prog \<Rightarrow> cname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
               ex_table \<Rightarrow> instr list \<Rightarrow> (ty\<^isub>i' err) list"
  "method_kil G C pTs rT mxs mxl et is ==
   (let first  = Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err));
        start  = OK first#(replicate (size is - 1) (OK None))
    in  kiljvm G mxs (1+size pTs+mxl) rT is et start)"



constdefs prog_kil ::"jvm_prog \<Rightarrow> ((cname \<times> mname) \<times> (ty\<^isub>i' err) list) list"
"prog_kil P \<equiv> map (\<lambda> (C,M). 
(let (D,pTs,rT,m) = method P C M; (mxs,mxl,is,et)=m 
 in ((C,M),method_kil P C pTs rT mxs mxl et is))) (methodnames P)"

section {* Single step BCV *}

constdefs
initss :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> (ty\<^isub>i' err) list"
"initss P C M \<equiv> 
 (let (D,pTs,rT,m) = method P C M;
      (mxs,mxl,is,et)=m;
      first  = Some (tl [Integer],(OK (Class C))#((map OK pTs))@(replicate mxl Err))
  in OK first#(replicate (size is - 1) (OK None)))"

(* @Stefan: tl [Integer] produces code of type ty list, as expected, whereas [] produces code of type _a list.
            []::ty list does not help either. *)

constdefs
initw:: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> nat set"
"initw P C M \<equiv>  
(let (D,pTs,rT,m) = method P C M;
     (mxs,mxl,is,et)=m
 in (unstables (JVM_SemiType.le P mxs mxl) (exec P mxs rT et is) (initss P C M)))"

consts
nxtkil :: "'s binop \<Rightarrow> 's step_type \<Rightarrow>
           's list \<Rightarrow> nat set \<Rightarrow> 's list \<times> nat set"
defs nxtkil_def:
"nxtkil f step ss w == (if w = {} 
 then (ss,w) 
 else (let p = some_elem w
       in propa f (step p (ss!p)) ss (w-{p})))"

constdefs
nxtjob:: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ((ty\<^isub>i' err) list \<times> nat set) \<Rightarrow> ((ty\<^isub>i' err) list \<times> nat set)"
"nxtjob P C M \<equiv> (\<lambda> (ss,w). 
 (let (D,pTs,rT,m) = method P C M;
      (mxs,mxl,is,et)=m
  in nxtkil (JVM_SemiType.sup P mxs mxl) (exec P mxs rT et is) ss w))"

constdefs
initjob:: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ((ty\<^isub>i' err) list \<times> nat set)"
"initjob P C M \<equiv> (initss P C M,initw P C M)" 

--{* printjob displays a method type augmented with corresponding instructions *}

constdefs 
printjob:: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ((ty\<^isub>i' err) list \<times> nat set) \<Rightarrow> ((instr \<times> (ty\<^isub>i' err)) list \<times> nat set)"
"printjob P C M \<equiv> (\<lambda> (ss,w). 
 (let (D,pTs,rT,m) = method P C M;
      (mxs,mxl,is,et)=m
  in (map (\<lambda>n. (is!n,ss!n)) (List.upt 0 (length ss)),w)))"

--{* parsejob removes the instructions from an augmented method type *}

constdefs
parsejob:: "((instr \<times> (ty\<^isub>i' err)) list \<times> nat set) \<Rightarrow> ((ty\<^isub>i' err) list \<times> nat set)"
"parsejob \<equiv> (\<lambda> (pss,w).  (map snd pss,w))" 

(* @Stefan: Code generator produces too weakly typed code for printjob. *)


--{* \clearpage *}

section {* Example *}

text {* Example taken from Fig. 2 in  [Klein,Wildmoser,Verified Bytecode Subroutines,JAR03] *}

subsection {* Declarations *}

constdefs
A::"jvm_method cdecl"
"A \<equiv> (''A'',(Object,[(''F'',Class ''A'')],[]))"

constdefs 
B::"jvm_method cdecl"
"B \<equiv> (''B'',(''A'',[],
[(''main'',[Integer],Void,(1,0,[
Load 0,
Store 1,
Load 0,
Getfield ''F'' ''A'',
Goto -3
],[]))]))"

(* @Gerwin: If we replace Goto -3 by Return the method is rejected, because according to the
   formalisation Return is only applicable if there is at least one element on the stack. Is
   this intended? *)

constdefs
prg::"jvm_prog"
"prg \<equiv> (SystemClasses @ [A,B])"

lemma [code]:
 "states (P::jvm_prog) mxs mxl = fst(sl P mxs mxl)"
by (simp add: states_def)

lemma [code]:
"check_types (P::jvm_prog) mxs mxl \<tau>s = ( set \<tau>s \<subseteq> states P mxs mxl)"
by (simp add: check_types_def)

lemma [code]:
"wt_method (P::jvm_prog) C Ts T\<^isub>r mxs mxl\<^isub>0 is xt \<tau>s =
  (0 < size is \<and> size \<tau>s = size is \<and>
  check_types P mxs (1+size Ts+mxl\<^isub>0) (map OK \<tau>s) \<and>
  wt_start P C Ts mxl\<^isub>0 \<tau>s \<and>
  (list_all (\<lambda> pc. P,T\<^isub>r,mxs,size is,xt \<turnstile> is!pc,pc :: \<tau>s) (upt 0 (size is))))"
by (simp add: wt_method_def list_all_conv)

lemma [code]:
"wf_jvm_prog_phi \<Phi> (P::jvm_prog) = wf_prog ((\<lambda>(P::jvm_prog) C (M,Ts,T\<^isub>r,(mxs,mxl\<^isub>0,is,xt)). 
      wt_method P C Ts T\<^isub>r mxs mxl\<^isub>0 is xt (\<Phi> C M))::jvm_method wf_mdecl_test) P"
by (simp add: wf_jvm_prog_phi_def)


lemma [code]:
"stk_esl (P::jvm_prog) mxs = upto_esl mxs (SemiType.esl P)"
by (simp add: stk_esl_def)

lemma [code]:
"JVM_SemiType.sl (P::jvm_prog) mxs mxl =
  Err.sl(Opt.esl(Product.esl (stk_esl P mxs) (Err.esl(loc_sl P mxl))))"
by (simp add: JVM_SemiType.sl_def)


generate_code
esl = "\<lambda> (P::jvm_prog). esl P"
thm Listn.upto_esl_def

lemma list_0 [code]:
"list 0 S = {[]}"
apply (subst list_def)
apply (rule set_ext)
apply (case_tac "x")
apply simp

apply simp
done

lemma list_Suc [code]:
"list (Suc n) S = UNION S (\<lambda> x. (\<lambda>xs. x # xs) ` (list n S))"
sorry

term "UNION (set (upt 0 m)) (\<lambda> n. list n S)"
term "Union{list n S |n. n \<le> m}"

thm upto_esl_def

lemma [code]:
"upto_esl m = (\<lambda>(A,r,f). (UNION (set (upt 0 m)) (\<lambda> n. list n A),Listn.le r, Listn.sup f))"
sorry


lemma [code]:
"Err.err S = insert Err (OK ` S)"
apply (simp add: err_def)
apply blast
done
thm Opt.opt_def
lemma [code]:
"Opt.opt S = insert None (Some ` S)"
by (simp add: Opt.opt_def, blast)

thm TypeRel.Methods.intros
(*
generate_code
wt_method = "\<lambda> (P::jvm_prog). wt_method P"
*)
(*
generate_code
bla = "(\<lambda>(P::jvm_prog) C (M,Ts,Tr,(mxs,mxl0,is,xt)). 
      wt_method P C Ts Tr mxs mxl0 is xt (\<Phi> C M))"
*)
thm "wf_jvm_prog_phi_def"

consts
removeErr::"'a err list \<Rightarrow> 'a list \<Rightarrow>  'a list"

primrec
"removeErr [] res = res"
"removeErr (a#as) res = (case a of Err \<Rightarrow> []
                                | OK \<tau>s \<Rightarrow> removeErr as (res@[\<tau>s]))"

thm foldl.simps

consts
convert_pt::"(((cname \<times> mname) \<times> ((ty\<^isub>i' err) list)) list) \<Rightarrow> ((cname \<times> mname) \<times> (ty\<^isub>i'  list)) list"

primrec
"convert_pt [] = []"
"convert_pt (mt#mts) = (let (cm,emt) = mt in (cm,removeErr emt [])#(convert_pt mts))"


constdefs map_of2:: "(('a \<times> 'b) \<times> 'c list) list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c list)"
"map_of2 ls \<equiv> (\<lambda> a b. (case map_of ls (a,b) of None \<Rightarrow> [] | Some cl \<Rightarrow> cl))"



generate_code
wf_jvm_prog = "\<lambda> \<Phi> (P::jvm_prog). wf_jvm_prog_phi \<Phi> P"
convert_pt = "convert_pt"
map_of2 = "map_of2"
prg = "prg"
prog_kil = "prog_kil"
initjob = "initjob prg ''B'' ''main''"
nxtjob = "nxtjob  prg ''B'' ''main''"
printjob = "\<lambda> job. printjob  prg ''B'' ''main'' job"
parsejob = "parsejob"


subsection {* Evaluation *}

text {* Compute method types of all methods. *}

ML {* print_depth 100; *}
ML {* val pt = (prog_kil prg); *}
ML {* val cpt = convert_pt pt; *}
ML {* wf_syscls prg; *}
ML {* distinct_fst prg; *}
ML {* val ac = wf_jvm_prog (map_of2 cpt) prg; *}
ML {* methodnames prg; *}
(* ML {* mt; *} *)

text {* Stepwise computation of a method type *}

ML {* val job = (printjob initjob); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
ML {* val job = printjob (nxtjob (parsejob job)); *}
--{* stable *}


end
