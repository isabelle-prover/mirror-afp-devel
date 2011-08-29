(*  Title:      Jinja/J/execute_Bigstep.thy
    ID:         $Id: execute_Bigstep.thy,v 1.8 2009-07-14 09:00:10 fhaftmann Exp $
    Author:     Tobias Nipkow
    Copyright   2004 Technische Universitaet Muenchen
*)

header {* \isaheader{Code Generation For BigStep} *}

theory execute_Bigstep imports BigStep Examples
  "~~/src/HOL/Library/Efficient_Nat"
begin

inductive map_val :: "expr list \<Rightarrow> val list \<Rightarrow> bool"
where
  Nil: "map_val [] []"
| Cons: "map_val xs ys \<Longrightarrow> map_val (Val y # xs) (y # ys)"

inductive map_val2 :: "expr list \<Rightarrow> val list \<Rightarrow> expr list \<Rightarrow> bool"
where
  Nil: "map_val2 [] [] []"
| Cons: "map_val2 xs ys zs \<Longrightarrow> map_val2 (Val y # xs) (y # ys) zs"
| Throw: "map_val2 (throw e # xs) [] (throw e # xs)"

theorem map_val_conv: "(xs = map Val ys) = map_val xs ys"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> map_val xs ys"
    apply (induct xs type:list)
    apply (case_tac ys)
    apply simp
    apply (rule map_val.Nil)
    apply simp
    apply (case_tac ys)
    apply simp
    apply simp
    apply (erule conjE)
    apply (rule map_val.Cons)
    apply simp
    done
  moreover have "map_val xs ys \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = map_val2 xs ys (throw e # zs)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> map_val2 xs ys (throw e # zs)"
    apply (induct xs type:list)
    apply (case_tac ys)
    apply simp
    apply simp
    apply simp
    apply (case_tac ys)
    apply simp
    apply (rule map_val2.Throw)
    apply simp
    apply (rule map_val2.Cons)
    apply simp
    done
  moreover have "map_val2 xs ys (throw e # zs) \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

lemma CallNull2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>; map_val evs vs \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done


lemma CallParamsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>;
     map_val2 evs vs (throw ex # es'') \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"
apply(rule eval_evals.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done

lemma Call2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     map_val evs vs;
     h\<^isub>2 a = Some(C,fs);  P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^isub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call, assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

code_pred 
  (modes: i \<Rightarrow> o \<Rightarrow> bool)
  map_val 
.

code_pred
  (modes: i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  map_val2
.

lemmas [code_pred_intro] =
 eval_evals.New eval_evals.NewFail
 eval_evals.Cast eval_evals.CastNull eval_evals.CastFail eval_evals.CastThrow
 eval_evals.Val eval_evals.Var
 eval_evals.BinOp eval_evals.BinOpThrow1 eval_evals.BinOpThrow2
 eval_evals.LAss eval_evals.LAssThrow
 eval_evals.FAcc eval_evals.FAccNull eval_evals.FAccThrow
 eval_evals.FAss eval_evals.FAssNull
 eval_evals.FAssThrow1 eval_evals.FAssThrow2
 eval_evals.CallObjThrow

declare CallNull2 [code_pred_intro CallNull2]
declare CallParamsThrow2 [code_pred_intro CallParamsThrow2]
declare Call2 [code_pred_intro Call2]

lemmas [code_pred_intro] =
 eval_evals.Block
 eval_evals.Seq eval_evals.SeqThrow
 eval_evals.CondT eval_evals.CondF eval_evals.CondThrow
 eval_evals.WhileF eval_evals.WhileT
 eval_evals.WhileCondThrow

declare eval_evals.WhileBodyThrow [code_pred_intro WhileBodyThrow2]

lemmas [code_pred_intro] =
 eval_evals.Throw eval_evals.ThrowNull
 eval_evals.ThrowThrow
 eval_evals.Try eval_evals.TryCatch eval_evals.TryThrow
 eval_evals.Nil eval_evals.Cons eval_evals.ConsThrow

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as execute)
  eval
proof -
  case eval
  from eval.prems show thesis
  proof(cases (no_simp))
    case CallNull thus ?thesis
      by(rule CallNull2[OF refl])(simp add: map_val_conv[symmetric])
  next
    case CallParamsThrow thus ?thesis
      by(rule CallParamsThrow2[OF refl])(simp add: map_val2_conv[symmetric])
  next
    case Call thus ?thesis
      by -(rule Call2[OF refl], simp_all add: map_val_conv[symmetric])
  next
    case WhileBodyThrow thus ?thesis by(rule WhileBodyThrow2[OF refl])
  qed(assumption|erule (4) that[OF refl]|erule (3) that[OF refl])+
next
  case evals
  from evals.prems show thesis
    by(cases (no_simp))(assumption|erule (3) that[OF refl])+
qed

notation execute ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ \<langle>'_, '_\<rangle>)" [51,0,0] 81)

definition "test1 = [] \<turnstile> \<langle>testExpr1,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test2 = [] \<turnstile> \<langle>testExpr2,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test3 = [] \<turnstile> \<langle>testExpr3,(empty,empty(''V''\<mapsto>Intg 77))\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test4 = [] \<turnstile> \<langle>testExpr4,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test5 = [(''Object'',('''',[],[])),(''C'',(''Object'',[(''F'',Integer)],[]))] \<turnstile> \<langle>testExpr5,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "test6 = [(''Object'',('''',[],[])), classI] \<turnstile> \<langle>testExpr6,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

definition "V = ''V''"
definition "C = ''C''"
definition "F = ''F''"

ML {*
  val SOME ((@{code Val} (@{code Intg} 5), _), _) = Predicate.yield @{code test1};
  val SOME ((@{code Val} (@{code Intg} 11), _), _) = Predicate.yield @{code test2};
  val SOME ((@{code Val} (@{code Intg} 83), _), _) = Predicate.yield @{code test3};

  val SOME ((_, (_, l)), _) = Predicate.yield @{code test4};
  val SOME (@{code Intg} 6) = l @{code V};

  val SOME ((_, (h, _)), _) = Predicate.yield @{code test5};
  val SOME (c, fs) = h 1;
  val SOME (obj, _) = h 0;
  val SOME (@{code Intg} i) = fs (@{code F}, @{code C});
  if c = @{code C} andalso obj = @{code Object} andalso i = 42 
    then () else error "";

  val SOME ((@{code Val} (@{code Intg} 160), _), _) = Predicate.yield @{code test6};
*}

definition "test7 = [classObject, classL] \<turnstile> \<langle>testExpr_BuildList, (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

definition "L = ''L''"
definition "N = ''N''"

ML {*
  val SOME ((_, (h, _)), _) = Predicate.yield @{code test7};
  val SOME (_, fs1) = h 0;
  val SOME (_, fs2) = h 1;
  val SOME (_, fs3) = h 2;
  val SOME (_, fs4) = h 3;

  val F = @{code "F"};
  val L = @{code "L"};
  val N = @{code "N"};
  
  if fs1 (F, L) = SOME (@{code Intg} 1) andalso
     fs1 (N, L) = SOME (@{code Addr} 1) andalso
     fs2 (F, L) = SOME (@{code Intg} 2) andalso
     fs2 (N, L) = SOME (@{code Addr} 2) andalso
     fs3 (F, L) = SOME (@{code Intg} 3) andalso
     fs3 (N, L) = SOME (@{code Addr} 3) andalso
     fs4 (F, L) = SOME (@{code Intg} 4) andalso
     fs4 (N, L) = SOME @{code Null}
  then () else error "";
*}

definition "test8 = [classObject, classA] \<turnstile> \<langle>testExpr_ClassA, (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
definition "i = ''int''"
definition "t = ''test''"
definition "A = ''A''"

ML {*
  val SOME ((_, (h, l)), _) = Predicate.yield @{code test8};
  val SOME (_, fs1) = h 0;
  val SOME (_, fs2) = h 1;

  val i = @{code "i"};
  val t = @{code "t"};
  val A = @{code "A"};

  if fs1 (i, A) = SOME (@{code Intg} 10) andalso 
     fs1 (t, A) = SOME @{code Null} andalso
     fs2 (i, A) = SOME (@{code Intg} 50) andalso 
     fs2 (t, A) = SOME @{code Null}
  then () else error "";
*}

end
