(*  Title:      Jinja/J/execute_Bigstep.thy
    ID:         $Id: execute_Bigstep.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Tobias Nipkow
    Copyright   2004 Technische Universitaet Muenchen
*)

header {* \isaheader{Code Generation For BigStep} *}

theory execute_BigStep = BigStep + Examples:

consts map_val :: "(expr list \<times> val list) set"

inductive map_val
intros
  Nil: "([], []) \<in> map_val"
  Cons: "(xs, ys) \<in> map_val \<Longrightarrow> (Val y # xs, y # ys) \<in> map_val"

consts map_val2 :: "(expr list \<times> val list \<times> expr list) set"

inductive map_val2
intros
  Nil: "([], [], []) \<in> map_val2"
  Cons: "(xs, ys, zs) \<in> map_val2 \<Longrightarrow> (Val y # xs, y # ys, zs) \<in> map_val2"
  Throw: "(throw e # xs, [], throw e # xs) \<in> map_val2"

theorem map_val_conv: "(xs = map Val ys) = ((xs, ys) \<in> map_val)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> (xs, ys) \<in> map_val"
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
  moreover have "(xs, ys) \<in> map_val \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = ((xs, ys, throw e # zs) \<in> map_val2)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> (xs, ys, throw e # zs) \<in> map_val2"
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
  moreover have "(xs, ys, throw e # zs) \<in> map_val2 \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

lemma CallNull2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>null,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>; (evs,vs) : map_val \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^isub>2\<rangle>"
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done


lemma CallParamsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^isub>1\<rangle>; P \<turnstile> \<langle>es,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,s\<^isub>2\<rangle>;
     (evs, vs, throw ex # es') : map_val2 \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^isub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^isub>2\<rangle>"
apply(rule eval_evals.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done


lemma Call2:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^isub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^isub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^isub>1\<rangle> [\<Rightarrow>] \<langle>evs,(h\<^isub>2,l\<^isub>2)\<rangle>;
     (evs,vs) : map_val;
     h\<^isub>2 a = Some(C,fs);  P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^isub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^isub>2,l\<^isub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^isub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^isub>3,l\<^isub>2)\<rangle>"
apply(rule Call, assumption+)
apply(simp add: map_val_conv[symmetric])
apply assumption+
done


lemmas [code ind] =
 eval_evals.New eval_evals.NewFail
 eval_evals.Cast eval_evals.CastNull eval_evals.CastFail eval_evals.CastThrow
 eval_evals.Val eval_evals.Var
 eval_evals.BinOp eval_evals.BinOpThrow1 eval_evals.BinOpThrow2
 eval_evals.LAss eval_evals.LAssThrow
 eval_evals.FAcc eval_evals.FAccNull eval_evals.FAccThrow
 eval_evals.FAss eval_evals.FAssNull
 eval_evals.FAssThrow1 eval_evals.FAssThrow2
 eval_evals.CallObjThrow CallNull2 CallParamsThrow2
 Call2[simplified Method_def, OF _ _ _ _ exI,OF _ _ _ _ conjI,no_vars]
 eval_evals.Block
 eval_evals.Seq eval_evals.SeqThrow
 eval_evals.CondT eval_evals.CondF eval_evals.CondThrow
 eval_evals.WhileF eval_evals.WhileT
 eval_evals.WhileCondThrow eval_evals.WhileBodyThrow
 eval_evals.Throw eval_evals.ThrowNull
 eval_evals.ThrowThrow
 eval_evals.Try eval_evals.TryCatch eval_evals.TryThrow
 eval_evals.Nil eval_evals.Cons eval_evals.ConsThrow


generate_code
 test1 = "[] \<turnstile> \<langle>testExpr1,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
 test2 = "[] \<turnstile> \<langle>testExpr2,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
 test3 = "[] \<turnstile> \<langle>testExpr3,(empty,empty(''V''\<mapsto>Intg 77))\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
 test4 = "[] \<turnstile> \<langle>testExpr4,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
 test5 = "[(''Object'',('''',[],[])),(''C'',(''Object'',[(''F'',Integer)],[]))] \<turnstile> \<langle>testExpr5,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
 test6 = "[(''Object'',('''',[],[])), classI] \<turnstile> \<langle>testExpr6,(empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"

 V = "''V''"
 F = "''F''"
 C = "''C''"
 N = "''N''"
 L = "''L''"

ML {* if fst (Seq.hd test1) = Val (Intg 5) then () else error "" *}
ML {* if fst (Seq.hd test2) = Val (Intg 11) then () else error "" *}
ML {* if fst (Seq.hd test3) = Val (Intg 83) then () else error "" *}
ML {* if (let val (_,(h,l)) = Seq.hd test4 in l V end) = Some (Intg 6) then () else error "" *}
ML {* if (let val (_,(h,l)) = Seq.hd test5
              val Some(c,fs) = h(Suc id_0)
              val Some(obj,_) = h(id_0)
          in (C=c,fs(F,C),[obj ,c])end)=
    (true, Some (Intg 42), [["O","b","j","e","c","t"], ["C"]])
    then () else error "" *}
ML {* if fst (Seq.hd test6) = Val (Intg 160) then () else error "" *}

generate_code
 test7 = "[classObject, classL] \<turnstile> \<langle>testExpr_BuildList, (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>";

ML {* if (let val (_,(h,_)) = Seq.hd test7
              val Some(_,fs1) = h(id_0)
              val Some(_,fs2) = h(Suc id_0)
              val Some(_,fs3) = h(Suc(Suc id_0))
              val Some(_,fs4) = h(Suc(Suc(Suc id_0)))
          in [(fs1(F,L), fs1(N,L)), (fs2(F,L), fs2(N,L)),
              (fs3(F,L), fs3(N,L)), (fs4(F,L), fs4(N,L))] end)=
      [(Some (Intg 1), Some (Addr (Suc id_0))),
       (Some (Intg 2), Some (Addr (Suc (Suc id_0)))),
       (Some (Intg 3), Some (Addr (Suc (Suc (Suc id_0))))),
       (Some (Intg 4), Some Null)] then () else error "" *}

generate_code
 test8 = "[classObject, classA] \<turnstile> \<langle>testExpr_ClassA, (empty,empty)\<rangle> \<Rightarrow> \<langle>_,_\<rangle>"
 i="''int''"
 t= "''test''"
 A="''A''"

ML {* if (let val (_,(h,l)) = Seq.hd test8
              val Some(_,fs1) = h(id_0)
              val Some(_,fs2) = h(Suc id_0)
          in [(fs1(i,A),fs1(t,A)), (fs2(i,A),fs2(t,A))] end)=
      [(Some (Intg 10), Some Null), (Some (Intg 50), Some Null)] then () else error "" *}

end
