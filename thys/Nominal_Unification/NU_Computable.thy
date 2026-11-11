(*<*)
theory NU_Computable
  imports NU_Completeness
begin
(*>*)
section \<open>The Computable Algorithm\<close>

text\<open>Option-typed version of \<open>sred_fun\<close>.\<close>

function sred_fun :: "(problem_type \<times> fresh_envs \<times> substs) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs) option" where
"sred_fun (([], ys), nabla, s) = Some (([], ys), nabla, s)" |
"sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) =
  (case t1 of
    Unit \<Rightarrow> (case t2 of
               Unit \<Rightarrow> sred_fun ((xs, ys), nabla, s)
             | Susp pi X \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) Unit)] (xs, ys),
                                              nabla, [(X, swap (rev pi) Unit)] \<bullet> s)
             | _ \<Rightarrow> None)
   | Paar u1 u2 \<Rightarrow> (case t2 of
                      Paar v1 v2 \<Rightarrow> sred_fun (((u1 \<approx>? v1) # (u2 \<approx>? v2) # xs, ys), nabla, s)
                    | Susp pi X \<Rightarrow>
                        if \<not> occurs X (Paar u1 u2)
                        then sred_fun (apply_subst [(X, swap (rev pi) (Paar u1 u2))] (xs, ys),
                                            nabla, [(X, swap (rev pi) (Paar u1 u2))] \<bullet> s)
                        else None
                    | _ \<Rightarrow> None)
   | Func F u \<Rightarrow> (case t2 of
                     Func G v \<Rightarrow> if F = G
                                  then sred_fun (((u \<approx>? v) # xs, ys), nabla, s)
                                  else None
                   | Susp pi X \<Rightarrow>
                       if \<not> occurs X (Func F u)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Func F u))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Func F u))] \<bullet> s)
                       else None
                   | _ \<Rightarrow> None)
   | Abst a u \<Rightarrow> (case t2 of
                    Abst b v \<Rightarrow> if a = b
                                 then sred_fun (((u \<approx>? v) # xs, ys), nabla, s)
                                 else sred_fun (((u \<approx>? swap [(a, b)] v) # xs, (a \<sharp>? v) # ys), nabla, s)
                  | Susp pi X \<Rightarrow>
                      if \<not> occurs X (Abst a u)
                      then sred_fun (apply_subst [(X, swap (rev pi) (Abst a u))] (xs, ys),
                                          nabla, [(X, swap (rev pi) (Abst a u))] \<bullet> s)
                      else None
                  | _ \<Rightarrow> None)
   | Atom a \<Rightarrow> (case t2 of
                  Atom b \<Rightarrow> if a = b then sred_fun ((xs, ys), nabla, s) else None
                | Susp pi X \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys),
                                                nabla, [(X, swap (rev pi) (Atom a))] \<bullet> s)
                | _ \<Rightarrow> None)
   | Susp pi X \<Rightarrow> (case t2 of
                     Unit \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) Unit)] (xs, ys),
                                            nabla, [(X, swap (rev pi) Unit)] \<bullet> s)
                   | Atom a \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys),
                                              nabla, [(X, swap (rev pi) (Atom a))] \<bullet> s)
                   | Paar v1 v2 \<Rightarrow>
                       if \<not> occurs X (Paar v1 v2)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Paar v1 v2))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Paar v1 v2))] \<bullet> s)
                       else None
                   | Func G v \<Rightarrow>
                       if \<not> occurs X (Func G v)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Func G v))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Func G v))] \<bullet> s)
                       else None
                   | Abst a v \<Rightarrow>
                       if \<not> occurs X (Abst a v)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Abst a v))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Abst a v))] \<bullet> s)
                       else None
                   | Susp pi2 Y \<Rightarrow>
                       if X = Y
                       then sred_fun ((xs, map (\<lambda>a. a \<sharp>? Susp [] X) (ds_list pi pi2) @ ys), nabla, s)
                       else sred_fun (apply_subst [(X, swap (rev pi) (Susp pi2 Y))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Susp pi2 Y))] \<bullet> s)))"
by pat_completeness auto

text\<open>\<open>sred_fun\<close> terminates because every recursive call performs an \<open>s_red\<close> step on
the problem component, so \<open>rank_r\<close> decreases on it.\<close>

termination sred_fun
  by (relation "inv_image rank_r fst")
     (auto simp: wf_rank_r simp del: swap.simps intro!: rank_r_sred)

function  cred_fun :: "(problem_type \<times> fresh_envs \<times> substs) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs) option"
  where
"cred_fun ((xs, (a \<sharp>? Unit)#ys), nabla, s) = cred_fun ((xs, ys), nabla, s)" |
"cred_fun ((xs, (a \<sharp>? Paar t1 t2)#ys), nabla, s) = cred_fun ((xs, (a\<sharp>?t1)#(a\<sharp>?t2)#ys), nabla, s)" |
"cred_fun ((xs, (a \<sharp>? Func F t)#ys), nabla, s) = cred_fun ((xs, (a\<sharp>?t)#ys), nabla, s)" |
"cred_fun ((xs, (a \<sharp>? Abst b t)#ys), nabla, s) = (if a = b then
                                                      cred_fun ((xs, ys), nabla, s)
                                                    else
                                                      cred_fun ((xs, (a\<sharp>?t)#ys), nabla, s))" |
"cred_fun ((xs, (a \<sharp>? Atom b)#ys), nabla, s) = (if a = b then
                                                  None
                                                else
                                                  cred_fun ((xs, ys), nabla, s))" |
"cred_fun ((xs, (a \<sharp>? Susp pi X)#ys), nabla, s) = cred_fun ((xs, ys), {((swapas (rev pi) a),X)}\<union>nabla, s)" |
"cred_fun ((xs, []), nabla, s) = Some ((xs, []), nabla, s)"
  by pat_completeness auto

termination cred_fun
  by (relation "measure (\<lambda>((xs, ys), nabla, s). size_fprobs ys)", auto)

text\<open>Combines \<open>sred_fun\<close>  and \<open>cred_fun\<close>, mirroring the \<open>red_plus\<close> relation: equations are solved first, then freshness constraints.\<close>

fun red_plus_fun :: "(problem_type \<times> fresh_envs \<times> substs) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs) option" where
"red_plus_fun (P, nabla, s) = (case sred_fun (P, nabla, s) of
                                 Some ((xs, ys), nabla', s') \<Rightarrow> cred_fun ((xs,ys), nabla', s')
                               | None \<Rightarrow> None)"

fun nomu_unify :: "problem_type \<Rightarrow> (fresh_envs \<times> substs) option" where
  "nomu_unify P = (case red_plus_fun (P, {}, []) of 
                    Some (_, nabla', s') \<Rightarrow> Some (nabla', s')
                    | None \<Rightarrow> None)"

text\<open>In generated SML code, equality on booleans is the native one.\<close>

code_printing constant "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : bool) = _)"

text\<open>Whenever \<open>cred_fun\<close> succeeds, the snd (freshness) list of the resulting problem is empty:
all freshness problems have been solved.\<close>

lemma cred_fun_some_snd_empty:
  assumes "cred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "snd P' = []"
  using assms by (induct "(P, nabla, s)" arbitrary: P nabla s P' nabla' s' rule: cred_fun.induct, auto split: if_splits)


(*<*)
end
(*>*)
