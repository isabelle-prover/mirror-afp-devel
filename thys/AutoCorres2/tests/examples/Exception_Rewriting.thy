(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Exception_Rewriting
imports
  "AutoCorres2_Main.AutoCorres_Main"
begin



install_C_file "Exception_Rewriting.c"

autocorres "Exception_Rewriting.c"


context ts_definition_goo
begin
thm ts_def [no_vars]
end

ML \<open>
val stats = Fun_Cache.cache_statistics ()
\<close>


context Exception_Rewriting_all_impl
begin
term "foo':: int \<Rightarrow> int \<Rightarrow> lifted_globals \<Rightarrow> int option"
thm foo'_def [no_vars]

lemma "foo' i j \<equiv> ofail"
  by (simp add: foo'_def)

term "cond_return'::int \<Rightarrow> (int, lifted_globals) res_monad"

thm cond_return'_def[no_vars]
lemma "cond_return' p \<equiv> finally (do {
                             _ \<leftarrow> when (p = 32 \<or> 2 < p) (when (p \<noteq> 30 \<and> p \<noteq> 2) (throw p));
                             v \<leftarrow> gets_the (foo' p p);
                             throw p
                           })"
  by (simp add: cond_return'_def)

term "nested_while':: int \<Rightarrow> (int, lifted_globals) res_monad"
thm nested_while'_def[no_vars]
lemma "nested_while' a \<equiv> finally
 (do {
    y \<leftarrow> try (do {
                (a, y) \<leftarrow>
                  whileLoop (\<lambda>(a, y) s. True)
                    (\<lambda>(a, y). do {
                          a \<leftarrow> condition (\<lambda>s. 3 < a)
                                 (throw (Inl 1))
                                 (condition (\<lambda>s. 1 < a)
                                    (return (a + 1))
                                    (do {
                                       _ \<leftarrow> liftE (finally (whileLoop (\<lambda>_ s. True)
                (\<lambda>_. throw ())
               ()));
                                       throw (Inr 4)
                                     }));
                          return (a, 4)
                        })
                   (a, 3);
                return y
              });
    _ \<leftarrow> liftE (do {
                  _ \<leftarrow> guard (\<lambda>_. 0 \<le> 2147483650 + y);
                  guard (\<lambda>_. y \<le> 2147483645)
                });
    throw (2 + y)
  })"
  by (simp add: nested_while'_def)


term "just_exit'::(32 signed word, unit, lifted_globals) exn_monad"
thm just_exit'_def[no_vars]
lemma "just_exit' \<equiv> throw 1"
  by (simp add: just_exit'_def)

term "call_exit':: (32 signed word, unit, lifted_globals) exn_monad"
thm call_exit'_def[no_vars]
lemma "call_exit' \<equiv> just_exit'"
  by (simp add: call_exit'_def)

term "ret_or_throw'::int \<Rightarrow> (32 signed word, int, lifted_globals) exn_monad"
thm ret_or_throw'_def[no_vars]
lemma "ret_or_throw' a \<equiv> condition (\<lambda>s. 2 < a)
                     (return 3)
                     (throw 1)"
  by (simp add: ret_or_throw'_def)

term "while_ret_or_break_or_continue':: int \<Rightarrow> (int, lifted_globals) res_monad"
thm while_ret_or_break_or_continue'_def[no_vars]
lemma "while_ret_or_break_or_continue' a \<equiv>
finally
 (try (whileLoop (\<lambda>a s. True)
         (\<lambda>a. condition (\<lambda>s. 3 < a)
                 (throw (Inl 1))
                 (condition (\<lambda>s. 1 < a)
                    (return (a + 1))
                    (throw (Inr a))))
        a))"
  by (simp add: while_ret_or_break_or_continue'_def)

term "fac_exit':: int \<Rightarrow> (32 signed word, int, lifted_globals) exn_monad"
thm fac_exit'.simps[no_vars]
lemma "fac_exit' n = condition (\<lambda>s. n < 0)
                (throw 1)
                (condition (\<lambda>s. n = 0)
                   (return 0)
                   (do { guard (\<lambda>s. n \<le> INT_MAX + 1);
                        fac_exit' (n - 1)
                    }))"
  apply(subst  fac_exit'.simps)
  apply simp
  done


term "while_comb'::int \<Rightarrow> (int, lifted_globals) res_monad"
thm while_comb'_def[no_vars]
lemma "while_comb' a \<equiv> do {
  x \<leftarrow> guard (\<lambda>s. - 1073741824 \<le> a);
  _ \<leftarrow> guard (\<lambda>s. 2 * a \<le> INT_MAX);
  x \<leftarrow> condition (\<lambda>s. 2 * a < 30) (do {
                                     _ \<leftarrow> guard (\<lambda>s. - (INT_MAX + 1) < 2 * a);
                                     return (2 * a - 1)
                                   })
        (do {
           _ \<leftarrow> guard (\<lambda>s. 2 * a \<le> INT_MAX - 1);
           return (2 * a + 1)
         });
  finally (do {
             _ \<leftarrow> try (do {
                         a \<leftarrow> whileLoop (\<lambda>a s. True) (\<lambda>a. condition (\<lambda>s. 3 < a) (throw (Inl 1)) (condition (\<lambda>s. 1 < a) (return (a + 1)) (throw (Inr ())))) a;
                         skip
                       });
             throw x
           })
}"
  by (simp add: while_comb'_def)

term "while_comb_exit':: int \<Rightarrow> (32 signed word, int, lifted_globals) exn_monad"
thm while_comb_exit'_def[no_vars]
lemma "while_comb_exit' a \<equiv> do {
  _ \<leftarrow> liftE (do {
                _ \<leftarrow> guard (\<lambda>s. - 1073741824 \<le> a);
                guard (\<lambda>s. 2 * a \<le> INT_MAX)
              });
  x \<leftarrow> liftE (condition (\<lambda>s. 2 * a < 30) (do {
                                            _ \<leftarrow> guard (\<lambda>s. - (INT_MAX + 1) < 2 * a);
                                            return (2 * a - 1)
                                          })
               (do {
                  _ \<leftarrow> guard (\<lambda>s. 2 * a \<le> INT_MAX - 1);
                  return (2 * a + 1)
                }));
  try (do {
         a \<leftarrow> whileLoop (\<lambda>a s. True) (\<lambda>a. condition (\<lambda>s. 3 < a) (throw (Inr 1)) (condition (\<lambda>s. 1 < a) (return (a + 1)) (throw (Inl 1)))) a;
         throw (Inr x)
       })
}"
  by (simp add: while_comb_exit'_def)

term "while_ret_or_throw'::int \<Rightarrow> (32 signed word, int, lifted_globals) exn_monad"
thm "while_ret_or_throw'_def"[no_vars]
lemma "while_ret_or_throw' a \<equiv>
try (do {
       ret \<leftarrow>
         try (whileLoop (\<lambda>ret s. True)
               (\<lambda>ret. condition (\<lambda>s. 3 < a) (throw (Inl (Inr 1)))
                        (condition (\<lambda>s. 1 < a) (throw (Inl (Inl 1))) (throw (Inr ()))))
               ());
       throw (Inr 2)
     })"
  by (simp add: while_ret_or_throw'_def)

term "control_flow'::int \<Rightarrow> (int, lifted_globals) res_monad"
term whileLoop


thm "control_flow'_def"[no_vars]
term bind

lemma "control_flow' n \<equiv> do {
  (b::int) \<leftarrow> unknown;
  finally (do {
             j \<leftarrow> whileLoop (\<lambda>j s. j < n)
                    (\<lambda>j. do {
                          (i, j) \<leftarrow> whileLoop (\<lambda>(i, j) s. i < n)
                                      (\<lambda>(i, j). do {
                                            j \<leftarrow> condition (\<lambda>s. b \<noteq> 0)
                                                   (throw 0)
                                                   (return j);
                                            liftE (do {
                                                     x \<leftarrow> guard (\<lambda>s. 0 \<le> 2147483649 + i);
                                                     _ \<leftarrow> guard (\<lambda>s. i < INT_MAX);
                                                     return (i + 1, j)
                                                   })
                                          })
                                     (j, j);
                          liftE (do {
                                   x \<leftarrow> guard (\<lambda>s. 0 \<le> 2147483649 + j);
                                   _ \<leftarrow> guard (\<lambda>s. j < INT_MAX);
                                   return (j + 1)
                                 })
                        })
                   0;
             throw 0
           })
}"
  unfolding control_flow'_def .


term "control_flow_exit'::int \<Rightarrow> (int, lifted_globals) res_monad"
thm "control_flow_exit'_def"[no_vars]
lemma "control_flow_exit' n \<equiv> do {
  b \<leftarrow> unknown::(int, lifted_globals) res_monad;
  i \<leftarrow> unknown;
  finally (do {
             (i, j) \<leftarrow> whileLoop (\<lambda>(i, j) s. j < n)
                         (\<lambda>(i, j). do {
                               (i, j) \<leftarrow> whileLoop (\<lambda>(i, j) s. i < n)
                                           (\<lambda>(i, j). do {
                                                 j \<leftarrow> condition (\<lambda>s. b \<noteq> 0)
                                                        (throw 0)
                                                        (return j);
                                                 liftE (do {
                                                          x \<leftarrow> guard (\<lambda>s. 0 \<le> 2147483649 + i);
                                                          _ \<leftarrow> guard (\<lambda>s. i \<le> INT_MAX - 1);
                                                          return (i + 1, j)
                                                        })
                                               })
                                          (j, j);
                               liftE (do {
                                        x \<leftarrow> guard (\<lambda>s. 0 \<le> 2147483649 + j);
                                        _ \<leftarrow> guard (\<lambda>s. j \<le> INT_MAX - 1);
                                        return (i, j + 1)
                                      })
                             })
                        (i, 0);
             liftE (do {
                      x \<leftarrow> guard (\<lambda>s. - (INT_MAX + 1) \<le> j + i);
                      _ \<leftarrow> guard (\<lambda>s. j + i \<le> INT_MAX);
                      return (j + i)
                    })
           })
}"
  by (simp add: control_flow_exit'_def)


term "control_flow_exit1'::int \<Rightarrow> (8 word, lifted_globals) res_monad"
thm "control_flow_exit1'_def"[no_vars]
lemma "control_flow_exit1' n \<equiv> finally (do {
                                    result \<leftarrow> whileLoop (\<lambda>result s. True)
                                                (\<lambda>result. do {
                                                      result \<leftarrow> condition (\<lambda>s. n \<noteq> 0)
                                                                  (throw 1)
                                                                  (return result);
                                                      _ \<leftarrow> unless (n = 0) (throw result);
                                                      return result
                                                    })
                                               0;
                                    return 1
                                  })"
  by (simp add: control_flow_exit1'_def)

term "plus'::32 word \<Rightarrow> 32 word \<Rightarrow> 32 word"
thm plus'_def[no_vars]
lemma "plus' a b \<equiv> a + b"
  by (simp add: plus'_def)

term "plus2':: 32 word \<Rightarrow> 32 word \<Rightarrow> lifted_globals \<Rightarrow> 32 word option"
thm "plus2'_def"[no_vars]
lemma "plus2' a b \<equiv> do {
  (a, b) \<leftarrow>
    owhile (\<lambda>(a, b) a. 0 < b) (\<lambda>(a, b). oreturn (a + 1, b - 1)) (a, b);
  oreturn a
}"
  by (simp add: plus2'_def)

term "call_plus':: 32 word"
thm "call_plus'_def"[no_vars]
lemma "call_plus' \<equiv> plus' 2 3"
  by (simp add: call_plus'_def)

term "fac'::32 word \<Rightarrow> lifted_globals \<Rightarrow> 32 word option"
thm "fac'.simps"[no_vars]
lemma "fac' n = ocondition (\<lambda>s. n = 0) (oreturn 0) (fac' (n - 1))"
  by (subst fac'.simps) simp


term "call_fac_exit':: int \<Rightarrow> (32 signed word, int, lifted_globals) exn_monad"
thm "call_fac_exit'_def"[no_vars]
lemma "call_fac_exit' n \<equiv> do {
  _ \<leftarrow> liftE (do {
                _ \<leftarrow> guard (\<lambda>s. 0 \<le> 2147483649 + n);
                guard (\<lambda>s. n \<le> INT_MAX - 1)
              });
  ret'int'1 \<leftarrow> fac_exit' (n + 1);
  _ \<leftarrow> guard (\<lambda>s. n \<le> 2147483645);
  ret'int'2 \<leftarrow> fac_exit' (n + 2);
  liftE (do {
           x \<leftarrow> guard (\<lambda>s. - (INT_MAX + 1) \<le> ret'int'1 + ret'int'2);
           _ \<leftarrow> guard (\<lambda>s. ret'int'1 + ret'int'2 \<le> INT_MAX);
           return (ret'int'1 + ret'int'2)
         })
}"
  by (simp add: call_fac_exit'_def)

term "even'::32 word \<Rightarrow> lifted_globals \<Rightarrow> 32 word option"
thm "even'.simps"[no_vars]
lemma "even' n =
ocondition (\<lambda>s. n = 0) (oreturn 1)
 (do {
    ret \<leftarrow> odd' (n - 1);
    oreturn (if ret = 0 then 1 else 0)
  })"
  by (subst even'.simps) simp

term "odd'::32 word \<Rightarrow> lifted_globals \<Rightarrow> 32 word option"
thm "odd'.simps"[no_vars]
lemma "odd' n =
ocondition (\<lambda>s. n = 0) (oreturn 0)
 (do {
    ret \<leftarrow> even' (n - 1);
    oreturn (if ret = 0 then 1 else 0)
  })"
  by (subst odd'.simps) simp

term "main'::32 word"
thm "main'_def"[no_vars]
thm plus'_def
lemma "main' \<equiv> if plus' 2 3 = 0 then 1 else 0"
  by (simp add: main'_def)

thm "goo'_def"[no_vars]
lemma "goo' a b c \<equiv> finally (do {
                         _ \<leftarrow> unless (a = 0) (unless (b = 0) (throw (- 1)));
                         ix \<leftarrow> whileLoop (\<lambda>ix s. ix = (0::32 word))
                                 (\<lambda>ix. do {
                                       ret'unsigned'1 \<leftarrow> return (id' c);
                                       _ \<leftarrow> unless (ret'unsigned'1 = 0) (throw (- 1));
                                       return 1
                                     })
                                0;
                         throw 0
                       })"
  by (simp add: goo'_def)
end

end


