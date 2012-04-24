(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Tests"
theory Test
imports Efficient_Nat Collections
begin
text_raw {*\label{thy:Test}*}


text {*
  In this theory, the performance of the basic operations (memb, ins, delete and iterator) of
  various set implementations is tested.
*}

  -- "Simple linear congruence generator for (low-quality) random numbers"
  definition "lcg_next s r = (s mod r, ((22695477::nat)*s + 1) mod 268435456)"

  -- "Repeatedly apply function"
  fun repeat where
    "repeat 0 f \<sigma> = \<sigma>" |
    "repeat (Suc n) f \<sigma> = repeat n f (f \<sigma>)"

  
  -- "Insert random number in range [0..M[ to set"
  definition "rnd_ins_step i M == (\<lambda>(t,s). let (x,s')=lcg_next s M; t'=i x t in (t',s'))"

  -- "Insert N random numbers in range 0..M"
  definition "rnd_insert e i s N M == repeat 
    N (rnd_ins_step i M) (e,s)"

  -- "Remove random number in range [0..M[ from set"
  definition "rnd_remove_step r M == (\<lambda>(t,s). let (x,s')=lcg_next s M; t'=r x t in (t',s'))"
  -- "Remove N random numbers in range 0..M from set"
  definition "rnd_remove r N M txs == 
    repeat N (rnd_remove_step r M) txs"

  -- "Test random number in range [0..M[ for membership"
  definition "rnd_memc_step m M t == (\<lambda>(c,s). let (x,s')=lcg_next s M; c'=if m x t then c+(1::nat) else c in (c',s'))"

  -- "Count how many of N random numbers in range [0..M[ are in set"
  definition "rnd_memc m N M txs ==
    let (t,s) = txs in
      repeat 
        N
        (rnd_memc_step m M t)
        (0::nat,s)
      "

  -- {* Parameters: empty, member, insert, delete, iterate,  seed, N, M \rightarrow count, size *}
  definition 
    test_all :: "(unit \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) 
      \<Rightarrow> ('s \<Rightarrow> (nat,nat) set_iterator) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)"
    where
    "test_all e m i d it s N M == let (t,s) = (rnd_remove d N M (rnd_insert (e ()) i s N M)) in
      (fst (rnd_memc m N M (t,s)), it t (\<lambda>_. True) (\<lambda>x c. c+(1::nat)) 0)"

  (* No iteration *)
  definition 
    test_all' :: "(unit \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
    where
    "test_all' e m i d s N M == let (t,s) = (rnd_remove d N M (rnd_insert (e ()) i s N M)) in
      (fst (rnd_memc m N M (t,s)))"

  (* No iteration, no removal *)
  definition 
    test_all'' :: "(unit \<Rightarrow> 's) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
    where
    "test_all'' e m i s N M == let (t,s) = (rnd_insert (e ()) i s N M) in
      (fst (rnd_memc m N M (t,s)))"



  definition "test_hs == test_all hs_empty hs_memb hs_ins hs_delete hs_iteratei"
  definition "test_rs == test_all rs_empty rs_memb rs_ins rs_delete rs_iteratei"
  definition "test_ls == test_all ls_empty ls_memb ls_ins ls_delete ls_iteratei"
  (*definition "test_ts == test_all ts_empty ts_memb ts_ins ts_delete ts_iteratei"*)
  definition "test_ahs == test_all ahs_empty ahs_memb ahs_ins ahs_delete ahs_iteratei"

  definition "test_hs' == test_all' hs_empty hs_memb hs_ins hs_delete"
  definition "test_rs' == test_all' rs_empty rs_memb rs_ins rs_delete"
  definition "test_ls' == test_all' ls_empty ls_memb ls_ins ls_delete"
  (*definition "test_ts' == test_all' ts_empty ts_memb ts_ins ts_delete"*)
  definition "test_ahs' == test_all' ahs_empty ahs_memb ahs_ins ahs_delete"
  definition "test_cg' == test_all' (\<lambda>_. {}) (op \<in>) insert (\<lambda>x s. s-{x})"


  definition "test_hs'' == test_all'' hs_empty hs_memb hs_ins"
  definition "test_rs'' == test_all'' rs_empty rs_memb rs_ins"
  definition "test_ls'' == test_all'' ls_empty ls_memb ls_ins"
  (*definition "test_ts'' == test_all'' ts_empty ts_memb ts_ins"*)
  definition "test_ahs'' == test_all'' ahs_empty ahs_memb ahs_ins"
  definition "test_cg'' == test_all'' (\<lambda>_. {}) (op \<in>) insert"

(*
  code_module Test file "/dev/stdout" contains test_cg' test_cg''
  ML {*
    open Test;

    val start = Time.now();
    test_cg' 1 8000 16000;
    val rt = Time.toMilliseconds (Time.now() - start);
    *}
*)


  export_code
    test_hs test_rs test_ls test_ahs 
    test_hs' test_rs' test_ls' test_ahs' test_cg'
    test_hs'' test_rs'' test_ls'' test_ahs'' test_cg''
    in SML 
    module_name Test
    

  (*
    Ad-hoc test code:
  *)
  ML_val {*
    val start = Time.now();
    @{code test_ahs} 1 100000 200000;
    val rt = Time.toMilliseconds (Time.now() - start);
    *}

  (*
  export_code 
    test_hs test_rs test_ls test_ts test_ahs 
    test_hs' test_rs' test_ls' test_ts' test_ahs'  test_nts' test_ntsc' test_cg'
    test_hs'' test_rs'' test_ls'' test_ts'' test_ahs''  test_nts'' test_cg''
    in SML 
    module_name Test 
    file "code/sml/generated/Test.ml"
  export_code 
    test_hs test_rs test_ls test_ts test_ahs
    test_hs' test_rs' test_ls' test_ts' test_ahs' test_nts' test_ntsc' test_cg'
    test_hs'' test_rs'' test_ls'' test_ts'' test_ahs'' test_nts'' test_cg''
    in OCaml 
    module_name Test 
    file "code/ocaml/generated/Test.ml"
  export_code 
    test_hs test_rs test_ls test_ts test_ahs
    test_hs' test_rs' test_ls' test_ts' test_ahs' test_nts' test_ntsc' test_cg'
    test_hs'' test_rs'' test_ls'' test_ts'' test_ahs'' test_nts'' test_cg''
    in Haskell 
    module_name Test 
    file "code/haskell/generated"
    (*string_classes*)
    *)


end
