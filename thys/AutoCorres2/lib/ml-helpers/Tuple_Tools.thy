(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "Proof Tools"

theory Tuple_Tools

imports Main
  "Misc_Antiquotation"
  TermPatternAntiquote
  ML_Fun_Cache

begin

section \<open>Tools for handling Tuples\<close>

text \<open>
The tools are supposed to help simplifiying expressions containing @{const case_prod}
constructions, like @{term "\<lambda>(w, x, y, z). f w x y z"}.

\<^item> Simprocs for single step splitting and simplification of tuples / \<open>case_prods\<close> instead of repeated
application of the built-in variants for pairs
\<^item> Looper for the simplifier to instantiate @{term f} in @{term "f (a,b,c)"} with
@{term "\<lambda>(a,b,c). g a b c"}
\<close>

subsection \<open>Antiquotations for terms with schematic variables\<close>

setup \<open>
let
  val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax
  fun pattern (ctxt, str) =
     str |> Proof_Context.read_term_pattern ctxt
         |> ML_Syntax.print_term
         |> ML_Syntax.atomic
in
 ML_Antiquotation.inline @{binding "pattern"} (parser >> pattern)
end
\<close>

ML \<open>@{pattern "\<lambda>(a,b,c). ?g a b c"}\<close>

setup \<open>
let
type style = term -> term;

fun pretty_term_style ctxt (style: style, t) =
  Document_Output.pretty_term ctxt (style t);

val basic_entity = Document_Output.antiquotation_pretty_source;

in
(* Document antiquotation that allows schematic variables *)
(basic_entity \<^binding>\<open>pattern\<close> (Term_Style.parse -- Args.term_pattern) pretty_term_style)
end
\<close>



text \<open>Unification only works modulo ordinary beta reduction but does not succeed on
tupled-beta reduction. For example the simplifier will not find an instatiation for the variable
@{pattern "?c"}
\<close>

schematic_goal "\<And>a b. (case (a, b) of (x, y) \<Rightarrow> f x y) \<equiv> ?c (a, b)"
  apply simp
  oops

text \<open>Such equations can typically occur in congruence rules when a pair is splitted by
@{thm split_paired_all}.\<close>

lemma tuple_up_eq_trivial: "f r  \<equiv> (\<lambda>x. f x) r"
  by simp

thm tuple_up_eq_trivial
lemma tuple_up_eq2: "f (fst r) (snd r) \<equiv> (case r of (x1, x2) \<Rightarrow> f x1 x2)"
  by (simp add: split_def)

text \<open>Constant to explictly trigger splitting by simproc \<^verbatim>\<open>SPLIT_simproc\<close> below\<close>


definition SPLIT :: "'a::{} \<Rightarrow> 'a"
  where "SPLIT P  \<equiv> P"

lemma SPLIT_cong: "PROP SPLIT P \<equiv> PROP SPLIT P"
  by simp

lemma case_prod_out: "(\<lambda>r. f ((\<lambda>(a,b). (g a b)) r)) = (\<lambda>(a, b). f (g a b))"
  apply (rule ext)
  apply (simp add: split_paired_all)
  done

lemma case_prod_eta_contract: "(\<lambda>x. (case_prod s) x) \<equiv> (case_prod s)"
  by simp

definition ETA_TUPLED :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "ETA_TUPLED f  \<equiv> f"

lemma ETA_TUPLED_trans: "f \<equiv> g \<Longrightarrow> ETA_TUPLED f \<equiv> g"
  by (simp add: ETA_TUPLED_def)

text \<open>Add the congruence rule @{thm SPLIT_cong} to the simpset together with the simproc
to avoid descending into @{term P} before the split.\<close>

ML \<open>
structure Bin =
struct

type Bin = bool list

fun bin_of_int n =
  if n < 0 then error ("bin: " ^ "cannot convert negativ number '" ^ string_of_int n ^ "'")
  else map (fn 0 => false | _ => true) (radixpand (2,n));

fun int_of_bin bs =
  let
    fun int_of pos [] = 0
      | int_of pos (false::bs) = int_of (2 * pos) bs
      | int_of pos (true::bs) = pos + int_of (2 * pos) bs
  in int_of 1 (rev bs) end

fun string_of_bin bs =
  let
    fun bit true = #"1"
      | bit false = #"0"
  in
     "0b" ^ String.implode (map bit bs)
  end

val bin_ord = list_ord bool_ord;
structure Bintab = Table(type key = Bin val ord = bin_ord);

val _ = @{assert} (int_of_bin (bin_of_int 1) = 1)
val _ = @{assert} (int_of_bin (bin_of_int 22) = 22)
val _ = @{assert} (int_of_bin (bin_of_int 43) = 43)
val _ = @{assert} (is_none (try bin_of_int ~1))
val _ = @{assert} (string_of_bin (bin_of_int 0) = "0b0")
val _ = @{assert} (string_of_bin (bin_of_int 1) = "0b1")
val _ = @{assert} (string_of_bin (bin_of_int 7) = "0b111")
val _ = @{assert} (string_of_bin (bin_of_int 23) = "0b10111")
end
\<close>

ML \<open>
structure Tuple_Tools = struct

\<comment> \<open>We document the effect of functions using assertions\<close>

\<comment> \<open>t has to be type correct and be equivalent to ct modulo beta/eta reduction and typing\<close>
fun assert_cterm' ctxt t ct =
  let
    val t1 = Envir.beta_eta_contract (Thm.term_of (Thm.cterm_of ctxt t))
    val t2 = Envir.beta_eta_contract (Thm.term_of ct)
  in @{assert} (Term.aconv_untyped (t1, t2)) end

val assert_cterm = assert_cterm' @{context}

fun assert_term t1 t2 = @{assert} (t1 = t2)

fun gen_mk_prod (t1, T1) (t2, T2) =
  (HOLogic.pair_const T1 T2 $ t1 $ t2, HOLogic.mk_prodT (T1, T2))

fun gen_mk_tuple [] = (@{term "()"}, @{typ "unit"})
  | gen_mk_tuple [(t, T)] = (t, T)
  | gen_mk_tuple (t::ts) = gen_mk_prod t (gen_mk_tuple ts)



\<comment> \<open>Functions to create various terms on tuples.
* The primed variants take a list of element types.
* The unprimed variants only take a number (arity of the tuple) and generate default element types.
\<close>

fun mk_elT_named n i = TFree (n ^ string_of_int i, @{sort "type"});
val mk_elT = mk_elT_named "'a"
fun mk_elT' Ts i = nth Ts (i-1);
fun mk_tupleT' Ts i = HOLogic.mk_tupleT (drop (i - 1) Ts);
fun mk_tupleT n i = mk_tupleT' (map mk_elT (1 upto n)) i;


fun mk_el_name_named x i = x ^ string_of_int i;
val mk_el_name = mk_el_name_named "x"

fun mk_el' Ts i = Free (mk_el_name i, mk_elT' Ts i);
fun mk_el_named' x Ts i = Free (mk_el_name_named x i, mk_elT' Ts i);
fun mk_el_named x i = Free (mk_el_name_named x i, mk_elT i);
fun mk_el i = Free (mk_el_name i, mk_elT i);


fun mk_tuple_bounds n = (1 upto n) |> map (fn i => (Bound (n - i), mk_elT i)) |> gen_mk_tuple |> fst
val mk_tuple_packed_name = "r";
fun mk_tuple n i = HOLogic.mk_tuple (map mk_el (i upto n));
fun mk_tuple_named x n i = HOLogic.mk_tuple (map (mk_el_named x) (i upto n));
fun mk_tuple' Ts n i = HOLogic.mk_tuple (map (mk_el' Ts) (i upto n))
fun mk_tuple_named' x Ts n i = HOLogic.mk_tuple (map (mk_el_named' x Ts) (i upto n))

fun mk_tuple_packed n = Free (mk_tuple_packed_name, mk_tupleT n 1);

fun mk_P n = Free ("P", map mk_elT (1 upto n) ---> @{typ "bool"});
fun mk_P_frees n = list_comb (mk_P n, map mk_el (1 upto n));
fun mk_P_bounds n = list_comb (mk_P n, map Bound (n-1 downto 0));

fun mk_Prop_P n = Free ("P", mk_tupleT n 1 --> @{typ "prop"});

fun mk_fun (name,resT) i n = Free (name, map mk_elT (i upto (i+n-1)) ---> resT);
fun mk_fun_bounds (name, resT) i n = list_comb (mk_fun (name, resT) i n, map Bound (n-1 downto 0));

fun mk_fun_with_types Ts (name,resT) = Free (name, map (mk_elT' Ts) (1 upto (length Ts)) ---> resT);
fun mk_fun_bounds_with_types Ts (name, resT) = list_comb (mk_fun_with_types Ts (name, resT), map Bound ((length Ts - 1) downto 0));

val mk_f_resT = @{typ "'b"};
val mk_f_name = "f";
fun mk_f n = Free (mk_f_name, map mk_elT (1 upto n) ---> mk_f_resT);
fun mk_f_frees n = list_comb (mk_f n, map mk_el (1 upto n));
fun mk_f_bounds n = list_comb (mk_f n, map Bound (n-1 downto 0));



fun mk_f_tupled n = Free (mk_f_name, mk_tupleT n 1 --> mk_f_resT)

fun mk_selT n i = mk_tupleT n 1 --> mk_elT i;
fun mk_selT' Ts i = mk_tupleT' Ts i --> mk_elT' Ts i;
fun mk_snd n i = Const (@{const_name \<open>snd\<close>}, mk_tupleT n i --> mk_tupleT n (i+1));
fun mk_snd' Ts i = Const (@{const_name \<open>snd\<close>}, mk_tupleT' Ts i --> mk_tupleT' Ts (i+1));
fun mk_fst n i = Const (@{const_name \<open>fst\<close>}, mk_tupleT n i --> mk_elT i);
fun mk_fst' Ts i = Const (@{const_name \<open>fst\<close>}, mk_tupleT' Ts i --> mk_elT' Ts i);

fun mk_snds' Ts i r =
  let
    val n = length Ts;
  in
    if n = 1 then r
    else
      if i = (n-1) then mk_snd' Ts 1 $ r
      else mk_snd' Ts (n - i) $ (mk_snds' Ts (i+1) r)
  end;

fun mk_snds n i r =
  if i = (n-1) then mk_snd n 1 $ r
  else mk_snd n (n - i) $ (mk_snds n (i+1) r)

fun mk_sel' Ts r i =
  let
    val n = length Ts;
  in
    if n = 1 then r
    else
      if i = 1 then mk_fst' Ts 1 $ r
      else if i = n then mk_snds' Ts 1 r
      else mk_fst' Ts i $ mk_snds' Ts (n - i + 1) r
  end;

val _ = assert_term (mk_sel' ([@{typ 'a}, @{typ 'b}, @{typ 'c}, @{typ 'd}]) (Bound 0) 4)
(Const (@{const_name snd}, @{typ "'c \<times> 'd \<Rightarrow> 'd"}) $
  (Const (@{const_name snd}, @{typ "'b \<times> 'c \<times> 'd \<Rightarrow> 'c \<times> 'd"}) $
    (Const (@{const_name snd}, @{typ "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'b \<times> 'c \<times> 'd"}) $ Bound 0)))

val _ = assert_term (mk_sel' ([@{typ 'a}, @{typ 'b}, @{typ 'c}, @{typ 'd}]) (Bound 0) 3)
(Const (@{const_name fst}, @{typ "'c \<times> 'd \<Rightarrow> 'c"}) $
  (Const (@{const_name snd}, @{typ "'b \<times> 'c \<times> 'd \<Rightarrow> 'c \<times> 'd"}) $
    (Const (@{const_name snd}, @{typ "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'b \<times> 'c \<times> 'd"}) $ Bound 0)))

fun mk_sel n r i =
  if i = 1 then mk_fst n 1 $ r
  else if i = n then mk_snds n 1 r
  else mk_fst n i $ mk_snds n (n - i + 1) r

fun mk_eq n r i =
  HOLogic.mk_eq (mk_sel n r i, mk_el i);

fun mk_case_prod_from T t i n =
  let
    fun mk_cp n i =
      if (n - i) <= 1 then
        HOLogic.case_prod_const (mk_elT i, mk_elT n, T) $
          (Abs (mk_el_name i, mk_elT i, Abs (mk_el_name n, mk_elT n, t)))
    else
        HOLogic.case_prod_const (mk_elT i, mk_tupleT n (i+1), T) $
          (Abs (mk_el_name i, mk_elT i, mk_cp n (i+1)))
  in mk_cp (n+i-1) i end;



fun mk_case_prod T t n =
  mk_case_prod_from T t 1 n

fun mk_case_prod_with_types Ts T t =
  let
    val n = length Ts
    fun mk_cp n i =
      if (n - i) <= 1 then
        HOLogic.case_prod_const (mk_elT' Ts i, mk_elT' Ts n, T) $
          (Abs (mk_el_name i, mk_elT' Ts i, Abs (mk_el_name n, mk_elT' Ts n, t)))
    else
        HOLogic.case_prod_const (mk_elT' Ts i, mk_tupleT' Ts (i+1), T) $
          (Abs (mk_el_name i, mk_elT' Ts i, mk_cp n (i+1)))
  in mk_cp n 1 end;

fun mk_case_prod_P n = mk_case_prod @{typ bool} (mk_P_bounds n) n;
fun mk_case_prod_f n = mk_case_prod mk_f_resT (mk_f_bounds n) n;
fun mk_case_prod_fun (name, resT) i n = mk_case_prod_from resT (mk_fun_bounds (name, resT) i n) i n;
fun mk_case_prod_fun_with_types Ts (name, resT) = mk_case_prod_with_types Ts resT (mk_fun_bounds_with_types Ts (name, resT));
fun mk_case_prod_f_tupled_bounds n = mk_case_prod mk_f_resT (mk_f_tupled n $ mk_tuple_bounds n) n

fun argTs_of_TVar n [(TVar ((x,_),_))] = map (mk_elT_named x) (1 upto n)
  | argTs_of_TVar _ Ts = Ts

fun mk_case_prod' name T n =
  if n <= 1 then Free (name, T)
  else
    let
      val (domT, rangeT) = dest_funT T
      val argTs = HOLogic.strip_tupleT domT |> argTs_of_TVar n
    in
      if length argTs = n
      then mk_case_prod_fun_with_types argTs (name, rangeT) (* Type was already instantiated so we take those types *)
      else mk_case_prod_fun (name, rangeT) 1 n
    end

fun mk_tuple_from_type name T n =
  if n <= 1 then Free (name, T)
  else
     let
       val Ts = HOLogic.strip_tupleT T
     in
       if length Ts = n
       then mk_tuple_named' name Ts n 1
       else mk_tuple_named name n 1
     end

fun mk_tuple_or_case_prod name T n =
  if is_some (try dest_funT T)
  then mk_case_prod' name T n
  else mk_tuple_from_type name T n


fun mk_f_sels n r = list_comb (mk_f n, map (mk_sel n r) (1 upto n));

fun mk_tuple_up_eq n =
  let
    val r = mk_tuple_packed n;
    val lhs = mk_f_sels n r;
    val rhs = mk_case_prod_f n $ r;
  in Logic.mk_equals (lhs, rhs) end

val _ = assert_cterm (mk_tuple_up_eq 3)
  @{cterm "f (fst r) (fst (snd r)) (snd (snd r)) \<equiv> case r of (x1, x2, x3) \<Rightarrow> f x1 x2 x3"}

fun mk_tuple_up_eq_thm ctxt n =
  let
    val fixes = [mk_tuple_packed n,mk_f n]
      |> map (fn (Free (x, _)) => x);
  in
    Goal.prove ctxt fixes [] (mk_tuple_up_eq n) (fn _ =>
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps [mk_meta_eq @{thm split_def}]) 1)
  end


fun mk_tuple_case_eq n =
  let
     val lhs = mk_case_prod_f n $ mk_tuple n 1
     val rhs = mk_f_frees n
  in
    Logic.mk_equals (lhs, rhs)
  end

val _ =  assert_cterm (mk_tuple_case_eq 3)
 @{cterm "case (x1, x2, x3) of (x1, x2, x3) \<Rightarrow> f x1 x2 x3 \<equiv> f x1 x2 x3"}

fun mk_tuple_case_eq_thm ctxt n =
  let
    val fixes = mk_f n::map mk_el (1 upto n)
      |> map (fn (Free (x, _)) => x)
  in
    Goal.prove ctxt fixes [] (mk_tuple_case_eq n) (fn _ =>
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm Product_Type.prod.case}]) 1)
  end



fun num_case_prod t =
  case strip_comb t of
    (Const (@{const_name case_prod},_) , (Abs (_, _, cp))::_) => 1 + num_case_prod cp
  | (Const (@{const_name case_prod},_) , _) => 1
  | _ => 0;

val strip_uu = prefix "strip_" Name.uu_

fun strip_case_prod t =
    case strip_comb t of
      (Const (@{const_name case_prod},_), Abs (x, xT, (Abs (y, yT, _)))::_) =>
         [(x,xT), (y, yT)]
     | (Const (@{const_name case_prod},cpT), Abs (x, xT, cp)::_) =>
          (case strip_comb cp of
            (Const (@{const_name case_prod},_), _) => (x,xT)::strip_case_prod cp
           | _ => (* eta expand lost abstraction in case_prod *)
                 ([(x,xT), (strip_uu, nth (binder_types cpT) 1)]))
     | (Const (@{const_name case_prod}, cpT), cp::_) =>
             (* eta expand lost abstractions in case_prod *)
             let
               val [xT, yT] = take 2 (binder_types (domain_type cpT))
             in [(strip_uu, xT), (strip_uu, yT)] end
     | _ => [];

fun strip_case_prod' (Abs (x, xT, _)) = [(x, xT)]
  | strip_case_prod' t = strip_case_prod t

fun mk_split_tupled_all_lhs n =
  Logic.list_all ([(mk_tuple_packed_name, mk_tupleT n 1)], (mk_Prop_P n) $ Bound 0)

fun mk_prod_bound (i,iT) (t,T) =
  HOLogic.pair_const iT T $ Bound i $ t

fun mk_prod_bounds [(i, iT), (j, jT)] = mk_prod_bound (i,iT) (Bound j, jT)
  | mk_prod_bounds ((i,iT)::xs) =
    let
      val t = mk_prod_bounds xs
    in mk_prod_bound (i,iT) (t, fastype_of t) end

fun mk_split_tupled_all_rhs n =
  let
    val _ = @{assert} (n >= 2)
  in
    Logic.list_all (map (fn i => (mk_el_name i, mk_elT i)) (1 upto n),
      (mk_Prop_P n) $ mk_prod_bounds (map (fn i => (n-i, mk_elT i)) (1 upto n)))
  end

fun mk_split_tupled_all n =
  Logic.mk_equals (mk_split_tupled_all_lhs n, mk_split_tupled_all_rhs n)

val _ = assert_cterm (mk_split_tupled_all 3)
 @{cterm "(\<And>r. PROP P r) \<equiv> (\<And>x1 x2 x3. PROP P (x1, x2, x3))"}

fun mk_split_tupled_all_thm ctxt n =
  Goal.prove ctxt ["P"] [] (mk_split_tupled_all n) (fn _ => simp_tac
    (put_simpset HOL_basic_ss ctxt addsimps @{thms split_paired_all}) 1)

fun mk_eta_tupled_eq n =
  let
    val lhs = mk_f_tupled n
    val rhs = mk_case_prod_f_tupled_bounds n
    val eq = Logic.mk_equals (lhs, rhs)
  in
    eq
  end

fun mk_eta_tupled_eq_thm ctxt n =
      Goal.prove @{context} [mk_f_name] [] (mk_eta_tupled_eq n) (fn _ =>
        simp_tac @{context} 1) |> Thm.transfer' ctxt


structure Data = Generic_Data(
  type T = (thm * thm * thm * thm) list;
  val empty = [];
  fun merge (thms1, thms2) = if length thms1 >= length thms2 then thms1 else thms2;
);


fun get_tuple_up_eq_thm ctxt n =
  if n <= 1 then @{thm tuple_up_eq_trivial}
  else
    Thm.transfer' ctxt (#1 (nth (Data.get (Context.Proof ctxt)) (n - 2)))
    handle Subscript => mk_tuple_up_eq_thm ctxt n

fun get_split_tupled_all_thm ctxt n =
  if n <= 1 then error ("get_split_tupled_all only makes sense for n >= 2")
  else
    Thm.transfer' ctxt (#2 (nth (Data.get (Context.Proof ctxt)) (n - 2)))
    handle Subscript => mk_split_tupled_all_thm ctxt n

fun get_tuple_case_eq_thm ctxt n =
  if n <= 1 then error ("get_tuple_case_eq_thm only makes sense for n >= 2")
  else
    Thm.transfer' ctxt (#3 (nth (Data.get (Context.Proof ctxt)) (n - 2)))
    handle Subscript => mk_tuple_case_eq_thm ctxt n

fun get_eta_tupled_eq_thm ctxt n =
  if n <= 1 then @{thm reflexive}
  else
    Thm.transfer' ctxt (#4 (nth (Data.get (Context.Proof ctxt)) (n - 2)))
    handle Subscript => mk_eta_tupled_eq_thm ctxt n

fun liberal_zip (x::xs) (y::ys) = (x,y)::liberal_zip xs ys
  | liberal_zip _ [] = []
  | liberal_zip [] _ = []

fun get_first_subterm P t =
  if P (Term.head_of t)
  then SOME t
  else
    case t of
      (t1 $ t2) => (case get_first_subterm P t1 of
                     NONE => get_first_subterm P t2
                   | some => some)
    | Abs (_, _ , t) => get_first_subterm P t
    | _ => NONE

\<comment> \<open>Split a tuple completely in one step, instead of repeated applications of @{thm split_paired_all}\<close>
val split_tupled_all_simproc =
  Simplifier.make_simproc @{context}{name = "split_tupled_all_simproc", kind = Simproc, identifier = [],
   lhss = [Proof_Context.read_term_pattern @{context} "\<And>r. PROP ?P r"],
    proc = fn _ => fn ctxt => fn ct =>
     let
        fun get_tuple_arity (Const (@{const_name "Pure.all"},_) $ (Abs (_, T, _))) =
            length (HOLogic.flatten_tupleT T)
          | get_tuple_arity _ = 0;
        val t = Thm.term_of ct
        val n = get_tuple_arity t
     in
       if n >= 2
       then
          let
            fun is_case_prod (Const (@{const_name case_prod}, _)) = true
              | is_case_prod _ = false

            fun guess_names t = case get_first_subterm is_case_prod t of
                  SOME t' => map fst (strip_case_prod t') |> filter_out (fn n => n = strip_uu)
                | _ => []

            val thm = get_split_tupled_all_thm ctxt n
                |> Drule.rename_bvars (liberal_zip (map mk_el_name (1 upto n)) (guess_names t))
          in SOME thm end
       else NONE
     end
   }

\<comment> \<open>Simplify a @{const case_prod} applied to a tuple constructed from @{const Pair} in one
step instead of repeated application of @{thm Product_Type.prod.case} or
@{thm Product_Type.case_prod_conv}\<close>

val tuple_case_simproc =
  Simplifier.make_simproc @{context} {name = "tuple_simproc", kind = Simproc, identifier = [],
   lhss = [Proof_Context.read_term_pattern @{context} "case_prod ?X (?x,?y)"],
    proc = fn _ => fn ctxt => fn ct =>
     let
        fun get_tuple_arity
             (t as (Const (@{const_name Product_Type.prod.case_prod}, _) $ _ $
                     (p as (Const (@{const_name Pair}, _) $ _ $ _)))) =
            Int.min (num_case_prod t + 1, length (HOLogic.strip_tuple p))
          | get_tuple_arity _ = 0;
        val n = get_tuple_arity (Thm.term_of ct)
     in
       if n >= 2
       then SOME (get_tuple_case_eq_thm ctxt n)
       else NONE
     end
   }

\<comment> \<open>Instantiaten for tupled-beta reduction\<close>

local
fun strip_all (Const (@{const_name "Pure.all"}, _ ) $  Abs (x,T,t)) =
  let
    val (vTs, bdy) = strip_all t
  in ((x,T)::vTs, bdy) end
  | strip_all t = ([], t)

fun dest_pair_bound (Const (@{const_name "Product_Type.Pair"}, _) $  Bound i $ p) =
      i::dest_pair_bound p
  | dest_pair_bound (Bound i) = [i]

fun lookup env i = nth env i

fun mk_name env (Bound i) = fst (lookup env i)
  | mk_name env (Var ((x,_),_)) = x
  | mk_name env (Free (x,_)) = x
  | mk_name env _ = Name.uu_;

fun mk_var env (Bound i) = SOME (lookup env i)
  | mk_var _ _ = NONE

fun is_Pair (Const (@{const_name "Product_Type.Pair"}, _) $ _ $ _) = true
  | is_Pair _ = false;

fun dest_tuple env (Const (@{const_name "Product_Type.Pair"}, _) $ t $ p)
    = mk_name env t :: (if is_Pair p then dest_tuple env p else [mk_name env p])

fun dest_tuple' env (Const (@{const_name "Product_Type.Pair"}, _) $ t $ p)
    = mk_var env t :: (if is_Pair p then dest_tuple' env p else [mk_var env p])

fun mk_case_prod' T seed [(n1,T1), (n2, T2)] =
      (Const (@{const_name "case_prod"}, (T1 --> T2 --> T) --> HOLogic.mk_prodT (T1, T2) --> T)$
           Abs (n1, T1, Abs (n2, T2, seed)),  HOLogic.mk_prodT (T1, T2))
  | mk_case_prod' T seed ((n1,T1)::bs) =
      let
        val (t',T2) = mk_case_prod' T seed  bs
      in (Const (@{const_name "case_prod"}, (T1 --> T2 --> T) --> HOLogic.mk_prodT (T1, T2) --> T)$
          Abs (n1, T1, t'), HOLogic.mk_prodT (T1, T2))
      end

fun get_tuple_var env (Var v $
     (p as (Const (@{const_name "Product_Type.Pair"}, _)$ _$ _))) =
       [(env, v, dest_tuple env p)]
  | get_tuple_var env (t1 $ t2) =
      (case get_tuple_var env t1 of
        [] => get_tuple_var env t2
       | xs => xs)
  | get_tuple_var env (Abs (x, T, t)) =
      get_tuple_var ((x,T)::env) t
  | get_tuple_var env _ = [];


fun dest_tuple'' env t = case try (dest_tuple' env) t of
      SOME xs => xs
    | NONE => [NONE]

fun flatten_upto_first_tuple xxs =
  let
    val (upto_one, more) = chop_prefix (fn xs => length xs <= 1) xxs
  in
    if null more then ([],[])
    else (flat (upto_one), hd more)
  end

(* finds function vars that are applied to a tuple in some argument e.g.
 *   ?f x y (a, b)
 *)
fun get_tuple_vars env (t as (_ $ _)) =
   (case strip_comb t of
      (Var v, ts) =>
        let
          val (args, tuple_args) = map (dest_tuple'' env) ts |> flatten_upto_first_tuple
          val rest = map (get_tuple_vars env) ts |> flat
        in
          if null tuple_args then rest
          else (env, v, (args, tuple_args)) :: rest
        end
     | (t, ts) => map (get_tuple_vars env) (t::ts) |> flat)
  | get_tuple_vars env (Abs (x, T, t)) =
      get_tuple_vars ((x,T)::env) t
  | get_tuple_vars _ _ = [];


fun get_distinct_tuple_vars env t =
  t |> get_tuple_vars env |> distinct (fn ((_,v1,_),(_,v2,_)) => v1 = v2)

in


val list_abs = fold_rev Term.abs

fun map_filter2 _ [] [] = []
  | map_filter2 f (x :: xs) (y :: ys) =
     let
       val vs = map_filter2 f xs ys
     in case f x y of SOME v => v :: vs | _ => vs end
  | map_filter2 _ _ _ = raise ListPair.UnequalLengths;

fun gen_calc_inst bound get_tuple_vars ctxt max_idx t = \<^try>\<open>
   get_tuple_vars [] t
  |> map (fn (_,((x,i), pT), (args, bs)) =>
    let
      val (all_argTs, finalT) = strip_type pT
      val (argTs, ([tupleT], rest_argTs)) = all_argTs |> chop (length args) ||> chop 1

      fun mk_vars bound vs Ts = (vs ~~ Ts)
        |> map (fn (SOME (x, _), T) => (true, (x, T))
            | (NONE, T) => if bound then (false, (Name.uu_, T)) else (true, (Name.uu_, T)))

      fun filter_tagged tags xs = map_filter2 (fn b => fn x => if b then SOME x else NONE) tags xs

      val tagged_args = mk_vars false args argTs
      val args = map snd tagged_args
      val tagged_tuple_args = mk_vars bound bs (HOLogic.flatten_tupleT tupleT)
      val tuple_args = map snd tagged_tuple_args
      val tagged_vars = tagged_args @ tagged_tuple_args
      val tags = map fst tagged_vars
      val vars = map snd tagged_vars

      val bnds = length vars - 1 downto 0 |> filter_tagged tags
      val Ts = map snd vars |> filter_tagged tags
      val rT = rest_argTs ---> finalT
      val newVar = Var ((x,max_idx+1), Ts ---> rT)
      val seed = Term.list_comb (newVar, map Bound bnds)
      val case_prod = fst (mk_case_prod' rT seed tuple_args)
      val inst = list_abs args case_prod
    in ((x,i), Thm.cterm_of ctxt inst) end
  ) catch _ => []\<close>

fun calc_first_inst bound = gen_calc_inst bound (fn env => take 1 o get_tuple_vars env)
val calc_inst = calc_first_inst true
val calc_inst' = calc_first_inst false
val calc_insts = gen_calc_inst false get_distinct_tuple_vars

end


(* For a goal with a schematic variable of the form

   ?f (x1,x2,...,xn)

   as it might occur in an congruence rule

      \<And>... x1 ... xn ... . ?X \<equiv> ?f (x1,x2,...,xn) ...

   instantiate ?f to \<lambda>(x1,x2,...,xn). ?f' x1 x2 ... xn ...

   Currently only instantiates the first such ?f it finds by a canonical traversal of the term.
   The tupled argument does not have to be the first argument, also works for the more general case
   like ?f t1 t2 (x1,x2,...,xn) t3 t4

   tuple_inst_tac can be used as a looper.
*)

fun cond_trace ctxt s =
  if Config.get ctxt Simplifier.simp_trace then tracing s else ()

fun tuple_inst_tac ctxt i = SUBGOAL (fn (trm, _) => fn st =>
  let
    val max_idx = Thm.maxidx_of_cterm (Thm.cprop_of st)
  in
    case calc_inst ctxt max_idx trm of
      [] => (cond_trace ctxt "tuple_inst_tac: no instantiation found"; no_tac st)
    | inst => let
                 val _ = cond_trace ctxt ("tuple_inst_tac: " ^ @{make_string} inst);
              in PRIMITIVE (Drule.infer_instantiate ctxt inst) st end
  end) i;

fun tuple_insts ctxt thm =
  let
    val max_idx = Thm.maxidx_of_cterm (Thm.cprop_of thm)
  in
    case calc_insts ctxt max_idx (Thm.prop_of thm) of
      [] => thm
    | inst => let
                 val _ = cond_trace ctxt ("tuple_inst_tac: " ^ @{make_string} inst);
              in Drule.infer_instantiate ctxt inst thm end
  end;

(* case_prod ?f (Pair ...) ... *)
fun is_case_prod_app_Pair t =
  case Term.strip_comb t of
    (Const (@{const_name "case_prod"}, _), _ :: maybe_pair :: _) => (case Term.strip_comb maybe_pair of
      (Const (@{const_name "Pair"}, _), _) => true | _ => false)
  | _ => false

(* apply beta reduction for Pairs *)
fun mksimps ctxt thm =
  let
    val thm' = (if exists_subterm is_case_prod_app_Pair (Thm.prop_of thm)
      then
         let
           val thm' = Simplifier.simplify (put_simpset HOL_ss ctxt addsimps @{thms Product_Type.prod.case}) thm
           val _ = cond_trace ctxt ("Tuple_Tools.mksimps: " ^ @{make_string} thm')
         in thm' end (* (%(x,y). f x y) (a,b) = f a b *)
      else thm)
  in (Simpdata.mksimps Simpdata.mksimps_pairs) ctxt thm'
  end

val SPLIT_simproc =
  Simplifier.make_simproc @{context} {name = "SPLIT_simproc", kind = Simproc, identifier = [],
    lhss = [Proof_Context.read_term_pattern @{context} "PROP SPLIT ?P",
            Proof_Context.read_term_pattern @{context} "SPLIT ?P"],
    proc = fn _ => fn ctxt => fn ct =>
     let
        fun get_tuple_arity (Const (@{const_name "SPLIT"}, _)$
              (Const (@{const_name "Pure.all"},_) $ (Abs (_, T, _)))) =
            length (HOLogic.flatten_tupleT T)
          | get_tuple_arity _ = 0;
        val t = Thm.term_of ct
        val n = get_tuple_arity t
     in
       if n >= 2
       then
          let
            fun is_case_prod (Const (@{const_name case_prod}, _)) = true
              | is_case_prod _ = false

            fun guess_names t = case get_first_subterm is_case_prod t of
                  SOME t' => map fst (strip_case_prod t') |> filter_out (fn n => n = strip_uu)
                | _ => []

            val split_thm = get_split_tupled_all_thm ctxt n
                |> Drule.rename_bvars (liberal_zip (map mk_el_name (1 upto n)) (guess_names t))

            val case_eq_thm = get_tuple_case_eq_thm ctxt n

            val conv = Conv.rewr_conv @{thm SPLIT_def}
                 then_conv Conv.rewr_conv split_thm
                 then_conv (Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv case_eq_thm))) ctxt)

          in SOME (conv ct) end
       else SOME @{thm SPLIT_def}
     end
   }

fun asserts [] x = x
  | asserts ((cond, msg)::xs) x = if cond x then asserts xs x else error (msg x)

structure Intlisttab = Table(type key = int list val ord = list_ord int_ord);

fun comb_product [] = [[]]
  | comb_product (xs:: yss) =
      let
        val prods = comb_product yss
        val prodss = map (fn x => map (fn ps => x::ps) prods) xs
      in
         flat prodss
      end

val _ = @{assert} (comb_product [[1,2],[3,4],[5,6]] =
       [[1, 3, 5], [1, 3, 6], [1, 4, 5], [1, 4, 6], [2, 3, 5], [2, 3, 6], [2, 4, 5], [2, 4, 6]])

(*
 * Generates a custom rule with the tuple arity of an abstracted variable. The position of the
 * abstraction is specified in the pattern (which is also used as simproc pattern). Every real variable
 * in that pattern (besides the dummy pattern _) will be considered as an abstraction to split. E.g.
 * thm: "\<And>v. P (?y v) \<Longrightarrow> seq ?x (\<lambda>x. ?y x)" with pattern "seq _ ?Y"
 * When this is applied to a term "seq x (\<lambda>(a,b,c). ?y a b c)" a rule of arity 3 will be generated:
 * "\<And>a b c. P (?y a b c) \<Longrightarrow> seq ?x (\<lambda>(a, b, c). ?y a b c)" which can be matched with the term.
 *)
fun split_rule_simproc ctxt name pattern rule =
  let
    val pat =  Proof_Context.read_term_pattern ctxt pattern
    fun dest_eq thm =
      let
        val @{term_pat "Trueprop (?lhs = ?rhs)"} = thm |> Thm.concl_of
      in (lhs, rhs) end

    val lhs = rule |> dest_eq |> fst

    val (tenv, term_env) = Pattern.match (Proof_Context.theory_of ctxt) (pat, lhs) (Vartab.empty, Vartab.empty)
    fun get_vars env (Abs (x, T, t)) = get_vars (env @ [(x,T)]) t
      | get_vars env t =
         (case Term.strip_comb t of
            (Var x, args) => (env, x, args) :: flat (map (get_vars env) args)
          | (_, args) => flat (map (get_vars env) args))


    fun msg s x = "split_rule_simproc: " ^ s

    fun is_dummy ((n, _)) = (n = "_dummy_")
    val rule_subterms = Vartab.dest term_env |> filter_out (is_dummy o fst) |> map (snd o snd)
    val rule_vars = flat (map (get_vars []) rule_subterms)
        |> map (asserts [
           (fn (env, var, args) => not (null env),  fn _ => "matched subterm for splitting has to be abstraction, use dummy pattern '_' to skip subterms" ),
           (fn (env, var, args) => not (null args), fn (env, var, args) =>
              ("Variable '" ^  Term.string_of_vname' (fst var) ^
               "' has to be applied to bound variable, about to be splitted")),
           (fn (env, var, args) => hd args = Bound (length env - 1), fn (env, var, args) =>
              ("first argument of variable '"  ^  Term.string_of_vname' (fst var) ^
               "'expected to be bound variable '" ^ (fst (hd env)) ^ "'"))
           ])
        |> map (#2)


    fun split_rule arities =
      let
        val (names, ctxt') = Variable.add_fixes (map (fst o fst) rule_vars) ctxt
        fun mk_inst ((var, T), (n, name)) i = ((var, Thm.cterm_of ctxt (mk_case_prod_fun (name, range_type T) i n)), i+n)
        val insts = fold_map mk_inst (rule_vars ~~ (arities ~~ names)) 1 |> fst

        val [rule'] = Drule.infer_instantiate ctxt' insts rule
          |> Simplifier.simplify (put_simpset HOL_basic_ss ctxt' addsimps @{thms case_prod_out})
          |> mk_meta_eq
          |> single
          |> Proof_Context.export ctxt' ctxt

      in
        rule'
      end
     val (split_rule, handler) = Fun_Cache.create_handler (Binding.map_name (fn name => name ^ "-cache") name)
       (fn tab => @{make_string} (Intlisttab.dest tab))
       Intlisttab.empty Intlisttab.lookup Intlisttab.update split_rule
     fun split_rule_names arity_names =
       let
         val arities = map fst arity_names
         val names = map snd arity_names
         val rule = split_rule arities
         fun sum ns = fold (fn n => fn m => n + m) ns 0
         val bound_names = map (mk_el_name) (1 upto (sum arities))
         val renamings = (bound_names ~~ flat (names)) |> filter_out (fn (_, n) => n = strip_uu)
       in
         Drule.rename_bvars renamings rule
       end

     fun trace_cache_info () =
         tracing (@{make_string} handler)

     (* populate

 cache, and as a side-effect check if splitting works *)
     val _ = map split_rule (comb_product (map (K (1 upto 3)) rule_vars))
     val _ = trace_cache_info ()
  in
    Simplifier.make_simproc ctxt {name = Binding.name_of name, kind = Simproc, identifier = [],
      lhss = [pat],
      proc = fn _ => fn ctxt => fn ct =>
        let
          val t = Thm.term_of ct
          val (tenv, term_env) = Pattern.match (Proof_Context.theory_of ctxt) (pat, t) (Vartab.empty, Vartab.empty)
          val subterms = Vartab.dest term_env |> filter_out (is_dummy o fst) |> map (snd o snd)
          val arity_names = map ((fn vars => (length vars, map fst vars)) o strip_case_prod) subterms
          val _ = asserts [(fn _ => length arity_names = length rule_vars, fn _ => "split_rule_simproc: unexpected number of matched subterms")]

        in
          if exists (fn (n,_) => n > 1) arity_names
          then
             let
               val splitted_rule = split_rule_names arity_names
             in SOME splitted_rule end
          else NONE
        end
    }
  end

fun tuple_inst_simp_tac ctxt i =
   tuple_inst_tac ctxt i THEN
   simp_tac (put_simpset HOL_ss ctxt addsimps @{thms Product_Type.prod.case}) i

fun tuple_refl_tac ctxt i =
  resolve_tac ctxt @{thms refl} i
  ORELSE (
    tuple_inst_simp_tac ctxt i THEN
    resolve_tac ctxt @{thms refl} i
  )

fun split_rule_simprocs ctxt = map (fn (name, rule, pattern) => split_rule_simproc ctxt name pattern rule)

fun gen_split_rule ctxt0 name_arities thm =
  let
    val ctxt = Variable.set_body false ctxt0
    val case_prod_eta_contract_thm = @{thm case_prod_eta_contract}
    val case_prod_conv = Conv.bottom_conv (
          K (Conv.try_conv (Conv.rewr_conv case_prod_eta_contract_thm)))
    val name_arities = name_arities |> sort_by fst
    val names = map fst name_arities
    val arities = map snd name_arities
    fun eta_contract ctxt thm = Conv.fconv_rule (case_prod_conv ctxt) thm
    val vars = Term.add_vars (Thm.prop_of thm) [] |>
      filter (fn ((n,_) ,_) => member (op =) names n) |> distinct (op =) |> sort_by (fst o fst)
    val names' = map (fst o fst) vars
    val insts = ((names' ~~ arities) ~~ vars)
      |> map (fn ((f, n), (var,T)) =>
        (var, mk_tuple_or_case_prod f T n))
    val new_names = [] |> fold Term.add_frees (map snd insts) |> map fst
    val (new_names', ctxt') = Variable.add_fixes new_names ctxt
    val _ = @{assert} (new_names = new_names')
    val (_, ctxt'') = ctxt' |> Variable.import_terms false (map snd insts) 
      |> apsnd (Context_Position.set_visible false)
    val insts = map (apsnd (Thm.cterm_of ctxt'')) insts
    val split_arities = arities |> filter (fn n => n > 1)
    val splits = map (get_split_tupled_all_thm ctxt) split_arities
    val case_eqs = map (get_tuple_case_eq_thm ctxt) split_arities
  in
    thm 
    |> Drule.infer_instantiate ctxt'' insts
    |> Simplifier.asm_full_simplify (put_simpset HOL_basic_ss ctxt'' addsimps 
      (@{thms case_prod_out} @ case_eqs @  splits))
    |> eta_contract ctxt''
    |> single
    |> Proof_Context.export ctxt'' ctxt
    |> hd
    |> Drule.zero_var_indexes
  end


fun split_rule ctxt names thm n = 
  if n <= 1 then thm 
  else gen_split_rule ctxt (map (fn name => (name, n)) names) thm

fun split_rule_bin ctxt names thm bin =
  split_rule ctxt names thm (Bin.int_of_bin bin)


val case_prod_conv = mk_meta_eq @{thm case_prod_conv}

fun print_conv msg (ct:cterm) =
  let
    val _ = tracing (msg ^ ": " ^ @{make_string} ct);
  in Conv.all_conv ct end



fun bounded_top_conv i conv ctxt ct =
  if i <= 0 then Conv.all_conv ct
  else
   (conv ctxt then_conv Conv.sub_conv (bounded_top_conv (i - 1) conv) ctxt) ct;

fun bounded_bottom_conv i conv ctxt ct =
  if i <= 0 then Conv.all_conv ct 
  else
    (Conv.sub_conv (bounded_bottom_conv (i - 1) conv) ctxt then_conv conv ctxt) ct;

fun bounded_top_rewrs_conv i rewrs = bounded_top_conv i (K (Conv.try_conv (Conv.rewrs_conv rewrs)));

fun bounded_bottom_rewrs_conv i rewrs = bounded_bottom_conv i (K 
  (Conv.try_conv (Conv.rewrs_conv rewrs)));


fun eta_expand_tupled_conv ctxt ct =
  let
    val arity_of = HOLogic.flatten_tupleT #> length
    val domT = Thm.typ_of_cterm ct |> domain_type
    val arity = domT |> arity_of
    val name_types = strip_case_prod' (Thm.term_of ct)
    val case_prod_arity = length name_types 
    val renamings = map (fn (n, T) => if arity_of T = 1 then SOME n else NONE) name_types
    val base_conv = 
          if case_prod_arity > 0 andalso case_prod_arity < arity then
            let
              val eta_contract_rule = get_eta_tupled_eq_thm ctxt case_prod_arity 
                |> Thm.symmetric
            in fn ct => Conv.rewr_conv eta_contract_rule ct handle CTERM _ => Conv.all_conv ct end
          else Conv.all_conv
    val conv =
          if arity > 1 andalso case_prod_arity < arity then
            base_conv then_conv
            Conv.rewr_conv (Drule.rename_bvars' renamings (get_eta_tupled_eq_thm ctxt arity)) then_conv
            bounded_bottom_rewrs_conv (arity * 2) [case_prod_conv] ctxt
         else Conv.all_conv 
  in
    conv ct
  end
  handle Match => Conv.all_conv ct

fun eta_expand_tuple ctxt = eta_expand_tupled_conv ctxt #> Thm.rhs_of

end
\<close>

simproc_setup ETA_TUPLED (\<open>ETA_TUPLED f\<close>) = \<open>fn _ => fn ctxt => fn ct =>
  let
    val arity = Thm.typ_of_cterm ct |> domain_type |> HOLogic.flatten_tupleT |> length
  in
    if arity <= 1 then
      SOME @{thm ETA_TUPLED_def}
    else
      SOME (@{thm ETA_TUPLED_trans} OF [Tuple_Tools.get_eta_tupled_eq_thm ctxt arity])
  end\<close>
declare [[simproc del: ETA_TUPLED]]

text \<open>Set up the theorem cache.
We could use "dynamic programming" here and rewrite "thm n" with one step of "thm (n - 1)" and @{thm split_def}\<close>





setup \<open>
Context.theory_map (Tuple_Tools.Data.map (fn _ => map (fn i =>
  (Thm.trim_context (Tuple_Tools.mk_tuple_up_eq_thm @{context} i),
   Thm.trim_context (Tuple_Tools.mk_split_tupled_all_thm @{context} i),
   Thm.trim_context (Tuple_Tools.mk_tuple_case_eq_thm @{context} i),
   Thm.trim_context (Tuple_Tools.mk_eta_tupled_eq_thm @{context} i))) (2 upto 50)))
\<close>

attribute_setup split_tuple = \<open>
let
  val parse_arity = Args.$$$ "arity" |-- Args.colon |-- Parse.nat
  val parse_names = Parse.and_list1 Parse.short_ident
in
  Scan.lift (parse_names -- parse_arity) >> (fn (names, arity) =>
  let
  in
    Thm.rule_attribute [] (fn context => fn thm => 
     Tuple_Tools.split_rule (Context.proof_of context) names thm arity)
  end)
end
\<close>

thm HOL.ext [split_tuple f and g arity: 3]


ML_val \<open>
val test = @{pattern "\<And>a b c s. f a b c \<equiv> ?c (a,b,k) s"}
val x = Tuple_Tools.calc_inst' @{context} 2 test
\<close>

text \<open>Especially in the case of congruence rules we prefer the more restrictive instantiation, where
the freshly introduced variable does not depend on 'non-bound' tuple components \<close>
ML_val \<open>
val test = @{pattern "\<And>a b c s. f a b c \<equiv> ?c (a,b,k) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>

(*
now i get: val x = [(("c", 0), "\<lambda>(a, b, uu_). ?c3 a b uu_")]

I guess before I had:

val x = [(("c", 0), "\<lambda>(a, b, uu_). ?c3 a b ")

Do I need both variants for different purposes, or is variant two enough or even
the proper solution as it avoids the issues
with congruence rules?

We have analysed the variables with dest_var' with explicit NONE result which we should be able
to use for this purpose.
*)

ML_val \<open>
val thm = Tuple_Tools.get_tuple_up_eq_thm @{context} 1
\<close>

ML_val \<open>
val thm = Tuple_Tools.get_tuple_up_eq_thm @{context} 0
\<close>

ML_val \<open>
val thm = Tuple_Tools.get_tuple_up_eq_thm @{context} 3
\<close>

ML_val \<open>
val thm = Tuple_Tools.get_split_tupled_all_thm @{context} 30
\<close>

ML_val \<open>
val thm = Tuple_Tools.get_split_tupled_all_thm @{context} 2
\<close>

ML_val \<open>
val thm = Tuple_Tools.get_tuple_case_eq_thm @{context} 2
\<close>

ML_val \<open>
val thm = Tuple_Tools.get_eta_tupled_eq_thm @{context} 2
\<close>

declare [[simp_trace=false]]

text \<open>Variable names should be preserved here, since all abstractions stay in place.\<close>
lemma "\<And>r. (\<lambda>(x,y). (x::nat) < y \<and> y < 200) r"
  apply (tactic \<open>
simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [Tuple_Tools.split_tupled_all_simproc, Tuple_Tools.tuple_case_simproc]
 delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}) 1
\<close>)
  oops

text \<open>Variable names are not preserved due to eta contraction:
  @{lemma "(\<lambda>(x,y). (x::nat) < y ) = case_prod (<)" by (rule refl)}\<close>
lemma "\<And>r. (\<lambda>(x,y). (x::nat) < y ) r"
  apply (tactic \<open>
simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [Tuple_Tools.split_tupled_all_simproc, Tuple_Tools.tuple_case_simproc]
 delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}) 1
\<close>)
  oops

lemma "(\<lambda>(x,y,p,z,f). (x::nat) < y) (a,b,c) = (case c of (p,z,f) \<Rightarrow> a < b)"
  apply (tactic \<open>
simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [Tuple_Tools.split_tupled_all_simproc, Tuple_Tools.tuple_case_simproc]
 delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}) 1
\<close>)
  done

lemma "\<And>r. (\<lambda>(x,y,p,z,f). (p::nat) < f) r"
  apply (tactic \<open>
simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [Tuple_Tools.split_tupled_all_simproc, Tuple_Tools.tuple_case_simproc]
 delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}) 1
\<close>)
  oops

lemma "(\<lambda>(x,y,p). (x::nat) < y) (a,b,c,d,e) = (a < b)"
  apply (tactic \<open>
simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [Tuple_Tools.split_tupled_all_simproc, Tuple_Tools.tuple_case_simproc]
 delsimps @{thms Product_Type.prod.case Product_Type.case_prod_conv}) 1
\<close>)
  done

ML_val \<open>
val test = @{pattern "\<And>a b c d e s. f a b c \<equiv> ?c a b (c,d,e) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>



ML_val \<open>
val test = @{pattern "\<And>a b c s. P x \<Longrightarrow> f a b c \<equiv> ?c (a,b,c) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>

ML_val \<open>
val test = @{pattern "\<And>a b c s. P x =simp=> f a b c \<equiv> ?c (a,b,c) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>


ML_val \<open>
val test = @{pattern "\<And>a b c s. f a b c \<equiv> ?c (a,b,k) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>

ML_val \<open>
val test = @{pattern "\<And>a b c s. f a b c \<equiv> ?c (a,b,k) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>

ML_val \<open>
val test = @{pattern "\<And>a b c s. f a b c \<equiv> ?c (a,x+y,x + y + z) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>

ML_val \<open>
val test = @{pattern "\<And>a b c s. f a b c \<equiv> ?c (a,x+y,x + y + z) s"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>

ML_val \<open>
val test = @{pattern "(\<And>a b c s. P x \<Longrightarrow> f a b c \<equiv> ?c (a,b,c) s) \<Longrightarrow> (\<And>a b c s. Q x)"}
val x = Tuple_Tools.calc_inst @{context} 2 test
\<close>


lemma "SPLIT (\<And>r. ((\<lambda>z. Q z \<and> (Q z \<longrightarrow> P z)) r))
 \<equiv> XXX"
  apply (tactic \<open>
simp_tac ( @{context}
 addsimprocs [Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc]
  |> Simplifier.add_cong @{thm SPLIT_cong}
  |> Simplifier.add_cong @{thm conj_cong}) 1
\<close>)
  oops

lemma "PROP SPLIT (\<And>r. ((\<lambda>(x,y,z). y < z \<and> z=s) r) \<Longrightarrow> P r)
 \<equiv> (\<And>x y z. y < z \<and> z = s \<Longrightarrow> P (x, y, s))"
  apply (tactic \<open>
asm_full_simp_tac (put_simpset HOL_basic_ss @{context}
 addsimprocs [Tuple_Tools.SPLIT_simproc, Tuple_Tools.tuple_case_simproc] |> Simplifier.add_cong @{thm SPLIT_cong}) 1
\<close>)
  done

schematic_goal "ETA_TUPLED (\<lambda>x::('a \<times>'b \<times> 'c). f x) = ?XXX"
  supply [[simp_trace]]
  thm Product_Type.cond_case_prod_eta
  supply [[simproc add: ETA_TUPLED]]
  apply (simp)
  done

context
  fixes f::"('a \<times> 'b \<times> 'c \<times> 'd) \<Rightarrow> nat"
  fixes c::"('a \<times> 'b \<times> 'c \<times> 'd) \<Rightarrow> 's \<Rightarrow> bool" 
begin


ML_val \<open>
val t1 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "f"}
val t2 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "\<lambda>(a, b). f (a, b)"}
val t3 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "\<lambda>(a, b, c). f (a, b, c)"}

val c1 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "c"}
val c2 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "\<lambda>(a, b) s. c (a,b) s"}
val d1 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "\<lambda>(a, (b::nat \<times> nat)) s. a < 2"}
val d2 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "\<lambda>(a, (b::nat \<times> nat \<times> nat)) s. a < 2"}
val d3 = Tuple_Tools.eta_expand_tupled_conv @{context} @{cterm "\<lambda>(a, (b::nat \<times> nat \<times> nat \<times> nat)) s. a < 2"}
\<close>

end


end