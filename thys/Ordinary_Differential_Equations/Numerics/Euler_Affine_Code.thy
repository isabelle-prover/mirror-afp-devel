section {* Euler Method on Affine Forms: Code *}
theory Euler_Affine_Code
imports
  Print
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/While_Combinator"
  "../Numerics/Runge_Kutta"
  "../../Affine_Arithmetic/Affine_Arithmetic"
begin

text{*\label{sec:euleraformcode}*}

record ('a, 'b, 'c) options =
  precision :: nat
  tolerance :: real
  stepsize :: real
  min_stepsize :: real
  iterations :: nat
  halve_stepsizes :: nat
  widening_mod :: nat
  max_tdev_thres :: real
  presplit_summary_tolerance :: real
  collect_mod :: nat
  collect_granularity :: real
  override_section :: "'a \<Rightarrow> real \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a * real"
  global_section :: "'b \<Rightarrow> ('a * real) option"
  stop_iteration :: "'b \<Rightarrow> bool"
  printing_fun :: "nat \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> unit"
  result_fun :: "nat * real * 'b * (real * 'b * real * 'b) list \<Rightarrow> 'c"

locale approximate_sets0 =
  fixes appr_of_ivl::"'a::{ordered_euclidean_space, executable_euclidean_space} \<Rightarrow> 'a \<Rightarrow> 'b"
  fixes msum_appr::"'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes set_of_appr::"'b \<Rightarrow> 'a set"
  fixes set_of_apprs::"'b list \<Rightarrow> 'a list set"
  fixes inf_of_appr::"'b \<Rightarrow> 'a"
  fixes sup_of_appr::"'b \<Rightarrow> 'a"
  fixes add_appr::"('a, 'b, 'c) options \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b option"
  fixes scale_appr::"('a, 'b, 'c) options \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b option"
  fixes scale_appr_ivl::"('a, 'b, 'c) options \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b option"
  fixes split_appr::"('a, 'b, 'c) options \<Rightarrow> 'b \<Rightarrow> 'b list"
  fixes disjoint_apprs::"'b \<Rightarrow> 'b \<Rightarrow> bool"
  fixes inter_appr_plane::"'b \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'b"
begin

text {* TODO: more conceptual refinement?! *}

definition ivl_appr_of_appr::"'b \<Rightarrow> 'b" where
  "ivl_appr_of_appr x = (appr_of_ivl (inf_of_appr x) (sup_of_appr x))"

end

declare approximate_sets0.ivl_appr_of_appr_def[code]

type_synonym 'a enclosure = "nat * real * 'a * (real * 'a * real * 'a) list"

locale approximate_ivp0 = approximate_sets0
  appr_of_ivl msum_appr set_of_appr set_of_apprs inf_of_appr sup_of_appr add_appr scale_appr scale_appr_ivl
  split_appr disjoint_apprs inter_appr_plane
for appr_of_ivl msum_appr set_of_appr set_of_apprs inf_of_appr
  and sup_of_appr::"'b \<Rightarrow> 'a::{ordered_euclidean_space, executable_euclidean_space}"
  and add_appr:: "('a, 'b, 'c) options \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b option"
  and scale_appr scale_appr_ivl split_appr disjoint_apprs inter_appr_plane +
  fixes ode_approx::"('a, 'b, 'c) options \<Rightarrow> 'b list \<Rightarrow> 'b option"
  fixes ode_d_approx:: "('a, 'b, 'c) options \<Rightarrow> 'b list \<Rightarrow> 'b option"
begin

abbreviation "extend_appr \<equiv> \<lambda>x l u. msum_appr x (appr_of_ivl l u)"

definition P_appr::"('a, 'b, 'c) options \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> 'b option" where
  "P_appr optns X0 h X = map_option (\<lambda>Y.
    extend_appr X0 (inf 0 (h *\<^sub>R inf_of_appr Y))
                   (sup  0 (h *\<^sub>R sup_of_appr Y)))
    (ode_approx optns [X])"

fun P_iter::"('a, 'b, 'c) options \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b option" where
  "P_iter optns X0 h 0 X =
    (let _ = print (STR ''=P_iter failed: '');
      _ = print_eucl (inf_of_appr X);
      _ = print (STR '' - '');
      _ = print_eucl (sup_of_appr X);
      _ = println (STR '''') in None)"
| "P_iter optns X0 h (Suc i) X =
    bind_err (STR ''=P_appr failed'') (P_appr optns X0 h X) (\<lambda>X'.
      let (l', u') = (inf_of_appr X', sup_of_appr X') in
      let (l, u) = (inf_of_appr X, sup_of_appr X) in
      if l \<le> l' \<and> u' \<le> u then Some X
      else P_iter optns X0 h i (appr_of_ivl (inf l' l - (if i mod (widening_mod optns) = 0 then abs (l' - l) else 0)) (sup u' u + (if i mod widening_mod optns = 0 then abs (u' - u) else 0))))"

fun cert_stepsize::"('a, 'b, 'c) options \<Rightarrow> 'b \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real * 'b) option" where
  "cert_stepsize optns X0 h n 0 = (let _ = println (STR ''=cert_stepsize failed'') in None)"
| "cert_stepsize optns X0 h n (Suc i) =
    (case P_iter optns (ivl_appr_of_appr X0) h n (ivl_appr_of_appr X0) of
      Some X' \<Rightarrow> Some (h, X')
    | None \<Rightarrow>
      let
        _ = print (STR ''=cert_stepsize failed on: '');
        _ = print_eucl (inf_of_appr X0);
        _ = print (STR '' - '');
        _ = print_eucl (sup_of_appr X0);
        _ = println (STR '''')
      in cert_stepsize optns X0 (h / 2) n i)"

lemma cert_stepsize_pos: "cert_stepsize optns X0 h n i = Some (h', cx) \<Longrightarrow> h > 0 \<Longrightarrow> h' > 0"
  by (induct i arbitrary: h h') (auto split: option.split_asm)

definition "euler_step optns X0 =
  bind_err (STR ''=certify stepsize failed'') (cert_stepsize optns X0 (stepsize optns) (iterations optns) (halve_stepsizes optns))
  (\<lambda>(h, CX).
      bind_err (STR ''=ode_approx X0 failed'') (ode_approx optns [X0])
      (\<lambda>X0'.
        bind_err (STR ''=ode_approx CX failed'') (ode_approx optns [CX])
        (\<lambda>F.
          bind_err (STR ''=ode_d_approx failed'') (ode_d_approx optns [CX, F])
          (\<lambda>D.
            bind_err (STR ''=scale_appr err failed'') (scale_appr optns (h*h) 2 (ivl_appr_of_appr D) [])
            (\<lambda>ERR.
                bind_err (STR ''=scale_appr euler failed'') (scale_appr optns h 1 X0' [X0])
                (\<lambda>S.
                  bind_err (STR ''=scale_appr_ivl euler failed'') (scale_appr_ivl optns 0 h X0' [X0])
                  (\<lambda>S'.
                    bind_err (STR ''=add_appr euler failed'') (add_appr optns X0 S [])
                    (\<lambda>X1.
                      bind_err (STR ''=add_appr euler_ivl failed'') (add_appr optns X0 S' [])
                      (\<lambda>CX1.
                        let
                          res = msum_appr X1 (ivl_appr_of_appr ERR);
                          res_ivl = msum_appr CX1 (appr_of_ivl (inf 0 (inf_of_appr ERR)) (sup 0 (sup_of_appr ERR)))
                        in
                        Some (h, res_ivl, res))))))))))"

fun advance_euler::"('a, 'b, 'c) options \<Rightarrow> 'b enclosure option \<Rightarrow> 'b enclosure option"
where
  "advance_euler optns None = None"
| "advance_euler optns (Some (i, t, X, XS)) =
    (case euler_step optns X of
      Some (h, CX, X1) \<Rightarrow>
        let _ = printing_fun optns i (t + h) X1
        in Some (Suc i, t + h, X1, (t, CX, t + h, X1)#XS)
    | None \<Rightarrow> None)"

primrec euler_series where
  "euler_series optns t0 X0 0 = Some (0, t0, X0, [])"
| "euler_series optns t0 X0 (Suc i) = advance_euler optns (euler_series optns t0 X0 i)"


subsection {* Checkpoint: Partition *}
text {* TODO: partitioning really needed when we do cancelling? *}

definition width_appr::"'b \<Rightarrow> real"
  where "width_appr x = infnorm (sup_of_appr x - inf_of_appr x)"

primrec split_appr_fp_iter where
  "split_appr_fp_iter optns XS 0 = XS"
| "split_appr_fp_iter optns XS (Suc i) =
    (let
      YS = concat (map (\<lambda>x.
        if width_appr x > max_tdev_thres optns
        then split_appr optns x
        else [x]) XS)
    in
      if length XS = length YS
      then YS
      else split_appr_fp_iter optns YS i)"

definition "split_appr_fp optns X = split_appr_fp_iter optns [X] 100"

primrec ivl_of_apprs::"'b list \<Rightarrow> 'b"
  where
  "ivl_of_apprs (x#xs) = (let
      i = fold (\<lambda>a b. inf (inf_of_appr a) b) xs (inf_of_appr x);
      s = fold (\<lambda>a b. sup (sup_of_appr a) b) xs (sup_of_appr x)
    in appr_of_ivl i s)"

definition partition
  where
 "partition optns r xs =
    (let
      rs = split_appr_fp (optns\<lparr>max_tdev_thres := collect_granularity optns\<rparr>) r;
      red_rs = map (\<lambda>r.
        case (filter (\<lambda>a. \<not> disjoint_apprs a r) xs) of [] \<Rightarrow> None
          | ds \<Rightarrow> let d = ivl_of_apprs ds
          in Some (appr_of_ivl (sup (inf_of_appr r) (inf_of_appr d)) (inf (sup_of_appr r) (sup_of_appr d)))) rs
    in map the (filter (-Option.is_none) red_rs))"

definition collect_apprs::"_ \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list"
  where "collect_apprs optns r XS =
    (let
      _ = print (STR ''= Collecting: '');
      _ = print (int_to_string (length XS));
      _ = print (STR ''aforms ... '');
      YS = partition optns r XS;
      _ = print (STR ''= Collected to  '');
      _ = print (int_to_string (length YS));
      _ = println (STR '' aforms!'')
    in YS)"

definition collect_cancel_apprs::"('a, 'b, 'c) options \<Rightarrow> nat \<Rightarrow> 'b list \<Rightarrow> 'b list"
  where
  "collect_cancel_apprs optns i xs =
    (if i mod collect_mod optns = 0
    then let
      _ = println (STR ''Collect_cancelling:'');
      r = ivl_of_apprs xs;
      checkpoint_grid = collect_apprs optns r xs;
      _ = println (STR ''checkpoint grid:'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) checkpoint_grid;
      steps = map (\<lambda>x. snd (snd (the (euler_step optns x)))) checkpoint_grid;
      _ = println (STR ''steps:'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) steps;
      outside_checkpoint =
        filter (\<lambda>x. \<not> (inf_of_appr r \<le> inf_of_appr x \<and> sup_of_appr x \<le> sup_of_appr r)) steps;
      _ = println (STR ''outside_checkpoint:'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) outside_checkpoint;
      inside_checkpoint =
        filter (\<lambda>x. (inf_of_appr r \<le> inf_of_appr x \<and> sup_of_appr x \<le> sup_of_appr r)) steps;
      _ = println (STR ''inside_checkpoint:'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) inside_checkpoint;
      steps_grid = collect_apprs optns r steps;
      _ = println (STR ''steps_grid'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) steps_grid;
      sg_not_cp_covered = fold (\<lambda>x xs. removeAll x xs) checkpoint_grid steps_grid;
      _ = println (STR ''sg_not_cp_covered'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) sg_not_cp_covered;
      s_not_covered = filter (\<lambda>x. list_ex (- disjoint_apprs x) sg_not_cp_covered) steps;
      _ = println (STR ''s_not_covered'');
      _ = map (\<lambda>x. printing_fun optns i 0 x) s_not_covered
    in remdups (outside_checkpoint @ s_not_covered)
    else xs)"

text {* TODO: certify common stepsize first, and establish a common history of disjunctions of
  zonotopes *}

fun map_enclosure_option::
  "(nat \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> 'b list) \<Rightarrow> 'b enclosure option list \<Rightarrow> 'b enclosure option list"
  where
  "map_enclosure_option f [] = []"
| "map_enclosure_option f (None#xs) = (None # map_enclosure_option f xs)"
| "map_enclosure_option f (Some (i, t, X, XS)#xs) = map (\<lambda>X. Some (i, t, X, XS)) (f i t X) @ map_enclosure_option f xs"

definition "euler_lists optns t0 X0 t1 =
  while_option (list_ex (\<lambda>x. case x of Some (i, t, X, XS) \<Rightarrow> t < t1 | None \<Rightarrow> False))
    ((\<lambda>x. let _ = print (STR ''Affine Forms: ''); _ = println (int_to_string (length x)) in x) o
      (map_enclosure_option (\<lambda>i t x. split_appr_fp optns x)) o
      (\<lambda>x. case x of Some (i, t, X, XS)#_ \<Rightarrow> map (\<lambda>x. Some (i, t, x, XS)) (collect_cancel_apprs optns i (map (fst o snd o snd o the) x))
        | None#_ \<Rightarrow> []) o
      map (advance_euler optns)) [Some (0, t0, X0, [])]"

definition "euler_lists_result optns t0 X0 t1 =
  map_option (map (map_option (result_fun optns))) (euler_lists optns t0 X0 t1)"

definition euler_series_result::
  "('a, 'b, 'c) options \<Rightarrow> real \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'c option"
  where [simp]: "euler_series_result optns t0 X0 i =
    map_option (result_fun optns) (euler_series optns t0 X0 i)"

lemma euler_series_print:
  "euler_series optns t0 X0 i =
    fold (\<lambda>a b.
      case b of
        None \<Rightarrow> None
      | Some (a', t0', X0', ress) \<Rightarrow>
        (case euler_step optns X0' of
          None \<Rightarrow> None
        | Some (h, CX, X1) \<Rightarrow>
          let
            _ = printing_fun optns a (t0' + h) X1
          in Some (Suc a', t0' + h, X1, (t0', CX, t0' + h, X1)#ress))) [0..<i] (Some (0, t0, X0, []))"
  unfolding Let_def
  by (induct i) (auto split: option.split)

definition "project_rect X b y =
  (let i = inf_of_appr X; s = sup_of_appr X in
  appr_of_ivl (i + (y - i \<bullet> b) *\<^sub>R b) (s + (y - s \<bullet> b) *\<^sub>R b))"

definition "sup_abs_appr X = sup (abs (inf_of_appr X)) (abs(sup_of_appr X))"

definition "intersects X b y \<longleftrightarrow> (inf_of_appr X \<bullet> b \<le> y \<and> sup_of_appr X \<bullet> b \<ge> y)"

text {* Precondition: X does not intersect b, but euler-step does! *}

primrec intersect'
  where
  "intersect' optns X b y h 0 = None"
| "intersect' optns X b y h (Suc i) =
    (let
      (h, CX, X1) = the (euler_step (optns\<lparr>stepsize:=h\<rparr>) X)
    in if intersects X1 b y then intersect' optns X b y (h*2) i else Some (inter_appr_plane CX b y))"

definition "intersect optns X b y = intersect' optns X b y (stepsize optns) 10"

definition "poincares2_step optns X0 b y =
  (let
    (h, CX, X1) = the (euler_step optns X0)
  in
    if intersects CX b y
    then the (intersect optns X0 b y)
    else X1
  )"

definition "strongest_direction optns f =
  (let
    af = sup_abs_appr f;
    (b, _) = fold (\<lambda>b (b', d'). if d' \<le> af \<bullet> b then (b, af \<bullet> b) else (b', d')) (Basis_list::'a list) 0;
    res = (if inf_of_appr f \<bullet> b < 0 \<and> sup_of_appr f \<bullet> b < 0 then (b, inf_of_appr f \<bullet> b)
      else if inf_of_appr f \<bullet> b > 0 \<and> sup_of_appr f \<bullet> b > 0 then (b, ((sup_of_appr f \<bullet> b)))
      else let _ = println (STR ''== ERROR finding next direction!'') in (0, 0))
  in res)"

definition "next_sections optns d Xs =
  (let
    set_dir_alist = map (\<lambda>X. (X, apsnd sgn (strongest_direction optns (the (ode_approx optns [X]))))) Xs;
    dirs = remdups (map snd set_dir_alist);
    dir_set_alist = map (\<lambda>bs. (bs, map fst (filter (\<lambda>(X, b, s). (b, s) = bs) set_dir_alist))) dirs;
    sctns = map (\<lambda>((b, s), Xs). if s = -1 then (Xs, (b, inf_of_appr (ivl_of_apprs Xs) \<bullet> b - d))
      else (Xs, (-b, - (sup_of_appr (ivl_of_apprs Xs) \<bullet> b + d))) ) dir_set_alist
  in
    map (\<lambda>(Xs, (b, s)). (Xs, override_section optns b s (inf_of_appr (ivl_of_apprs Xs)) (sup_of_appr (ivl_of_apprs Xs)))) sctns)"

definition "poincares2_iter optns X0 b y =
  while (list_ex (\<lambda>(X, b, y). \<not>stop_iteration optns X))
    (concat o (map (\<lambda>(X, b, y).
      let
        F = the (ode_approx optns [X]);
        (bs, fs) = strongest_direction optns F;
        (b, y) = (if bs = b then (b, y)
          else if fs \<le> 0 \<and> fs * 3 \<le> 4 * ((inf_of_appr F) \<bullet> b) then (bs, inf_of_appr X \<bullet> b)
          else if fs \<ge> 0 \<and> 4 * ((sup_of_appr F) \<bullet> b) \<le> fs * 3 then (bs, sup_of_appr X \<bullet> b)
          else (b, y));
        (b, y) = (case global_section optns X of None \<Rightarrow> (b, y)
          | Some (b, y) \<Rightarrow> (b, y));
        X1 = poincares2_step optns X b y;
        X1s = split_appr_fp optns X1
      in map (\<lambda>X. (X, b, y)) X1s)))"

definition "poincares optns X0s b y =
  while (\<lambda>(XS, PS, RS). XS \<noteq> [])
    (\<lambda>(XS, PS, RS).
      let
        _ = print (STR ''=XS: '');
        _ = print (int_to_string (length XS));
        _ = print (STR '' PS: '');
        _ = print (int_to_string (length PS));
        _ = print (STR '' RS: '');
        _ = print (int_to_string (length RS));
        _ = print (STR '' Flowing towards: '');
        _ = print_eucl b;
        _ = print (STR '' -- '');
        _ = print_real y;
        _ = println (STR '''');
        XS = concat (map (\<lambda>(h, X). map (Pair h) (split_appr_fp optns X)) XS);
        XS = filter (\<lambda>(h, X). inf_of_appr X \<bullet> b \<ge> y \<or> sup_of_appr X \<bullet> b \<ge> y) XS;
        _ = print (STR ''=XS above: '');
        _ = println (int_to_string (length XS));
        _ = map (printing_fun optns 0 0 o snd) XS;
        YS = map (\<lambda>(h, X). case (euler_step (optns\<lparr>stepsize:=h\<rparr>) X) of Some res \<Rightarrow> (h, X, res) | None \<Rightarrow> undefined) XS;
        (IS, NIS) = List.partition (\<lambda>(h, X0, t, CX, X). (inf_of_appr X \<bullet> b \<le> y \<or> sup_of_appr X \<bullet> b \<le> y)) YS;
        (RS', NIS) = List.partition (\<lambda>(_, _, _, _, X).
          list_ex (\<lambda>b'. b \<noteq> b' \<and>
              (let sa = sup_abs_appr (the (ode_approx optns [X])) in abs (sa \<bullet> b) * 4 \<le> 3 * abs (sa \<bullet> b')))
            Basis_list) NIS;
        XS' = ''concat (map (%X. split_appr_fp (optns(|max_tdev_thres:=collect_granularity optns|)) X) (map fst IS)'';
        (IS1, IS2) = List.partition (\<lambda>(h, X0, t, CX, X). h \<le> min_stepsize optns) IS;
        IS2' = (map (\<lambda>(h, X0, t, CX, X). (h / 2, X0)) IS2);
        QS = map (\<lambda>(h, X0, t, CX, X). project_rect CX b y) IS1
      in (map (\<lambda>(h, X0, t, CX, X). (h, X)) (NIS @ IS1) @ IS2', PS@QS, RS @ map (snd o snd o snd o snd)RS')
    )
    (map (\<lambda>X. (stepsize optns, X)) X0s, [], [])" --{* Verbindung mit Euler, parametrisiert mit h! *}

definition "poincares_collected optns X0s b y =
  (case snd (poincares optns X0s b y) of ([], RS) \<Rightarrow> ([], RS)
    | (PS, RS) \<Rightarrow> (collect_apprs optns (ivl_of_apprs PS) PS, RS))"

definition "print_poincares optns X0s b y =
  (let (qs, rs) = poincares_collected optns X0s b y;
    _ = map (printing_fun optns 0 0) qs
   in (qs, rs))"

definition "poincare_distance_d optns X0s =
  while (list_ex (\<lambda>(XS, b, y). b \<noteq> 0))
    (\<lambda>groups. let _ = print (STR ''= Groups: ''); _ = println (int_to_string (length groups)) in concat (map (\<lambda>(Xs, b, y).
      if b = 0 then [(Xs, b, y)] else
      let
        (Ys, Rs) = print_poincares optns Xs b y;
        Yss = next_sections optns 2 Ys;
        Rss = next_sections optns 0 Rs;
        _ = print (STR ''= Ys: '');
        _ = print (int_to_string (length Yss));
        _ = print (STR '' Rss: '');
        _ = print (int_to_string (length Rss))
      in
        Yss@Rss) groups)
    ) (next_sections optns 2 X0s)"

definition "poincare_distance_d_print optns X0s =
  (let
    res = poincare_distance_d optns X0s;
    _ = print (STR ''= Returning: '');
    _ = print (int_to_string (length res));
    _ = println (STR '''');
    _ = map (printing_fun optns 0 0) (concat (map fst res))
  in res)"

end

declare approximate_ivp0.strongest_direction_def[code]
declare approximate_ivp0.poincares2_iter_def[code]
declare approximate_ivp0.poincares2_step_def[code]
declare approximate_ivp0.intersect_def[code]
declare approximate_ivp0.intersect'.simps[code]
declare approximate_ivp0.intersects_def[code]
declare approximate_ivp0.sup_abs_appr_def[code]
declare approximate_ivp0.project_rect_def[code]
declare approximate_ivp0.poincares_def[code]
declare approximate_ivp0.poincare_distance_d_def[code]
declare approximate_ivp0.poincare_distance_d_print_def[code]
declare approximate_ivp0.next_sections_def[code]
declare approximate_ivp0.poincares_collected_def[code]
declare approximate_ivp0.print_poincares_def[code]
declare approximate_ivp0.P_appr_def[code]
declare approximate_ivp0.P_iter.simps[code]
declare approximate_ivp0.cert_stepsize.simps[code]
declare approximate_ivp0.euler_step_def[code]
declare approximate_ivp0.advance_euler.simps[code]
declare approximate_ivp0.collect_cancel_apprs_def[code]
declare approximate_ivp0.euler_series_result_def[code]
declare approximate_ivp0.map_enclosure_option.simps[code]
declare approximate_ivp0.euler_lists_def[code]
declare approximate_ivp0.euler_lists_result_def[code]
declare approximate_ivp0.euler_series_print[code]
declare approximate_ivp0.collect_apprs_def[code]
declare approximate_ivp0.ivl_of_apprs.simps[code]
declare approximate_ivp0.partition_def[code]
declare approximate_ivp0.split_appr_fp_iter.simps[code]
declare approximate_ivp0.split_appr_fp_def[code]
declare approximate_ivp0.width_appr_def[code]

abbreviation "msum_aform' \<equiv> \<lambda>X. msum_aform (degree_aform X) X"

abbreviation "uncurry_options \<equiv> \<lambda>f x. f (precision x) (tolerance x)"

text {* intersection with plane *}

definition inter_aform_plane where
  "inter_aform_plane X b y = X"

locale aform_approximate_sets0 =
  approximate_sets0
    aform_of_ivl msum_aform' Affine Joints
    Inf_aform Sup_aform
    "uncurry_options add_aform_componentwise::('a, 'a::executable_euclidean_space aform, (real \<times> ((real \<times> 'a \<times> 'a \<times> real \<times> 'a \<times> 'a) list))) options \<Rightarrow> _"
    "uncurry_options scaleQ_aform_componentwise"
    "uncurry_options scaleR_aform_ivl"
    "\<lambda>optns. split_aform_largest (precision optns) (presplit_summary_tolerance optns)"
    disjoint_aforms
    inter_aform_plane

interpretation aform_approximate_sets0 .

locale aform_approximate_ivp0 =
  approximate_ivp0
    aform_of_ivl msum_aform' Affine Joints
    Inf_aform Sup_aform
    "uncurry_options add_aform_componentwise::('a, 'a::executable_euclidean_space aform, (real \<times> ((real \<times> 'a \<times> 'a \<times> real \<times> 'a \<times> 'a) list))) options \<Rightarrow> _"
    "uncurry_options scaleQ_aform_componentwise"
    "uncurry_options scaleR_aform_ivl"
    "\<lambda>optns. split_aform_largest (precision optns) (presplit_summary_tolerance optns)"
    disjoint_aforms
    inter_aform_plane

interpretation aform_approximate_ivp0 x y for x y .

definition print_rectangle
  where
  "print_rectangle m i t0 X =
    (let
      _ = print (int_to_string i);
      _ = print (STR '': '');
      _ = print_real t0
    in
      if i mod m = 0 then
        let
          R = Radius X;
          _ = print (STR '': '');
          _ = print_eucl (fst X - R);
          _ = print (STR '' - '');
          _ = print_eucl (fst X + R);
          _ = print (STR ''; devs: '');
          _ = print (int_to_string (length (list_of_pdevs (snd X))));
          _ = print (STR ''; width: '');
          _ = print_real (infnorm R);
          _ = print (STR ''; tdev: '');
          _ = print_eucl R;
          _ = print (STR ''; maxdev: '');
          _ = print_eucl (snd (max_pdev (snd X)));
          _ = println (STR '''')
        in ()
      else println (STR ''''))"

definition print_aform::"'a::executable_euclidean_space aform \<Rightarrow> unit"
  where
  "print_aform X =
    (let
      _ = print (STR ''aform('');
      _ = print (int_to_string (length (Basis_list::'a list)));
      _ = print (STR ''): '');
      _ = print_eucl (fst X);
      _ = print (STR '' -- '');
      _ = map (\<lambda>(i, x). print_eucl x) (list_of_pdevs (snd X));
      _ = println (STR '''')
    in ())"

definition "ivls_of_aforms p ress = map (\<lambda>(t0, CX, t1, X).
    (t0, eucl_truncate_down p (Inf_aform CX), eucl_truncate_up p (Sup_aform CX), t1,
      eucl_truncate_down p (Inf_aform X), eucl_truncate_up p (Sup_aform X))) ress"

primrec summarize_ivls where
  "summarize_ivls [] = None"
| "summarize_ivls (x#xs) = (case summarize_ivls xs of
      None \<Rightarrow> Some x
    | Some (t0', cl', cu', t1', xl', xu') \<Rightarrow>
      case x of (t0, cl, cu, t1, xl, xu) \<Rightarrow>
      if t0 = t1' then
        Some (min t0 t0', inf cl cl', sup cu cu', max t1 t1',
          if t1 \<le> t1' then xl' else xl, if t1 \<le> t1' then xu' else xu)
      else None)"

fun "set_res_of_ivl_res"
where "set_res_of_ivl_res (t0, CXl, CXu, t1 ,Xl, Xu) = (t0, {CXl .. CXu}, t1, {Xl .. Xu})"

fun parts::"nat\<Rightarrow>'a list\<Rightarrow>'a list list"
where
  "parts n [] = []"
| "parts 0 xs = [xs]"
| "parts n xs = take n xs # parts n (drop n xs)"

definition summarize_enclosure
where "summarize_enclosure p m xs =
  map the (filter (-Option.is_none) (map summarize_ivls (parts m (ivls_of_aforms p xs))))"

definition "ivls_result p m = (apsnd (summarize_enclosure p m o snd)) o snd"

definition "default_optns =
    \<lparr>
    precision = 53,
    tolerance = FloatR 1 (- 8),
    stepsize  = FloatR 1 (- 8),
    min_stepsize = FloatR 1 (- 8),
    iterations = 40,
    halve_stepsizes = 10,
    widening_mod = 40,
    max_tdev_thres = FloatR 1 100,
    presplit_summary_tolerance = FloatR 1 0,
    collect_mod = 0,
    collect_granularity = FloatR 1 100,
    override_section = (\<lambda>_ _ _ _. (0, 0)),
    global_section = (\<lambda>_. None),
    stop_iteration = (\<lambda>_. False),
    printing_fun = (\<lambda>_ _. print_aform),
    result_fun = ivls_result 23 1
  \<rparr>"

end

