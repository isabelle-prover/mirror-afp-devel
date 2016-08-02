theory Plot
imports
  "Print"
begin

datatype plotcomponent =
    Lower nat
  | Upper nat
  | Tdev nat
  | Maxdev nat
  | Width
  | Numdevs

primrec plotcomponent_string where
  "plotcomponent_string (Lower i) = ''x_'' @ show (Suc i)"
| "plotcomponent_string (Upper i) = ''X_'' @ show (Suc i)"
| "plotcomponent_string (Tdev i) = ''radius_'' @ show (Suc i)"
| "plotcomponent_string (Maxdev i) = ''max_gen_'' @ show (Suc i)"
| "plotcomponent_string Numdevs = ''|max_gen|''"
| "plotcomponent_string Width = ''#gen''"

primrec plotcomponent_index::"'a::executable_euclidean_space itself \<Rightarrow> plotcomponent \<Rightarrow> nat" where
  \<open>plotcomponent_index _ (Lower i) = Suc i\<close>
| \<open>plotcomponent_index _ (Upper i) = length (Basis_list::'a list) + Suc i\<close>
| \<open>plotcomponent_index _ (Tdev i) =  2 * length (Basis_list::'a list) + Suc i\<close>
| \<open>plotcomponent_index _ (Maxdev i) = 3 * length (Basis_list::'a list) + Suc i\<close>
| \<open>plotcomponent_index _ Numdevs = 4 * length (Basis_list::'a list)\<close>
| \<open>plotcomponent_index _ Width = 4 * length (Basis_list::'a list) + 1\<close>

definition "shows_gnuplot_box_header (_::'a::executable_euclidean_space itself) f x ys =
    (shows_string ''set xlabel '' o shows_quote (shows_string (plotcomponent_string x)) o shows_string ''\<newline>'' o
      (shows_list_gen (\<lambda>y. shows_string '' using '' o shows (plotcomponent_index TYPE('a) x) o
      shows_string '':'' o shows (plotcomponent_index TYPE('a) y) o shows_string ('' title '') o
        shows_quote (shows_string (plotcomponent_string y)))
      '''' (* empty *)
      (''plot '' @ shows_quote (shows_string f) []) (* left *)
      ((shows_string '', '' o shows_quote (shows_string '''')) '''') (* sep *)
      '''' (*right*)
      ys) o shows_string ''\<newline>'')"

definition "show_list_empty shws xs = shows_list_gen shws [] [] [] [] xs"

definition gnuplot_box::"'a::executable_euclidean_space aform list \<Rightarrow> plotcomponent \<Rightarrow> plotcomponent list \<Rightarrow> _"
where
  "gnuplot_box aforms x ys =
    (shows_gnuplot_box_header TYPE('a) (''-'') x ys o
    show_list_empty (\<lambda>y. show_list_empty shows_box_of_aform aforms o shows_string ''e\<newline>'') ys) ''''"

(*
set style arrow 1 nohead
set xlabel "x"
set ylabel "y"
set style arrow 1 nohead lc -1
plot '< cat' using 1:2:3:4 with vectors arrowstyle 1
*)

definition "gnuplot_aform2d_header f x y =
    shows ''set size ratio -1\<newline>'' o
    shows ''set xlabel '' o shows_quote (shows '' x_'' o shows (Suc x)) o shows ''\<newline>'' o
    shows ''set ylabel '' o shows_quote (shows '' x_'' o shows (Suc y)) o shows ''\<newline>'' o
    shows ''set style arrow 1 nohead lc -1\<newline>'' o
    shows ''plot '' o shows_quote (shows_string f) o shows ''using 1:2:3:4 with vectors arrowstyle 1'' o
    shows_string ('' notitle\<newline>'')"

definition gnuplot_aform2d::"'a::executable_euclidean_space aform list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> _"
where
  "gnuplot_aform2d aforms x y = (
    gnuplot_aform2d_header ''-'' x y o
    show_list_empty (shows_segments_of_aform (Basis_list ! x) (Basis_list ! y)) aforms o shows ''e\<newline>'') ''''"


context begin

private definition
  "aform_test_list = the (do {
    let p = 40;
    let t = FloatR 1 (-10);
    let rotate = Ex_Affine_Approximation.rotate45' p t;
    let x1 = aform_of_ivl (1::real, 1::real) (2, 3);
    x2 \<leftarrow> rotate x1 [];
    x3 \<leftarrow> rotate x2 [x1];
    x4 \<leftarrow> rotate x3 [x1, x2];
    let x5 = msum_aform 100 x2 x4;
    Some [x1, x2, x3, x4, x5]
  })"

text \<open>The 'Raw Output' of the following command can be fed to gnuplot\<close>
value [code] "print (String.implode (gnuplot_aform2d aform_test_list 0 1))"

private definition
  "aform_test_list2 = the (do {
    let p = 40;
    let t = 1;
    let rotate = Ex_Affine_Approximation.rotate45' p t;
    let x1 = aform_of_ivl (1::real, 1::real) (1, 2);
    x2 \<leftarrow> add_aform_componentwise p t x1 x1 [];
    x3 \<leftarrow> add_aform_componentwise p t x2 x2 [x1];
    x4 \<leftarrow> add_aform_componentwise p t x3 x3 [x1, x2];
    x5 \<leftarrow> add_aform_componentwise p t x4 x4 [x1, x2, x3];
    Some [x1, x2, x3, x4, x5]
  })"

text \<open>The 'Raw Output' of the following command can be fed to gnuplot\<close>
value [code] "print (String.implode (gnuplot_box aform_test_list2 (Lower 0) [Lower 1, Upper 1]))"

end

end