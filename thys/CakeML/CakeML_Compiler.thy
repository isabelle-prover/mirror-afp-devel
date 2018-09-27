chapter "CakeML Compiler"

theory CakeML_Compiler
imports
  "generated/CakeML/Ast"
  "Show.Show_Instances"
keywords "cakeml" :: diag
begin

hide_const (open) Lem_string.concat

section \<open>Printing\<close>

definition unsupported_code :: "'a \<Rightarrow> string" where
"unsupported_code _ = Code.abort (STR ''unsupported code'') (\<lambda>_. [])"

fun intercalate :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
"intercalate _ [] = []" |
"intercalate _ [y] = y" |
"intercalate x (y # ys) = y @ x @ intercalate x ys"

definition parens :: "string \<Rightarrow> string" where
"parens s = (if List.null s then s else ''('' @ s @ '')'')"

fun print_pat :: "Ast.pat \<Rightarrow> string" where
"print_pat Ast.Pany = ''_''" |
"print_pat (Ast.Pvar n) = parens n" |
"print_pat (Ast.Pcon (Some (Short ctor)) xs) = parens (ctor @ '' '' @ intercalate '' '' (map print_pat xs))" |
"print_pat p = unsupported_code p"

definition print_clause :: "string \<Rightarrow> string \<Rightarrow> string" where
"print_clause p t = p @ '' => '' @ t"

fun print_lit :: "Ast.lit \<Rightarrow> string" where
\<open>print_lit (IntLit n) = show n\<close> |
\<open>print_lit (StrLit s) = ''"'' @ show s @ ''"''\<close> |
\<open>print_lit l = unsupported_code l\<close>

fun print_exp :: "Ast.exp0 \<Rightarrow> string" where
"print_exp (Ast.Var (Short n)) = parens n" |
"print_exp (Ast.App oper [e1, e2]) = (
  let s1 = ''('' @ parens (print_exp e1); s2 = parens (print_exp e2) @ '')'' in
    (case oper of Ast.Opapp \<Rightarrow> s1 @ '' '' @ s2
                | Ast.Opn Ast.Plus \<Rightarrow> s1 @ '' + '' @ s2
                | Ast.Opn Ast.Times \<Rightarrow> s1 @ '' * '' @ s2
                | _ \<Rightarrow> unsupported_code oper)
)" |
"print_exp (Ast.Con (Some (Short ctor)) es) = ''('' @ ctor @ '' '' @ intercalate '' '' (map print_exp es) @ '')''" |
"print_exp (Ast.Fun x e) = ''(fn '' @ x @ '' => '' @ print_exp e @ '')''" |
"print_exp (Ast.Mat e cs) = ''(case '' @ print_exp e @ '' of '' @ intercalate '' | '' (map (\<lambda>(p, t). print_clause (print_pat p) (print_exp t)) cs) @ '')''" |
"print_exp (Ast.Lit lit) = ''('' @ print_lit lit @ '')''" |
"print_exp e = unsupported_code e"

fun print_dec :: "Ast.dec \<Rightarrow> string" where
"print_dec (Ast.Dletrec _ fs) =
  ''fun '' @
    intercalate '' and ''
      (map (\<lambda>(name, x, body). name @ '' '' @ x @ '' = '' @ print_exp body) fs)" |
"print_dec (Ast.Dlet _ pat body) =
  ''val '' @ print_pat pat @ '' = '' @ print_exp body" |
"print_dec d = unsupported_code d"

fun print_top :: "Ast.top0 \<Rightarrow> string" where
"print_top (Ast.Tdec d) = print_dec d  @ '';\<newline>''" |
"print_top d = unsupported_code d"

definition print_prog :: "Ast.prog \<Rightarrow> string" where
"print_prog ts = concat (map print_top ts)"

section \<open>Setup\<close>

ML_file "compiler.ML"

end