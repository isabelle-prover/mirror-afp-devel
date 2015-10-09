(*****************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

theory Init
imports "~~/src/HOL/Library/Code_Char"
        "isabelle_home/src/HOL/Isabelle_Main0"

begin

section\<open>Optimization on the String Datatype\<close>

text\<open>The following types will allow to delay all concatenations on @{typ "char list"},
     until we reach the end. As optimization, we also consider the use of @{typ String.literal}
     besides @{typ "char list"}.\<close>

type_notation natural ("nat")
definition "Succ x = x + 1"

datatype string\<^sub>b\<^sub>a\<^sub>s\<^sub>e = ST String.literal
                   | ST' "char list"
                   (* NOTE one can further optimize here
                           by adding another constructor for representing "nat"
                           (oid management) *)

datatype abr_string = (* NOTE operations in this datatype must not decrease the size of the string *)
                      SS_base string\<^sub>b\<^sub>a\<^sub>s\<^sub>e
                    | String_concatWith abr_string "abr_string list"

syntax "_string1" :: "_ \<Rightarrow> abr_string" ("\<langle>(_)\<rangle>")
translations "\<langle>x\<rangle>" \<rightleftharpoons> "CONST SS_base (CONST ST (CONST STR x))"

syntax "_string2" :: "_ \<Rightarrow> String.literal" ("\<prec>(_)\<succ>")
translations "\<prec>x\<succ>" \<rightleftharpoons> "CONST STR x"

syntax "_string3" :: "_ \<Rightarrow> abr_string" ("\<lless>(_)\<ggreater>")
translations "\<lless>x\<ggreater>" \<rightleftharpoons> "CONST SS_base (CONST ST' x)"

syntax "_char1" :: "_ \<Rightarrow> abr_string" ("\<degree>(_)\<degree>")
translations "\<degree>x\<degree>" \<rightleftharpoons> "CONST SS_base (CONST ST' ((CONST Cons) x (CONST Nil)))"

type_notation abr_string ("string")

section\<open>Basic Extension of the Standard Library\<close>

subsection\<open>Polymorphic Cartouches\<close>

text\<open>We generalize the construction of cartouches for them to be used ``polymorphically'',
     however the type inference is not automatic: 
     types of all cartouche expressions will need to be specified
     earlier before their use (we will however provide a default type).\<close>

ML\<open>
val cartouche_grammar =
  [ ("char list", snd)
  , ("String.literal", (fn (_, x) => Syntax.const @{const_syntax STR} $ x))
  , ("abr_string", (fn (_, x) => Syntax.const @{const_syntax SS_base}
                                 $ (Syntax.const @{const_syntax ST}
                                    $ (Syntax.const @{const_syntax STR}
                                       $ x))))]
\<close>

ML\<open>
fun parse_translation_cartouche binding l f_char accu = 
  let val cartouche_type = Attrib.setup_config_string binding (K (fst (hd l)))
      (* if there is no type specified, by default we set the first element
         to be the default type of cartouches *) in
  fn ctxt =>
    string_tr
      let val cart_type = Config.get ctxt cartouche_type in
      case (List.find (fn (s, _) => s = cart_type)
                          l) of
        NONE => error ("Unregistered return type for the cartouche: \"" ^ cart_type ^ "\"")
      | SOME (_, f) => f
      end
      f_char
      accu
      (Symbol_Pos.cartouche_content o Symbol_Pos.explode)
  end
\<close>

parse_translation \<open>
  [( @{syntax_const "_cartouche_string"}
   , parse_translation_cartouche @{binding cartouche_type} cartouche_grammar (K I) ())]
\<close>

text\<open>This is the special command which sets the type of subsequent cartouches.
     Note: here the given type is currently parsed as a string,
           one should extend it to be a truly ``typed'' type...\<close>
declare[[cartouche_type = "abr_string"]]

subsection\<open>Operations on List\<close>

datatype ('a, 'b) nsplit = Nsplit_text 'a
                         | Nsplit_sep 'b
locale L
begin
definition map where "map f l = rev (foldl (\<lambda>l x. f x # l) [] l)"
definition "flatten l = foldl (\<lambda>acc l. foldl (\<lambda>acc x. x # acc) acc (rev l)) [] (rev l)"
definition "mapi f l = rev (fst (foldl (\<lambda>(l,cpt) x. (f cpt x # l, Succ cpt)) ([], 0::nat) l))"
definition "iter f = foldl (\<lambda>_. f) ()"
definition "maps f x = L.flatten (L.map f x)"
definition append where "append a b = L.flatten [a, b]"
definition filter where "filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"
definition "mapM f l accu =
  (let (l, accu) = List.fold (\<lambda>x (l, accu). let (x, accu) = f x accu in (x # l, accu)) l ([], accu) in
   (rev l, accu))"
definition "assoc x1 l = List.fold (\<lambda>(x2, v). \<lambda>None \<Rightarrow> if x1 = x2 then Some v else None | x \<Rightarrow> x) l None"
definition split where "split l = (L.map fst l, L.map snd l)"
definition upto where "upto i j =
 (let to_i = \<lambda>n. int_of_integer (integer_of_natural n) in
  L.map (natural_of_integer o integer_of_int) (List.upto (to_i i) (to_i j)))"
definition "split_at f l =
 (let f = \<lambda>x. \<not> f x in
  (takeWhile f l, case dropWhile f l of [] \<Rightarrow> (None, []) | x # xs \<Rightarrow> (Some x, xs)))"
definition take where "take reverse lg l = reverse (snd (L.split (takeWhile (\<lambda>(n, _). n < lg) (enumerate 0 (reverse l)))))"
definition "take_last = take rev"
definition "take_first = take id"
definition "replace_gen f_res l c0 lby =
 (let Nsplit_text = \<lambda>l lgen. if l = [] then lgen else Nsplit_text l # lgen in
  case List.fold
         (\<lambda> c1 (l, lgen).
           if c0 c1 then
             (lby, Nsplit_sep c1 # Nsplit_text l lgen)
           else
             (c1 # l, lgen))
         (rev l)
         ([], [])
  of (l, lgen) \<Rightarrow> f_res (Nsplit_text l lgen))"
definition "nsplit_f l c0 = replace_gen id l c0 []"
definition "replace = replace_gen (L.flatten o L.map (\<lambda> Nsplit_text l \<Rightarrow> l | _ \<Rightarrow> []))"

fun map_find_aux where
   "map_find_aux accu f l = (\<lambda> [] \<Rightarrow> List.rev accu
                         | x # xs \<Rightarrow> (case f x of Some x \<Rightarrow> List.fold Cons accu (x # xs)
                                                | None \<Rightarrow> map_find_aux (x # accu) f xs)) l"
definition "map_find = map_find_aux []"

end
notation L.append (infixr "@@@@" 65)

lemmas [code] =
  (*def*)
  L.map_def
  L.flatten_def
  L.mapi_def
  L.iter_def
  L.maps_def
  L.append_def
  L.filter_def
  L.rev_map_def
  L.mapM_def
  L.assoc_def
  L.split_def
  L.upto_def
  L.split_at_def
  L.take_def
  L.take_last_def
  L.take_first_def
  L.replace_gen_def
  L.nsplit_f_def
  L.replace_def
  L.map_find_def

  (*fun*)
  L.map_find_aux.simps

subsection\<open>Operations on Char\<close>

definition "char_escape = Char Nibble0 Nibble9"
definition "ST0 c = \<lless>[c]\<ggreater>"
definition "ST0_base c = ST' [c]"

subsection\<open>Operations on String (I)\<close>

locale S
locale String
locale String\<^sub>b\<^sub>a\<^sub>s\<^sub>e

definition (in S) "flatten = String_concatWith \<open>\<close>"
definition (in String) "flatten a b = S.flatten [a, b]"
notation String.flatten (infixr "@@" 65)
definition (in String) "make n c = \<lless>L.map (\<lambda>_. c) (L.upto 1 n)\<ggreater>"
definition (in String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) "map_gen replace g = (\<lambda> ST s \<Rightarrow> replace \<open>\<close> (Some s) \<open>\<close>
                                                | ST' s \<Rightarrow> S.flatten (L.map g s))"
fun (in String) map_gen where
   "map_gen replace g e =
     (\<lambda> SS_base s \<Rightarrow> String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.map_gen replace g s
      | String_concatWith abr l \<Rightarrow> String_concatWith (map_gen replace g abr) (List.map (map_gen replace g) l)) e"
definition (in String) "foldl_one f accu s = foldl f accu (String.explode s)"
definition (in String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) foldl where "foldl f accu = (\<lambda> ST s \<Rightarrow> String.foldl_one f accu s
                                                       | ST' s \<Rightarrow> List.foldl f accu s)"
fun (in String) foldl where
   "foldl f accu e =
     (\<lambda> SS_base s \<Rightarrow> String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.foldl f accu s
      | String_concatWith abr l \<Rightarrow>
        (case l of [] \<Rightarrow> accu
                 | x # xs \<Rightarrow> List.foldl (\<lambda>accu. foldl f (foldl f accu abr)) (foldl f accu x) xs)) e"
definition (in S) "replace_chars f s1 s s2 =
  s1 @@ (case s of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> flatten (L.map f (String.explode s))) @@ s2"
definition (in String) map where "map f = map_gen (S.replace_chars (\<lambda>c. \<degree>f c\<degree>)) (\<lambda>x. \<degree>f x\<degree>)"
definition (in String) "replace_chars f = map_gen (S.replace_chars (\<lambda>c. f c)) f"
definition (in String) "all f = foldl (\<lambda>b s. b & f s) True"
definition (in String) length where "length = foldl (\<lambda>n _. Suc n) 0"
definition (in String) "to_list s = rev (foldl (\<lambda>l c. c # l) [] s)"
definition (in String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) "to_list = (\<lambda> ST s \<Rightarrow> String.explode s | ST' l \<Rightarrow> l)"
definition (in String) "to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e = (\<lambda> SS_base s \<Rightarrow> s | s \<Rightarrow> ST' (to_list s))"
definition (in String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) "to_String = SS_base"
definition (in String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) "is_empty = (\<lambda> ST s \<Rightarrow> s = STR ''''
                                       | ST' s \<Rightarrow> s = [])"
fun (in String) is_empty where
   "is_empty e = (\<lambda> SS_base s \<Rightarrow> String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.is_empty s | String_concatWith _ l \<Rightarrow> list_all is_empty l) e"
definition (in String) "equal s1 s2 = (to_list s1 = to_list s2)"
notation String.equal (infixl "\<triangleq>" 50)
definition (in String) "assoc x l = L.assoc (to_list x) (L.map (map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list id) l)"
definition (in String) "member l x = List.member (L.map String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list l) (to_list x)"
definition (in String\<^sub>b\<^sub>a\<^sub>s\<^sub>e) "flatten l = String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S.flatten (L.map to_String l))"

lemmas [code] =
  (*def*)
  S.flatten_def
  String.flatten_def
  String.make_def
  String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.map_gen_def
  String.foldl_one_def
  String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.foldl_def
  S.replace_chars_def
  String.map_def
  String.replace_chars_def
  String.all_def
  String.length_def
  String.to_list_def
  String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list_def
  String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
  String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String_def
  String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.is_empty_def
  String.equal_def
  String.assoc_def
  String.member_def
  String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.flatten_def

  (*fun*)
  String.map_gen.simps
  String.foldl.simps
  String.is_empty.simps

subsection\<open>Operations on String (II)\<close>

definition "wildcard = \<open>_\<close>"

definition "nat_raw_to_str = L.map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
context String
begin
definition "lowercase = map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "uppercase = map (\<lambda>c. let n = nat_of_char c in if n < 97 then c else char_of_nat (n - 32))"
definition "to_bold_number = replace_chars (\<lambda>c. [\<open>\<zero>\<close>, \<open>\<one>\<close>, \<open>\<two>\<close>, \<open>\<three>\<close>, \<open>\<four>\<close>, \<open>\<five>\<close>, \<open>\<six>\<close>, \<open>\<seven>\<close>, \<open>\<eight>\<close>, \<open>\<nine>\<close>] ! (nat_of_char c - 48))"
fun of_nat_aux where
   "of_nat_aux l (n :: Nat.nat) = (if n < 10 then n # l else of_nat_aux (n mod 10 # l) (n div 10))"
definition of_nat where "of_nat n = \<lless>nat_raw_to_str (of_nat_aux [] n)\<ggreater>"
definition "of_natural = of_nat o nat_of_natural"
end
lemmas [code] =
  (*def*)
  String.lowercase_def
  String.uppercase_def
  String.to_bold_number_def
  String.of_nat_def
  String.of_natural_def

  (*fun*)
  String.of_nat_aux.simps

definition "add_0 n =
 (let n = nat_of_char n in
  S.flatten (L.map (\<lambda>_. \<open>0\<close>) (upt 0 (if n < 10 then 2 else if n < 100 then 1 else 0)))
  @@ String.of_nat n)"
definition "is_letter n = (n \<ge> CHR ''A'' & n \<le> CHR ''Z'' | n \<ge> CHR ''a'' & n \<le> CHR ''z'')"
definition "is_digit n = (n \<ge> CHR ''0'' & n \<le> CHR ''9'')"
definition "is_special = List.member '' <>^_=-./(){}''"
context String
begin
definition "base255 = replace_chars (\<lambda>c. if is_letter c then \<degree>c\<degree> else add_0 c)"
definition "isub = replace_chars (\<lambda>c.
  if is_letter c | is_digit c | List.member ''_'' c then \<open>\<^sub>\<close> @@ \<degree>c\<degree> else add_0 c)"
definition "isup s = \<open>__\<close> @@ s"
end
lemmas [code] =
  (*def*)
  String.base255_def
  String.isub_def
  String.isup_def

definition "text_of_str str =
 (let s = \<open>c\<close>
    ; ap = \<open> # \<close> in
  S.flatten [ \<open>(let \<close>, s, \<open> = char_of_nat in \<close>
          , String.replace_chars (\<lambda>c.
                                    if is_letter c then
                                      S.flatten [\<open>CHR ''\<close>,\<degree>c\<degree>,\<open>''\<close>,ap]
                                    else
                                      S.flatten [s, \<open> \<close>,  add_0 c, ap])
                                 str
          , \<open>[])\<close>])"
definition' \<open>text2_of_str = String.replace_chars (\<lambda>c. S.flatten [\<open>\\<close>, \<open><\<close>, \<degree>c\<degree>, \<open>>\<close>])\<close>

definition "textstr_of_str f_flatten f_char f_str str =
 (let str0 = String.to_list str
    ; f_letter = \<lambda>c. is_letter c | is_digit c | is_special c
    ; s = \<open>c\<close>
    ; f_text = \<lambda> Nsplit_text l \<Rightarrow> S.flatten [f_str (S.flatten [\<open>STR ''\<close>,\<lless>l\<ggreater>,\<open>''\<close>])]
               | Nsplit_sep c \<Rightarrow> S.flatten [f_char c]
    ; str = case L.nsplit_f str0 (Not o f_letter) of
              [] \<Rightarrow> S.flatten [f_str \<open>STR ''''\<close>]
            | [x] \<Rightarrow> f_text x
            | l \<Rightarrow> S.flatten (L.map (\<lambda>x. \<open>(\<close> @@ f_text x @@ \<open>) # \<close>) l) @@ \<open>[]\<close> in
  if list_all f_letter str0 then
    str
  else
    f_flatten (S.flatten [ \<open>(\<close>, str, \<open>)\<close> ]))"

definition' \<open>escape_sml = String.replace_chars (\<lambda>x. if x = Char Nibble2 Nibble2 then \<open>\"\<close> else \<degree>x\<degree>)\<close>
text \<open>Because of @{theory "Code_Char"}, it is not possible of extracting
@{term "\<lambda> Char Nibble2 Nibble2 \<Rightarrow> \<open>\"\<close> | x \<Rightarrow> \<degree>x\<degree>"}.\<close>
definition "mk_constr_name name = (\<lambda> x. S.flatten [String.isub name, \<open>_\<close>, String.isub x])"
definition "mk_dot s1 s2 = S.flatten [\<open>.\<close>, s1, s2]"
definition "mk_dot_par_gen dot l_s = S.flatten [dot, \<open>(\<close>, case l_s of [] \<Rightarrow> \<open>\<close> | x # xs \<Rightarrow> S.flatten [x, S.flatten (L.map (\<lambda>s. \<open>, \<close> @@ s) xs) ], \<open>)\<close>]"
definition "mk_dot_par dot s = mk_dot_par_gen dot [s]"
definition "mk_dot_comment s1 s2 s3 = mk_dot s1 (S.flatten [s2, \<open> /*\<close>, s3, \<open>*/\<close>])"

definition "hol_definition s = S.flatten [s, \<open>_def\<close>]"
definition "hol_split s = S.flatten [s, \<open>.split\<close>]"

end
