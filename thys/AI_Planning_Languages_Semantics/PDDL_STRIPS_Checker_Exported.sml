structure Str_Literal : sig
  type int = IntInf.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open IntInf;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;

structure PDDL_Checker_Exported : sig
  type char
  type nat
  datatype ordera = Eq | Lt | Gt
  datatype 'a formula = Atom of 'a | Bot | Not of 'a formula |
    And of 'a formula * 'a formula | Or of 'a formula * 'a formula |
    Imp of 'a formula * 'a formula
  datatype predicate = Pred of char list
  datatype 'a atom = PredAtm of predicate * 'a list | Eqa of 'a * 'a
  datatype object = Obj of char list
  datatype variable = Var of char list
  type 'a set
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
  type ('a, 'b) mapping
  datatype term = VAR of variable | CONST of object
  datatype typea = Either of (char list) list
  datatype 'a ast_effect = Effect of 'a atom formula list * 'a atom formula list
  datatype ast_action_schema =
    Action_Schema of
      char list * (variable * typea) list * term atom formula * term ast_effect
  datatype predicate_decl = PredDecl of predicate * typea list
  datatype ast_domain =
    Domain of
      (char list * char list) list * predicate_decl list *
        (object * typea) list * ast_action_schema list
  datatype ast_problem =
    Problem of
      ast_domain * (object * typea) list * object atom formula list *
        object atom formula
  datatype plan_action = PAction of char list * object list
  val bigOr : 'a formula list -> 'a formula
  val implode : char list -> string
  val bigAnd : 'a formula list -> 'a formula
  val explode : string -> char list
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  val map_atom : ('a -> 'b) -> 'a atom -> 'b atom
  val check_plan : ast_problem -> plan_action list -> (string, unit) sum
  val predicate : 'a atom -> predicate
end = struct

fun less_eq_bool false b = true
  | less_eq_bool true b = b;

fun less_bool false b = b
  | less_bool true b = false;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_bool = {less_eq = less_eq_bool, less = less_bool} : bool ord;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype nat = Nat of IntInf.int;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list,
    shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

fun shows_prec_list A_ p xs = shows_list A_ xs;

val zero_nat : nat = Nat (0 : IntInf.int);

fun shows_string x = (fn a => x @ a);

fun shows_sep s sep [] = shows_string []
  | shows_sep s sep [x] = s x
  | shows_sep s sep (x :: v :: va) = s x o sep o shows_sep s sep (v :: va);

fun null [] = true
  | null (x :: xs) = false;

fun shows_list_gen showsx e l s r xs =
  (if null xs then shows_string e
    else shows_string l o shows_sep showsx (shows_string s) xs o
           shows_string r);

fun showsp_list s p xs =
  shows_list_gen (s zero_nat)
    [Chara (true, true, false, true, true, false, true, false),
      Chara (true, false, true, true, true, false, true, false)]
    [Chara (true, true, false, true, true, false, true, false)]
    [Chara (false, false, true, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)]
    [Chara (true, false, true, true, true, false, true, false)] xs;

fun shows_list_list A_ xss = showsp_list (shows_prec_list A_) zero_nat xss;

fun show_list A_ =
  {shows_prec = shows_prec_list A_, shows_list = shows_list_list A_} :
  ('a list) show;

fun equality_list eq_a [] [] = true
  | equality_list eq_a [] (y :: ya) = false
  | equality_list eq_a (x :: xa) [] = false
  | equality_list eq_a (x :: xa) (y :: ya) =
    eq_a x y andalso equality_list eq_a xa ya;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};
val ceq = #ceq : 'a ceq -> ('a -> 'a -> bool) option;

fun ceq_lista A_ =
  (case ceq A_ of NONE => NONE | SOME eq_a => SOME (equality_list eq_a));

fun ceq_list A_ = {ceq = ceq_lista A_} : ('a list) ceq;

datatype ('a, 'b) phantom = Phantom of 'b;

datatype set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT |
  Set_Monada;

val set_impl_lista : (('a list), set_impla) phantom = Phantom Set_Choose;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};
val set_impl = #set_impl : 'a set_impl -> ('a, set_impla) phantom;

val set_impl_list = {set_impl = set_impl_lista} : ('a list) set_impl;

val cEnum_list :
  (('a list) list *
    ((('a list -> bool) -> bool) * (('a list -> bool) -> bool))) option
  = NONE;

type 'a cenum =
  {cEnum :
     ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option};
val cEnum = #cEnum :
  'a cenum ->
    ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option;

val cenum_list = {cEnum = cEnum_list} : ('a list) cenum;

datatype ordera = Eq | Lt | Gt;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};
val ccompare = #ccompare : 'a ccompare -> ('a -> 'a -> ordera) option;

fun comparator_list comp_a [] [] = Eq
  | comparator_list comp_a [] (y :: ya) = Lt
  | comparator_list comp_a (x :: xa) [] = Gt
  | comparator_list comp_a (x :: xa) (y :: ya) =
    (case comp_a x y of Eq => comparator_list comp_a xa ya | Lt => Lt
      | Gt => Gt);

fun ccompare_lista A_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a => SOME (comparator_list comp_a));

fun ccompare_list A_ = {ccompare = ccompare_lista A_} : ('a list) ccompare;

datatype mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT |
  Mapping_Mapping;

val mapping_impl_lista : (('a list), mapping_impla) phantom =
  Phantom Mapping_Choose;

type 'a mapping_impl = {mapping_impl : ('a, mapping_impla) phantom};
val mapping_impl = #mapping_impl :
  'a mapping_impl -> ('a, mapping_impla) phantom;

val mapping_impl_list = {mapping_impl = mapping_impl_lista} :
  ('a list) mapping_impl;

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

fun shows_prec_char p c = (fn a => c :: a);

fun shows_list_char cs = shows_string cs;

val show_char = {shows_prec = shows_prec_char, shows_list = shows_list_char} :
  char show;

fun lexordp_eq A_ [] ys = true
  | lexordp_eq A_ xs [] = null xs
  | lexordp_eq A_ (x :: xs) (y :: ys) =
    less A_ x y orelse not (less A_ y x) andalso lexordp_eq A_ xs ys;

fun less_eq_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7))
  (Chara (c0, c1, c2, c3, c4, c5, c6, c7)) =
  lexordp_eq ord_bool [b7, b6, b5, b4, b3, b2, b1, b0]
    [c7, c6, c5, c4, c3, c2, c1, c0];

fun lexordp A_ [] ys = not (null ys)
  | lexordp A_ xs [] = false
  | lexordp A_ (x :: xs) (y :: ys) =
    less A_ x y orelse not (less A_ y x) andalso lexordp A_ xs ys;

fun less_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7))
  (Chara (c0, c1, c2, c3, c4, c5, c6, c7)) =
  lexordp ord_bool [b7, b6, b5, b4, b3, b2, b1, b0]
    [c7, c6, c5, c4, c3, c2, c1, c0];

val ord_char = {less_eq = less_eq_char, less = less_char} : char ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_char = {ord_preorder = ord_char} : char preorder;

val order_char = {preorder_order = preorder_char} : char order;

val ceq_chara : (char -> char -> bool) option = SOME equal_chara;

val ceq_char = {ceq = ceq_chara} : char ceq;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_char = {order_linorder = order_char} : char linorder;

fun comparator_of (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then Lt
    else (if eq A1_ x y then Eq else Gt));

fun compare_char x = comparator_of (equal_char, linorder_char) x;

val ccompare_chara : (char -> char -> ordera) option = SOME compare_char;

val ccompare_char = {ccompare = ccompare_chara} : char ccompare;

datatype 'a formula = Atom of 'a | Bot | Not of 'a formula |
  And of 'a formula * 'a formula | Or of 'a formula * 'a formula |
  Imp of 'a formula * 'a formula;

fun equal_formulaa A_ (Or (x51, x52)) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Or (x51, x52)) = false
  | equal_formulaa A_ (And (x41, x42)) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) (And (x41, x42)) = false
  | equal_formulaa A_ (Not x3) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Not x3) = false
  | equal_formulaa A_ (Not x3) (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) (Not x3) = false
  | equal_formulaa A_ (Not x3) (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) (Not x3) = false
  | equal_formulaa A_ Bot (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) Bot = false
  | equal_formulaa A_ Bot (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) Bot = false
  | equal_formulaa A_ Bot (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) Bot = false
  | equal_formulaa A_ Bot (Not x3) = false
  | equal_formulaa A_ (Not x3) Bot = false
  | equal_formulaa A_ (Atom x1) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) (Not x3) = false
  | equal_formulaa A_ (Not x3) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) Bot = false
  | equal_formulaa A_ Bot (Atom x1) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Imp (y61, y62)) =
    equal_formulaa A_ x61 y61 andalso equal_formulaa A_ x62 y62
  | equal_formulaa A_ (Or (x51, x52)) (Or (y51, y52)) =
    equal_formulaa A_ x51 y51 andalso equal_formulaa A_ x52 y52
  | equal_formulaa A_ (And (x41, x42)) (And (y41, y42)) =
    equal_formulaa A_ x41 y41 andalso equal_formulaa A_ x42 y42
  | equal_formulaa A_ (Not x3) (Not y3) = equal_formulaa A_ x3 y3
  | equal_formulaa A_ (Atom x1) (Atom y1) = eq A_ x1 y1
  | equal_formulaa A_ Bot Bot = true;

fun equal_formula A_ = {equal = equal_formulaa A_} : 'a formula equal;

fun comparator_formula comp_a (Atom x) (Atom y) = comp_a x y
  | comparator_formula comp_a (Atom x) Bot = Lt
  | comparator_formula comp_a (Atom x) (Not ya) = Lt
  | comparator_formula comp_a (Atom x) (And (yb, yc)) = Lt
  | comparator_formula comp_a (Atom x) (Or (yd, ye)) = Lt
  | comparator_formula comp_a (Atom x) (Imp (yf, yg)) = Lt
  | comparator_formula comp_a Bot (Atom y) = Gt
  | comparator_formula comp_a Bot Bot = Eq
  | comparator_formula comp_a Bot (Not ya) = Lt
  | comparator_formula comp_a Bot (And (yb, yc)) = Lt
  | comparator_formula comp_a Bot (Or (yd, ye)) = Lt
  | comparator_formula comp_a Bot (Imp (yf, yg)) = Lt
  | comparator_formula comp_a (Not x) (Atom y) = Gt
  | comparator_formula comp_a (Not x) Bot = Gt
  | comparator_formula comp_a (Not x) (Not ya) = comparator_formula comp_a x ya
  | comparator_formula comp_a (Not x) (And (yb, yc)) = Lt
  | comparator_formula comp_a (Not x) (Or (yd, ye)) = Lt
  | comparator_formula comp_a (Not x) (Imp (yf, yg)) = Lt
  | comparator_formula comp_a (And (x, xa)) (Atom y) = Gt
  | comparator_formula comp_a (And (x, xa)) Bot = Gt
  | comparator_formula comp_a (And (x, xa)) (Not ya) = Gt
  | comparator_formula comp_a (And (x, xa)) (And (yb, yc)) =
    (case comparator_formula comp_a x yb
      of Eq => comparator_formula comp_a xa yc | Lt => Lt | Gt => Gt)
  | comparator_formula comp_a (And (x, xa)) (Or (yd, ye)) = Lt
  | comparator_formula comp_a (And (x, xa)) (Imp (yf, yg)) = Lt
  | comparator_formula comp_a (Or (x, xa)) (Atom y) = Gt
  | comparator_formula comp_a (Or (x, xa)) Bot = Gt
  | comparator_formula comp_a (Or (x, xa)) (Not ya) = Gt
  | comparator_formula comp_a (Or (x, xa)) (And (yb, yc)) = Gt
  | comparator_formula comp_a (Or (x, xa)) (Or (yd, ye)) =
    (case comparator_formula comp_a x yd
      of Eq => comparator_formula comp_a xa ye | Lt => Lt | Gt => Gt)
  | comparator_formula comp_a (Or (x, xa)) (Imp (yf, yg)) = Lt
  | comparator_formula comp_a (Imp (x, xa)) (Atom y) = Gt
  | comparator_formula comp_a (Imp (x, xa)) Bot = Gt
  | comparator_formula comp_a (Imp (x, xa)) (Not ya) = Gt
  | comparator_formula comp_a (Imp (x, xa)) (And (yb, yc)) = Gt
  | comparator_formula comp_a (Imp (x, xa)) (Or (yd, ye)) = Gt
  | comparator_formula comp_a (Imp (x, xa)) (Imp (yf, yg)) =
    (case comparator_formula comp_a x yf
      of Eq => comparator_formula comp_a xa yg | Lt => Lt | Gt => Gt);

fun le_of_comp acomp x y =
  (case acomp x y of Eq => true | Lt => true | Gt => false);

fun less_eq_formula (A1_, A2_) =
  le_of_comp (comparator_formula (comparator_of (A1_, A2_)));

fun lt_of_comp acomp x y =
  (case acomp x y of Eq => false | Lt => true | Gt => false);

fun less_formula (A1_, A2_) =
  lt_of_comp (comparator_formula (comparator_of (A1_, A2_)));

fun ord_formula (A1_, A2_) =
  {less_eq = less_eq_formula (A1_, A2_), less = less_formula (A1_, A2_)} :
  'a formula ord;

fun preorder_formula (A1_, A2_) = {ord_preorder = ord_formula (A1_, A2_)} :
  'a formula preorder;

fun order_formula (A1_, A2_) = {preorder_order = preorder_formula (A1_, A2_)} :
  'a formula order;

fun equality_formula eq_a (Atom x) (Atom y) = eq_a x y
  | equality_formula eq_a (Atom x) Bot = false
  | equality_formula eq_a (Atom x) (Not ya) = false
  | equality_formula eq_a (Atom x) (And (yb, yc)) = false
  | equality_formula eq_a (Atom x) (Or (yd, ye)) = false
  | equality_formula eq_a (Atom x) (Imp (yf, yg)) = false
  | equality_formula eq_a Bot (Atom y) = false
  | equality_formula eq_a Bot Bot = true
  | equality_formula eq_a Bot (Not ya) = false
  | equality_formula eq_a Bot (And (yb, yc)) = false
  | equality_formula eq_a Bot (Or (yd, ye)) = false
  | equality_formula eq_a Bot (Imp (yf, yg)) = false
  | equality_formula eq_a (Not x) (Atom y) = false
  | equality_formula eq_a (Not x) Bot = false
  | equality_formula eq_a (Not x) (Not ya) = equality_formula eq_a x ya
  | equality_formula eq_a (Not x) (And (yb, yc)) = false
  | equality_formula eq_a (Not x) (Or (yd, ye)) = false
  | equality_formula eq_a (Not x) (Imp (yf, yg)) = false
  | equality_formula eq_a (And (x, xa)) (Atom y) = false
  | equality_formula eq_a (And (x, xa)) Bot = false
  | equality_formula eq_a (And (x, xa)) (Not ya) = false
  | equality_formula eq_a (And (x, xa)) (And (yb, yc)) =
    equality_formula eq_a x yb andalso equality_formula eq_a xa yc
  | equality_formula eq_a (And (x, xa)) (Or (yd, ye)) = false
  | equality_formula eq_a (And (x, xa)) (Imp (yf, yg)) = false
  | equality_formula eq_a (Or (x, xa)) (Atom y) = false
  | equality_formula eq_a (Or (x, xa)) Bot = false
  | equality_formula eq_a (Or (x, xa)) (Not ya) = false
  | equality_formula eq_a (Or (x, xa)) (And (yb, yc)) = false
  | equality_formula eq_a (Or (x, xa)) (Or (yd, ye)) =
    equality_formula eq_a x yd andalso equality_formula eq_a xa ye
  | equality_formula eq_a (Or (x, xa)) (Imp (yf, yg)) = false
  | equality_formula eq_a (Imp (x, xa)) (Atom y) = false
  | equality_formula eq_a (Imp (x, xa)) Bot = false
  | equality_formula eq_a (Imp (x, xa)) (Not ya) = false
  | equality_formula eq_a (Imp (x, xa)) (And (yb, yc)) = false
  | equality_formula eq_a (Imp (x, xa)) (Or (yd, ye)) = false
  | equality_formula eq_a (Imp (x, xa)) (Imp (yf, yg)) =
    equality_formula eq_a x yf andalso equality_formula eq_a xa yg;

fun ceq_formulaa A_ =
  (case ceq A_ of NONE => NONE | SOME eq_a => SOME (equality_formula eq_a));

fun ceq_formula A_ = {ceq = ceq_formulaa A_} : 'a formula ceq;

val set_impl_formulaa : ('a formula, set_impla) phantom = Phantom Set_RBT;

val set_impl_formula = {set_impl = set_impl_formulaa} : 'a formula set_impl;

fun linorder_formula (A1_, A2_) = {order_linorder = order_formula (A1_, A2_)} :
  'a formula linorder;

fun ccompare_formulaa A_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a => SOME (comparator_formula comp_a));

fun ccompare_formula A_ = {ccompare = ccompare_formulaa A_} :
  'a formula ccompare;

fun equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y andalso eq_b xa ya;

fun ceq_proda A_ B_ =
  (case ceq A_ of NONE => NONE
    | SOME eq_a =>
      (case ceq B_ of NONE => NONE
        | SOME eq_b => SOME (equality_prod eq_a eq_b)));

fun ceq_prod A_ B_ = {ceq = ceq_proda A_ B_} : ('a * 'b) ceq;

fun of_phantom (Phantom x) = x;

fun set_impl_choose2 Set_Monada Set_Monada = Set_Monada
  | set_impl_choose2 Set_RBT Set_RBT = Set_RBT
  | set_impl_choose2 Set_DList Set_DList = Set_DList
  | set_impl_choose2 Set_Collect Set_Collect = Set_Collect
  | set_impl_choose2 x y = Set_Choose;

fun set_impl_proda A_ B_ =
  Phantom
    (set_impl_choose2 (of_phantom (set_impl A_)) (of_phantom (set_impl B_)));

fun set_impl_prod A_ B_ = {set_impl = set_impl_proda A_ B_} :
  ('a * 'b) set_impl;

fun comparator_prod comp_a comp_b (x, xa) (y, ya) =
  (case comp_a x y of Eq => comp_b xa ya | Lt => Lt | Gt => Gt);

fun ccompare_proda A_ B_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a =>
      (case ccompare B_ of NONE => NONE
        | SOME comp_b => SOME (comparator_prod comp_a comp_b)));

fun ccompare_prod A_ B_ = {ccompare = ccompare_proda A_ B_} :
  ('a * 'b) ccompare;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype predicate = Pred of char list;

fun equal_predicatea (Pred x) (Pred ya) = equal_lista equal_char x ya;

datatype 'a atom = PredAtm of predicate * 'a list | Eqa of 'a * 'a;

fun equal_atoma A_ (PredAtm (x11, x12)) (Eqa (x21, x22)) = false
  | equal_atoma A_ (Eqa (x21, x22)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (Eqa (x21, x22)) (Eqa (y21, y22)) =
    eq A_ x21 y21 andalso eq A_ x22 y22
  | equal_atoma A_ (PredAtm (x11, x12)) (PredAtm (y11, y12)) =
    equal_predicatea x11 y11 andalso equal_lista A_ x12 y12;

fun equal_atom A_ = {equal = equal_atoma A_} : 'a atom equal;

fun comparator_predicate (Pred x) (Pred y) =
  comparator_list (comparator_of (equal_char, linorder_char)) x y;

fun comparator_atom comp_e_n_t (PredAtm (x, xa)) (PredAtm (y, ya)) =
  (case comparator_predicate x y of Eq => comparator_list comp_e_n_t xa ya
    | Lt => Lt | Gt => Gt)
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (Eqa (yb, yc)) = Lt
  | comparator_atom comp_e_n_t (Eqa (x, xa)) (PredAtm (y, ya)) = Gt
  | comparator_atom comp_e_n_t (Eqa (x, xa)) (Eqa (yb, yc)) =
    (case comp_e_n_t x yb of Eq => comp_e_n_t xa yc | Lt => Lt | Gt => Gt);

fun less_eq_atom (A1_, A2_) =
  le_of_comp (comparator_atom (comparator_of (A1_, A2_)));

fun less_atom (A1_, A2_) =
  lt_of_comp (comparator_atom (comparator_of (A1_, A2_)));

fun ord_atom (A1_, A2_) =
  {less_eq = less_eq_atom (A1_, A2_), less = less_atom (A1_, A2_)} :
  'a atom ord;

fun preorder_atom (A1_, A2_) = {ord_preorder = ord_atom (A1_, A2_)} :
  'a atom preorder;

fun order_atom (A1_, A2_) = {preorder_order = preorder_atom (A1_, A2_)} :
  'a atom order;

fun equality_predicate (Pred x) (Pred y) = equality_list equal_chara x y;

fun equality_atom eq_e_n_t (PredAtm (x, xa)) (PredAtm (y, ya)) =
  equality_predicate x y andalso equality_list eq_e_n_t xa ya
  | equality_atom eq_e_n_t (PredAtm (x, xa)) (Eqa (yb, yc)) = false
  | equality_atom eq_e_n_t (Eqa (x, xa)) (PredAtm (y, ya)) = false
  | equality_atom eq_e_n_t (Eqa (x, xa)) (Eqa (yb, yc)) =
    eq_e_n_t x yb andalso eq_e_n_t xa yc;

fun ceq_atoma A_ =
  (case ceq A_ of NONE => NONE | SOME eq_ent => SOME (equality_atom eq_ent));

fun ceq_atom A_ = {ceq = ceq_atoma A_} : 'a atom ceq;

fun linorder_atom (A1_, A2_) = {order_linorder = order_atom (A1_, A2_)} :
  'a atom linorder;

fun ccompare_atoma A_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_ent => SOME (comparator_atom comp_ent));

fun ccompare_atom A_ = {ccompare = ccompare_atoma A_} : 'a atom ccompare;

datatype object = Obj of char list;

fun equal_objecta (Obj x) (Obj ya) = equal_lista equal_char x ya;

val equal_object = {equal = equal_objecta} : object equal;

fun comparator_object (Obj x) (Obj y) =
  comparator_list (comparator_of (equal_char, linorder_char)) x y;

fun less_eq_object x = le_of_comp comparator_object x;

fun less_object x = lt_of_comp comparator_object x;

val ord_object = {less_eq = less_eq_object, less = less_object} : object ord;

val preorder_object = {ord_preorder = ord_object} : object preorder;

val order_object = {preorder_order = preorder_object} : object order;

fun equality_object (Obj x) (Obj y) = equality_list equal_chara x y;

val ceq_objecta : (object -> object -> bool) option = SOME equality_object;

val ceq_object = {ceq = ceq_objecta} : object ceq;

val linorder_object = {order_linorder = order_object} : object linorder;

val ccompare_objecta : (object -> object -> ordera) option =
  SOME comparator_object;

val ccompare_object = {ccompare = ccompare_objecta} : object ccompare;

val mapping_impl_objecta : (object, mapping_impla) phantom =
  Phantom Mapping_RBT;

val mapping_impl_object = {mapping_impl = mapping_impl_objecta} :
  object mapping_impl;

datatype variable = Var of char list;

fun equal_variablea (Var x) (Var ya) = equal_lista equal_char x ya;

val equal_variable = {equal = equal_variablea} : variable equal;

val equal_predicate = {equal = equal_predicatea} : predicate equal;

fun less_eq_predicate x = le_of_comp comparator_predicate x;

fun less_predicate x = lt_of_comp comparator_predicate x;

val ord_predicate = {less_eq = less_eq_predicate, less = less_predicate} :
  predicate ord;

val preorder_predicate = {ord_preorder = ord_predicate} : predicate preorder;

val order_predicate = {preorder_order = preorder_predicate} : predicate order;

val linorder_predicate = {order_linorder = order_predicate} :
  predicate linorder;

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

datatype ('b, 'a) mapping_rbt = Mapping_RBTa of ('b, 'a) rbt;

datatype 'a set_dlist = Abs_dlist of 'a list;

datatype 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;

datatype ('b, 'a) alist = Alist of ('b * 'a) list;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);

datatype ('a, 'b) generator = Generator of (('b -> bool) * ('b -> 'a * 'b));

datatype term = VAR of variable | CONST of object;

datatype typea = Either of (char list) list;

datatype 'a ast_effect = Effect of 'a atom formula list * 'a atom formula list;

datatype ast_action_schema =
  Action_Schema of
    char list * (variable * typea) list * term atom formula * term ast_effect;

datatype predicate_decl = PredDecl of predicate * typea list;

datatype ast_domain =
  Domain of
    (char list * char list) list * predicate_decl list * (object * typea) list *
      ast_action_schema list;

datatype ast_problem =
  Problem of
    ast_domain * (object * typea) list * object atom formula list *
      object atom formula;

datatype plan_action = PAction of char list * object list;

datatype ground_action =
  Ground_Action of object atom formula * object ast_effect;

fun id x = (fn xa => xa) x;

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun emptyc A_ = Mapping_RBTa Empty;

fun emptyb A_ = Abs_dlist [];

fun set_empty_choose (A1_, A2_) =
  (case ccompare A2_
    of NONE =>
      (case ceq A1_ of NONE => Set_Monad [] | SOME _ => DList_set (emptyb A1_))
    | SOME _ => RBT_set (emptyc A2_));

fun set_empty (A1_, A2_) Set_Collect = Collect_set (fn _ => false)
  | set_empty (A1_, A2_) Set_DList = DList_set (emptyb A1_)
  | set_empty (A1_, A2_) Set_RBT = RBT_set (emptyc A2_)
  | set_empty (A1_, A2_) Set_Monada = Set_Monad []
  | set_empty (A1_, A2_) Set_Choose = set_empty_choose (A1_, A2_);

fun bot_set (A1_, A2_, A3_) = set_empty (A1_, A2_) (of_phantom (set_impl A3_));

fun list_of_dlist A_ (Abs_dlist x) = x;

fun foldc A_ x xc = fold x (list_of_dlist A_ xc);

fun impl_ofa B_ (Mapping_RBTa x) = x;

fun folda f Empty x = x
  | folda f (Branch (c, lt, k, v, rt)) x = folda f rt (f k v (folda f lt x));

fun foldb A_ x xc = folda (fn a => fn _ => x a) (impl_ofa A_ xc);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun fun_upda equal f aa b a = (if equal aa a then b else f a);

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun rbt_comp_ins c f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_comp_ins c f k v (Branch (B, l, x, y, r)) =
    (case c k x of Eq => Branch (B, l, x, f k y v, r)
      | Lt => balance (rbt_comp_ins c f k v l) x y r
      | Gt => balance l x y (rbt_comp_ins c f k v r))
  | rbt_comp_ins c f k v (Branch (R, l, x, y, r)) =
    (case c k x of Eq => Branch (R, l, x, f k y v, r)
      | Lt => Branch (R, rbt_comp_ins c f k v l, x, y, r)
      | Gt => Branch (R, l, x, y, rbt_comp_ins c f k v r));

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);

fun rbt_comp_insert c =
  rbt_comp_insert_with_key c (fn _ => fn _ => fn nv => nv);

fun the (SOME x2) = x2;

fun insertb A_ xc xd xe =
  Mapping_RBTa (rbt_comp_insert (the (ccompare A_)) xc xd (impl_ofa A_ xe));

fun list_member equal [] y = false
  | list_member equal (x :: xs) y = equal x y orelse list_member equal xs y;

fun list_insert equal x xs = (if list_member equal xs x then xs else x :: xs);

fun inserta A_ xb xc =
  Abs_dlist (list_insert (the (ceq A_)) xb (list_of_dlist A_ xc));

fun balance_right a k x (Branch (R, b, s, y, c)) =
  Branch (R, a, k, x, Branch (B, b, s, y, c))
  | balance_right (Branch (B, a, k, x, b)) s y Empty =
    balance (Branch (R, a, k, x, b)) s y Empty
  | balance_right (Branch (B, a, k, x, b)) s y (Branch (B, va, vb, vc, vd)) =
    balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z Empty =
    Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, balance (paint R a) k x b, s, y,
        Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
  | balance_right Empty k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Empty)) k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh))) k x Empty
    = Empty
  | balance_right Empty k x (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Empty)) k x
    (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl))) k x
    (Branch (B, va, vb, vc, vd)) = Empty;

fun balance_left (Branch (R, a, k, x, b)) s y c =
  Branch (R, Branch (B, a, k, x, b), s, y, c)
  | balance_left Empty k x (Branch (B, a, s, y, b)) =
    balance Empty k x (Branch (R, a, s, y, b))
  | balance_left (Branch (B, va, vb, vc, vd)) k x (Branch (B, a, s, y, b)) =
    balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
  | balance_left Empty k x (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
        balance b t z (paint R c))
  | balance_left Empty k x Empty = Empty
  | balance_left Empty k x (Branch (R, Empty, vb, vc, vd)) = Empty
  | balance_left Empty k x (Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd))
    = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x Empty = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Empty, vf, vg, vh)) = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)) = Empty;

fun combine Empty x = x
  | combine (Branch (v, va, vb, vc, vd)) Empty = Branch (v, va, vb, vc, vd)
  | combine (Branch (R, a, k, x, b)) (Branch (R, c, s, y, d)) =
    (case combine b c
      of Empty => Branch (R, a, k, x, Branch (R, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, a, k, x, b)) (Branch (B, c, s, y, d)) =
    (case combine b c
      of Empty => balance_left a k x (Branch (B, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, va, vb, vc, vd)) (Branch (R, b, k, x, c)) =
    Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
  | combine (Branch (R, a, k, x, b)) (Branch (B, va, vb, vc, vd)) =
    Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));

fun rbt_comp_del c x Empty = Empty
  | rbt_comp_del c x (Branch (uu, a, y, s, b)) =
    (case c x y of Eq => combine a b | Lt => rbt_comp_del_from_left c x a y s b
      | Gt => rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left c x (Branch (B, lt, z, v, rt)) y s b =
  balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
  | rbt_comp_del_from_left c x Empty y s b =
    Branch (R, rbt_comp_del c x Empty, y, s, b)
  | rbt_comp_del_from_left c x (Branch (R, va, vb, vc, vd)) y s b =
    Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right c x a y s (Branch (B, lt, z, v, rt)) =
  balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
  | rbt_comp_del_from_right c x a y s Empty =
    Branch (R, a, y, s, rbt_comp_del c x Empty)
  | rbt_comp_del_from_right c x a y s (Branch (R, va, vb, vc, vd)) =
    Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));

fun rbt_comp_delete c k t = paint B (rbt_comp_del c k t);

fun delete A_ xb xc =
  Mapping_RBTa (rbt_comp_delete (the (ccompare A_)) xb (impl_ofa A_ xc));

fun list_remove1 equal x [] = []
  | list_remove1 equal x (y :: xs) =
    (if equal x y then xs else y :: list_remove1 equal x xs);

fun removea A_ xb xc =
  Abs_dlist (list_remove1 (the (ceq A_)) xb (list_of_dlist A_ xc));

fun insert (A1_, A2_) xa (Complement x) = Complement (remove (A1_, A2_) xa x)
  | insert (A1_, A2_) x (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "insert RBT_set: ccompare = None")
          (fn _ => insert (A1_, A2_) x (RBT_set rbt))
      | SOME _ => RBT_set (insertb A2_ x () rbt))
  | insert (A1_, A2_) x (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "insert DList_set: ceq = None")
          (fn _ => insert (A1_, A2_) x (DList_set dxs))
      | SOME _ => DList_set (inserta A1_ x dxs))
  | insert (A1_, A2_) x (Set_Monad xs) = Set_Monad (x :: xs)
  | insert (A1_, A2_) x (Collect_set a) =
    (case ceq A1_
      of NONE =>
        (raise Fail "insert Collect_set: ceq = None")
          (fn _ => insert (A1_, A2_) x (Collect_set a))
      | SOME eq => Collect_set (fun_upda eq a x true))
and remove (A1_, A2_) x (Complement a) = Complement (insert (A1_, A2_) x a)
  | remove (A1_, A2_) x (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "remove RBT_set: ccompare = None")
          (fn _ => remove (A1_, A2_) x (RBT_set rbt))
      | SOME _ => RBT_set (delete A2_ x rbt))
  | remove (A1_, A2_) x (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "remove DList_set: ceq = None")
          (fn _ => remove (A1_, A2_) x (DList_set dxs))
      | SOME _ => DList_set (removea A1_ x dxs))
  | remove (A1_, A2_) x (Collect_set a) =
    (case ceq A1_
      of NONE =>
        (raise Fail "remove Collect: ceq = None")
          (fn _ => remove (A1_, A2_) x (Collect_set a))
      | SOME eq => Collect_set (fun_upda eq a x false));

fun image (A1_, A2_) (B1_, B2_, B3_) h (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "image RBT_set: ccompare = None")
        (fn _ => image (A1_, A2_) (B1_, B2_, B3_) h (RBT_set rbt))
    | SOME _ => foldb A2_ (insert (B1_, B2_) o h) rbt (bot_set (B1_, B2_, B3_)))
  | image (A1_, A2_) (B1_, B2_, B3_) g (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "image DList_set: ceq = None")
          (fn _ => image (A1_, A2_) (B1_, B2_, B3_) g (DList_set dxs))
      | SOME _ =>
        foldc A1_ (insert (B1_, B2_) o g) dxs (bot_set (B1_, B2_, B3_)))
  | image (A1_, A2_) (B1_, B2_, B3_) f (Complement (Complement b)) =
    image (A1_, A2_) (B1_, B2_, B3_) f b
  | image (A1_, A2_) (B1_, B2_, B3_) f (Collect_set a) =
    (raise Fail "image Collect_set")
      (fn _ => image (A1_, A2_) (B1_, B2_, B3_) f (Collect_set a))
  | image (A1_, A2_) (B1_, B2_, B3_) f (Set_Monad xs) = Set_Monad (map f xs);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map_of A_ [] k = NONE
  | map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k);

fun memberc A_ xa = list_member (the (ceq A_)) (list_of_dlist A_ xa);

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun rbt_comp_lookup c Empty k = NONE
  | rbt_comp_lookup c (Branch (uu, l, x, y, r)) k =
    (case c k x of Eq => SOME y | Lt => rbt_comp_lookup c l k
      | Gt => rbt_comp_lookup c r k);

fun lookupb A_ xa = rbt_comp_lookup (the (ccompare A_)) (impl_ofa A_ xa);

fun memberb A_ t x = equal_option equal_unit (lookupb A_ t x) (SOME ());

fun member (A1_, A2_) x (Set_Monad xs) =
  (case ceq A1_
    of NONE =>
      (raise Fail "member Set_Monad: ceq = None")
        (fn _ => member (A1_, A2_) x (Set_Monad xs))
    | SOME eq => list_member eq xs x)
  | member (A1_, A2_) xa (Complement x) = not (member (A1_, A2_) xa x)
  | member (A1_, A2_) x (RBT_set rbt) = memberb A2_ rbt x
  | member (A1_, A2_) x (DList_set dxs) = memberc A1_ dxs x
  | member (A1_, A2_) x (Collect_set a) = a x;

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun collect A_ p =
  (case cEnum A_ of NONE => Collect_set p
    | SOME (enum, _) => Set_Monad (filter p enum));

fun fst (x1, x2) = x1;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

val empty : ('a, 'b) alist = Alist [];

fun impl_of (Alist x) = x;

fun lookup A_ xa = map_of A_ (impl_of xa);

fun updatea A_ xc xd xe = Alist (update A_ xc xd (impl_of xe));

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (membera A_ xs x) andalso distinct A_ xs;

fun set_aux (A1_, A2_) Set_Monada = Set_Monad
  | set_aux (A1_, A2_) Set_Choose =
    (case ccompare A2_
      of NONE =>
        (case ceq A1_ of NONE => Set_Monad
          | SOME _ =>
            foldl (fn s => fn x => insert (A1_, A2_) x s)
              (DList_set (emptyb A1_)))
      | SOME _ =>
        foldl (fn s => fn x => insert (A1_, A2_) x s) (RBT_set (emptyc A2_)))
  | set_aux (A1_, A2_) impl =
    foldl (fn s => fn x => insert (A1_, A2_) x s) (set_empty (A1_, A2_) impl);

fun set (A1_, A2_, A3_) xs = set_aux (A1_, A2_) (of_phantom (set_impl A3_)) xs;

fun mapping_empty_choose A_ =
  (case ccompare A_ of NONE => Assoc_List_Mapping empty
    | SOME _ => RBT_Mapping (emptyc A_));

fun mapping_empty A_ Mapping_RBT = RBT_Mapping (emptyc A_)
  | mapping_empty A_ Mapping_Assoc_List = Assoc_List_Mapping empty
  | mapping_empty A_ Mapping_Mapping = Mapping (fn _ => NONE)
  | mapping_empty A_ Mapping_Choose = mapping_empty_choose A_;

fun emptya (A1_, A2_) = mapping_empty A1_ (of_phantom (mapping_impl A2_));

fun bigOr [] = Bot
  | bigOr (f :: fs) = Or (f, bigOr fs);

fun lookupa (A1_, A2_) (RBT_Mapping t) = lookupb A1_ t
  | lookupa (A1_, A2_) (Assoc_List_Mapping al) = lookup A2_ al;

fun updateb (A1_, A2_) k v (RBT_Mapping t) =
  (case ccompare A1_
    of NONE =>
      (raise Fail "update RBT_Mapping: ccompare = None")
        (fn _ => updateb (A1_, A2_) k v (RBT_Mapping t))
    | SOME _ => RBT_Mapping (insertb A1_ k v t))
  | updateb (A1_, A2_) k v (Assoc_List_Mapping al) =
    Assoc_List_Mapping (updatea A2_ k v al)
  | updateb (A1_, A2_) k v (Mapping m) = Mapping (fun_upd A2_ m k (SOME v));

fun is_none NONE = true
  | is_none (SOME x) = false;

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun bigAnd [] = Not Bot
  | bigAnd (f :: fs) = And (f, bigAnd fs);

fun default (A1_, A2_) k v m =
  (if not (is_none (lookupa (A1_, A2_) m k)) then m
    else updateb (A1_, A2_) k v m);

fun bind m f = (case m of Inl a => Inl a | Inr a => f a);

fun of_alist (A1_, A2_, A3_) xs =
  foldr (fn (a, b) => updateb (A1_, A2_) a b) xs (emptya (A1_, A3_));

fun rbt_init x = ([], x);

fun check b e = (if b then Inr () else Inl e);

fun map_entry (A1_, A2_) k f m =
  (case lookupa (A1_, A2_) m k of NONE => m
    | SOME v => updateb (A1_, A2_) k (f v) m);

fun init A_ xa = rbt_init (impl_ofa A_ xa);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun apsnd f (x, y) = (x, f y);

fun dlist_all A_ x xc = list_all x (list_of_dlist A_ xc);

fun catch_error m f = (case m of Inl a => f a | Inr a => Inr a);

fun forallM f [] = Inr ()
  | forallM f (x :: xs) =
    bind (catch_error (f x) (fn xa => Inl (x, xa))) (fn _ => forallM f xs);

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

fun map_default (A1_, A2_) k v f m =
  map_entry (A1_, A2_) k f (default (A1_, A2_) k v m);

fun rbt_has_next ([], Empty) = false
  | rbt_has_next (vb :: vc, va) = true
  | rbt_has_next (v, Branch (vb, vc, vd, ve, vf)) = true;

fun generator (Generator x) = x;

fun snd (x1, x2) = x2;

fun next g = snd (generator g);

fun rbt_keys_next ((k, t) :: kts, Empty) = (k, (kts, t))
  | rbt_keys_next (kts, Branch (c, l, k, v, r)) =
    rbt_keys_next ((k, r) :: kts, l);

fun lookup_default (B1_, B2_) d m k =
  (case lookupa (B1_, B2_) m k of NONE => d | SOME v => v);

fun formula_semantics a (Atom k) = a k
  | formula_semantics uu Bot = false
  | formula_semantics a (Not f) = not (formula_semantics a f)
  | formula_semantics a (And (f, g)) =
    formula_semantics a f andalso formula_semantics a g
  | formula_semantics a (Or (f, g)) =
    formula_semantics a f orelse formula_semantics a g
  | formula_semantics a (Imp (f, g)) =
    (if formula_semantics a f then formula_semantics a g else true);

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val (_, a) = bit_cut_integer q6;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, a)
                        end;

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun lift_opt m e = (case m of NONE => Inl e | SOME a => Inr a);

val one_nat : nat = Nat (1 : IntInf.int);

fun has_next g = fst (generator g);

fun integer_of_nat (Nat x) = x;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun string_of_digit n =
  (if equal_nat n zero_nat
    then [Chara (false, false, false, false, true, true, false, false)]
    else (if equal_nat n one_nat
           then [Chara (true, false, false, false, true, true, false, false)]
           else (if equal_nat n (nat_of_integer (2 : IntInf.int))
                  then [Chara (false, true, false, false, true, true, false,
                                false)]
                  else (if equal_nat n (nat_of_integer (3 : IntInf.int))
                         then [Chara (true, true, false, false, true, true,
                                       false, false)]
                         else (if equal_nat n (nat_of_integer (4 : IntInf.int))
                                then [Chara
(false, false, true, false, true, true, false, false)]
                                else (if equal_nat n
   (nat_of_integer (5 : IntInf.int))
                                       then [Chara
       (true, false, true, false, true, true, false, false)]
                                       else (if equal_nat n
          (nat_of_integer (6 : IntInf.int))
      then [Chara (false, true, true, false, true, true, false, false)]
      else (if equal_nat n (nat_of_integer (7 : IntInf.int))
             then [Chara (true, true, true, false, true, true, false, false)]
             else (if equal_nat n (nat_of_integer (8 : IntInf.int))
                    then [Chara (false, false, false, true, true, true, false,
                                  false)]
                    else [Chara (true, false, false, true, true, true, false,
                                  false)])))))))));

fun showsp_nat p n =
  (if less_nat n (nat_of_integer (10 : IntInf.int))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 : IntInf.int))) o
           shows_string
             (string_of_digit
               (modulo_nat n (nat_of_integer (10 : IntInf.int)))));

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val rbt_keys_generator :
  ('a, (('a * ('a, 'b) rbt) list * ('a, 'b) rbt)) generator
  = Generator (rbt_has_next, rbt_keys_next);

fun list_all_fusion g p s =
  (if has_next g s then let
                          val (x, sa) = next g s;
                        in
                          p x andalso list_all_fusion g p sa
                        end
    else true);

fun map_formula f (Atom x1) = Atom (f x1)
  | map_formula f Bot = Bot
  | map_formula f (Not x3) = Not (map_formula f x3)
  | map_formula f (And (x41, x42)) = And (map_formula f x41, map_formula f x42)
  | map_formula f (Or (x51, x52)) = Or (map_formula f x51, map_formula f x52)
  | map_formula f (Imp (x61, x62)) = Imp (map_formula f x61, map_formula f x62);

fun tab_succ (A1_, A2_, A3_) l =
  lookup_default (A1_, A2_) []
    (fold (fn (u, v) => map_default (A1_, A2_) u [] (fn a => v :: a)) l
      (emptya (A1_, A3_)));

fun ty_term varT objT (VAR v) = varT v
  | ty_term varT objT (CONST c) =
    lookupa (ccompare_object, equal_object) objT c;

fun equal_order Lt Gt = false
  | equal_order Gt Lt = false
  | equal_order Eq Gt = false
  | equal_order Gt Eq = false
  | equal_order Eq Lt = false
  | equal_order Lt Eq = false
  | equal_order Gt Gt = true
  | equal_order Lt Lt = true
  | equal_order Eq Eq = true;

fun sorted_list_subset_fusion less eq g1 g2 s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           has_next g2 s2 andalso
             let
               val (y, s2a) = next g2 s2;
             in
               (if eq x y then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                 else less y x andalso
                        sorted_list_subset_fusion less eq g1 g2 s1 s2a)
             end
         end
    else true);

fun less_eq_set (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A3_
    of NONE =>
      (raise Fail "subset RBT_set RBT_set: ccompare = None")
        (fn _ => less_eq_set (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2))
    | SOME c =>
      (case ceq A2_
        of NONE =>
          sorted_list_subset_fusion (lt_of_comp c)
            (fn x => fn y => equal_order (c x y) Eq) rbt_keys_generator
            rbt_keys_generator (init A3_ rbt1) (init A3_ rbt2)
        | SOME eq =>
          sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
            rbt_keys_generator (init A3_ rbt1) (init A3_ rbt2)))
  | less_eq_set (A1_, A2_, A3_) (Complement a1) (Complement a2) =
    less_eq_set (A1_, A2_, A3_) a2 a1
  | less_eq_set (A1_, A2_, A3_) (Collect_set p) (Complement a) =
    less_eq_set (A1_, A2_, A3_) a (collect A1_ (fn x => not (p x)))
  | less_eq_set (A1_, A2_, A3_) (RBT_set rbt) b =
    (case ccompare A3_
      of NONE =>
        (raise Fail "subset RBT_set1: ccompare = None")
          (fn _ => less_eq_set (A1_, A2_, A3_) (RBT_set rbt) b)
      | SOME _ =>
        list_all_fusion rbt_keys_generator (fn x => member (A2_, A3_) x b)
          (init A3_ rbt))
  | less_eq_set (A1_, A2_, A3_) (DList_set dxs) c =
    (case ceq A2_
      of NONE =>
        (raise Fail "subset DList_set1: ceq = None")
          (fn _ => less_eq_set (A1_, A2_, A3_) (DList_set dxs) c)
      | SOME _ => dlist_all A2_ (fn x => member (A2_, A3_) x c) dxs)
  | less_eq_set (A1_, A2_, A3_) (Set_Monad xs) c =
    list_all (fn x => member (A2_, A3_) x c) xs;

fun quicksort_acc A_ ac [] = ac
  | quicksort_acc A_ ac [x] = x :: ac
  | quicksort_acc A_ ac (x :: v :: va) =
    quicksort_part A_ ac x [] [] [] (v :: va)
and quicksort_part A_ ac x lts eqs gts [] =
  quicksort_acc A_ (eqs @ x :: quicksort_acc A_ ac gts) lts
  | quicksort_part A_ ac x lts eqs gts (z :: zs) =
    (if less A_ x z then quicksort_part A_ ac x lts eqs (z :: gts) zs
      else (if less A_ z x then quicksort_part A_ ac x (z :: lts) eqs gts zs
             else quicksort_part A_ ac x lts (z :: eqs) gts zs));

fun quicksort A_ = quicksort_acc A_ [];

fun shows_prec_nat x = showsp_nat x;

fun map_atom f (PredAtm (x11, x12)) = PredAtm (x11, map f x12)
  | map_atom f (Eqa (x21, x22)) = Eqa (f x21, f x22);

fun map_ast_effect f (Effect (x1, x2)) =
  Effect (map (map_formula (map_atom f)) x1, map (map_formula (map_atom f)) x2);

fun subst_term psubst (VAR x) = psubst x
  | subst_term psubst (CONST c) = c;

fun instantiate_action_schema (Action_Schema (n, params, pre, eff)) args =
  let
    val tsubst =
      subst_term (the o map_of equal_variable (zip (map fst params) args));
    val pre_inst = (map_formula o map_atom) tsubst pre;
    val a = map_ast_effect tsubst eff;
  in
    Ground_Action (pre_inst, a)
  end;

fun namea (Action_Schema (x1, x2, x3, x4)) = x1;

fun actions (Domain (x1, x2, x3, x4)) = x4;

fun index_by B_ f l = map_of B_ (map (fn x => (f x, x)) l);

fun resolve_action_schema d n =
  index_by (equal_list equal_char) namea (actions d) n;

fun resolve_action_schemaE d n =
  lift_opt (resolve_action_schema d n)
    (fn _ =>
      shows_prec_list show_char zero_nat
        [Chara (false, true, true, true, false, false, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, true, true, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false)] o
        shows_prec_list show_char zero_nat n);

fun primitives (Either x) = x;

fun dfs_reachable (A1_, A2_, A3_) succ d w =
  let
    val (_, (_, brk)) =
      whilea (fn (_, (wa, brk)) => not brk andalso not (null wa))
        (fn (v, (va :: wa, _)) =>
          (if d va then (v, (va :: wa, true))
            else (if member (A1_, A2_) va v then (v, (wa, false))
                   else let
                          val vb = insert (A1_, A2_) va v;
                          val wb = succ va @ wa;
                        in
                          (vb, (wb, false))
                        end)))
        (bot_set (A1_, A2_, A3_), (w, false));
  in
    brk
  end;

fun of_type_impl g oT t =
  list_all
    (fn pt =>
      dfs_reachable
        (ceq_list ceq_char, ccompare_list ccompare_char, set_impl_list) g
        (equal_lista equal_char pt) (primitives t))
    (primitives oT);

fun is_obj_of_type_impl (A1_, A2_) stg mp n t =
  (case lookupa (A1_, A2_) mp n of NONE => false
    | SOME oT => of_type_impl stg oT t);

fun parameters (Action_Schema (x1, x2, x3, x4)) = x2;

fun precondition (Ground_Action (x1, x2)) = x1;

fun apply_effect (Effect (a, d)) s =
  fold (insert
         (ceq_formula (ceq_atom ceq_object),
           ccompare_formula (ccompare_atom ccompare_object)))
    a (fold (remove
              (ceq_formula (ceq_atom ceq_object),
                ccompare_formula (ccompare_atom ccompare_object)))
        d s);

fun effect (Ground_Action (x1, x2)) = x2;

fun domain (Problem (x1, x2, x3, x4)) = x1;

fun valuation m =
  (fn a =>
    (case a
      of PredAtm (p, xs) =>
        member
          (ceq_formula (ceq_atom ceq_object),
            ccompare_formula (ccompare_atom ccompare_object))
          (Atom (PredAtm (p, xs))) m
      | Eqa (aa, b) => equal_objecta aa b));

fun holds m f = formula_semantics (valuation m) f;

fun en_exE2 p g mp =
  (fn PAction (n, args) => fn m =>
    bind (resolve_action_schemaE (domain p) n)
      (fn a =>
        bind (check
               (list_all2
                 (is_obj_of_type_impl (ccompare_object, equal_object) g mp) args
                 (map snd (parameters a)))
               (fn _ =>
                 shows_prec_list show_char zero_nat
                   [Chara (false, false, false, false, true, false, true,
                            false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, false, true, false, true, true,
                             false)]))
          (fn _ =>
            let
              val ai = instantiate_action_schema a args;
            in
              bind (check (holds m (precondition ai))
                     (fn _ =>
                       shows_prec_list show_char zero_nat
                         [Chara (false, false, false, false, true, false, true,
                                  false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (false, false, true, false, false, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (true, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, true, true, true,
                                   false),
                           Chara (false, true, true, false, false, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, false, true, true,
                                   false)]))
                (fn _ => Inr (apply_effect (effect ai) m))
            end)));

fun goal (Problem (x1, x2, x3, x4)) = x4;

fun valid_plan_fromE p stg mp si s [] =
  check (holds s (goal p))
    (fn _ =>
      shows_prec_list show_char zero_nat
        [Chara (false, false, false, false, true, false, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false)])
  | valid_plan_fromE p stg mp si s (pi :: pi_s) =
    bind (catch_error (en_exE2 p stg mp pi s)
           (fn x =>
             Inl (fn _ =>
                   shows_prec_list show_char zero_nat
                     [Chara (true, false, false, false, false, true, true,
                              false),
                       Chara (false, false, true, false, true, true, true,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false),
                       Chara (true, true, false, false, true, true, true,
                               false),
                       Chara (false, false, true, false, true, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (false, false, false, false, true, true, true,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false)] o
                     shows_prec_nat zero_nat si o
                     shows_prec_list show_char zero_nat
                       [Chara (false, true, false, true, true, true, false,
                                false),
                         Chara (false, false, false, false, false, true, false,
                                 false)] o
                     x ())))
      (fn sa => valid_plan_fromE p stg mp (plus_nat si one_nat) sa pi_s);

fun consts (Domain (x1, x2, x3, x4)) = x3;

fun mp_constT d =
  of_alist (ccompare_object, equal_object, mapping_impl_object) (consts d);

fun objects (Problem (x1, x2, x3, x4)) = x2;

fun mp_objT p =
  of_alist (ccompare_object, equal_object, mapping_impl_object)
    (consts (domain p) @ objects p);

fun is_of_type ty_ent stg v t =
  (case ty_ent v of NONE => false | SOME vT => of_type_impl stg vT t);

fun predicates (Domain (x1, x2, x3, x4)) = x2;

fun siga d =
  map_of equal_predicate (map (fn PredDecl (a, b) => (a, b)) (predicates d));

fun wf_pred_atom d ty_ent stg (p, vs) =
  (case siga d p of NONE => false
    | SOME a => list_all2 (is_of_type ty_ent stg) vs a);

fun wf_fact p ot stg =
  wf_pred_atom (domain p) (lookupa (ccompare_object, equal_object) ot) stg;

fun wf_fmla_atom2 p mp stg f =
  (case f of Atom (PredAtm (pa, vs)) => wf_fact p mp stg (pa, vs)
    | Atom (Eqa (_, _)) => false | Bot => false | Not _ => false
    | And (_, _) => false | Or (_, _) => false | Imp (_, _) => false);

fun types (Domain (x1, x2, x3, x4)) = x1;

fun wf_type d (Either ts) =
  less_eq_set (cenum_list, ceq_list ceq_char, ccompare_list ccompare_char)
    (set (ceq_list ceq_char, ccompare_list ccompare_char, set_impl_list) ts)
    (insert (ceq_list ceq_char, ccompare_list ccompare_char)
      [Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (false, true, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false)]
      (image
        (ceq_prod (ceq_list ceq_char) (ceq_list ceq_char),
          ccompare_prod (ccompare_list ccompare_char)
            (ccompare_list ccompare_char))
        (ceq_list ceq_char, ccompare_list ccompare_char, set_impl_list) fst
        (set (ceq_prod (ceq_list ceq_char) (ceq_list ceq_char),
               ccompare_prod (ccompare_list ccompare_char)
                 (ccompare_list ccompare_char),
               set_impl_prod set_impl_list set_impl_list)
          (types d))));

fun wf_atom d ty_ent stg (PredAtm (p, vs)) = wf_pred_atom d ty_ent stg (p, vs)
  | wf_atom d ty_ent stg (Eqa (a, b)) =
    not (is_none (ty_ent a)) andalso not (is_none (ty_ent b));

fun wf_fmla d ty_ent stg (Atom a) = wf_atom d ty_ent stg a
  | wf_fmla d ty_ent stg Bot = true
  | wf_fmla d ty_ent stg (And (phi_1, phi_2)) =
    wf_fmla d ty_ent stg phi_1 andalso wf_fmla d ty_ent stg phi_2
  | wf_fmla d ty_ent stg (Or (phi_1, phi_2)) =
    wf_fmla d ty_ent stg phi_1 andalso wf_fmla d ty_ent stg phi_2
  | wf_fmla d ty_ent stg (Imp (phi_1, phi_2)) =
    wf_fmla d ty_ent stg phi_1 andalso wf_fmla d ty_ent stg phi_2
  | wf_fmla d ty_ent stg (Not phi) = wf_fmla d ty_ent stg phi;

fun inita (Problem (x1, x2, x3, x4)) = x3;

fun prepend_err_msg A_ msg e =
  (fn _ =>
    shows_prec A_ zero_nat msg o
      shows_prec_list show_char zero_nat
        [Chara (false, true, false, true, true, true, false, false),
          Chara (false, false, false, false, false, true, false, false)] o
      e ());

fun wf_predicate_decl d (PredDecl (p, ts)) = list_all (wf_type d) ts;

fun wf_fmla_atom1 d ty_ent stg (Atom (PredAtm (p, vs))) =
  wf_pred_atom d ty_ent stg (p, vs)
  | wf_fmla_atom1 d ty_ent stg (Atom (Eqa (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg Bot = false
  | wf_fmla_atom1 d ty_ent stg (Not v) = false
  | wf_fmla_atom1 d ty_ent stg (And (v, va)) = false
  | wf_fmla_atom1 d ty_ent stg (Or (v, va)) = false
  | wf_fmla_atom1 d ty_ent stg (Imp (v, va)) = false;

fun wf_effect da ty_ent stg (Effect (a, d)) =
  list_all (wf_fmla_atom1 da ty_ent stg) a andalso
    list_all (wf_fmla_atom1 da ty_ent stg) d;

fun wf_action_schema d stg conT (Action_Schema (n, params, pre, eff)) =
  let
    val tyv = ty_term (map_of equal_variable params) conT;
  in
    distinct equal_variable (map fst params) andalso
      (wf_fmla d tyv stg pre andalso wf_effect d tyv stg eff)
  end;

fun pred (PredDecl (x1, x2)) = x1;

fun name (Pred x) = x;

fun check_all_list B_ p l msg msgf =
  catch_error
    (forallM
      (fn x =>
        check (p x)
          (fn _ =>
            shows_prec B_ zero_nat msg o
              shows_prec_list show_char zero_nat
                [Chara (false, true, false, true, true, true, false, false),
                  Chara (false, false, false, false, false, true, false,
                          false)] o
              msgf x))
      l)
    (fn x => Inl (snd x));

fun check_wf_types d =
  check_all_list (show_list show_char)
    (fn (_, t) =>
      equal_lista equal_char t
        [Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (false, true, false, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false)] orelse
        member (ceq_list ceq_char, ccompare_list ccompare_char) t
          (image
            (ceq_prod (ceq_list ceq_char) (ceq_list ceq_char),
              ccompare_prod (ccompare_list ccompare_char)
                (ccompare_list ccompare_char))
            (ceq_list ceq_char, ccompare_list ccompare_char, set_impl_list) fst
            (set (ceq_prod (ceq_list ceq_char) (ceq_list ceq_char),
                   ccompare_prod (ccompare_list ccompare_char)
                     (ccompare_list ccompare_char),
                   set_impl_prod set_impl_list set_impl_list)
              (types d))))
    (types d)
    [Chara (true, false, true, false, true, false, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false)]
    (shows_prec_list show_char zero_nat o snd);

fun no_stutter A_ [] = true
  | no_stutter A_ [uu] = true
  | no_stutter A_ (a :: b :: l) =
    not (eq A_ a b) andalso no_stutter A_ (b :: l);

fun distinct_ds (A1_, A2_) l =
  no_stutter A1_
    (quicksort ((ord_preorder o preorder_order o order_linorder) A2_) l);

fun check_wf_domain d stg conT =
  bind (check_wf_types d)
    (fn _ =>
      bind (check
             (distinct_ds (equal_predicate, linorder_predicate)
               (map pred (predicates d)))
             (fn _ =>
               shows_prec_list show_char zero_nat
                 [Chara (false, false, true, false, false, false, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false)]))
        (fn _ =>
          bind (check_all_list (show_list show_char) (wf_predicate_decl d)
                 (predicates d)
                 [Chara (true, false, true, true, false, false, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, true, true, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, true, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false)]
                 (shows_prec_list show_char zero_nat o name o pred))
            (fn _ =>
              bind (check
                     (distinct_ds (equal_object, linorder_object)
                       (map fst (consts d)))
                     (fn _ =>
                       shows_prec_list show_char zero_nat
                         [Chara (false, false, true, false, false, false, true,
                                  false),
                           Chara (true, false, true, false, true, true, true,
                                   false),
                           Chara (false, false, false, false, true, true, true,
                                   false),
                           Chara (false, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, true, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (false, false, true, false, false, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false)]))
                (fn _ =>
                  bind (check (list_all (fn (_, a) => wf_type d a) (consts d))
                         (fn _ =>
                           shows_prec_list show_char zero_nat
                             [Chara (true, false, true, true, false, false,
                                      true, false),
                               Chara (true, false, false, false, false, true,
                                       true, false),
                               Chara (false, false, true, true, false, true,
                                       true, false),
                               Chara (false, true, true, false, false, true,
                                       true, false),
                               Chara (true, true, true, true, false, true, true,
                                       false),
                               Chara (false, true, false, false, true, true,
                                       true, false),
                               Chara (true, false, true, true, false, true,
                                       true, false),
                               Chara (true, false, true, false, false, true,
                                       true, false),
                               Chara (false, false, true, false, false, true,
                                       true, false),
                               Chara (false, false, false, false, false, true,
                                       false, false),
                               Chara (false, false, true, false, true, true,
                                       true, false),
                               Chara (true, false, false, true, true, true,
                                       true, false),
                               Chara (false, false, false, false, true, true,
                                       true, false),
                               Chara (true, false, true, false, false, true,
                                       true, false)]))
                    (fn _ =>
                      bind (check
                             (distinct (equal_list equal_char)
                               (map namea (actions d)))
                             (fn _ =>
                               shows_prec_list show_char zero_nat
                                 [Chara (false, false, true, false, false,
  false, true, false),
                                   Chara (true, false, true, false, true, true,
   true, false),
                                   Chara (false, false, false, false, true,
   true, true, false),
                                   Chara (false, false, true, true, false, true,
   true, false),
                                   Chara (true, false, false, true, false, true,
   true, false),
                                   Chara (true, true, false, false, false, true,
   true, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (false, false, true, false, true, true,
   true, false),
                                   Chara (true, false, true, false, false, true,
   true, false),
                                   Chara (false, false, false, false, false,
   true, false, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (true, true, false, false, false, true,
   true, false),
                                   Chara (false, false, true, false, true, true,
   true, false),
                                   Chara (true, false, false, true, false, true,
   true, false),
                                   Chara (true, true, true, true, false, true,
   true, false),
                                   Chara (false, true, true, true, false, true,
   true, false),
                                   Chara (false, false, false, false, false,
   true, false, false),
                                   Chara (false, true, true, true, false, true,
   true, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (true, false, true, true, false, true,
   true, false),
                                   Chara (true, false, true, false, false, true,
   true, false)]))
                        (fn _ =>
                          check_all_list (show_list show_char)
                            (wf_action_schema d stg conT) (actions d)
                            [Chara (true, false, true, true, false, false, true,
                                     false),
                              Chara (true, false, false, false, false, true,
                                      true, false),
                              Chara (false, false, true, true, false, true,
                                      true, false),
                              Chara (false, true, true, false, false, true,
                                      true, false),
                              Chara (true, true, true, true, false, true, true,
                                      false),
                              Chara (false, true, false, false, true, true,
                                      true, false),
                              Chara (true, false, true, true, false, true, true,
                                      false),
                              Chara (true, false, true, false, false, true,
                                      true, false),
                              Chara (false, false, true, false, false, true,
                                      true, false),
                              Chara (false, false, false, false, false, true,
                                      false, false),
                              Chara (true, false, false, false, false, true,
                                      true, false),
                              Chara (true, true, false, false, false, true,
                                      true, false),
                              Chara (false, false, true, false, true, true,
                                      true, false),
                              Chara (true, false, false, true, false, true,
                                      true, false),
                              Chara (true, true, true, true, false, true, true,
                                      false),
                              Chara (false, true, true, true, false, true, true,
                                      false)]
                            (shows_prec_list show_char zero_nat o namea)))))));

fun check_wf_problem p stg conT mp =
  let
    val d = domain p;
  in
    bind (catch_error (check_wf_domain d stg conT)
           (fn x =>
             Inl (prepend_err_msg (show_list show_char)
                   [Chara (false, false, true, false, false, false, true,
                            false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, true, true, false, true, false, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false)]
                   x)))
      (fn _ =>
        bind (check
               (distinct_ds (equal_object, linorder_object)
                 (map fst (objects p) @ map fst (consts d)))
               (fn _ =>
                 shows_prec_list show_char zero_nat
                   [Chara (false, false, true, false, false, false, true,
                            false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, false, true, true,
                             false),
                     Chara (false, true, false, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true,
                             false)]))
          (fn _ =>
            bind (check (list_all (fn (_, a) => wf_type d a) (objects p))
                   (fn _ =>
                     shows_prec_list show_char zero_nat
                       [Chara (true, false, true, true, false, false, true,
                                false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false)]))
              (fn _ =>
                bind (check
                       (distinct_ds
                         (equal_formula (equal_atom equal_object),
                           linorder_formula
                             (equal_atom equal_object,
                               linorder_atom (equal_object, linorder_object)))
                         (inita p))
                       (fn _ =>
                         shows_prec_list show_char zero_nat
                           [Chara (false, false, true, false, false, false,
                                    true, false),
                             Chara (true, false, true, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, true, true,
                                     true, false),
                             Chara (false, false, true, true, false, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, true, false, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (false, true, true, false, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, true, false, false, true, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, true, false, false, true, true,
                                     false)]))
                  (fn _ =>
                    bind (check (list_all (wf_fmla_atom2 p mp stg) (inita p))
                           (fn _ =>
                             shows_prec_list show_char zero_nat
                               [Chara (true, false, true, true, false, false,
true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, true, false, true,
 true, false),
                                 Chara (false, true, true, false, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false),
                                 Chara (true, false, true, true, false, true,
 true, false),
                                 Chara (true, false, true, false, false, true,
 true, false),
                                 Chara (false, false, true, false, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (false, true, true, false, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false),
                                 Chara (true, false, true, true, false, true,
 true, false),
                                 Chara (true, false, true, false, true, true,
 true, false),
                                 Chara (false, false, true, true, false, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, true, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, true, false, false, true, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, true, false, false, true,
 true, false)]))
                      (fn _ =>
                        check (wf_fmla d
                                (lookupa (ccompare_object, equal_object) mp) stg
                                (goal p))
                          (fn _ =>
                            shows_prec_list show_char zero_nat
                              [Chara (true, false, true, true, false, false,
                                       true, false),
                                Chara (true, false, false, false, false, true,
true, false),
                                Chara (false, false, true, true, false, true,
true, false),
                                Chara (false, true, true, false, false, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, false, true, true, false, true,
true, false),
                                Chara (true, false, true, false, false, true,
true, false),
                                Chara (false, false, true, false, false, true,
true, false),
                                Chara (false, false, false, false, false, true,
false, false),
                                Chara (true, true, true, false, false, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (true, false, false, false, false, true,
true, false),
                                Chara (false, false, true, true, false, true,
true, false),
                                Chara (false, false, false, false, false, true,
false, false),
                                Chara (false, true, true, false, false, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, false, true, true, false, true,
true, false),
                                Chara (true, false, true, false, true, true,
true, false),
                                Chara (false, false, true, true, false, true,
true, false),
                                Chara (true, false, false, false, false, true,
true, false)]))))))
  end;

fun i p =
  set (ceq_formula (ceq_atom ceq_object),
        ccompare_formula (ccompare_atom ccompare_object), set_impl_formula)
    (inita p);

fun subtype_edge (ty, superty) = (superty, ty);

fun stg d =
  tab_succ
    (ccompare_list ccompare_char, equal_list equal_char, mapping_impl_list)
    (map subtype_edge (types d));

fun check_plan p pi_s =
  catch_error
    let
      val stga = stg (domain p);
      val conT = mp_constT (domain p);
      val mp = mp_objT p;
    in
      bind (check_wf_problem p stga conT mp)
        (fn _ => valid_plan_fromE p stga mp one_nat (i p) pi_s)
    end
    (fn x => Inl (implode (x () [])));

fun predicate (PredAtm (x11, x12)) = x11;

end; (*struct PDDL_Checker_Exported*)
