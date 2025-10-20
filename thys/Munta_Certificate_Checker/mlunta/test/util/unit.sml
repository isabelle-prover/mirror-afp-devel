(* A simple unit testing utility *)
infix 4 >+
infix 5 >++
signature SML_UNIT = sig
  type test_fun = unit -> unit
  val json_file_to_string: string -> string
  datatype test =
           TestCase of test_fun |
           TestLabel of string * test |
           TestSuite of test list

  val assert_true: bool -> test_fun
  val assert_equal: ''a -> ''a -> test_fun
  val assert_exception: ('a -> 'b) -> exn -> 'a -> test_fun
  val assert_cmp: ('a -> 'b -> bool) -> 'a -> 'b -> test_fun
  val assert_cmp_res: ('a -> 'b -> bool) -> 'a -> 'b -> string ->
                      string -> test_fun
  (* val todo: string -> unit *)
  (* val single_test: string -> test_fun -> test *)
  (* val test_list: string -> test list -> test *)
  val >+ : string * test_fun -> test
  val >++ : string * test list -> test
  val run_test: test -> unit
  val first_do: string -> bool -> test -> unit
end

structure SMLUnit : SML_UNIT = struct
type test_fun = unit -> unit
datatype test =
         TestCase of test_fun |
         TestLabel of string * test |
         TestSuite of test list

fun json_file_to_string file =
    let
      val stream = TextIO.openIn file
      fun all input =
          case TextIO.inputLine input of
              SOME line => (String.explode line |> filter (fn #"\n" => false | _ => true) |> String.implode) ^ all input |
              NONE => ""
      val str = all stream
    in
      (TextIO.closeIn stream; str)
    end

fun error () = print "Failed XXX"
fun success () = print "Correct!"


fun assert_true x () = if x then success () else error ()
fun assert_true_res f x () = if x then success () else (error (); f ())
fun assert_false x () = if not x then success () else error ()
(* fun assert_raises f x = (f x; error ()) handle _ => success () *)
fun assert_exception f exn x () =
    (f x; error ()) handle exn => success ()
                                 handle _ => error ()
fun assert_equal x y =
    assert_true (x = y)

fun assert_cmp cmp x y =
    assert_true (cmp x y)
fun assert_cmp_res cmp x y str_is str_expected =
    assert_true_res (fn () => print ("is: " ^ str_is ^ "\n"
                                   ^ "expected: " ^ str_expected ^ "\n"))
                    (cmp x y)
fun test_case t = TestCase t
fun single_test name t = TestLabel (name, test_case t)
fun test_list name ts = TestLabel (name, TestSuite ts)


fun (name >+ t) = single_test name t
fun (name >++ ts) = test_list name ts

fun run_test t =
    case t of
        TestCase f => (f (); print "\n") |
        TestLabel (name, t) => (print ("Test " ^ name ^ ": "); run_test t) |
        TestSuite ts => (print "\n"; List.app run_test ts; print "\n")

fun first_do name pre ts =
    (
      print ("Before Tests " ^ name ^ ": ");
      if pre then (success (); print "\n"; run_test ts) else error ()
    )
(* fun after_do name post ts = TestCase (fn () => ts (); post) *)
end
