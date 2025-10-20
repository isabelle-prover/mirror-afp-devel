(* XXX:  Add cmp for parse_json_types since lists order does not matter*)
structure ParseJsonTATest : TESTSUITE = struct
open Either
open Error
open JsonError
open SMLUnit

val root = "test/resources/"
val test_names = ["simple.muntax", "fddi.muntax", "simple_fail.muntax"]
val test_paths = List.map (fn s => root ^ s) test_names
val test_handles = List.map (json_file_to_string) test_paths
val files_right = List.all (fn "" => false | _ => true) test_handles
val tests_parse = List.map (fn s => s |> JsonP.parse)

val test_inputs = tests_parse test_handles
fun parse_ta json = json |> Either.bindR ParseJson.net
val results = List.map parse_ta test_inputs

val expected = [
    Right
        {automata = rev
         [("TA1",
           {committed = [],
            edges =
            [{guard = "(x > 0) && (y < 2)", label = "", source = 5, target = 7,
              update = "x := 0"},
             {guard = "", label = "", source = 7, target = 6, update = ""},
             {guard = "", label = "", source = 6, target = 5,
              update = "y := 0, x := 0"}], initial = 5,
            nodes =
            [{id = 7, invar = "", name = "C"},
             {id = 6, invar = "", name = "B"},
             {id = 5, invar = "x <= 3", name = "A"}]}),
          ("TA2",
           {committed = [],
            edges =
            [{guard = "", label = "", source = 8, target = 9, update = ""},
             {guard = "", label = "", source = 9, target = 9, update = ""}],
            initial = 8,
            nodes =
            [ {id = 9, invar = "", name = "N"},
              {id = 8, invar = "", name = "M"}]})],
         broadcast_channels = [],
         clocks = "x, y", formula = "E<> TA1.C",
        vars = ""},

    Right
        {automata = rev
         [("RING",
           {committed = [],
            edges = rev
            [{guard = "x0 <= 0", label = "tt1!", source = 5, target = 6,
              update = ""},
             {guard = "", label = "rt1?", source = 6, target = 8,
              update = "x0 := 0"},
             {guard = "x0 <= 0", label = "tt2!", source = 8, target = 7,
              update = ""},
             {guard = "", label = "rt2?", source = 7, target = 5,
              update = "x0 := 0"}],
            initial = 5,
            nodes =
            [{id = 8, invar = "x0 <= 0", name = "ring_to_2"},
             {id = 7, invar = "", name = "ring_2"},
             {id = 6, invar = "", name = "ring_1"},
             {id = 5, invar = "", name = "ring_to_1"}]}),

          ("ST1",
           {committed = [],
            edges = rev
            [{guard = "x1 >= 20 && y1 >= 120", label = "rt1!", source = 9,
              target = 11, update = ""},
             {guard = "x1 >= 20 && y1 < 120", label = "", source = 11,
              target = 10, update = ""},
             {guard = "", label = "rt1!", source = 10, target = 9, update = ""},
             {guard = "", label = "tt1?", source = 14, target = 11,
              update = "z1 := 0, x1 := 0"},
             {guard = "", label = "rt1!", source = 13, target = 14, update = ""},
             {guard = "x1 >= 20 && y1 < 120", label = "", source = 12,
              target = 13, update = ""},
             {source = 12, target = 14, guard = "x1 >= 20 && z1 >= 120",
              label = "rt1!", update = ""},
             {source = 9,target = 12, guard = "", label = "tt1?",
              update = "y1 := 0, x1 := 0"}],
            initial = 9, nodes =
                         [{id = 14, invar = "", name = "y_idle"},
                          {id = 13, invar = "z1 <= 120", name = "z_async"},
                          {id = 12, invar = "x1 <= 20", name = "z_sync"},
                          {id = 11, invar = "x1 <= 20", name = "y_sync"},
                          {id = 10, invar = "y1 <= 120", name = "y_async"},
                          {id = 9, invar = "", name = "z_idle"}]}),
          ("ST2",
           {committed = [],
            edges = rev
            [{guard = "x2 >= 20 && y2 >= 120", label = "rt1!", source = 9,
              target = 11, update = ""},
             {guard = "x2 >= 20 && y2 < 120", label = "", source = 11,
              target = 10,
              update = ""},
             {guard = "", label = "rt1!", source = 10, target = 9, update = ""},
             {guard = "", label = "tt1?", source = 14, target = 11,
              update = "z2 := 0, x2 := 0"},
             {source = 13,target = 14,guard = "",label = "rt1!",update = ""},
             {source = 12,target = 13,guard = "x2 >= 20 && y2 < 120",label = "",
              update = ""},
             {source = 12,target = 14,guard = "x2 >= 20 && z2 >= 120",
              label = "rt1!", update = ""},
             {source = 9,target = 12,guard = "",label = "tt1?",
              update = "y2 := 0, x2 := 0"}],
            initial = 9, nodes =
                         [
                           {id = 14, invar = "", name = "y_idle"},
                           {id = 13, invar = "z2 <= 120", name = "z_async"},
                           {id = 12, invar = "x2 <= 20", name = "z_sync"},
                           {id = 11, invar = "x2 <= 20", name = "y_sync"},
                           {id = 10, invar = "y2 <= 120", name = "y_async"},
                           {id = 9, invar = "", name = "z_idle"}]})],
         broadcast_channels = [],
         clocks = "x0, x1, y1, z1, x2, y2, z2",
         vars = "id[-1:2]",
         formula =
         "E<> ((ST1.z_sync || ST1.z_async || ST1.y_sync || ST1.y_async)" ^
         "  && (ST2.z_sync || ST2.z_async || ST2.y_sync || ST2.y_async)  )"
        },
    Left
        [JsonError (NotInObject "clocks"), JsonError (NotInObject "vars"),
         JsonError (NotInObject "formula"), JsonError (NotInObject "name"),
         JsonError (NotInObject "target")]
]

fun check_files () =
    (if files_right
     then
         (* let *)
         (*     val res = tests_parse test_handles *)
         (* in (List.app *)
         (*      (fn (x, y) => Testing.success ("Parsing Json file " ^ y) |> print) *)
         (*      (res ~~ test_names); *)
         (*     List.app *)
         (*      (fn (Either.Left _) => *)
         (*          print (Testing.error "Parsing Json") *)
         (*      | (Either.Right _) => *)
         (*        print (Testing.success "Parsing Json Did not throw errors")) *)
         (*      (tests_parse test_handles) *)
         (*    ) *)
       (* end *)
       true
     else false
            (* print (Testing.error "One of the test files is not existent") *)
    )

fun single_test (name, (res, expected)) =
    name >+ assert_equal res expected

fun tests name  = name >++ List.map single_test (test_names ~~ (results ~~ expected))

fun check name =
      first_do "Checking for Files" (check_files ()) (tests name)

end
