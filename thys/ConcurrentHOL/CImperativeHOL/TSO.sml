(*
How does Poly/ML handle weak memory? (x86-only for now)

stock litmus test: under TSO both threads can read 0
on page 1 of https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.pdf

intuitively both threads buffer their writes and read from the main memory, allowing
them both to read 0, which is not a sequentially consistent behaviour.

emailed to David Matthews 2021-01-03
 *)

fun t0 lock x y done0 () = (
    while true do
      let val _ = while !lock do ();
          val _ = x := 1
          val yv = !y
          val _ = print ("t0: " ^ Int.toString yv ^ " ")
          val _ = done0 := true
          val _ = while not (!lock) do ();
          val _ = done0 := true
      in () end
);

fun t1 lock x y done1 () = (
    while true do
      let val _ = while !lock do ();
          val _ = y := 1
          val xv = !x
          val _ = print ("t1: " ^ Int.toString xv ^ " ")
          val _ = done1 := true
          val _ = while not (!lock) do ()
          val _ = done1 := true
      in () end
);

fun main () =
  let val lock = ref true
      val x = ref 0
      val y = ref 0
      val done0 = ref false
      val done1 = ref false
      val _ = Thread.Thread.fork (t0 lock x y done0, [])
      val _ = Thread.Thread.fork (t1 lock x y done1, [])
  in
      while true do (
(* TSO order ensures that writes to `x`, `y` are committed before `lock` is released *)
          lock := false;
          while not (!done0) orelse not (!done1) do ();
          print "\n";
          x := 0;
          y := 0;
          done0 := false;
          done1 := false;
          lock := true;
          while not (!done0) orelse not (!done1) do ();
          done0 := false;
          done1 := false
      )
  end
