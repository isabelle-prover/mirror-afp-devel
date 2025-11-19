structure BinIOUtil = struct
fun write v strm =
    BinIO.output (strm, v)

fun save_data filename magic_number data =
    let
      val strm = BinIO.openOut filename
      val _ = write magic_number strm
    in
      strm |> tap (write data) |> BinIO.closeOut
    end
end

structure TextIOUtil = struct
fun write text strm =
    TextIO.output (strm, text)

fun save_data filename data =
    let
      val strm = TextIO.openOut filename
    in
      strm |> tap (write data) |> TextIO.closeOut
    end

fun read_file file =
    let
      val stream = TextIO.openIn file
      fun all input =
          case TextIO.inputLine input of
              SOME line => (String.explode line
                           (* |> filter p *)
                           |> map (fn #"\t" => #" " |
                                      #"\n" => #" " |
                                      x => x)
                           |> String.implode) ^ all input |
              NONE => ""
      val str = all stream
    in
      (TextIO.closeIn stream; str)
    end

end
