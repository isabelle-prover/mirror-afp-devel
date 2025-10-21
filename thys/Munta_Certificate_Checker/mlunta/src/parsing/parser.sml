structure Parser = struct
fun parse json_str =
    let
      open Either
    in
      json_str
      |> tap (K (Log.info "Parsing JSON"))
      |> JsonP.parse
      |> bindR ParseJson.net
      |> tap (K (Log.info "Parsing Network Language"))
      |> bindR ParseBexps.network
    end
end
