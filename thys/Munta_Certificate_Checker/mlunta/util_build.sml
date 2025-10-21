structure Build = struct
fun subdir subdir files =
    app use (map (fn x => subdir ^ x ^ ".sml") files);
end
