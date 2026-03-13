let rec vsota_nar_st = function
  | 0 -> 0
  | n -> n + vsota_nar_st (n-1)

let is_prime = fun n ->
    let rec inn i n = if i*i > n then true else match (n mod i) with
      | 0 -> false
    | _ -> inn (i+1) n in
  inn 2 n

(*
let () = vsota_nar_st 9 |> Printf.printf "%d\n";
*)

let () = is_prime 11 |> Printf.printf "%B\n";
