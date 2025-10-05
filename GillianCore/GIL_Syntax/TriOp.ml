type t = TypeDef__.triop = Ite [@@deriving eq, ord]

let to_yojson = TypeDef__.triop_to_yojson
let of_yojson = TypeDef__.triop_of_yojson

let str (x : t) =
  match x with
  | Ite -> "Ite"
